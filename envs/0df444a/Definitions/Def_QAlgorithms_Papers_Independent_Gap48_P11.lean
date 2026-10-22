-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P11
-- name    : QAlgorithms_Papers_Independent_Gap48_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:28:34.449275+00:00
-- url     : https://prove2.me/theorems/57ac191c-65ac-4274-819a-397d40aae9fd
-- title:
--   Definitions for Composing Quantum Protocols in a Classical Environment
-- statement:
--   The objects the formalized statements of *Composing Quantum Protocols in a Classical Environment* (arXiv:0804.1059) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CQProbabilityBlocks`: PDF p.3: the subnormalized quantum block belonging to each classical label.
--   - `blockMatrix`: PDF p.3: diagonal embedding in the named classical computational basis.
--   - `IsNormalizedCQ`: PDF p.3: normalized positive density operator, with classical off-diagonal blocks zero.
--   - `classicalLabelMass`: PDF p.3: probability of the classical label, obtained by tracing its quantum block.
--   - `classicalPushforward`: PDF p.3: relabel classical registers and discard the unused labels by an actual sum.
--   - `IsExtension`: PDF p.3 and footnote 4: a single classical extension must preserve the original state exactly after discarding/relabeling its extra classical registers.
--   - `conditionalMarkovReconstruction`: PDF p.4: rho_{C <-> g(C) <-> E}; only the conditional quantum block is replaced. The actual classical law is retained. For a zero-mass fiber, its whole block is zero; no conditional state on an impossible fiber is asserted to be the zero density state.
--   - `cqDistance`: PDF p.4: closeness is half the trace norm of the full block-diagonal difference.
--   - `reconstructRight`: PDF p.4, Lemma 2.1(1): rho_{X <-> Y <-> ZE}, with Z retained in the right register. Its (x,y,z) block is P_XY(x,y)/P_Y(y) times the given (y,z,E) marginal.
--   - `productMarginals`: PDF pp.3–4, Lemma 2.1(2): rho_X tensor rho_ZE, both marginals of r.
--   - `uniformProduct`: PDF pp.3–4, Lemma 2.1(3): I/|X| tensor the actual rho_ZE marginal. Every use below has a nonempty X, so the reciprocal is not division by zero.
--   - `appendClassicalFunction`: PDF p.4, Lemma 2.2: append the computed value f(x,y); preserve X,Y and E.
--   - `eventProb`: PDF pp.3–4: probability of a deterministic event on the classical label.
--   - `conditioned`: PDF p.3, equation (1): condition the given classical law, preserving its quantum blocks. For an impossible event use the original normalized state as the arbitrary conditional version. Such a version is used only with its zero weight in Lemma 2.3.
-- source:
--   Composing Quantum Protocols in a Classical Environment, arXiv:0804.1059v2, https://arxiv.org/abs/0804.1059v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics

/-!
Fehr–Schaffner, arXiv:0804.1059v2, §2 and Appendix A, PDF pp.3–4,19.
Classical registers use finite alphabets. A block includes its classical probability;
positivity and total trace one enforce normalization. All marginal/reconstructed blocks
are computed from the given state. Zero-probability conditioning fibers contribute zero.
The local CQ names distinguish these concepts from unrelated short names in the
frozen catalogue (coordinate partitions, CQ channels, and matrix concatenation).
Protocol-level declarations are deferred in the assigned unit's HARD.md: no unrelated
channel fields are substituted for interactive execution or sequential substitution.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P11

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.3: the subnormalized quantum block belonging to each classical label. -/
abbrev CQProbabilityBlocks (C E : Type*) := C → Matrix E E ℂ

/-- PDF p.3: diagonal embedding in the named classical computational basis. -/
def blockMatrix {C E : Type*} (r : CQProbabilityBlocks C E) : Matrix (C × E) (C × E) ℂ :=
  fun a b => if a.1 = b.1 then r a.1 a.2 b.2 else 0

/-- PDF p.3: normalized positive density operator, with classical off-diagonal blocks zero. -/
def IsNormalizedCQ {C E : Type*} [Fintype C] [Fintype E] (r : CQProbabilityBlocks C E) : Prop :=
  QAlgorithms.IsDensityMatrix (blockMatrix r)

/-- PDF p.3: probability of the classical label, obtained by tracing its quantum block. -/
def classicalLabelMass {C E : Type*} [Fintype E] (r : CQProbabilityBlocks C E) (c : C) : ℝ :=
  (r c).trace.re

/-- PDF p.3: relabel classical registers and discard the unused labels by an actual sum. -/
def classicalPushforward {C D E : Type*} [Fintype C] (r : CQProbabilityBlocks C E) (g : C → D) : CQProbabilityBlocks D E :=
  fun d => ∑ c, if g c = d then r c else 0

/-- PDF p.3 and footnote 4: a single classical extension must preserve the original
state exactly after discarding/relabeling its extra classical registers. -/
def IsExtension {C D E : Type*} [Fintype C] [Fintype D] [Fintype E]
    (r : CQProbabilityBlocks C E) (s : CQProbabilityBlocks D E) (forget : D → C) : Prop :=
  IsNormalizedCQ s ∧ classicalPushforward s forget = r

/-- PDF p.4: rho_{C <-> g(C) <-> E}; only the conditional quantum block is replaced.
The actual classical law is retained. For a zero-mass fiber, its whole block is zero;
no conditional state on an impossible fiber is asserted to be the zero density state. -/
def conditionalMarkovReconstruction {C D E : Type*} [Fintype C] [Fintype E]
    (r : CQProbabilityBlocks C E) (g : C → D) : CQProbabilityBlocks C E :=
  fun c => ((classicalLabelMass r c / classicalLabelMass (classicalPushforward r g) (g c) : ℝ) : ℂ) • classicalPushforward r g (g c)

/-- PDF p.4: closeness is half the trace norm of the full block-diagonal difference. -/
def cqDistance {C E : Type*} [Fintype C] [Fintype E]
    (r s : CQProbabilityBlocks C E) : ℝ :=
  QAlgorithms.traceDistance (blockMatrix r) (blockMatrix s)

/-- PDF p.4, Lemma 2.1(1): rho_{X <-> Y <-> ZE}, with Z retained in the right register.
Its (x,y,z) block is P_XY(x,y)/P_Y(y) times the given (y,z,E) marginal. -/
def reconstructRight {X Y Z E : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype E] (r : CQProbabilityBlocks (X × Y × Z) E) : CQProbabilityBlocks (X × Y × Z) E :=
  fun c =>
    ((classicalLabelMass (classicalPushforward r (fun t => (t.1, t.2.1))) (c.1, c.2.1) /
      classicalLabelMass (classicalPushforward r (fun t => t.2.1)) c.2.1 : ℝ) : ℂ) •
        classicalPushforward r (fun t => t.2) c.2

/-- PDF pp.3–4, Lemma 2.1(2): rho_X tensor rho_ZE, both marginals of r. -/
def productMarginals {X Z E : Type*} [Fintype X] [Fintype Z] [Fintype E]
    (r : CQProbabilityBlocks (X × Z) E) : CQProbabilityBlocks (X × Z) E :=
  fun c => (classicalLabelMass (classicalPushforward r Prod.fst) c.1 : ℂ) • classicalPushforward r Prod.snd c.2

/-- PDF pp.3–4, Lemma 2.1(3): I/|X| tensor the actual rho_ZE marginal.
Every use below has a nonempty X, so the reciprocal is not division by zero. -/
def uniformProduct {X Z E : Type*} [Fintype X] [Fintype Z]
    (r : CQProbabilityBlocks (X × Z) E) : CQProbabilityBlocks (X × Z) E :=
  fun c => ((Fintype.card X : ℂ)⁻¹) • classicalPushforward r Prod.snd c.2

/-- PDF p.4, Lemma 2.2: append the computed value f(x,y); preserve X,Y and E. -/
def appendClassicalFunction {X Y T E : Type*} (r : CQProbabilityBlocks (X × Y) E) (f : X → Y → T) :
    CQProbabilityBlocks ((X × T) × Y) E :=
  fun c => if c.1.2 = f c.1.1 c.2 then r (c.1.1, c.2) else 0

/-- PDF pp.3–4: probability of a deterministic event on the classical label. -/
def eventProb {C E : Type*} [Fintype C] [Fintype E]
    (r : CQProbabilityBlocks C E) (event : C → Prop) : ℝ :=
  ∑ c, if event c then classicalLabelMass r c else 0

/-- PDF p.3, equation (1): condition the given classical law, preserving its quantum blocks.
For an impossible event use the original normalized state as the arbitrary conditional
version. Such a version is used only with its zero weight in Lemma 2.3. -/
def conditioned {C E : Type*} [Fintype C] [Fintype E]
    (r : CQProbabilityBlocks C E) (event : C → Prop) : CQProbabilityBlocks C E :=
  if 0 < eventProb r event then
    fun c => if event c then ((eventProb r event)⁻¹ : ℂ) • r c else 0
  else r

/-- PDF p.3 sanity case: a singleton classical label embeds exactly its density block. -/
example {E : Type*} (a : Matrix E E ℂ) (i j : E) :
    blockMatrix (fun _ : Unit => a) ((), i) ((), j) = a i j := by
  simp [blockMatrix]

/-- PDF p.3 sanity case: the singleton classical and quantum state is admissible. -/
example : IsNormalizedCQ (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) := by
  have h : blockMatrix (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) =
      (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ) := by
    ext a b
    have hab : a = b := Subsingleton.elim _ _
    subst b
    simp [blockMatrix, Matrix.one_apply]
  rw [IsNormalizedCQ, h]
  exact ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩

/-- PDF p.3 sanity case: the zero matrix is excluded even when the classical alphabet is empty. -/
example {C E : Type*} [Fintype C] [Fintype E] :
    ¬ IsNormalizedCQ (0 : CQProbabilityBlocks C E) := by
  simp [IsNormalizedCQ, blockMatrix, QAlgorithms.IsDensityMatrix, Matrix.trace]

/-- PDF pp.3–4 sanity case: an impossible event has zero probability and zero weighted
contribution, without a positive-probability-event hypothesis on Lemma 2.3. -/
example {C E : Type*} [Fintype C] [Fintype E] (r : CQProbabilityBlocks C E) :
    eventProb r (fun _ => False) = 0 ∧
      (0 : ℂ) • conditionalMarkovReconstruction (conditioned r (fun _ => False)) (fun _ => ()) = 0 := by
  simp [eventProb]

/-- PDF p.4 sanity case: reconstruction with the complete classical label keeps every
positive-mass block, rather than requiring all blocks to have positive mass. -/
example {C E : Type*} [Fintype C] [Fintype E] (r : CQProbabilityBlocks C E) (c : C)
    (hc : classicalLabelMass r c ≠ 0) : conditionalMarkovReconstruction r id c = r c := by
  have hm : classicalPushforward r id = r := by
    funext d
    simp [classicalPushforward]
  simp [conditionalMarkovReconstruction, hm, hc]

/-- PDF p.3 sanity case: adding no registers is an exact classical extension. -/
example {C E : Type*} [Fintype C] [Fintype E] (r : CQProbabilityBlocks C E) (hr : IsNormalizedCQ r) :
    IsExtension r r id := by
  refine ⟨hr, ?_⟩
  funext c
  simp [classicalPushforward]

/-- PDF p.4 sanity case: deterministic augmentation copies Y when f(x,y)=y. -/
example {X Y E : Type*} (r : CQProbabilityBlocks (X × Y) E) (x : X) (y : Y) :
    appendClassicalFunction r (fun _ y => y) ((x, y), y) = r (x, y) := by
  simp [appendClassicalFunction]

end QAlgorithms.Papers.Independent.Gap48.P11


