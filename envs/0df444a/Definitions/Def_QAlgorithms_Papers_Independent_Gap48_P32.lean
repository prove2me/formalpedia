-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
-- name    : QAlgorithms_Papers_Independent_Gap48_P32
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:25:09.729702+00:00
-- url     : https://prove2.me/theorems/4597e155-fa13-46a4-9d47-b9729279288e
-- title:
--   Definitions for "Squashed Entanglement" - An Additive Entanglement Measure
-- statement:
--   The objects the formalized statements of *"Squashed Entanglement" - An Additive Entanglement Measure* (arXiv:quant-ph/0308088) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pairOfState`: PDF p.2, Proposition 3: only change the two-party dependent-function basis of the accepted selective LOCC states into the ordinary product basis.
--   - `fannesEta`: PDF p.6, Lemma 13: the source's universal concave eta function, in bits. The physical domain is x >= 0; at x=0 the value is 0.
--   - `ConditionalFannesConjecture`: PDF p.6, Conjecture 14, as a HYPOTHESIS, uniform in all finite B dimensions. No theorem here asserts this predicate without assuming it.
--   - `UniformExtensionBound`: PDF p.6: a SINGLE dimension bound, preceding rho and every extension. This is a conditional assumption, not a claimed dimension bound.
--   - `DistillationRate`: PDF p.4, Proposition 10: operational two-way LOCC distillation rate. All sufficiently large positive block lengths admit full unconditional outputs, with vanishing full trace norm error and log2(Schmidt rank)/n rate. The target rank l=1 is allowed, including at rate zero.
--   - `twoWayDistillable`: PDF p.4, Proposition 10: supremum of the actual LOCC distillation rates. For density matrices in positive dimensions the set contains zero and is bounded by the smaller marginal entropy. Nonphysical inputs are never used in results.
--   - `antisymmetricQutrit`: PDF p.4, Example 9: normalized projector onto the two-qutrit antisymmetric subspace. (I-F)/6 equals the displayed mixture of the three antisymmetric kets.
--   - `commonBasisCQ`: PDF p.7, (A1)--(A2): a CQ state in the orthonormal basis of columns of U. The same U is used for the two states in the theorem.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, https://arxiv.org/abs/quant-ph/0308088v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42

/-!
Christandl--Winter, arXiv:quant-ph/0308088v3. Finite positive-dimensional
registers, normalized states, bit entropies, and the full trace norm throughout.
The accepted squashed value ranges over all positive finite extension dimensions.
Compilation is pending the separate mechanical handoff.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

local notation "sq" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed
local notation "cmi" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual
local notation "mi" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
local notation "ef" => QAlgorithms.Papers.Independent.Information100.P08.formation

-- Reuse exact accepted generic tensor pairing and partial traces.
open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)
open QAlgorithms.Papers.Independent.Information100.P08 (firstPair secondPair)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- PDF p.2, Proposition 3: only change the two-party dependent-function basis
of the accepted selective LOCC states into the ordinary product basis. -/
def pairOfState (s : QAlgorithms.Papers.Independent.Claimed50.P33.FiniteState 2) :
    Matrix (Fin (s.dims 0) × Fin (s.dims 1)) (Fin (s.dims 0) × Fin (s.dims 1)) ℂ :=
  fun p q => s.rho (Fin.cases p.1 (Fin.cases p.2 (fun i => Fin.elim0 i)))
    (Fin.cases q.1 (Fin.cases q.2 (fun i => Fin.elim0 i)))

/-- PDF p.6, Lemma 13: the source's universal concave eta function, in bits.
The physical domain is x >= 0; at x=0 the value is 0. -/
def fannesEta (x : ℝ) : ℝ := if x ≤ 1/4 then -x * Real.logb 2 x else 1/2

/-- PDF p.6, Conjecture 14, as a HYPOTHESIS, uniform in all finite B dimensions.
No theorem here asserts this predicate without assuming it. -/
def ConditionalFannesConjecture : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b →
  ∀ rho sigma : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
    IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ epsilon : ℝ, 0 ≤ epsilon → traceNorm (rho-sigma) ≤ epsilon →
    |conditionalEntropy rho - conditionalEntropy sigma| ≤
      fannesEta (2*epsilon) + 3*epsilon*Real.logb 2 a

/-- PDF p.6: a SINGLE dimension bound, preceding rho and every extension.
This is a conditional assumption, not a claimed dimension bound. -/
def UniformExtensionBound {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (d : ℕ) : Prop :=
  ∀ rho : Matrix (A × B) (A × B) ℂ, IsDensityMatrix rho →
  ∀ e : ℕ, 0 < e →
  ∀ omega : Matrix ((A × B) × Fin e) ((A × B) × Fin e) ℂ,
    IsDensityMatrix omega → traceRight omega = rho →
    ∃ tau : Matrix ((A × B) × Fin d) ((A × B) × Fin d) ℂ,
      IsDensityMatrix tau ∧ traceRight tau = rho ∧ cmi tau ≤ cmi omega

/-- PDF p.4, Proposition 10: operational two-way LOCC distillation rate.
All sufficiently large positive block lengths admit full unconditional outputs,
with vanishing full trace norm error and log2(Schmidt rank)/n rate.
The target rank l=1 is allowed, including at rate zero. -/
def DistillationRate {a b : ℕ}
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → 0 < n → ∃ l : ℕ, 0 < l ∧
    n * (R-delta) ≤ Real.logb 2 l ∧
    ∃ L : Superop (Fin (a^n) × Fin (b^n)) (Fin l × Fin l),
      QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC L ∧
      traceNorm (L (QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower rho n) -
        QAlgorithms.Papers.Independent.Dependency50.P19.epr l) ≤ epsilon

/-- PDF p.4, Proposition 10: supremum of the actual LOCC distillation rates.
For density matrices in positive dimensions the set contains zero and is bounded
by the smaller marginal entropy. Nonphysical inputs are never used in results. -/
def twoWayDistillable {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ :=
  sSup {R : ℝ | DistillationRate rho R}

/-- PDF p.4, Example 9: normalized projector onto the two-qutrit antisymmetric
subspace. (I-F)/6 equals the displayed mixture of the three antisymmetric kets. -/
def antisymmetricQutrit : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun i j => ((if i=j then 1 else 0) -
    (if i.1=j.2 ∧ i.2=j.1 then 1 else 0)) / 6

/-- PDF p.7, (A1)--(A2): a CQ state in the orthonormal basis of columns of U.
The same U is used for the two states in the theorem. -/
def commonBasisCQ {A B : Type} [Fintype B]
    (p : B → ℝ) (rho : B → Matrix A A ℂ) (U : Matrix B B ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  fun i j => ∑ k, (p k : ℂ) * rho k i.1 j.1 * U i.2 k * conj (U j.2 k)

/-- Regrouping keeps both factors' off-diagonal entries (PDF p.3). -/
example {A A1 B B1 : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix (A1 × B1) (A1 × B1) ℂ) (a a2 : A) (a1 a3 : A1)
    (b b2 : B) (b1 b3 : B1) :
    regroupProduct rho sigma ((a,a1),(b,b1)) ((a2,a3),(b2,b3)) =
      rho (a,b) (a2,b2) * sigma (a1,b1) (a3,b3) := rfl

/-- Eta has the required zero-error value (PDF p.6). -/
example : fannesEta 0 = 0 := by norm_num [fannesEta]

/-- The constant branch has value 1/2 above the cutoff (PDF p.6). -/
example : fannesEta 1 = 1/2 := by norm_num [fannesEta]

/-- The antisymmetric matrix kills |00> and gives the correct off-diagonal sign. -/
example : antisymmetricQutrit (0,0) (0,0) = 0 ∧
    antisymmetricQutrit (0,1) (1,0) = -(1/6 : ℂ) := by
  norm_num [antisymmetricQutrit]

/-- The two-register LOCC adapter is a basis relabeling, not a reduction (PDF p.2). -/
example (s : QAlgorithms.Papers.Independent.Claimed50.P33.FiniteState 2)
    (p q : Fin (s.dims 0) × Fin (s.dims 1)) :
    pairOfState s p q = s.rho (Fin.cases p.1 (Fin.cases p.2 (fun i => Fin.elim0 i)))
      (Fin.cases q.1 (Fin.cases q.2 (fun i => Fin.elim0 i))) := rfl

/-- Tracing singleton primed factors changes no matrix entry (PDF p.3). -/
example {A B : Type}
    (rho : Matrix ((A × Unit) × (B × Unit)) ((A × Unit) × (B × Unit)) ℂ)
    (i j : A × B) : firstPair rho i j = rho ((i.1,()),(i.2,())) ((j.1,()),(j.2,())) := by
  simp [firstPair]

/-- Tracing singleton unprimed factors changes no matrix entry (PDF p.3). -/
example {A1 B1 : Type}
    (rho : Matrix ((Unit × A1) × (Unit × B1)) ((Unit × A1) × (Unit × B1)) ℂ)
    (i j : A1 × B1) : secondPair rho i j = rho (((),i.1),((),i.2)) (((),j.1),((),j.2)) := by
  simp [secondPair]

/-- A common one-dimensional classical register is exactly a weighted A state (PDF p.7). -/
example {A : Type} (p : Unit → ℝ) (rho : Unit → Matrix A A ℂ) (i j : A) :
    commonBasisCQ p rho (1 : Matrix Unit Unit ℂ) (i,()) (j,()) = (p () : ℂ) * rho () i j := by
  simp [commonBasisCQ]

/-- The conjectural bound specializes at equal one-dimensional states (PDF p.6). -/
example (h : ConditionalFannesConjecture)
    (rho : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
    (hrho : IsDensityMatrix rho) :
    |conditionalEntropy rho - conditionalEntropy rho| ≤
      fannesEta (2 * 0) + 3 * 0 * Real.logb 2 (1 : ℕ) :=
  h 1 1 (by decide) (by decide) rho rho hrho hrho 0 (by norm_num)
    (by simp [traceNorm, cfc_zero])

/-- A uniform bound supplies a genuine bounded-size witness (PDF p.6). -/
example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (d : ℕ) (h : UniformExtensionBound (A := A) (B := B) d)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (omega : Matrix ((A × B) × Fin 1) ((A × B) × Fin 1) ℂ)
    (homega : IsDensityMatrix omega) (htrace : traceRight omega = rho) :
    ∃ tau : Matrix ((A × B) × Fin d) ((A × B) × Fin d) ℂ,
      IsDensityMatrix tau ∧ traceRight tau = rho ∧ cmi tau ≤ cmi omega :=
  h rho hrho 1 (by decide) omega homega htrace

/-- The operational value is the supremum of precisely these rates (PDF p.4). -/
example {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    twoWayDistillable rho = sSup {R : ℝ | DistillationRate rho R} := rfl

/-- Achievable distillation rates cannot be negative (PDF p.4). -/
example {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (R : ℝ) (h : DistillationRate rho R) : 0 ≤ R := h.1

section Bipartite

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [instAne : Nonempty A] [instBne : Nonempty B]

include instAne instBne

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32


