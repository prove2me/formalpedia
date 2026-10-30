-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P07
-- name    : QAlgorithms_Papers_Independent_Extend50_P07
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T15:37:21.982892+00:00
-- url     : https://prove2.me/theorems/f0d94e2a-d4b5-4ff7-9b46-40f308dd3e88
-- title:
--   Definitions for Universal construction of decoders from encoding black boxes
-- statement:
--   The objects the formalized statements of *Universal construction of decoders from encoding black boxes* (arXiv:2110.00258) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Isometry`: PDF p.4, Eq. (1): finite isometries in computational coordinates.
--   - `tensorRight`: PDF p.5, Eq. (4): a map on the first factor, with the second factor untouched. Off-diagonal blocks of the auxiliary register are retained.
--   - `Parallel`: PDF pp.5--6, Eq. (4): exactly k parallel oracle slots, finite auxiliary space, fixed preprocessing and fixed final instrument. None of these fields takes V.
--   - `Parallel.run`: PDF p.5, Eq. (4): successful branch on an arbitrary joint input operation.
--   - `Delayed`: PDF p.9, Eqs. (10)--(11): the oracle is applied to a fixed resource state before the eventual input arrives. The input is retained as a separate register.
--   - `Delayed.run`: PDF p.9, Eq. (10): successful delayed-input branch, including the resource correlations with its auxiliary space.
--   - `oracleCopies`: PDF p.6: all k slots receive the same unknown channel.
--   - `ExactInverse`: PDF p.4, Eq. (2), and p.6, Eq. (5): an exact CP left inverse on every operator, with the entire successful branch equal to p times that inverse. In particular p=0 forces a zero branch even off the code.
--   - `inversionProbabilities`: PDF pp.6--8: feasible uniform parallel inversion coefficients.
--   - `inversionOpt`: PDF p.8, Eq. (8): optimal parallel coefficient. For positive d≤D the feasible set contains zero (abort) and is bounded above by one by definition.
--   - `inversionBound`: PDF pp.7--8: Figure 2(a)'s coefficient. Zero ports mean abort, without calling a zero-port teleportation construction. The formula is used only for d≥2.
--   - `decoder`: PDF p.7, Eq. (7): full off-code decoder. The identity is not divided by d.
--   - `pseudoConjugate`: PDF p.21, Eq. (60): the full pseudo complex-conjugate CP map.
--   - `transposeChoi`: PDF pp.6,22, Eq. (65): Kraus transposition swaps Choi legs, without conjugating coefficients and without merely transposing the Choi matrix.
--   - `completeAction`: PDF pp.17--18: complete extension of a k-slot linear supermap. Each slot has arbitrary ancillary input and output; the auxiliary coherences are retained. This tests individual channel slots, not a joint channel allowed to signal between slots.
--   - `General`: PDF pp.17--18: general two-outcome superinstrument, including indefinite causal order. Positivity is complete CP preservation. Normalization tests all ancillary input/output extensions of each individual CPTP slot.
--   - `General.run`: PDF p.6, Eq. (5), for the general class: every slot gets the same V.
--   - `General.draw`: PDF p.23, Eq. (69): the unsuccessful branch of a general protocol.
--   - `transposeSuperChoi`: PDF p.38, Eq. (155), in the fixed (slot, past/future) ordering: p D d times the two normalized maximally entangled projectors.
--   - `oneSlot`: PDF p.38: identify a single input slot with the one-letter tensor word.
--   - `gateTeleport`: PDF pp.22--23, Figure 9: normalized entangled resource (factor 1/d) and successful Bell projection (factor 1/D), written as their contraction.
--   - `embedding`: PDF p.15, Eq. (38): fixed natural computational embedding, not chosen from V.
--   - `RoundTree`: PDF pp.23--24: a finite protocol tree. Each attempt executes the supplied k-slot instrument once, stops on success, and continues only on a draw.
--   - `RoundTree.queryCount`: PDF p.24: worst-case query count, obtained from the actual attempt nodes.
--   - `RoundTree.success`: PDF pp.23--24: successful operation of the finite tree, with early exit.
--   - `RoundTree.failure`: PDF pp.23--24: the branch where all attempts draw.
--   - `repeatProtocol`: PDF p.24: the constructed m-round repetition of a single supplied protocol.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, https://arxiv.org/abs/2110.00258v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

/-!
Yoshida--Soeda--Murao, arXiv:2110.00258v5 (PDF page numbers).
All registers have fixed computational coordinates. Choi matrices are unnormalized,
input first. Probabilities in the statements are the scale in Eq. (5).
New definitions are local to this paper; the accepted definition layer is unchanged.
Coordinate, CP and instrument interfaces are imported from pinned accepted modules.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P07

-- Reuse pinned accepted interfaces; no duplicate declarations or exported aliases.
open QAlgorithms.Papers.Independent.Information100.P75 (Mat)
open QAlgorithms.Papers.Independent.Information100.P58 (Word)
open QAlgorithms.Papers.Independent.Information100.P06 (Choi)
open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)
open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)
open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)
open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

/-- PDF p.4, Eq. (1): finite isometries in computational coordinates. -/
def Isometry (d D : ℕ) :=
  {V : Matrix (Fin D) (Fin d) ℂ // Vᴴ * V = 1}

/-- PDF p.5, Eq. (4): a map on the first factor, with the second factor untouched.
Off-diagonal blocks of the auxiliary register are retained. -/
def tensorRight {I O A : Type} (Phi : Superop I O) : Superop (I × A) (O × A) :=
  fun X a b => Phi (fun i j => X (i, a.2) (j, b.2)) a.1 b.1

/-- PDF pp.5--6, Eq. (4): exactly k parallel oracle slots, finite auxiliary
space, fixed preprocessing and fixed final instrument. None of these fields takes V. -/
structure Parallel (d D P F k : ℕ) where
  memory : ℕ
  memoryPos : 0 < memory
  pre : Superop (Fin P) (Word k d × Fin memory)
  preTP : IsChannel pre
  post : RectangularInstrument (Word k D × Fin memory) (Fin F) Bool

/-- PDF p.5, Eq. (4): successful branch on an arbitrary joint input operation. -/
def Parallel.run {d D P F k : ℕ} (A : Parallel d D P F k)
    (Lambda : Superop (Word k d) (Word k D)) : Superop (Fin P) (Fin F) :=
  fun X => A.post.branch false (tensorRight Lambda (A.pre X))

/-- PDF p.9, Eqs. (10)--(11): the oracle is applied to a fixed resource state
before the eventual input arrives. The input is retained as a separate register. -/
structure Delayed (d D P F k : ℕ) where
  memory : ℕ
  memoryPos : 0 < memory
  resource : Mat (Word k d × Fin memory)
  resourceState : IsDensityMatrix resource
  post : RectangularInstrument (Fin P × (Word k D × Fin memory)) (Fin F) Bool

/-- PDF p.9, Eq. (10): successful delayed-input branch, including the resource
correlations with its auxiliary space. -/
def Delayed.run {d D P F k : ℕ} (A : Delayed d D P F k)
    (Lambda : Superop (Word k d) (Word k D)) : Superop (Fin P) (Fin F) :=
  fun X => A.post.branch false (Matrix.kronecker X (tensorRight Lambda A.resource))

/-- PDF p.6: all k slots receive the same unknown channel. -/
def oracleCopies {d D : ℕ} (k : ℕ) (V : Isometry d D) :
    Superop (Word k d) (Word k D) :=
  piSuperop (fun _ => conjSuperop V.val)

/-- PDF p.4, Eq. (2), and p.6, Eq. (5): an exact CP left inverse on every
operator, with the entire successful branch equal to p times that inverse.
In particular p=0 forces a zero branch even off the code. -/
def ExactInverse {d D : ℕ} (B : Superop (Fin D) (Fin d)) (p : ℝ)
    (V : Isometry d D) : Prop :=
  ∃ R : Superop (Fin D) (Fin d), FiniteKrausCP R ∧
    (∀ X, R (conjSuperop V.val X) = X) ∧ (∀ Y, B Y = (p : ℂ) • R Y)

/-- PDF pp.6--8: feasible uniform parallel inversion coefficients. -/
def inversionProbabilities (d D k : ℕ) : Set ℝ :=
  {p | 0 ≤ p ∧ p ≤ 1 ∧ ∃ A : Parallel d D D d k,
    ∀ V : Isometry d D, ExactInverse (A.run (oracleCopies k V)) p V}

/-- PDF p.8, Eq. (8): optimal parallel coefficient. For positive d≤D the
feasible set contains zero (abort) and is bounded above by one by definition. -/
def inversionOpt (d D k : ℕ) : ℝ := sSup (inversionProbabilities d D k)

/-- PDF pp.7--8: Figure 2(a)'s coefficient. Zero ports mean abort, without
calling a zero-port teleportation construction. The formula is used only for d≥2. -/
def inversionBound (d k : ℕ) : ℝ :=
  let m := k / (d - 1)
  if m = 0 then 0 else (m : ℝ) / ((d : ℝ)^2 + (m : ℝ) - 1)

/-- PDF p.7, Eq. (7): full off-code decoder. The identity is not divided by d. -/
def decoder {d D : ℕ} (V : Isometry d D) : Superop (Fin D) (Fin d) :=
  fun X => V.valᴴ * X * V.val + ((1 - V.val * V.valᴴ) * X).trace • 1

/-- PDF p.21, Eq. (60): the full pseudo complex-conjugate CP map. -/
def pseudoConjugate {d D : ℕ} (V : Isometry d D) : Superop (Fin d) (Fin D) :=
  fun X => conjSuperop (V.val.map conj) X +
    X.trace • ((1 - V.val * V.valᴴ).map conj)

/-- PDF pp.6,22, Eq. (65): Kraus transposition swaps Choi legs, without
conjugating coefficients and without merely transposing the Choi matrix. -/
def transposeChoi {I O : Type} (J : Choi I O) : Choi O I :=
  fun a b => J (a.2, a.1) (b.2, b.1)

/-- PDF pp.17--18: complete extension of a k-slot linear supermap. Each slot
has arbitrary ancillary input and output; the auxiliary coherences are retained.
This tests individual channel slots, not a joint channel allowed to signal between slots. -/
def completeAction {d D P F k : ℕ}
    (S : Choi (Word k d) (Word k D) →ₗ[ℂ] Choi (Fin P) (Fin F))
    (r s : Fin k → ℕ)
    (J : (i : Fin k) → Choi (Fin (r i) × Fin d) (Fin (s i) × Fin D)) :
    Choi (Fin P × ((i : Fin k) → Fin (r i)))
      (Fin F × ((i : Fin k) → Fin (s i))) :=
  fun a b =>
    S (fun u v => ∏ i,
      J i ((a.1.2 i, u.1 i), (a.2.2 i, u.2 i))
        ((b.1.2 i, v.1 i), (b.2.2 i, v.2 i)))
      (a.1.1, a.2.1) (b.1.1, b.2.1)

/-- PDF pp.17--18: general two-outcome superinstrument, including indefinite
causal order. Positivity is complete CP preservation. Normalization tests all
ancillary input/output extensions of each individual CPTP slot. -/
structure General (d D P F k : ℕ) where
  success : Choi (Word k d) (Word k D) →ₗ[ℂ] Choi (Fin P) (Fin F)
  failure : Choi (Word k d) (Word k D) →ₗ[ℂ] Choi (Fin P) (Fin F)
  successCP : (choi success).PosSemidef
  failureCP : (choi failure).PosSemidef
  complete : ∀ r s : Fin k → ℕ, (∀ i, 0 < r i) → (∀ i, 0 < s i) →
    ∀ J : (i : Fin k) → Choi (Fin (r i) × Fin d) (Fin (s i) × Fin D),
      (∀ i, ChannelChoi (J i)) →
      (completeAction success r s J).PosSemidef ∧
      (completeAction failure r s J).PosSemidef ∧
      ChannelChoi (completeAction success r s J + completeAction failure r s J)

/-- PDF p.6, Eq. (5), for the general class: every slot gets the same V. -/
def General.run {d D P F k : ℕ} (A : General d D P F k)
    (V : Isometry d D) : Superop (Fin P) (Fin F) :=
  fromChoi (A.success (choi (oracleCopies k V)))

/-- PDF p.23, Eq. (69): the unsuccessful branch of a general protocol. -/
def General.draw {d D P F k : ℕ} (A : General d D P F k)
    (V : Isometry d D) : Superop (Fin P) (Fin F) :=
  fromChoi (A.failure (choi (oracleCopies k V)))

/-- PDF p.38, Eq. (155), in the fixed (slot, past/future) ordering:
p D d times the two normalized maximally entangled projectors. -/
def transposeSuperChoi (d D : ℕ) (p : ℝ) :
    Mat ((Word 1 d × Word 1 D) × (Fin D × Fin d)) :=
  fun a b => if a.1.2 0 = a.2.1 ∧ a.1.1 0 = a.2.2 ∧
      b.1.2 0 = b.2.1 ∧ b.1.1 0 = b.2.2 then (p : ℂ) else 0

/-- PDF p.38: identify a single input slot with the one-letter tensor word. -/
def oneSlot {d D : ℕ} (J : Choi (Fin d) (Fin D)) : Choi (Word 1 d) (Word 1 D) :=
  fun a b => J (a.1 0, a.2 0) (b.1 0, b.2 0)

/-- PDF pp.22--23, Figure 9: normalized entangled resource (factor 1/d)
and successful Bell projection (factor 1/D), written as their contraction. -/
def gateTeleport {d D : ℕ} (Lambda : Superop (Fin d) (Fin D)) :
    Superop (Fin D) (Fin d) :=
  fun X i j => (1 / ((D : ℂ) * (d : ℂ))) *
    ∑ o, ∑ q, X o q * Lambda (Matrix.single i j 1) o q

/-- PDF p.15, Eq. (38): fixed natural computational embedding, not chosen from V. -/
def embedding (d D : ℕ) : Matrix (Fin D) (Fin d) ℂ :=
  fun o i => if o.val = i.val then 1 else 0

/-- PDF pp.23--24: a finite protocol tree. Each attempt executes the supplied
k-slot instrument once, stops on success, and continues only on a draw. -/
inductive RoundTree (d D k : ℕ) where
  | stop
  | attempt (round : General d D D D k) (next : RoundTree d D k)

/-- PDF p.24: worst-case query count, obtained from the actual attempt nodes. -/
def RoundTree.queryCount {d D k : ℕ} : RoundTree d D k → ℕ
  | .stop => 0
  | .attempt _ next => k + next.queryCount

/-- PDF pp.23--24: successful operation of the finite tree, with early exit. -/
def RoundTree.success {d D k : ℕ} :
    RoundTree d D k → Isometry d D → Superop (Fin D) (Fin D)
  | .stop, _ => fun _ => 0
  | .attempt A next, V => fun X => A.run V X + next.success V (A.draw V X)

/-- PDF pp.23--24: the branch where all attempts draw. -/
def RoundTree.failure {d D k : ℕ} :
    RoundTree d D k → Isometry d D → Superop (Fin D) (Fin D)
  | .stop, _ => id
  | .attempt A next, V => fun X => next.failure V (A.draw V X)

/-- PDF p.24: the constructed m-round repetition of a single supplied protocol. -/
def repeatProtocol {d D k : ℕ} (A : General d D D D k) : ℕ → RoundTree d D k
  | 0 => .stop
  | m + 1 => .attempt A (repeatProtocol A m)

/-! Small semantic checks; no theorem proofs from the paper are attempted. -/

example {I A : Type} (X : Mat (I × A)) :
    tensorRight (fun Y : Mat I => Y) X = X := by
  rfl

example {I O : Type} (J : Choi I O) :
    transposeChoi (transposeChoi J) = J := by
  rfl

example (d : ℕ) : inversionBound d 0 = 0 := by
  simp [inversionBound]

example {d D k : ℕ} (A : General d D D D k) :
    (repeatProtocol A 0).queryCount = 0 := by
  rfl

example {d D k : ℕ} (A : General d D D D k) (V : Isometry d D)
    (X : Mat (Fin D)) : (repeatProtocol A 1).success V X = A.run V X := by
  simp [repeatProtocol, RoundTree.success]

example (d D : ℕ) (i : Fin d) (o : Fin D) (h : o.val = i.val) :
    embedding d D o i = 1 := by
  simp [embedding, h]

example {I O : Type} [Fintype I] : FiniteKrausCP (fun _ : Mat I => (0 : Mat O)) := by
  refine ⟨0, fun i => Fin.elim0 i, ?_⟩
  funext X
  simp [krausApply]

example {I O : Type} [Fintype I] :
    fromChoi (0 : Choi I O) = (fun _ : Mat I => (0 : Mat O)) := by
  funext X a b
  simp [fromChoi]

example {d D P F k : ℕ} (r s : Fin k → ℕ)
    (J : (i : Fin k) → Choi (Fin (r i) × Fin d) (Fin (s i) × Fin D)) :
    completeAction (0 : Choi (Word k d) (Word k D) →ₗ[ℂ]
      Choi (Fin P) (Fin F)) r s J = 0 := by
  rfl

example (d : ℕ) (X : Mat (Fin d)) :
    decoder (⟨1, by simp⟩ : Isometry d d) X = X := by
  simp [decoder]

end QAlgorithms.Papers.Independent.Extend50.P07


