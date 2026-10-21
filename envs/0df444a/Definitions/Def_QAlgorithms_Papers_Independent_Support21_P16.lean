-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16
-- name    : QAlgorithms_Papers_Independent_Support21_P16
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T04:35:46.943414+00:00
-- url     : https://prove2.me/theorems/bceab199-e5c5-407c-8e86-ccdfbb76a0ba
-- title:
--   Definitions for Optimal Cloning of Pure States
-- statement:
--   The objects the formalized statements of *Optimal Cloning of Pure States* (arXiv:quant-ph/9804001) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TensorSpace`: PDF pp.3,5: the full n-system Hilbert space, with its L2 inner product.
--   - `CloneMap`: PDF pp.4–6: unbundled Schroedinger map; admissibility supplies linearity.
--   - `coherentTensor`: PDF pp.5–6: the frozen tensor-vector coordinates, packaged with the L2 norm.
--   - `boseSpace`: PDF p.5: the actual subspace fixed by EVERY tensor-factor permutation.
--   - `BoseSupported`: PDF p.6: both sides of an operator are supported on the Bose subspace.
--   - `boseDimension`: PDF p.5 Eq.(3.2): symmetric dimension, using the final natural binomial.
--   - `BoseOccupation`: PDF p.5: occupation tuples, finitely bounded by n and with EXACT total n.
--   - `occupationKet`: PDF p.5 Eq.(3.1): explicit positive real normalized occupation vector. Every word with the given occupation has amplitude sqrt(prod_a o_a! / n!).
--   - `occupationEmbedding`: PDF p.5: the concrete real embedding from occupation coordinates to words.
--   - `occupationCoefficient`: PDF p.5 Eq.(3.1): coefficient of the occupation vector in phi tensor n.
--   - `boseMixed`: PDF p.6: tau_n is the maximally mixed state on the Bose sector.
--   - `oneMixed`: PDF p.7: the one-particle maximally mixed state, in one-particle coordinates.
--   - `IsBoseInputChannel`: PDF pp.4–6: linear completely positive corner-input channel. The map is canonically zero-extended; trace preservation is ONLY on the input corner. No covariance or output symmetry is imposed.
--   - `HasBoseOutput`: PDF pp.6–7: Bose-supported outputs, imposed only where the source uses it.
--   - `tensorWithIdentity`: PDF p.6 Eq.(3.3): rho tensor the identity on the final M-N factors. The inequality guards all truncated subtraction and index casts.
--   - `canonicalCloner`: PDF p.6 Eq.(3.3): the actual canonical cloner, zero outside the Bose corner.
--   - `cloningOverlap`: PDF p.5 Eq.(2.1): global pure-target overlap, not root or one-site fidelity.
--   - `cloningFidelity`: PDF p.5 Eq.(2.1): infimum over ALL normalized pure inputs. For admissible maps and d>0 the set is nonempty and contained in [0,1].
--   - `optimalFidelity`: PDF p.9 Eq.(4.1): supremum of the admissible worst-case global fidelities. The maximum-attainment theorem supplies an actual feasible maximizer.
--   - `prependWord`: PDF p.7: split off the first tensor factor; n>=1 is explicit.
--   - `oneSite`: PDF p.7: computed one-site restriction, tracing out sites 2 through n.
--   - `HasBlackCowCoefficient`: PDF p.7 Eq.(3.7): relational Black Cow coefficient, valid even for d=1. The trace factor is essential for arbitrary, possibly non-normalized operators.
--   - `canonicalCoefficient`: PDF pp.7–8 Eq.(3.8): the specified representative coefficient of T-hat.
--   - `coefficientFactor`: PDF p.7: explicit one-index factor realizing the coefficient quotient.
--   - `UnitaryGroup`: PDF p.9: U(d) in the fixed one-particle basis.
--   - `rotatedCloner`: PDF p.9 Eq.(4.2): output adjoint on the LEFT; output unitary on the RIGHT.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, https://arxiv.org/abs/quant-ph/9804001v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

/-!
Werner, Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1.
All page numbers below are PDF page numbers. The input is the actual Bose
corner, zero-extended to ambient matrices. Competitors have unrestricted
full-tensor outputs. The objective is the worst-case many-particle overlap.
New constructions are local to this paper; matching definitions are imported
from the frozen accepted library, including its reviewed paper modules. The unpinned comparison of all figures of merit is deferred.
-/

noncomputable section

open scoped Matrix ComplexOrder
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)
open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

/-- PDF pp.3,5: the full n-system Hilbert space, with its L2 inner product. -/
abbrev TensorSpace (d n : ℕ) := EuclideanSpace ℂ (Word n d)

/-- PDF pp.4–6: unbundled Schroedinger map; admissibility supplies linearity. -/
abbrev CloneMap (d N M : ℕ) := TensorMat d N → TensorMat d M

/-- PDF pp.5–6: the frozen tensor-vector coordinates, packaged with the L2 norm. -/
def coherentTensor {d : ℕ} (n : ℕ) (phi : EuclideanSpace ℂ (Fin d)) : TensorSpace d n :=
  WithLp.toLp 2 (powerVector n phi)

/-- PDF p.5: the actual subspace fixed by EVERY tensor-factor permutation. -/
def boseSpace (d n : ℕ) : Submodule ℂ (TensorSpace d n) where
  carrier := {v | ∀ p : Equiv.Perm (Fin n), ∀ x : Word n d, v (x ∘ p) = v x}
  zero_mem' := by intro p x; rfl
  add_mem' := by
    intro v w hv hw p x
    change v (x ∘ p) + w (x ∘ p) = v x + w x
    rw [hv p x, hw p x]
  smul_mem' := by
    intro c v hv p x
    change c * v (x ∘ p) = c * v x
    rw [hv p x]

/-- PDF p.6: both sides of an operator are supported on the Bose subspace. -/
def BoseSupported {d n : ℕ} (A : TensorMat d n) : Prop :=
  boseProjector d n * A = A ∧ A * boseProjector d n = A

/-- PDF p.5 Eq.(3.2): symmetric dimension, using the final natural binomial. -/
def boseDimension (d n : ℕ) : ℕ := Nat.choose (d + n - 1) n

/-- PDF p.5: occupation tuples, finitely bounded by n and with EXACT total n. -/
abbrev BoseOccupation (d n : ℕ) :=
  {o : Fin d → Fin (n + 1) // ∑ a, (o a).val = n}

/-- PDF p.5 Eq.(3.1): explicit positive real normalized occupation vector.
Every word with the given occupation has amplitude sqrt(prod_a o_a! / n!). -/
def occupationKet (d n : ℕ) (o : BoseOccupation d n) : TensorSpace d n :=
  WithLp.toLp 2 fun x =>
    if ∀ a : Fin d, (Finset.univ.filter (fun k : Fin n => x k = a)).card = (o.val a).val
    then (Real.sqrt ((∏ a : Fin d, (Nat.factorial (o.val a).val : ℝ)) /
      (Nat.factorial n : ℝ)) : ℂ)
    else 0

/-- PDF p.5: the concrete real embedding from occupation coordinates to words. -/
def occupationEmbedding (d n : ℕ) : Matrix (Word n d) (BoseOccupation d n) ℂ :=
  fun x o => occupationKet d n o x

/-- PDF p.5 Eq.(3.1): coefficient of the occupation vector in phi tensor n. -/
def occupationCoefficient {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d))
    (o : BoseOccupation d n) : ℂ :=
  (Real.sqrt (Nat.factorial n : ℝ) : ℂ) *
    ∏ a : Fin d, phi a ^ (o.val a).val /
      (Real.sqrt (Nat.factorial (o.val a).val : ℝ) : ℂ)

/-- PDF p.6: tau_n is the maximally mixed state on the Bose sector. -/
def boseMixed (d n : ℕ) : TensorMat d n :=
  (boseDimension d n : ℂ)⁻¹ • boseProjector d n

/-- PDF p.7: the one-particle maximally mixed state, in one-particle coordinates. -/
def oneMixed (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (d : ℂ)⁻¹ • 1

/-- PDF pp.4–6: linear completely positive corner-input channel. The map is
canonically zero-extended; trace preservation is ONLY on the input corner.
No covariance or output symmetry is imposed. -/
def IsBoseInputChannel {d N M : ℕ} (T : CloneMap d N M) : Prop :=
  (∃ L : TensorMat d N →ₗ[ℂ] TensorMat d M,
    (∀ A, T A = L A) ∧ QAlgorithms.Entanglement.IsCompletelyPositive L) ∧
  (∀ A, T A = T (boseProjector d N * A * boseProjector d N)) ∧
  ∀ A, (T A).trace = (boseProjector d N * A * boseProjector d N).trace

/-- PDF pp.6–7: Bose-supported outputs, imposed only where the source uses it. -/
def HasBoseOutput {d N M : ℕ} (T : CloneMap d N M) : Prop :=
  ∀ A, BoseSupported (T A)

/-- PDF p.6 Eq.(3.3): rho tensor the identity on the final M-N factors.
The inequality guards all truncated subtraction and index casts. -/
def tensorWithIdentity {d N M : ℕ} (hNM : N ≤ M) (A : TensorMat d N) : TensorMat d M :=
  fun x y =>
    A (fun k => x ⟨k.val, by omega⟩) (fun k => y ⟨k.val, by omega⟩) *
    ∏ k : Fin (M - N),
      if x ⟨N + k.val, by omega⟩ = y ⟨N + k.val, by omega⟩ then 1 else 0

/-- PDF p.6 Eq.(3.3): the actual canonical cloner, zero outside the Bose corner. -/
def canonicalCloner {d N M : ℕ} (hNM : N ≤ M) : CloneMap d N M :=
  fun A => ((boseDimension d N : ℂ) / (boseDimension d M : ℂ)) •
    (boseProjector d M *
      tensorWithIdentity hNM (boseProjector d N * A * boseProjector d N) *
      boseProjector d M)

/-- PDF p.5 Eq.(2.1): global pure-target overlap, not root or one-site fidelity. -/
def cloningOverlap {d N M : ℕ} (T : CloneMap d N M)
    (phi : EuclideanSpace ℂ (Fin d)) : ℝ :=
  ((QAlgorithms.pureDensity (coherentTensor M phi)) *
    T (QAlgorithms.pureDensity (coherentTensor N phi))).trace.re

/-- PDF p.5 Eq.(2.1): infimum over ALL normalized pure inputs.
For admissible maps and d>0 the set is nonempty and contained in [0,1]. -/
def cloningFidelity {d N M : ℕ} (T : CloneMap d N M) : ℝ :=
  sInf {r : ℝ | ∃ phi : EuclideanSpace ℂ (Fin d),
    ‖phi‖ = 1 ∧ r = cloningOverlap T phi}

/-- PDF p.9 Eq.(4.1): supremum of the admissible worst-case global fidelities.
The maximum-attainment theorem supplies an actual feasible maximizer. -/
def optimalFidelity (d N M : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ T : CloneMap d N M, IsBoseInputChannel T ∧ r = cloningFidelity T}

/-- PDF p.7: split off the first tensor factor; n>=1 is explicit. -/
def prependWord {d n : ℕ} (hn : 1 ≤ n) (a : Fin d) (z : Word (n - 1) d) : Word n d :=
  fun k => if h : k.val = 0 then a else z ⟨k.val - 1, by omega⟩

/-- PDF p.7: computed one-site restriction, tracing out sites 2 through n. -/
def oneSite {d n : ℕ} (hn : 1 ≤ n) (A : TensorMat d n) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ∑ z : Word (n - 1) d, A (prependWord hn a z) (prependWord hn b z)

/-- PDF p.7 Eq.(3.7): relational Black Cow coefficient, valid even for d=1.
The trace factor is essential for arbitrary, possibly non-normalized operators. -/
def HasBlackCowCoefficient {d N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (T : CloneMap d N M) (gamma : ℝ) : Prop :=
  ∀ A, BoseSupported A →
    oneSite hM (T A) = (gamma : ℂ) • oneSite hN A +
      (((1 - gamma : ℝ) : ℂ) * A.trace) • oneMixed d

/-- PDF pp.7–8 Eq.(3.8): the specified representative coefficient of T-hat. -/
def canonicalCoefficient (d N M : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) + N) * (((d : ℝ) + M) / M)

/-- PDF p.7: explicit one-index factor realizing the coefficient quotient. -/
def coefficientFactor (d n : ℕ) : ℝ := (n : ℝ) / ((d : ℝ) + n)

/-- PDF p.9: U(d) in the fixed one-particle basis. -/
abbrev UnitaryGroup (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

/-- PDF p.9: Borel measurable structure on the actual compact unitary group. -/
local instance unitaryMeasurable (d : ℕ) : MeasurableSpace (UnitaryGroup d) :=
  borel (UnitaryGroup d)

/-- PDF p.9 Eq.(4.2): output adjoint on the LEFT; output unitary on the RIGHT. -/
def rotatedCloner {d N M : ℕ} (u : UnitaryGroup d) (T : CloneMap d N M) : CloneMap d N M :=
  QAlgorithms.Papers.Independent.Renew46.P45.rotateCloner (N := M) (M := N) u T

/-! Small construction sanity checks; these do not prove any source theorem. -/

example {d : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (x : Word 0 d) :
    coherentTensor 0 phi x = 1 := by
  simp [coherentTensor, powerVector]

example {d : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (x : Word 1 d) :
    coherentTensor 1 phi x = phi (x 0) := by
  simp [coherentTensor, powerVector]

example : boseDimension 2 2 = 3 := by
  norm_num [boseDimension, Nat.choose]

example : occupationKet 1 1
    ⟨fun _ => (1 : Fin 2), by simp⟩ (fun _ => (0 : Fin 1)) = 1 := by
  simp [occupationKet]

example : (boseDimension 2 1 : ℝ) / boseDimension 2 2 = 2 / 3 := by
  norm_num [boseDimension, Nat.choose]

example (d : ℕ) (A : TensorMat d 0) (x y : Word 0 d) :
    tensorWithIdentity (N := 0) (M := 0) (by omega) A x y = A x y := by
  simp [tensorWithIdentity]

example {d : ℕ} (a : Fin d) (z : Word 0 d) :
    prependWord (n := 1) (by omega) a z 0 = a := by
  simp [prependWord]

example : canonicalCoefficient 2 1 2 = 2 / 3 := by
  norm_num [canonicalCoefficient]

example : canonicalCoefficient 2 1 2 + (1 - canonicalCoefficient 2 1 2) / 2 = 5 / 6 := by
  norm_num [canonicalCoefficient]

end QAlgorithms.Papers.Independent.Support21.P16


