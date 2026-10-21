-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45
-- name    : QAlgorithms_Papers_Independent_Renew46_P45
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:38:40.776462+00:00
-- url     : https://prove2.me/theorems/ef70429e-4bc1-4d1d-97b9-4cd6f03d10b5
-- title:
--   Definitions for Optimal Cloning of Pure States, Judging Single Clones
-- statement:
--   The objects the formalized statements of *Optimal Cloning of Pure States, Judging Single Clones* (arXiv:quant-ph/9807010) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TensorMat`
--   - `CloneFunction`
--   - `U`
--   - `boseProjector`: PDF p.2: orthogonal projector onto the actual permutation-fixed Bose space.
--   - `siteObservable`: PDF p.2: one-site observable; Lean sites are zero based.
--   - `boseGenerator`: PDF pp.4–5: actual tensor differential restricted to the Bose subspace.
--   - `powerVector`: PDF p.2: tensor power in the tensor-word basis.
--   - `pureTensorExpectation`: PDF p.2: bra-ket pureTensorExpectation, conjugate linear in the bra.
--   - `IsEffect`: PDF p.2: positive effect bounded by the identity.
--   - `IsBoseCP`: PDF pp.2,5: complex-linear CP maps into the actual Bose corner; complete positivity uses all matrix amplifications, without unitality.
--   - `IsCloning`: PDF p.2: CP unital Heisenberg cloning map on full-output observables. In corner coordinates unitality is T(I)=P_N.
--   - `cloningError`: PDF p.2 Eq.(1), absolute values confirmed pp.3,5: worst-case single-site probability error over all normalized pure inputs and effects. On cloners in the stated regime the defining set is nonempty and bounded in [0,1].
--   - `appendWord`: PDF p.2 Eq.(3): concatenate input and blank words. N≤M guards Nat subtraction.
--   - `optimalCloner`: PDF pp.2–3 Eq.(3): explicit Heisenberg dual of (d[N]/d[M]) P_M (rho tensor I) P_M, restricted to the Bose input corner.
--   - `sharpError`: PDF p.3 Theorem 1: sharp constant, using real arithmetic and absolute value.
--   - `IsCloningCovariant`: PDF p.3 Eq.(4): actual tensor action, whose input corner is pi_N^+.
--   - `IsPermutationInvariant`: PDF p.4: invariance under all output tensor-factor permutations.
--   - `rotateCloner`: PDF p.3 Eq.(5): rotation action; input adjoint is on the left.
--   - `permuteCloner`: PDF p.4: output reordering action.
--   - `haarAverage`: PDF p.3 Eq.(6): entrywise Haar average. Integrability is a conclusion of symmetrization, not an extra hypothesis on the input cloner.
--   - `permutationAverage`: PDF p.4: normalized finite permutation average.
--   - `mixCloners`: PDF p.5: pointwise convex combination.
--   - `cloneCoefficient`: PDF p.5: computed real omega, extracted by testing the traceless diagonal (1,-1,0,...) on |0>^N after summing output generators. For d≥2,N≥1 Corollary 4 identifies this number with the source's omega.
--   - `SmoothUnitaryRep`: PDF pp.4,12: actual finite-dimensional unitary representation and its complexified differential. Derivatives along EVERY differentiable unitary curve through identity pin this linear map to the actual infinitesimal action. Continuity of a finite-dimensional unitary Lie-group homomorphism supplies the usual smooth regime. All derivative tests are entrywise.
--   - `definingRepresentation`: PDF pp.3,12: defining representation, with the actual identity differential. This complete construction pins the representation bundle to an inhabited, concrete model independently of the theorem targets.
--   - `IsCloningRepresentationIrreducible`: PDF p.12: nonzero carrier and no proper invariant complex subspace.
--   - `HasHighestWeight`: PDF p.12 Appendix A2: dominant integral highest weight, tied to a nonzero highest-weight vector of the actual complexified differential.
--   - `IsTensorIntertwiner`: PDF pp.6,8: actual isometric intertwiner out of the Bose space; zero on its orthogonal complement in corner coordinates.
--   - `CloningBlock`: PDF p.6 Proposition 5: actual irreducible carriers, isometric full-output inclusion and intertwiner. Individual block permutation symmetry is not assumed.
--   - `blockApply`: PDF p.6: block map on FULL-output observables, including j* A j.
--   - `firstCasimir`: PDF p.14 Eq.(A6): represented first Casimir.
--   - `secondCasimir`: PDF p.14 Eq.(A6): represented second GL(d) Casimir.
--   - `specialCasimir`: PDF p.14 Eqs.(A7)–(A8), correcting the first C_1 to C_2 in A7: positive SU(d) normalization, uniformly used throughout.
--   - `secondCasimirValue`: PDF p.14 Eq.(A6): numerical C_2 value of a highest weight.
--   - `casimirValue`: PDF p.14 Eq.(A8): numerical SU(d) Casimir value.
--   - `symmetricWeight`: PDF p.13: actual Bose representation has weight (N,0,...,0).
--   - `weightCoefficient`: PDF pp.7–8 Eqs.(17),(21): coefficient from carrier Casimir labels.
--   - `weightObjective`: PDF p.9 Eq.(27): one-based k is j.val+1. All subtraction is integral.
--   - `IsWeightFeasible`: PDF pp.9–10: proof-pinned corrected W_1, including m_d≥0 and mu_d≥0. This local domain permits both N≤M and N≥M.
--   - `maximizingRemoval`: PDF p.10 Lemma 6: both branches, with integral N-M.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, https://arxiv.org/abs/quant-ph/9807010v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

/-!
Keyl–Werner, arXiv:quant-ph/9807010v1. Bose operators are zero-extended
corner matrices P_N B(H^N) P_N, with identity P_N. The output is the FULL
tensor space. Printed unrestricted uniqueness is deferred in HARD.md.
Source corrections to Lemma 6 and Theorem 8 are documented in the unit.
-/

noncomputable section

open scoped Matrix ComplexOrder
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

abbrev TensorMat (d n : ℕ) := Matrix (Word n d) (Word n d) ℂ

abbrev CloneFunction (d N M : ℕ) := TensorMat d M → TensorMat d N

abbrev U (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

/-- PDF p.2: orthogonal projector onto the actual permutation-fixed Bose space. -/
def boseProjector (d n : ℕ) : TensorMat d n :=
  ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
    ∑ p : Equiv.Perm (Fin n), QAlgorithms.Schur.tensorPermutation d n p

/-- PDF p.2: one-site observable; Lean sites are zero based. -/
def siteObservable {d n : ℕ} (a : Mat d) (k : Fin n) : TensorMat d n :=
  fun x y => a (x k) (y k) * ∏ l ∈ Finset.univ.erase k,
    (if x l = y l then 1 else 0)

/-- PDF pp.4–5: actual tensor differential restricted to the Bose subspace. -/
def boseGenerator (d n : ℕ) (a : Mat d) : TensorMat d n :=
  boseProjector d n * (∑ k : Fin n, siteObservable a k) * boseProjector d n

/-- PDF p.2: tensor power in the tensor-word basis. -/
def powerVector {d : ℕ} (n : ℕ) (psi : Fin d → ℂ) : Word n d → ℂ :=
  fun x => ∏ k, psi (x k)

/-- PDF p.2: bra-ket pureTensorExpectation, conjugate linear in the bra. -/
def pureTensorExpectation {I : Type*} [Fintype I] (v : I → ℂ) (a : Matrix I I ℂ) : ℂ :=
  ∑ x, ∑ y, star (v x) * a x y * v y

/-- PDF p.2: positive effect bounded by the identity. -/
def IsEffect {I : Type*} [Fintype I] [DecidableEq I]
    (a : Matrix I I ℂ) : Prop := a.PosSemidef ∧ (1 - a).PosSemidef

/-- PDF pp.2,5: complex-linear CP maps into the actual Bose corner;
complete positivity uses all matrix amplifications, without unitality. -/
def IsBoseCP {I : Type*} [Fintype I] (d N : ℕ)
    (T : Matrix I I ℂ → TensorMat d N) : Prop :=
  ∃ L : Matrix I I ℂ →ₗ[ℂ] TensorMat d N,
    (∀ A, T A = L A) ∧ QAlgorithms.Entanglement.IsCompletelyPositive L ∧
    ∀ A, boseProjector d N * T A * boseProjector d N = T A

/-- PDF p.2: CP unital Heisenberg cloning map on full-output observables.
In corner coordinates unitality is T(I)=P_N. -/
def IsCloning {d N M : ℕ} (T : CloneFunction d N M) : Prop :=
  IsBoseCP d N T ∧ T 1 = boseProjector d N

/-- PDF p.2 Eq.(1), absolute values confirmed pp.3,5: worst-case single-site
probability error over all normalized pure inputs and effects. On cloners in
the stated regime the defining set is nonempty and bounded in [0,1]. -/
def cloningError {d N M : ℕ} (T : CloneFunction d N M) : ℝ :=
  sSup {r : ℝ | ∃ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 ∧
    ∃ a : Mat d, IsEffect a ∧ ∃ k : Fin M,
    r = |(pureTensorExpectation (powerVector N psi) (T (siteObservable a k)) -
      pureTensorExpectation psi a).re|}

/-- PDF p.2 Eq.(3): concatenate input and blank words. N≤M guards Nat subtraction. -/
def appendWord {d N M : ℕ} (hNM : N ≤ M) (x : Word N d)
    (z : Word (M - N) d) : Word M d :=
  fun k => if hk : k.val < N then x ⟨k.val, hk⟩
    else z ⟨k.val - N, by omega⟩

/-- PDF pp.2–3 Eq.(3): explicit Heisenberg dual of
(d[N]/d[M]) P_M (rho tensor I) P_M, restricted to the Bose input corner. -/
def optimalCloner {d N M : ℕ} (hNM : N ≤ M) : CloneFunction d N M :=
  fun A => ((Nat.choose (d + N - 1) N : ℂ) /
      (Nat.choose (d + M - 1) M : ℂ)) •
    (boseProjector d N *
      (Matrix.of (fun x y => ∑ z : Word (M - N) d,
        (boseProjector d M * A * boseProjector d M)
          (appendWord hNM x z) (appendWord hNM y z)) : TensorMat d N) * boseProjector d N)

/-- PDF p.3 Theorem 1: sharp constant, using real arithmetic and absolute value. -/
def sharpError (d N M : ℕ) : ℝ :=
  ((d : ℝ) - 1) / d * |1 - (N : ℝ) / ((N : ℝ) + d) * (((M : ℝ) + d) / M)|

/-- PDF p.3 Eq.(4): actual tensor action, whose input corner is pi_N^+. -/
def IsCloningCovariant {d N M : ℕ} (T : CloneFunction d N M) : Prop :=
  ∀ u : U d, ∀ A,
    T (QAlgorithms.piKron M (u : Mat d) * A * (QAlgorithms.piKron M (u : Mat d))ᴴ) =
      QAlgorithms.piKron N (u : Mat d) * T A * (QAlgorithms.piKron N (u : Mat d))ᴴ

/-- PDF p.4: invariance under all output tensor-factor permutations. -/
def IsPermutationInvariant {d N M : ℕ} (T : CloneFunction d N M) : Prop :=
  ∀ p : Equiv.Perm (Fin M), ∀ A,
    T (QAlgorithms.Schur.tensorPermutation d M p * A *
      (QAlgorithms.Schur.tensorPermutation d M p)ᴴ) = T A

/-- PDF p.3 Eq.(5): rotation action; input adjoint is on the left. -/
def rotateCloner {d N M : ℕ} (u : U d) (T : CloneFunction d N M) : CloneFunction d N M :=
  fun A => (QAlgorithms.piKron N (u : Mat d))ᴴ *
    T (QAlgorithms.piKron M (u : Mat d) * A * (QAlgorithms.piKron M (u : Mat d))ᴴ) *
    QAlgorithms.piKron N (u : Mat d)

/-- PDF p.4: output reordering action. -/
def permuteCloner {d N M : ℕ} (p : Equiv.Perm (Fin M))
    (T : CloneFunction d N M) : CloneFunction d N M :=
  fun A => T (QAlgorithms.Schur.tensorPermutation d M p * A *
    (QAlgorithms.Schur.tensorPermutation d M p)ᴴ)

/-- Borel measurable structure on the actual compact matrix unitary group. -/
local instance unitaryMeasurable (d : ℕ) : MeasurableSpace (U d) := borel (U d)

/-- PDF p.3 Eq.(6): entrywise Haar average. Integrability is a conclusion
of symmetrization, not an extra hypothesis on the input cloner. -/
def haarAverage {d N M : ℕ} (mu : Measure (U d))
    (T : CloneFunction d N M) : CloneFunction d N M :=
  fun A x y => ∫ u : U d, rotateCloner u T A x y ∂mu

/-- PDF p.4: normalized finite permutation average. -/
def permutationAverage {d N M : ℕ} (T : CloneFunction d N M) : CloneFunction d N M :=
  fun A => ((Fintype.card (Equiv.Perm (Fin M)) : ℂ)⁻¹) •
    ∑ p : Equiv.Perm (Fin M), permuteCloner p T A

/-- PDF p.5: pointwise convex combination. -/
def mixCloners {I J : Type*} (t : ℝ) (T S : I → J → J → ℂ) : I → J → J → ℂ :=
  fun A x y => (t : ℂ) * T A x y + ((1 - t : ℝ) : ℂ) * S A x y

/-- PDF p.5: computed real omega, extracted by testing the traceless
diagonal (1,-1,0,...) on |0>^N after summing output generators.
For d≥2,N≥1 Corollary 4 identifies this number with the source's omega. -/
def cloneCoefficient {d N M : ℕ} (hd : 0 < d) (T : CloneFunction d N M) : ℝ :=
  let a : Mat d := fun i j => if i = j then
    (if i.val = 0 then 1 else if i.val = 1 then -1 else 0) else 0
  let z : Word N d := fun _ => ⟨0, hd⟩
  (T (∑ k : Fin M, siteObservable a k) z z).re / N

/-- PDF pp.4,12: actual finite-dimensional unitary representation and its
complexified differential. Derivatives along EVERY differentiable unitary
curve through identity pin this linear map to the actual infinitesimal action.
Continuity of a finite-dimensional unitary Lie-group homomorphism supplies
the usual smooth regime. All derivative tests are entrywise. -/
structure SmoothUnitaryRep (d h : ℕ) where
  action : U d →* U h
  continuous_entry : ∀ i j, Continuous (fun u => (action u : Mat h) i j)
  differential : Mat d →ₗ[ℂ] Mat h
  differential_spec : ∀ (u : ℝ → U d) (X : Mat d), u 0 = 1 →
    (∀ i j, HasDerivAt (fun t => (u t : Mat d) i j) (X i j) 0) →
    ∀ i j, HasDerivAt (fun t => (action (u t) : Mat h) i j)
      (differential X i j) 0

/-- PDF pp.3,12: defining representation, with the actual identity differential.
This complete construction pins the representation bundle to an inhabited,
concrete model independently of the theorem targets. -/
def definingRepresentation (d : ℕ) : SmoothUnitaryRep d d where
  action := MonoidHom.id (U d)
  continuous_entry := by
    intro i j
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  differential := LinearMap.id
  differential_spec := by
    intro u X hzero hdiff i j
    exact hdiff i j

/-- The defining representation has precisely the defining infinitesimal action. -/
example (d : ℕ) (X : Mat d) : (definingRepresentation d).differential X = X := by
  rfl

/-- PDF p.12: nonzero carrier and no proper invariant complex subspace. -/
def IsCloningRepresentationIrreducible {d h : ℕ} (pi : SmoothUnitaryRep d h) : Prop :=
  0 < h ∧ ∀ W : Submodule ℂ (Fin h → ℂ),
    (∀ u : U d, ∀ v ∈ W, Matrix.mulVec (pi.action u : Mat h) v ∈ W) →
    W = ⊥ ∨ W = ⊤

/-- PDF p.12 Appendix A2: dominant integral highest weight, tied to a nonzero
highest-weight vector of the actual complexified differential. -/
def HasHighestWeight {d h : ℕ} (pi : SmoothUnitaryRep d h) (m : Fin d → ℤ) : Prop :=
  IsCloningRepresentationIrreducible pi ∧ (∀ i j, i ≤ j → m j ≤ m i) ∧
  ∃ v : Fin h → ℂ, v ≠ 0 ∧
    (∀ j, Matrix.mulVec (pi.differential (Matrix.single j j 1)) v = (m j : ℂ) • v) ∧
    ∀ j k, j < k → Matrix.mulVec (pi.differential (Matrix.single j k 1)) v = 0

/-- PDF pp.6,8: actual isometric intertwiner out of the Bose space;
zero on its orthogonal complement in corner coordinates. -/
def IsTensorIntertwiner {d N a b : ℕ} (pa : SmoothUnitaryRep d a)
    (pb : SmoothUnitaryRep d b) (V : Matrix (Fin a × Fin b) (Word N d) ℂ) : Prop :=
  V * boseProjector d N = V ∧ Vᴴ * V = boseProjector d N ∧
  ∀ u : U d, V * QAlgorithms.piKron N (u : Mat d) =
    Matrix.kronecker (pa.action u : Mat a) (pb.action u : Mat b) * V

/-- PDF p.6 Proposition 5: actual irreducible carriers, isometric full-output
inclusion and intertwiner. Individual block permutation symmetry is not assumed. -/
structure CloningBlock (d N M : ℕ) where
  a : ℕ
  b : ℕ
  pa : SmoothUnitaryRep d a
  pb : SmoothUnitaryRep d b
  irreducible_a : IsCloningRepresentationIrreducible pa
  irreducible_b : IsCloningRepresentationIrreducible pb
  inclusion : Matrix (Word M d) (Fin a) ℂ
  inclusion_isometry : inclusionᴴ * inclusion = 1
  inclusion_intertwines : ∀ u : U d,
    QAlgorithms.piKron M (u : Mat d) * inclusion = inclusion * (pa.action u : Mat a)
  V : Matrix (Fin a × Fin b) (Word N d) ℂ
  V_intertwines : IsTensorIntertwiner pa pb V

/-- PDF p.6: block map on FULL-output observables, including j* A j. -/
def blockApply {d N M : ℕ} (B : CloningBlock d N M) : CloneFunction d N M :=
  fun A => B.Vᴴ * Matrix.kronecker (B.inclusionᴴ * A * B.inclusion) (1 : Mat B.b) * B.V

/-- PDF p.14 Eq.(A6): represented first Casimir. -/
def firstCasimir {d h : ℕ} (pi : SmoothUnitaryRep d h) : Mat h :=
  ∑ j : Fin d, pi.differential (Matrix.single j j 1)

/-- PDF p.14 Eq.(A6): represented second GL(d) Casimir. -/
def secondCasimir {d h : ℕ} (pi : SmoothUnitaryRep d h) : Mat h :=
  ∑ j : Fin d, ∑ k : Fin d,
    pi.differential (Matrix.single j k 1) * pi.differential (Matrix.single k j 1)

/-- PDF p.14 Eqs.(A7)–(A8), correcting the first C_1 to C_2 in A7:
positive SU(d) normalization, uniformly used throughout. -/
def specialCasimir {d h : ℕ} (pi : SmoothUnitaryRep d h) : Mat h :=
  secondCasimir pi - (1 / (d : ℂ)) • (firstCasimir pi * firstCasimir pi)

/-- PDF p.14 Eq.(A6): numerical C_2 value of a highest weight. -/
def secondCasimirValue {d : ℕ} (m : Fin d → ℤ) : ℝ :=
  (∑ j : Fin d, (m j : ℝ)^2) +
    ∑ j : Fin d, ∑ k : Fin d, if j < k then (m j : ℝ) - m k else 0

/-- PDF p.14 Eq.(A8): numerical SU(d) Casimir value. -/
def casimirValue {d : ℕ} (m : Fin d → ℤ) : ℝ :=
  secondCasimirValue m - (∑ j : Fin d, (m j : ℝ))^2 / d

/-- PDF p.13: actual Bose representation has weight (N,0,...,0). -/
def symmetricWeight (d N : ℕ) : Fin d → ℤ := fun j => if j.val = 0 then N else 0

/-- PDF pp.7–8 Eqs.(17),(21): coefficient from carrier Casimir labels. -/
def weightCoefficient {d : ℕ} (N : ℕ) (m n : Fin d → ℤ) : ℝ :=
  1 / 2 + (casimirValue m - casimirValue n) /
    (2 * casimirValue (symmetricWeight d N))

/-- PDF p.9 Eq.(27): one-based k is j.val+1. All subtraction is integral. -/
def weightObjective {d : ℕ} (m mu : Fin d → ℤ) : ℤ :=
  ∑ j : Fin d, mu j * (2 * m j - 2 * ((j.val : ℤ) + 1) - mu j)

/-- PDF pp.9–10: proof-pinned corrected W_1, including m_d≥0 and mu_d≥0.
This local domain permits both N≤M and N≥M. -/
def IsWeightFeasible (d N M : ℕ) (m mu : Fin d → ℤ) : Prop :=
  (∀ j, 0 ≤ m j) ∧ (∀ j, 0 ≤ mu j) ∧
  (∀ i j, i ≤ j → m j ≤ m i) ∧
  (∑ j, m j) = (M : ℤ) ∧ (∑ j, mu j) = (N : ℤ) ∧
  ∀ i j : Fin d, j.val = i.val + 1 → mu i ≤ m i - m j

/-- PDF p.10 Lemma 6: both branches, with integral N-M. -/
def maximizingRemoval (d N M : ℕ) : Fin d → ℤ :=
  fun j => if N ≤ M then (if j.val = 0 then N else 0)
    else if j.val = 0 then M else if j.val + 1 = d then (N : ℤ) - M else 0

/-- Empty tensor product amplitude (PDF p.2 convention). -/
example {d : ℕ} (psi : Fin d → ℂ) (x : Word 0 d) : powerVector 0 psi x = 1 := by
  simp [powerVector]

/-- Zero-copy infinitesimal action (PDF p.4 generator sum). -/
example (d : ℕ) (a : Mat d) : boseGenerator d 0 a = 0 := by
  simp [boseGenerator]

/-- Both removal branches agree at N=M (PDF p.10). -/
example (d N : ℕ) : maximizingRemoval d N N = symmetricWeight d N := by
  funext j
  simp [maximizingRemoval, symmetricWeight]

/-- Trivial numerical Casimir (PDF p.14). -/
example (d : ℕ) : casimirValue (fun _ : Fin d => (0 : ℤ)) = 0 := by
  simp [casimirValue, secondCasimirValue]

/-- Actual map at a mixCloners endpoint (PDF p.5). -/
example {I J : Type*} (T S : I → J → J → ℂ) : mixCloners 1 T S = T := by
  funext A x y
  simp [mixCloners]

end QAlgorithms.Papers.Independent.Renew46.P45


