-- Prove2me | Definitions.Def_OAIQ4Kq002
-- name    : OAIQ4Kq002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:29:57.567852+00:00
-- url     : https://prove2.me/theorems/5c1558f4-71e2-44cf-9a4b-ca17952766be
-- title:
--   Definitions bundle OAIQ4Kq002 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 221 declarations of OpenAI's Lean: 48 definitions, 4 inductive types or structures, 5 instances and 164 theorems. The definitions and types are `OAI.Kaplansky.ActualDefectIndex`, `OAI.Kaplansky.BoundedMatrixTerm`, `OAI.Kaplansky.ComplexGrassmann.coordinatePunctureDimensions`, `OAI.Kaplansky.CuntzDimensionState`, `OAI.Kaplansky.CuntzDimensionState.complexValue`, `OAI.Kaplansky.CuntzDimensionState.distribution`, `OAI.Kaplansky.CuntzDimensionState.positiveValue`, `OAI.Kaplansky.CuntzDimensionState.regularize`, `OAI.Kaplansky.CuntzDimensionState.regularized`, `OAI.Kaplansky.CuntzDimensionState.signedValue`, `OAI.Kaplansky.CuntzDimensionState.spectralValue`, `OAI.Kaplansky.CuntzDimensionState.value`, `OAI.Kaplansky.CuntzEquivalent`, `OAI.Kaplansky.CuntzLE`, `OAI.Kaplansky.CuntzMonoid`, `OAI.Kaplansky.CuntzPositiveMatrix`, `OAI.Kaplansky.CuntzPositiveMatrix.add`, `OAI.Kaplansky.CuntzPositiveMatrix.cutoff`, `OAI.Kaplansky.CuntzPositiveMatrix.unit`, `OAI.Kaplansky.CuntzPositiveMatrix.zero`, `OAI.Kaplansky.LineCoreIsUnitary`, `OAI.Kaplansky.PositiveDimensionFunctional`, `OAI.Kaplansky.PositiveDimensionFunctional.ConeLowerSemicontinuous`, `OAI.Kaplansky.PositiveDimensionFunctional.ScaleInvariant`, `OAI.Kaplansky.PositiveDimensionFunctional.compactValue`, `OAI.Kaplansky.PositiveDimensionFunctional.content`, `OAI.Kaplansky.PositiveDimensionFunctional.majorants`, `OAI.Kaplansky.PositiveDimensionFunctional.measure`, `OAI.Kaplansky.QuasitraceCandidate`, `OAI.Kaplansky.affineAvoidanceSet`, `OAI.Kaplansky.continuousDimensionCutoff`, `OAI.Kaplansky.continuousRealInclusion`, `OAI.Kaplansky.coordinateFunctional`, `OAI.Kaplansky.corner`, `OAI.Kaplansky.cuntzBlock`, `OAI.Kaplansky.cuntzBlockHom`, `OAI.Kaplansky.cuntzClass`, `OAI.Kaplansky.cuntzCutoff`, `OAI.Kaplansky.cuntzUnit`, `OAI.Kaplansky.cutoffSquareFactor` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: `BundleTests_Base`, `BundleTests_Bundles`, `ComplexBundle_DirectSum`, `ComplexBundle_Hyperplane`, `ComplexBundle_PointExpansion`, `ComplexBundle_RealModel`, `ComplexBundle_Replacement`, `Cuntz_Comparison`, `Cuntz_Content`, `Cuntz_Cutoff`, `Cuntz_Distribution`, `Cuntz_Measure`, `Cuntz_Monoid`, `Cuntz_Regularization`, `Cuntz_RegularizedState`, `Cuntz_Spectral`, `Cuntz_SquareCutoff`, `Cuntz_Squares`, `Cuntz_State`, `IntegralHomology_AffineAvoidance`, `IntegralHomology_OpenUnion`, `IntegralHomology_ProjectiveClass`, `Kaplansky_ActualAlgebra`, `Kaplansky_BundlePolynomials`, `Kaplansky_Products`, `Kaplansky_Shift`, `Kaplansky_Words`, `MatrixScaling_Expansion`, `Quasitrace_Compactness`, `Quasitrace_Extension`, `Quasitrace_Matrix`.
--
--   **Imports.** It imports the published bundle `Def_KaplanskyQuasitrace`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ4Kq005`, `OAIQ4Kq006`, `OAIQ4Kq007` and `OAIQ4Kq008`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyQuasitrace

section
-- module Solutions.OAIQ4_Kq.BundleTests_Base
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

namespace Kaplansky
open scoped BigOperators

theorem three_sum_pow_four (n : ℕ) : 3*(∑ i : Fin n,4^i.val)+1=4^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,pow_succ]
    simp only [Fin.val_castSucc,Fin.val_last]
    omega

end Kaplansky

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_DirectSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite direct sums of line bundles, metrics, inclusions, and projections. -/

section
open Bundle Topology

open Bundle Topology
open scoped BigOperators InnerProductSpace
namespace Kaplansky
variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

/-- The ordinary isometry condition on the given line-bundle transitions. -/
def LineCoreIsUnitary : Prop := ∀ s a b x,
  x ∈ (C s).baseSet a → x ∈ (C s).baseSet b → ∀ z w : ℂ,
  inner ℂ ((C s).coordChange a b x z) ((C s).coordChange a b x w) = inner ℂ z w

end Kaplansky

end

open Bundle Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Bundles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Test bundles, Hermitian metrics, and their trivial initial stage. -/

section
open Bundle Topology
open scoped BigOperators InnerProductSpace
namespace Kaplansky

theorem complex_unit_mul_inner (u : ℂ) (hu : star u*u=1) (z w : ℂ) :
    inner ℂ (u*z) (u*w) = inner ℂ z w := by
  change (u*w)*star (u*z) = w*star z
  rw [star_mul]
  calc
    (u*w) * (star z * star u) = (star u*u)*(w*star z) := by ring
    _ = _ := by rw [hu,one_mul]

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Hyperplane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Hyperplane sections, dual evaluation, graph coordinates, and their zero. -/

section
open Bundle Topology
open scoped InnerProductSpace
namespace Kaplansky
variable {d : ℕ}

def coordinateFunctional (i : Fin d) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp (EuclideanSpace.equiv (Fin d) ℂ).toLinearEquiv.toLinearMap

@[simp] theorem coordinateFunctional_apply (i : Fin d) (v : EuclideanSpace ℂ (Fin d)) :
    coordinateFunctional i v=v i := rfl

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky

def positiveCoordinate (k : ℕ) (i : Fin k) : Fin (1+k) := ⟨i.val+1,by omega⟩

def firstCoordinateVector (k : ℕ) : EuclideanSpace ℂ (Fin (1+k)) :=
  WithLp.toLp 2 (Pi.single 0 (1 : ℂ))

theorem firstCoordinateVector_ne_zero (k : ℕ) : firstCoordinateVector k≠0 := by
  intro h
  have he := congrArg (fun v : EuclideanSpace ℂ (Fin (1+k)) => v 0) h
  simp [firstCoordinateVector] at he

end Kaplansky

open Bundle Topology
open scoped InnerProductSpace

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_PointExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-point incidence avoidance and expansion inequalities. -/

open scoped MeasureTheory
open Set Module MeasureTheory MeasureTheory.Measure
namespace Kaplansky.Incidence

theorem point_dimension_inequality_iff {q d r s t : ℕ} (hsd : s≤d) (htr : t ≤ r) :
    ((q : ℤ)*s-t)*(r-t)-(s : ℤ)*(d-s)>0 ↔
      s*(d-s)+t*(r-t)<q*s*(r-t) := by
  rw [← Int.ofNat_sub hsd,← Int.ofNat_sub htr]
  constructor
  · intro h
    have hh : ((s*(d-s)+t*(r-t) : ℕ) : ℤ)<((q*s*(r-t) : ℕ) : ℤ) := by
      push_cast
      nlinarith
    exact_mod_cast hh
  · intro h
    have hh : ((s*(d-s)+t*(r-t) : ℕ) : ℤ)<((q*s*(r-t) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at hh
    nlinarith

end Kaplansky.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_RealModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real models of complex bundles and smooth finite line sums. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky

variable {S : Type*} [Fintype S]

def lineDiagonal (c : S → ℂ) : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  (EuclideanSpace.equiv S ℂ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun s => c s • (ContinuousLinearMap.proj s : (S → ℂ) →L[ℂ] ℂ))).comp
      (EuclideanSpace.equiv S ℂ).toContinuousLinearMap)

def lineDiagonalLinear : (S → ℂ) →ₗ[ℂ] (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) where
  toFun := lineDiagonal
  map_add' c d := by ext v s; change (c s+d s)*v s=c s*v s+d s*v s; ring
  map_smul' z c := by ext v s; change (z*c s)*v s=z*(c s*v s); ring

end Kaplansky

end

open Bundle Topology
open scoped Manifold ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.MatrixScaling_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic and finite-block expansion inequalities. -/

noncomputable section
open scoped BigOperators
open LinearMap
namespace Kaplansky
variable {n : ℕ} {E F G H : Type*}
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup G] [Module ℂ G] [AddCommGroup H] [Module ℂ H]

/-- The kernel of the last-block projection is the first-block intersection. -/
def prodSubmoduleKernelEquiv (S : Submodule ℂ (E × F)) :
    S.comap (LinearMap.inl ℂ E F) ≃ₗ[ℂ]
      LinearMap.ker ((LinearMap.snd ℂ E F).comp S.subtype) where
  toFun x := ⟨⟨(x.val,0),x.property⟩,rfl⟩
  invFun x := ⟨x.val.val.1, by
    have hz : x.val.val.2 = 0 := x.property
    change (x.val.val.1,0) ∈ S
    rw [← hz]
    exact x.val.property⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.property.symm
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_smul' z x := by
    apply Subtype.ext
    apply Subtype.ext
    simp

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem prod_submodule_finrank (S : Submodule ℂ (E × F)) :
    Module.finrank ℂ (S.comap (LinearMap.inl ℂ E F)) +
      Module.finrank ℂ (S.map (LinearMap.snd ℂ E F)) = Module.finrank ℂ S := by
  have h := LinearMap.finrank_range_add_finrank_ker ((LinearMap.snd ℂ E F).comp S.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  rw [← (prodSubmoduleKernelEquiv S).finrank_eq] at h
  omega

end Kaplansky

end

noncomputable section
namespace Kaplansky
variable {n : ℕ}

def piSuccLinearEquiv {k : ℕ} (E : Fin (k+1) → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)] :
    (∀ j, E j) ≃ₗ[ℂ] E 0 × (∀ j : Fin k, E j.succ) where
  toFun v := (v 0,fun j => v j.succ)
  invFun v := Fin.cases v.1 v.2
  left_inv v := by funext j; refine Fin.cases ?_ (fun i => ?_) j <;> rfl
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.ComplexBundle_Replacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Quantitative bundle rank margins and repeated-line replacement maps. -/

namespace Kaplansky

theorem small_incidence (m s D : ℝ) (hm : 0 < m) (hs : 0 < s)
    (hsm : s ≤ m) (hD : 64*m ≤ D) :
    0 < (16*s-2*s)*(D/4-2*s)-s*(D-s) ∧
    133*m*s ≤ (16*s-2*s)*(D/4-2*s)-s*(D-s) := by
  have h1 := mul_le_mul_of_nonneg_right hD hs.le
  have h2 := mul_le_mul_of_nonneg_right hsm hs.le
  have h3 : 0 < m*s := mul_pos hm hs
  constructor <;> nlinarith

end Kaplansky

section
open scoped BigOperators
namespace Kaplansky
variable {d r n : ℕ} {L : Type*} [AddCommGroup L] [Module ℂ L]

def lineCoordinates (e : L ≃ₗ[ℂ] ℂ) (d : ℕ) : (Fin d → L) ≃ₗ[ℂ] (Fin d → ℂ) where
  toFun v j := e (v j)
  invFun v j := e.symm (v j)
  left_inv v := by funext j; exact e.symm_apply_apply _
  right_inv v := by funext j; exact e.apply_symm_apply _
  map_add' v w := by funext j; exact map_add e _ _
  map_smul' c v := by funext j; exact map_smul e _ _

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular matrix comparison, block sums, and reindexing of positive matrices. -/

noncomputable section
open scoped Topology Matrix
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι κ ν : Type*} [Fintype κ] [Fintype ν]

/-- Rectangular Cuntz comparison: norm closure of actual conjugations.
The finite product topology here is the topology of the C*-matrix norm. -/
def CuntzLE (a : Matrix ι ι A) (b : Matrix κ κ A) : Prop :=
  a ∈ closure (Set.range fun v : Matrix ι κ A => v * b * v.conjTranspose)

namespace CuntzLE

theorem exact (b : Matrix κ κ A) (v : Matrix ι κ A) :
    CuntzLE (v * b * v.conjTranspose) b := subset_closure ⟨v, rfl⟩

theorem refl [Fintype ι] (a : Matrix ι ι A) : CuntzLE a a := by
  classical
  simpa using exact a (1 : Matrix ι ι A)

theorem zero (b : Matrix κ κ A) : CuntzLE (0 : Matrix ι ι A) b := by
  simpa using exact b (0 : Matrix ι κ A)

theorem isClosed (b : Matrix κ κ A) : IsClosed {a : Matrix ι ι A | CuntzLE a b} :=
  isClosed_closure

theorem of_mem_closure {s : Set (Matrix ι ι A)} {a : Matrix ι ι A}
    {b : Matrix κ κ A} (ha : a ∈ closure s) (hs : ∀ x ∈ s, CuntzLE x b) :
    CuntzLE a b := (isClosed b).closure_subset_iff.mpr hs ha

theorem conjugate {a : Matrix κ κ A} {b : Matrix ν ν A} (h : CuntzLE a b)
    (v : Matrix ι κ A) : CuntzLE (v * a * v.conjTranspose) b := by
  have hc : Continuous (fun x : Matrix κ κ A => v * x * v.conjTranspose) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  apply of_mem_closure ((image_closure_subset_closure_image hc) ⟨a, h, rfl⟩)
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using exact b (v * w)

theorem trans {a : Matrix ι ι A} {b : Matrix κ κ A} {c : Matrix ν ν A}
    (hab : CuntzLE a b) (hbc : CuntzLE b c) : CuntzLE a c := by
  apply of_mem_closure hab
  rintro _ ⟨v, rfl⟩
  exact hbc.conjugate v

/-- Explicit norm-approximation contract, using the actual C*-matrix norm. -/
theorem iff_approx [Fintype ι] (a : Matrix ι ι A) (b : Matrix κ κ A) :
    CuntzLE a b ↔ ∀ ε : ℝ, 0 < ε → ∃ v : Matrix ι κ A,
      ‖CStarMatrix.ofMatrix (a - v * b * v.conjTranspose)‖ < ε := by
  change CStarMatrix.ofMatrix a ∈ closure (Set.range fun v : Matrix ι κ A =>
    CStarMatrix.ofMatrix (v * b * v.conjTranspose)) ↔ _
  rw [Metric.mem_closure_iff]
  simp only [Set.mem_range, exists_exists_eq_and, dist_eq_norm]
  rfl

end CuntzLE

variable [Fintype ι]

/-- Mutual actual rectangular comparison; no order or state is assumed. -/
def CuntzEquivalent (a : Matrix ι ι A) (b : Matrix κ κ A) : Prop :=
  CuntzLE a b ∧ CuntzLE b a

namespace CuntzEquivalent

theorem refl (a : Matrix ι ι A) : CuntzEquivalent a a := ⟨.refl a, .refl a⟩
theorem symm {a : Matrix ι ι A} {b : Matrix κ κ A}
    (h : CuntzEquivalent a b) : CuntzEquivalent b a := ⟨h.2, h.1⟩

theorem trans {a : Matrix ι ι A} {b : Matrix κ κ A} {c : Matrix ν ν A}
    (h : CuntzEquivalent a b) (h' : CuntzEquivalent b c) : CuntzEquivalent a c :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

end CuntzEquivalent
end Kaplansky

end

noncomputable section
open scoped Topology Matrix
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A]
variable {ι κ ν μ : Type*}

/-- Block addition before passing to Cuntz classes. -/
def cuntzBlock (a : Matrix ι ι A) (b : Matrix κ κ A) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) A := Matrix.fromBlocks a 0 0 b

theorem continuous_cuntzBlock : Continuous (fun p : Matrix ι ι A × Matrix κ κ A =>
    cuntzBlock p.1 p.2) := by
  apply continuous_matrix
  intro i j
  cases i <;> cases j <;> dsimp [cuntzBlock, Matrix.fromBlocks] <;> fun_prop

variable [Fintype κ] [Fintype μ]

theorem cuntzBlock_conjugate (a : Matrix κ κ A) (b : Matrix μ μ A)
    (v : Matrix ι κ A) (w : Matrix ν μ A) :
    (Matrix.fromBlocks v 0 0 w) * cuntzBlock a b *
      (Matrix.fromBlocks v 0 0 w).conjTranspose =
      cuntzBlock (v * a * v.conjTranspose) (w * b * w.conjTranspose) := by
  simp [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- Actual rectangular comparison is compatible with block addition. -/
theorem CuntzLE.block {a : Matrix ι ι A} {b : Matrix κ κ A}
    {c : Matrix ν ν A} {d : Matrix μ μ A} (hab : CuntzLE a b) (hcd : CuntzLE c d) :
    CuntzLE (cuntzBlock a c) (cuntzBlock b d) := by
  have hp : (a, c) ∈ closure ((Set.range fun v : Matrix ι κ A => v * b * v.conjTranspose) ×ˢ
      (Set.range fun w : Matrix ν μ A => w * d * w.conjTranspose)) := by
    rw [closure_prod_eq]
    exact ⟨hab, hcd⟩
  apply CuntzLE.of_mem_closure ((image_closure_subset_closure_image continuous_cuntzBlock) ⟨(a,c), hp, rfl⟩)
  rintro _ ⟨⟨_, _⟩, ⟨⟨v, rfl⟩, ⟨w, rfl⟩⟩, rfl⟩
  simpa only [cuntzBlock_conjugate] using
    CuntzLE.exact (cuntzBlock b d) (Matrix.fromBlocks v 0 0 w)

variable [Fintype ι] [Fintype ν]

theorem CuntzEquivalent.block {a : Matrix ι ι A} {b : Matrix κ κ A}
    {c : Matrix ν ν A} {d : Matrix μ μ A} (hab : CuntzEquivalent a b)
    (hcd : CuntzEquivalent c d) : CuntzEquivalent (cuntzBlock a c) (cuntzBlock b d) :=
  ⟨hab.1.block hcd.1, hab.2.block hcd.2⟩

end Kaplansky

end

noncomputable section
open scoped Topology Matrix
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A]
variable {ι κ ν : Type*} [Fintype ι] [Fintype ν]

/-- Taking the same row and column submatrix is an actual rectangular conjugation. -/
theorem CuntzLE.submatrix (a : Matrix ι ι A) (f : κ → ι) :
    CuntzLE (a.submatrix f f) a := by
  classical
  have he : (1 : Matrix ι ι A).submatrix f id * a *
      ((1 : Matrix ι ι A).submatrix f id).conjTranspose = a.submatrix f f := by
    rw [Matrix.conjTranspose_submatrix]
    simp only [Matrix.conjTranspose_one]
    have hleft : (1 : Matrix ι ι A).submatrix f id * a = a.submatrix f id := by
      simpa using Matrix.one_submatrix_mul f (Equiv.refl ι) a
    rw [hleft]
    simpa using Matrix.mul_submatrix_one (Equiv.refl ι) f (a.submatrix f id)
  rw [← he]
  exact CuntzLE.exact _ _

variable [Fintype κ]

/-- Relabeling the finite coordinates preserves the actual Cuntz class. -/
theorem cuntzEquivalent_submatrix_equiv (a : Matrix ι ι A) (e : κ ≃ ι) :
    CuntzEquivalent (a.submatrix e e) a := by
  refine ⟨CuntzLE.submatrix a e, ?_⟩
  simpa using CuntzLE.submatrix (a.submatrix e e) e.symm

/-- Enlarging by an arbitrary zero corner does not change a Cuntz class. -/
theorem cuntzEquivalent_block_zero (a : Matrix ι ι A) :
    CuntzEquivalent (cuntzBlock a (0 : Matrix κ κ A)) a := by
  classical
  let v : Matrix (ι ⊕ κ) ι A := Matrix.fromRows 1 0
  have he : v * a * v.conjTranspose = cuntzBlock a (0 : Matrix κ κ A) := by
    simp [v, cuntzBlock, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromRows_mul]
    ext i j
    cases i <;> cases j <;> rfl
  refine ⟨he ▸ CuntzLE.exact a v, ?_⟩
  exact CuntzLE.submatrix (cuntzBlock a (0 : Matrix κ κ A)) Sum.inl

/-- The permutation exchanging the blocks witnesses commutativity. -/
theorem cuntzEquivalent_block_comm (a : Matrix ι ι A) (b : Matrix κ κ A) :
    CuntzEquivalent (cuntzBlock a b) (cuntzBlock b a) := by
  have h := cuntzEquivalent_submatrix_equiv (cuntzBlock b a) (Equiv.sumComm ι κ)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  cases i <;> cases j <;> rfl

/-- Rebracketing three blocks witnesses associativity. -/
theorem cuntzEquivalent_block_assoc (a : Matrix ι ι A) (b : Matrix κ κ A)
    (c : Matrix ν ν A) :
    CuntzEquivalent (cuntzBlock (cuntzBlock a b) c) (cuntzBlock a (cuntzBlock b c)) := by
  have h := cuntzEquivalent_submatrix_equiv (cuntzBlock a (cuntzBlock b c))
    (Equiv.sumAssoc ι κ ν)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;> rfl

end Kaplansky

end

noncomputable section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem cuntzBlock_nonneg (a : Matrix ι ι A) (b : Matrix κ κ A)
    (ha : 0 ≤ CStarMatrix.ofMatrix a) (hb : 0 ≤ CStarMatrix.ofMatrix b) :
    0 ≤ CStarMatrix.ofMatrix (cuntzBlock a b) := by
  classical
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι A) := CStarAlgebra.instNonnegSpectrumClass'
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix κ κ A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix κ κ A) := CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨x, hx⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := CStarMatrix.ofMatrix a)).mp ha
  obtain ⟨y, hy⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := CStarMatrix.ofMatrix b)).mp hb
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) := CStarAlgebra.instNonnegSpectrumClass'
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
  refine ⟨CStarMatrix.ofMatrix (cuntzBlock (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)), ?_⟩
  change cuntzBlock a b =
    (cuntzBlock (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)).conjTranspose *
      cuntzBlock (CStarMatrix.ofMatrix.symm x) (CStarMatrix.ofMatrix.symm y)
  change a = (CStarMatrix.ofMatrix.symm x).conjTranspose * CStarMatrix.ofMatrix.symm x at hx
  change b = (CStarMatrix.ofMatrix.symm y).conjTranspose * CStarMatrix.ofMatrix.symm y at hy
  simp only [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_inj]
  exact ⟨hx, True.intro, True.intro, hy⟩

theorem cuntzSubmatrix_nonneg (a : Matrix ι ι A) (e : κ ≃ ι)
    (ha : 0 ≤ CStarMatrix.ofMatrix a) :
    0 ≤ CStarMatrix.ofMatrix (a.submatrix e e) := by
  classical
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix ι ι A) := CStarAlgebra.instNonnegSpectrumClass'
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix κ κ A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix κ κ A) := CStarAlgebra.instNonnegSpectrumClass'
  obtain ⟨x, hx⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := CStarMatrix.ofMatrix a)).mp ha
  refine CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
    ⟨CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm x).submatrix e e), ?_⟩
  change a.submatrix e e =
    ((CStarMatrix.ofMatrix.symm x).submatrix e e).conjTranspose *
      (CStarMatrix.ofMatrix.symm x).submatrix e e
  change a = (CStarMatrix.ofMatrix.symm x).conjTranspose * CStarMatrix.ofMatrix.symm x at hx
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hx]

/-- An actual positive matrix with a finite, explicitly stored size. -/
structure CuntzPositiveMatrix (A : Type*) [CStarAlgebra A] where
  size : ℕ
  matrix : Matrix (Fin size) (Fin size) A
  nonneg : 0 ≤ CStarMatrix.ofMatrix matrix

namespace CuntzPositiveMatrix

def zero : CuntzPositiveMatrix A := ⟨0, 0, le_rfl⟩

def unit (n : ℕ) : CuntzPositiveMatrix A := ⟨n, 1, zero_le_one⟩

/-- Actual block addition, relabeled by the standard finite-sum equivalence. -/
def add (a b : CuntzPositiveMatrix A) : CuntzPositiveMatrix A where
  size := a.size + b.size
  matrix := (cuntzBlock a.matrix b.matrix).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  nonneg := cuntzSubmatrix_nonneg _ _ (cuntzBlock_nonneg _ _ a.nonneg b.nonneg)

instance instPreorder : Preorder (CuntzPositiveMatrix A) where
  le a b := CuntzLE a.matrix b.matrix
  le_refl a := .refl a.matrix
  le_trans _ _ _ := CuntzLE.trans

theorem add_equiv (a b : CuntzPositiveMatrix A) :
    CuntzEquivalent (add a b).matrix (cuntzBlock a.matrix b.matrix) :=
  cuntzEquivalent_submatrix_equiv _ _

theorem add_le_add {a b c d : CuntzPositiveMatrix A} (hab : a ≤ b) (hcd : c ≤ d) :
    add a c ≤ add b d :=
  (add_equiv a c).1.trans ((CuntzLE.block hab hcd).trans (add_equiv b d).2)

theorem zero_le (a : CuntzPositiveMatrix A) : zero ≤ a := .zero a.matrix

end CuntzPositiveMatrix
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Content
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact dimension contents, their finite measures, and positive support. -/

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky

/-- The elementary dimension properties used to construct a compact content.
This is an auxiliary interface, not a quasitrace or a linearity assumption. -/
structure PositiveDimensionFunctional (X : Type*) [TopologicalSpace X] where
  toFun : C(X, ℝ) → ℝ
  nonneg : ∀ f, 0 ≤ f → 0 ≤ toFun f
  mono : ∀ f g, 0 ≤ f → f ≤ g → toFun f ≤ toFun g
  subadd : ∀ f g, 0 ≤ f → 0 ≤ g → toFun (f+g) ≤ toFun f + toFun g
  orthogonal : ∀ f g, 0 ≤ f → 0 ≤ g → f*g=0 → toFun (f+g) = toFun f + toFun g

namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

/-- Continuous nonnegative functions majorizing one on the compact set. -/
def majorants (K : Compacts X) : Set C(X, ℝ) := {f | 0 ≤ f ∧ ∀ x ∈ K, 1 ≤ f x}

def compactValue (K : Compacts X) : ℝ := sInf (D.toFun '' majorants K)

theorem majorants_nonempty (K : Compacts X) : (majorants K).Nonempty :=
  ⟨1, zero_le_one, fun _ _ => le_rfl⟩

theorem majorant_values_bddBelow (K : Compacts X) : BddBelow (D.toFun '' majorants K) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact D.nonneg f hf.1

theorem compactValue_nonneg (K : Compacts X) : 0 ≤ D.compactValue K := by
  apply le_csInf ((majorants_nonempty K).image D.toFun)
  rintro _ ⟨f, hf, rfl⟩
  exact D.nonneg f hf.1

theorem compactValue_le (K : Compacts X) {f : C(X, ℝ)} (hf : f ∈ majorants K) :
    D.compactValue K ≤ D.toFun f := csInf_le (D.majorant_values_bddBelow K) ⟨f, hf, rfl⟩

theorem le_compactValue (K : Compacts X) {r : ℝ}
    (h : ∀ f ∈ majorants K, r ≤ D.toFun f) : r ≤ D.compactValue K := by
  apply le_csInf ((majorants_nonempty K).image D.toFun)
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

theorem compactValue_le_one (K : Compacts X) : D.compactValue K ≤ D.toFun 1 :=
  D.compactValue_le K ⟨zero_le_one, fun _ _ => le_rfl⟩

theorem compactValue_mono (K L : Compacts X) (h : (K : Set X) ⊆ L) :
    D.compactValue K ≤ D.compactValue L := by
  apply D.le_compactValue
  intro f hf
  exact D.compactValue_le K ⟨hf.1, fun x hx => hf.2 x (h hx)⟩

theorem compactValue_sup_le (K L : Compacts X) :
    D.compactValue (K ⊔ L) ≤ D.compactValue K + D.compactValue L := by
  apply (sub_le_iff_le_add).mp
  apply D.le_compactValue K
  intro f hf
  suffices h : D.compactValue (K ⊔ L) - D.toFun f ≤ D.compactValue L by linarith
  apply D.le_compactValue L
  intro g hg
  have hfg : f+g ∈ majorants (K ⊔ L) := by
    refine ⟨add_nonneg hf.1 hg.1, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact (hf.2 x hx).trans (le_add_of_nonneg_right (hg.1 x))
    · exact (hg.2 x hx).trans (le_add_of_nonneg_left (hf.1 x))
  have h := (D.compactValue_le (K ⊔ L) hfg).trans (D.subadd f g hf.1 hg.1)
  linarith

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky

/-- Disjoint closed sets admit nonnegative continuous cutoffs with disjoint
supports and sum at most one. -/
theorem exists_disjoint_compact_cutoffs {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (hKL : Disjoint K L) :
    ∃ u v : C(X, ℝ), 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧ u*v=0 ∧
      (∀ x ∈ K, u x=1) ∧ (∀ x ∈ L, v x=1) := by
  obtain ⟨f, hfK, hfL, hf⟩ := exists_continuous_zero_one_of_isClosed hK hL hKL
  let u : C(X, ℝ) := ⟨fun x => max (1-3*f x) 0, by fun_prop⟩
  let v : C(X, ℝ) := ⟨fun x => max (3*f x-2) 0, by fun_prop⟩
  refine ⟨u, v, (fun x => le_max_right _ _), (fun x => le_max_right _ _), ?_, ?_, ?_, ?_⟩
  · intro x
    change max (1-3*f x) 0 + max (3*f x-2) 0 ≤ 1
    have hx := hf x
    rcases le_total (1-3*f x) 0 with h | h <;>
      rcases le_total (3*f x-2) 0 with h' | h'
    · rw [max_eq_right h, max_eq_right h']; norm_num
    · rw [max_eq_right h, max_eq_left h']; linarith [hx.2]
    · rw [max_eq_left h, max_eq_right h']; linarith [hx.1]
    · linarith
  · ext x
    change max (1-3*f x) 0 * max (3*f x-2) 0 = 0
    by_cases h : 1-3*f x ≤ 0
    · rw [max_eq_right h, zero_mul]
    · rw [max_eq_right (by linarith : 3*f x-2 ≤ 0), mul_zero]
  · intro x hx
    change max (1-3*f x) 0 = 1
    rw [hfK hx]
    norm_num
  · intro x hx
    change max (3*f x-2) 0 = 1
    rw [hfL hx]
    norm_num

end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace
open scoped NNReal ENNReal
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] [NormalSpace X] (D : PositiveDimensionFunctional X)

theorem compactValue_sup_disjoint (K L : Compacts X)
    (hKL : Disjoint (K : Set X) L) (hK : IsClosed (K : Set X)) (hL : IsClosed (L : Set X)) :
    D.compactValue (K ⊔ L) = D.compactValue K + D.compactValue L := by
  apply le_antisymm (D.compactValue_sup_le K L)
  apply D.le_compactValue
  intro f hf
  obtain ⟨u, v, hu, hv, huv, hzero, huK, hvL⟩ :=
    exists_disjoint_compact_cutoffs (K : Set X) L hK hL hKL
  have huf : u*f ∈ majorants K := by
    refine ⟨fun x => mul_nonneg (hu x) (hf.1 x), ?_⟩
    intro x hx
    change 1 ≤ u x*f x
    rw [huK x hx, one_mul]
    exact hf.2 x (Or.inl hx)
  have hvf : v*f ∈ majorants L := by
    refine ⟨fun x => mul_nonneg (hv x) (hf.1 x), ?_⟩
    intro x hx
    change 1 ≤ v x*f x
    rw [hvL x hx, one_mul]
    exact hf.2 x (Or.inr hx)
  have hm : u*f+v*f ≤ f := by
    intro x
    change u x*f x+v x*f x ≤ f x
    have h := mul_le_mul_of_nonneg_right (huv x) (hf.1 x)
    change (u x+v x)*f x ≤ 1*f x at h
    simpa only [add_mul, one_mul] using h
  have hz : (u*f)*(v*f)=0 := by
    calc
      (u*f)*(v*f) = (u*v)*(f*f) := by ring
      _ = 0 := by rw [hzero, zero_mul]
  calc
    _ ≤ D.toFun (u*f)+D.toFun (v*f) := add_le_add (D.compactValue_le K huf) (D.compactValue_le L hvf)
    _ = D.toFun (u*f+v*f) := (D.orthogonal _ _ huf.1 hvf.1 hz).symm
    _ ≤ D.toFun f := D.mono _ _ (add_nonneg huf.1 hvf.1) hm

/-- An actual compact content obtained by infima of positive dimension values. -/
def content : MeasureTheory.Content X where
  toFun K := ⟨D.compactValue K, D.compactValue_nonneg K⟩
  mono' K L h := D.compactValue_mono K L h
  sup_le' K L := D.compactValue_sup_le K L
  sup_disjoint' K L h hK hL := NNReal.eq (D.compactValue_sup_disjoint K L h hK hL)

@[simp] theorem content_toReal (K : Compacts X) : (D.content K).toReal = D.compactValue K := by
  exact ENNReal.coe_toReal _

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] [NormalSpace X] [R1Space X]
    [MeasurableSpace X] [BorelSpace X] (D : PositiveDimensionFunctional X)

/-- The Borel measure furnished by the proved compact content. -/
def measure : Measure X := D.content.measure

theorem measure_open (U : Opens X) :
    D.measure (U : Set X) = D.content.innerContent U := by
  rw [measure, Content.measure_apply _ U.isOpen.measurableSet, Content.outerMeasure_opens]

theorem measure_open_eq_sup (U : Opens X) :
    D.measure (U : Set X) = ⨆ (K : Compacts X) (_ : (K : Set X) ⊆ U), D.content K :=
  D.measure_open U

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] in
theorem content_le_one (K : Compacts X) : D.content K ≤ ENNReal.ofReal (D.toFun 1) := by
  rw [← ENNReal.ofReal_toReal (show D.content K ≠ ∞ from ENNReal.coe_ne_top)]
  rw [D.content_toReal K]
  exact ENNReal.ofReal_le_ofReal (D.compactValue_le_one K)

theorem measure_univ_le : D.measure Set.univ ≤ ENNReal.ofReal (D.toFun 1) := by
  change D.measure ((⊤ : Opens X) : Set X) ≤ _
  rw [D.measure_open_eq_sup]
  exact iSup₂_le fun K _ => D.content_le_one K

instance measure_isFiniteMeasure : IsFiniteMeasure D.measure :=
  ⟨D.measure_univ_le.trans_lt ENNReal.ofReal_lt_top⟩

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

theorem zero_value : D.toFun 0 = 0 := by
  have h := D.orthogonal 0 0 le_rfl le_rfl (mul_zero _)
  rw [add_zero] at h
  linarith

theorem compactValue_empty : D.compactValue ⊥ = 0 := by
  apply le_antisymm _ (D.compactValue_nonneg _)
  rw [← D.zero_value]
  exact D.compactValue_le _ ⟨le_rfl, fun _ hx => False.elim hx⟩

/-- Positive scalar invariance is a dimension property, not spectral homogeneity. -/
def ScaleInvariant : Prop := ∀ (f : C(X, ℝ)), 0 ≤ f → ∀ r : ℝ, 0 < r →
  D.toFun (r • f) = D.toFun f

theorem compactValue_le_of_pos (hscale : D.ScaleInvariant) (K : Compacts X)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (hK : ∀ x ∈ K, 0 < f x) :
    D.compactValue K ≤ D.toFun f := by
  by_cases hne : (K : Set X).Nonempty
  · obtain ⟨x, hx, hmin⟩ := K.isCompact.exists_isMinOn hne f.continuous.continuousOn
    have hp := hK x hx
    rw [← hscale f hf ((f x)⁻¹) (inv_pos.mpr hp)]
    apply D.compactValue_le
    refine ⟨fun y => mul_nonneg (inv_nonneg.mpr hp.le) (hf y), ?_⟩
    intro y hy
    change 1 ≤ (f x)⁻¹ * f y
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hp).mpr (by simpa using hmin hy)
  · have h : K = ⊥ := by
      ext x
      change (x ∈ K) ↔ False
      exact ⟨fun hx => hne ⟨x, hx⟩, False.elim⟩
    rw [h, D.compactValue_empty]
    exact D.nonneg f hf

variable [CompactSpace X]

/-- A function vanishing off K has dimension at most the compact content of K. -/
theorem value_le_compactValue_of_support (hscale : D.ScaleInvariant) (K : Compacts X)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (hs : ∀ x, x ∉ K → f x=0) :
    D.toFun f ≤ D.compactValue K := by
  apply D.le_compactValue
  intro g hg
  have hp : 0 < ‖f‖+1 := by linarith [norm_nonneg f]
  have hle : f ≤ (‖f‖+1) • g := by
    intro x
    change f x ≤ (‖f‖+1)*g x
    by_cases hx : x ∈ K
    · have hb : f x ≤ ‖f‖+1 := (f.apply_le_norm x).trans (by linarith)
      exact hb.trans (le_mul_of_one_le_right hp.le (hg.2 x hx))
    · rw [hs x hx]
      exact mul_nonneg hp.le (hg.1 x)
  calc
    D.toFun f ≤ D.toFun ((‖f‖+1) • g) := D.mono _ _ hf hle
    _ = D.toFun g := hscale g hg.1 _ hp

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal Topology
namespace Kaplansky

/-- Continuous scalar cutoff, used only for uniform approximation of functions. -/
def continuousDimensionCutoff {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (t : ℝ) : C(X, ℝ) :=
  ⟨fun x => max (f x-t) 0, by fun_prop⟩

theorem continuousDimensionCutoff_nonneg {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (t : ℝ) :
    0 ≤ continuousDimensionCutoff f t := fun _ => le_max_right _ _

theorem continuousDimensionCutoff_zero {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (hf : 0 ≤ f) :
    continuousDimensionCutoff f 0 = f := by
  ext x
  change max (f x-0) 0 = f x
  rw [sub_zero, max_eq_left (show 0 ≤ f x from hf x)]

namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

/-- Lower semicontinuity is required only on the nonnegative cone. -/
def ConeLowerSemicontinuous : Prop :=
  LowerSemicontinuous (fun f : {f : C(X, ℝ) // 0 ≤ f} => D.toFun f.val)

theorem exists_positive_cutoff (hsc : D.ConeLowerSemicontinuous)
    (f : C(X, ℝ)) (hf : 0 ≤ f) {r : ℝ} (hr : r < D.toFun f) :
    ∃ t : ℝ, 0 < t ∧ r < D.toFun (continuousDimensionCutoff f t) := by
  let g : ℝ → {f : C(X, ℝ) // 0 ≤ f} :=
    fun t => ⟨continuousDimensionCutoff f t, continuousDimensionCutoff_nonneg f t⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × X => max (f p.2-p.1) 0)
    fun_prop
  have h0 : r < D.toFun (g 0).val := by
    simpa only [g, continuousDimensionCutoff_zero f hf] using hr
  have he := (hsc.comp hg) 0 r h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ/2, half_pos hδ, hball ?_⟩
  change dist (δ/2) (0 : ℝ) < δ
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  linarith

variable [CompactSpace X] [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

/-- The finite measure represents dimension on every positive support.
The proof uses genuine compact contents and lower semicontinuity, not an
assumed measure representation or finite-spectrum approximation. -/
theorem measure_positive_support (hscale : D.ScaleInvariant) (hsc : D.ConeLowerSemicontinuous)
    (f : C(X, ℝ)) (hf : 0 ≤ f) :
    D.measure {x | 0 < f x} = ENNReal.ofReal (D.toFun f) := by
  let U : Opens X := ⟨{x | 0 < f x}, isOpen_lt continuous_const f.continuous⟩
  change D.measure (U : Set X) = _
  apply le_antisymm
  · rw [D.measure_open_eq_sup]
    refine iSup₂_le fun K hK => ?_
    rw [← ENNReal.ofReal_toReal (show D.content K ≠ ∞ from ENNReal.coe_ne_top), D.content_toReal]
    exact ENNReal.ofReal_le_ofReal (D.compactValue_le_of_pos hscale K f hf (fun x hx => hK hx))
  · have hl : D.toFun f ≤ (D.measure (U : Set X)).toReal := by
      apply le_of_forall_lt
      intro r hr
      obtain ⟨t, ht, hrt⟩ := D.exists_positive_cutoff hsc f hf hr
      let K : Compacts X := ⟨{x | t ≤ f x}, (isClosed_le continuous_const f.continuous).isCompact⟩
      have hKU : (K : Set X) ⊆ U := fun x hx => ht.trans_le hx
      have hs : ∀ x, x ∉ K → continuousDimensionCutoff f t x = 0 := by
        intro x hx
        change max (f x-t) 0=0
        apply max_eq_right
        have hx' : ¬t ≤ f x := hx
        linarith
      have hle := D.value_le_compactValue_of_support hscale K
        (continuousDimensionCutoff f t) (continuousDimensionCutoff_nonneg f t) hs
      have hm : D.compactValue K ≤ (D.measure (U : Set X)).toReal := by
        rw [← D.content_toReal K, D.measure_open]
        apply ENNReal.toReal_mono
        · rw [← D.measure_open]
          exact measure_ne_top _ _
        · exact D.content.le_innerContent K U hKU
      exact hrt.trans_le (hle.trans hm)
    calc
      ENNReal.ofReal (D.toFun f) ≤ ENNReal.ofReal (D.measure (U : Set X)).toReal :=
        ENNReal.ofReal_le_ofReal hl
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)

end PositiveDimensionFunctional
end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Monoid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered Cuntz monoid and compression by its order unit. -/

noncomputable section
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The ordered Cuntz monoid of actual positive finite matrices over A.
The order is rectangular norm comparison, not an assumed abstract relation. -/
abbrev CuntzMonoid (A : Type*) [CStarAlgebra A] :=
  Antisymmetrization (CuntzPositiveMatrix A) (· ≤ ·)

def cuntzClass (a : CuntzPositiveMatrix A) : CuntzMonoid A :=
  toAntisymmetrization (· ≤ ·) a

theorem cuntzClass_le (a b : CuntzPositiveMatrix A) :
    cuntzClass a ≤ cuntzClass b ↔ CuntzLE a.matrix b.matrix :=
  toAntisymmetrization_le_toAntisymmetrization_iff

theorem cuntzClass_eq (a b : CuntzPositiveMatrix A) :
    cuntzClass a = cuntzClass b ↔ CuntzEquivalent a.matrix b.matrix := by
  rw [le_antisymm_iff, cuntzClass_le, cuntzClass_le]
  rfl

instance instZeroCuntzMonoid : Zero (CuntzMonoid A) := ⟨cuntzClass .zero⟩
instance instAddCuntzMonoid : Add (CuntzMonoid A) where
  add := Quotient.map₂ CuntzPositiveMatrix.add (fun _ _ ha _ _ hb =>
    ⟨CuntzPositiveMatrix.add_le_add ha.1 hb.1, CuntzPositiveMatrix.add_le_add ha.2 hb.2⟩)

@[simp] theorem cuntzClass_add (a b : CuntzPositiveMatrix A) :
    cuntzClass (a.add b) = cuntzClass a + cuntzClass b := rfl

instance instAddCommMonoidCuntzMonoid : AddCommMonoid (CuntzMonoid A) where
  add_assoc a b c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv (a.add b) c).trans
      (((CuntzPositiveMatrix.add_equiv a b).block (.refl c.matrix)).trans
        ((cuntzEquivalent_block_assoc a.matrix b.matrix c.matrix).trans
          (((CuntzEquivalent.refl a.matrix).block (CuntzPositiveMatrix.add_equiv b c).symm).trans
            (CuntzPositiveMatrix.add_equiv a (b.add c)).symm)))
  add_comm a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv a b).trans
      ((cuntzEquivalent_block_comm a.matrix b.matrix).trans
        (CuntzPositiveMatrix.add_equiv b a).symm)
  add_zero a := by
    induction a using Quotient.inductionOn with | h a =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv a .zero).trans (cuntzEquivalent_block_zero a.matrix)
  zero_add a := by
    induction a using Quotient.inductionOn with | h a =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv .zero a).trans
      ((cuntzEquivalent_block_comm _ _).trans (cuntzEquivalent_block_zero a.matrix))
  nsmul := nsmulRec

theorem cuntzMonoid_nonneg (x : CuntzMonoid A) : 0 ≤ x := by
  induction x using Quotient.inductionOn with | h x =>
  exact (cuntzClass_le _ _).mpr (CuntzPositiveMatrix.zero_le x)

/-- Class of the n-by-n identity. -/
def cuntzUnit (A : Type*) [CStarAlgebra A] (n : ℕ) : CuntzMonoid A :=
  cuntzClass (.unit n)

theorem cuntzUnit_zero : cuntzUnit A 0 = 0 := by
  apply (cuntzClass_eq _ _).mpr
  have h : (CuntzPositiveMatrix.unit (A := A) 0).matrix = 0 := by
    ext i
    exact Fin.elim0 i
  change CuntzEquivalent _ (0 : Matrix (Fin 0) (Fin 0) A)
  rw [h]
  exact .refl _

theorem cuntzUnit_add (m n : ℕ) : cuntzUnit A (m+n) = cuntzUnit A m + cuntzUnit A n := by
  apply (cuntzClass_eq _ _).mpr
  have h : (CuntzPositiveMatrix.add (CuntzPositiveMatrix.unit (A := A) m)
      (CuntzPositiveMatrix.unit n)).matrix = (1 : Matrix (Fin (m+n)) (Fin (m+n)) A) := by
    simp [CuntzPositiveMatrix.add, CuntzPositiveMatrix.unit, cuntzBlock,
      Matrix.fromBlocks_one]
  change CuntzEquivalent 1 _
  rw [h]
  exact .refl _

theorem cuntzUnit_nsmul (n : ℕ) : n • cuntzUnit A 1 = cuntzUnit A n := by
  induction n with
  | zero => simp [cuntzUnit_zero]
  | succ n ih => rw [succ_nsmul, ih, ← cuntzUnit_add]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Dimension states of the Cuntz monoid and positivity. -/

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- A normalized dimension state on actual positive finite matrices.
This is a semigroup state, not yet a quasitrace or its regularization. -/
structure CuntzDimensionState (A : Type*) [CStarAlgebra A] where
  state : CuntzMonoid A →+ ℝ
  monotone : Monotone state
  normalized : state (cuntzUnit A 1) = 1

namespace CuntzDimensionState

def value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : ℝ := d.state (cuntzClass a)

theorem value_mono (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzLE a.matrix b.matrix) : d.value a ≤ d.value b :=
  d.monotone ((cuntzClass_le a b).mpr h)

theorem value_eq (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzEquivalent a.matrix b.matrix) : d.value a = d.value b :=
  le_antisymm (d.value_mono h.1) (d.value_mono h.2)

theorem value_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) :
    d.value (a.add b) = d.value a + d.value b := by
  simp only [value, cuntzClass_add, map_add]

theorem value_unit (d : CuntzDimensionState A) (n : ℕ) :
    d.value (.unit n) = (n : ℝ) := by
  change d.state (cuntzUnit A n) = _
  rw [← cuntzUnit_nsmul, map_nsmul, d.normalized]
  simp

theorem value_zero (d : CuntzDimensionState A) : d.value .zero = 0 := d.state.map_zero

theorem value_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : 0 ≤ d.value a := by
  simpa only [map_zero, value] using d.monotone (cuntzMonoid_nonneg (cuntzClass a))

end CuntzDimensionState
end Kaplansky

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- Positive order gives actual approximate conjugation. An inverse
square-root of b+δ1 supplies a contraction and an error bounded by δ. -/
theorem exists_positiveOrder_approx {a b : A} (ha : 0 ≤ a) (hab : a ≤ b)
    (ε : ℝ) (hε : 0 < ε) : ∃ v : A, ‖a - v*b*star v‖ < ε := by
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hd0 : 0 ≤ δ • (1 : A) := smul_nonneg hδ.le zero_le_one
  have hd : IsStrictlyPositive (δ • (1 : A)) := by
    refine ⟨hd0, ?_⟩
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (isUnit_iff_ne_zero.mpr hδ.ne').map (algebraMap ℝ A)
  let Q := b + δ • (1 : A)
  have hQ : IsStrictlyPositive Q := IsStrictlyPositive.nonneg_add (ha.trans hab) hd
  let S := CFC.sqrt a
  let L := Q ^ (-(1/2) : ℝ)
  let v := S * L
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hL : star L = L := (CFC.rpow_nonneg (a := Q) (y := (-(1/2) : ℝ))).isSelfAdjoint.star_eq
  have hv : ‖v‖ ≤ 1 := (le_iff_norm_sqrt_mul_rpow a Q ha hQ).mp
    (hab.trans (le_add_of_nonneg_right hd0))
  have he : v * Q * star v = a := by
    calc
      v * Q * star v = S * (L * Q * L) * S := by simp only [v, star_mul, hS, hL, mul_assoc]
      _ = S * S := by rw [CFC.conjugate_rpow_neg_one_half Q hQ]; simp
      _ = a := CFC.sqrt_mul_sqrt_self a ha
  have herr : a - v*b*star v = δ • (v*star v) := by
    rw [← he]
    simp only [Q, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, add_sub_cancel_left]
  refine ⟨v, ?_⟩
  rw [herr, norm_smul, Real.norm_of_nonneg hδ.le]
  have hn := norm_nonneg v
  have hsq : ‖v‖ * ‖v‖ ≤ 1 := by nlinarith
  have hbound : δ * (‖v‖ * ‖v‖) ≤ δ := by nlinarith
  exact (mul_le_mul_of_nonneg_left (by simpa only [norm_star] using norm_mul_le v (star v)) hδ.le).trans_lt
    (hbound.trans_lt (half_lt_self hε))

theorem cuntzLE_of_nonneg_le {n : ℕ} {a b : CStarMatrix (Fin n) (Fin n) A}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    CuntzLE (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) := by
  apply (CuntzLE.iff_approx _ _).mpr
  intro ε hε
  obtain ⟨v, hv⟩ := exists_positiveOrder_approx ha hab ε hε
  exact ⟨CStarMatrix.ofMatrix.symm v, hv⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Cutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Functional calculus cutoffs and perturbation comparison. -/

open scoped Matrix CStarAlgebra Topology

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The genuine continuous spectral cutoff (a-ε)₊. -/
def cuntzCutoff (a : A) (ε : ℝ) : A := cfc (fun t : ℝ => max (t-ε) 0) a

theorem cuntzCutoff_nonneg (a : A) (ε : ℝ) : 0 ≤ cuntzCutoff a ε :=
  cfc_nonneg fun _ _ => le_max_right _ _

theorem cuntzCutoff_le {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 ≤ ε) :
    cuntzCutoff a ε ≤ a := by
  have h : cfc (fun t : ℝ => max (t-ε) 0) a ≤ cfc (fun t : ℝ => t) a :=
    cfc_mono fun t ht => max_le (sub_le_self t hε) (spectrum_nonneg_of_nonneg ha ht)
  simpa only [cuntzCutoff, cfc_id' ℝ a ha.isSelfAdjoint] using h

theorem cuntzCutoff_antitone (a : A) : Antitone (cuntzCutoff a) := by
  intro ε δ h
  exact cfc_mono fun _ _ => max_le_max_right 0 (sub_le_sub_left h _)

/-- Uniform norm control, with the actual C*-norm. -/
theorem norm_sub_cuntzCutoff_le {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖a - cuntzCutoff a ε‖ ≤ ε := by
  have he : cfc (fun t : ℝ => t - max (t-ε) 0) a = a - cuntzCutoff a ε := by
    rw [cfc_sub (fun t : ℝ => t) (fun t => max (t-ε) 0) a,
      cfc_id' ℝ a ha.isSelfAdjoint]
    rfl
  rw [← he]
  apply norm_cfc_le hε
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg ha ht
  rcases le_total ε t with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), sub_sub_cancel, Real.norm_of_nonneg hε]
  · rw [max_eq_right (sub_nonpos.mpr h), sub_zero, Real.norm_of_nonneg ht0]
    exact h

/-- Norm comparison of positives is detected by all strictly positive
spectral cutoffs. This does not assume continuity of a dimension state. -/
theorem cuntzLE_iff_all_cutoffs {n m : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a)
    (b : CStarMatrix (Fin m) (Fin m) A) :
    CuntzLE (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) ↔
      ∀ ε : ℝ, 0 < ε → CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε))
        (CStarMatrix.ofMatrix.symm b) := by
  constructor
  · intro h ε hε
    exact (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg a ε) (cuntzCutoff_le ha hε.le)).trans h
  · intro h
    apply (CuntzLE.iff_approx _ _).mpr
    intro ε hε
    obtain ⟨v, hv⟩ := (CuntzLE.iff_approx _ _).mp (h (ε/2) (half_pos hε)) (ε/2) (half_pos hε)
    refine ⟨v, ?_⟩
    let q : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix
      (v * CStarMatrix.ofMatrix.symm b * v.conjTranspose)
    change ‖a - q‖ < ε
    have hv' : ‖cuntzCutoff a (ε/2) - q‖ < ε/2 := hv
    calc
      ‖a - q‖ ≤ ‖a - cuntzCutoff a (ε/2)‖ + ‖cuntzCutoff a (ε/2) - q‖ := by
        simpa only [dist_eq_norm] using dist_triangle a (cuntzCutoff a (ε/2)) q
      _ ≤ ε/2 + ‖cuntzCutoff a (ε/2) - q‖ := by
        have hn := norm_sub_cuntzCutoff_le ha (half_pos hε).le
        linarith
      _ < ε := by linarith

/-- The cutoff remains an actual positive matrix of the same finite size. -/
def CuntzPositiveMatrix.cutoff (a : CuntzPositiveMatrix A) (ε : ℝ) : CuntzPositiveMatrix A :=
  ⟨a.size, CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) ε),
    cuntzCutoff_nonneg _ _⟩

theorem CuntzDimensionState.cutoff_value_antitone (d : CuntzDimensionState A)
    (a : CuntzPositiveMatrix A) : Antitone (fun ε => d.value (a.cutoff ε)) := by
  intro ε δ h
  exact d.value_mono (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_antitone _ h))

theorem CuntzDimensionState.cutoff_value_le (d : CuntzDimensionState A)
    (a : CuntzPositiveMatrix A) {ε : ℝ} (hε : 0 ≤ ε) : d.value (a.cutoff ε) ≤ d.value a :=
  d.value_mono (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_le a.nonneg hε))


/-- Positive scalar multiplication is implemented by scalar conjugation. -/
theorem cuntzLE_smul {n : ℕ} (a : CStarMatrix (Fin n) (Fin n) A)
    {r : ℝ} (hr : 0 ≤ r) :
    CuntzLE (CStarMatrix.ofMatrix.symm (r • a)) (CStarMatrix.ofMatrix.symm a) := by
  let v : CStarMatrix (Fin n) (Fin n) A := Real.sqrt r • 1
  have h : v * a * star v = r • a := by
    simp only [v, star_smul, star_trivial, star_one, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, smul_smul, Real.mul_self_sqrt hr]
  have h' := CuntzLE.exact (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm v)
  change CuntzLE (CStarMatrix.ofMatrix.symm (v * a * star v)) _ at h'
  rwa [h] at h'

theorem cuntzEquivalent_pos_smul {n : ℕ} (a : CStarMatrix (Fin n) (Fin n) A)
    {r : ℝ} (hr : 0 < r) :
    CuntzEquivalent (CStarMatrix.ofMatrix.symm (r • a)) (CStarMatrix.ofMatrix.symm a) := by
  refine ⟨cuntzLE_smul a hr.le, ?_⟩
  simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using
    cuntzLE_smul (r • a) (inv_nonneg.mpr hr.le)


/-- A cutoff square root localized above ε. The inequality is scalar
functional calculus in a single self-adjoint element. -/
theorem exists_cutoff_localizer {a : A} (ha : 0 ≤ a) (ε : ℝ) :
    ∃ x : A, star x = x ∧ x*x = cuntzCutoff a ε ∧
      ε • cuntzCutoff a ε ≤ x*a*x := by
  let f : ℝ → ℝ := fun t => Real.sqrt (max (t-ε) 0)
  let x := cfc f a
  have hx : star x = x := (cfc_nonneg (f := f) (a := a)
    (fun t _ => Real.sqrt_nonneg _) : 0 ≤ x).isSelfAdjoint.star_eq
  have hsq : x*x = cuntzCutoff a ε := by
    rw [← cfc_mul f f a]
    exact cfc_congr fun t _ => Real.mul_self_sqrt (le_max_right _ _)
  refine ⟨x, hx, hsq, ?_⟩
  have hid := cfc_id' ℝ a ha.isSelfAdjoint
  change ε • cfc (fun t : ℝ => max (t-ε) 0) a ≤ cfc f a * a * cfc f a
  have he : cfc (fun t => f t * t * f t) a = cfc f a * a * cfc f a := by
    rw [cfc_mul (fun t => f t * t) f a, cfc_mul f (fun t : ℝ => t) a, hid]
  rw [← he, ← cfc_const_mul ε (fun t : ℝ => max (t-ε) 0) a]
  refine cfc_mono (hf := by fun_prop) (hg := by dsimp [f]; fun_prop) ?_
  intro t ht
  have he : f t * t * f t = t * max (t-ε) 0 := by
    calc
      f t * t * f t = t * (f t * f t) := by ring
      _ = t * max (t-ε) 0 := by rw [show f t * f t = max (t-ε) 0 from Real.mul_self_sqrt (le_max_right _ _)]
  rw [he]
  rcases le_total t ε with h | h
  · rw [max_eq_right (sub_nonpos.mpr h)]; simp
  · exact mul_le_mul_of_nonneg_right h (le_max_right _ _)

/-- A strict norm perturbation gives cutoff Cuntz comparison.
No operator monotonicity of the positive-part function is used. -/
theorem cuntzLE_cutoff_of_norm_sub_lt {n : ℕ}
    {a b : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) (hb : IsSelfAdjoint b)
    {ε : ℝ} (h : ‖a-b‖ < ε) :
    CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε))
      (CStarMatrix.ofMatrix.symm b) := by
  let δ := ‖a-b‖
  have hδ : 0 < ε-δ := sub_pos.mpr h
  have hab : a ≤ b + δ • 1 := by
    have he := (ha.isSelfAdjoint.sub hb).le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at he
    exact sub_le_iff_le_add'.mp he
  obtain ⟨x, hx, hsq, hloc⟩ := exists_cutoff_localizer ha ε
  have hc := star_left_conjugate_le_conjugate hab x
  simp only [hx, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hsq] at hc
  have hbound : (ε-δ) • cuntzCutoff a ε ≤ x*b*x := by
    rw [sub_smul]
    exact sub_le_iff_le_add.mpr (hloc.trans hc)
  have hpos : 0 ≤ (ε-δ) • cuntzCutoff a ε := smul_nonneg hδ.le (cuntzCutoff_nonneg a ε)
  have hcmp := cuntzLE_of_nonneg_le hpos hbound
  have hsc := cuntzEquivalent_pos_smul (cuntzCutoff a ε) hδ
  have hex := CuntzLE.exact (CStarMatrix.ofMatrix.symm b) (CStarMatrix.ofMatrix.symm x)
  change CuntzLE (CStarMatrix.ofMatrix.symm (x*b*star x)) _ at hex
  rw [hx] at hex
  exact hsc.2.trans (hcmp.trans hex)


/-- Every positive cutoff of a Cuntz-smaller matrix is already below a
strictly positive cutoff of the larger matrix, including unequal sizes. -/
theorem CuntzLE.exists_cutoff {n m : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} {b : CStarMatrix (Fin m) (Fin m) A}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : CuntzLE (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ CuntzLE (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε))
      (CStarMatrix.ofMatrix.symm (cuntzCutoff b δ)) := by
  obtain ⟨v, hv⟩ := (CuntzLE.iff_approx _ _).mp h (ε/2) (half_pos hε)
  let g : CStarMatrix (Fin m) (Fin m) A → CStarMatrix (Fin n) (Fin n) A :=
    fun y => CStarMatrix.ofMatrix (v * CStarMatrix.ofMatrix.symm y * v.conjTranspose)
  have hg : Continuous g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε/2) (half_pos hε)
  let δ := η/2
  have hδ : 0 < δ := half_pos hη
  have hdist : dist (cuntzCutoff b δ) b < η := by
    rw [dist_eq_norm, norm_sub_rev]
    exact (norm_sub_cuntzCutoff_le hb hδ.le).trans_lt (half_lt_self hη)
  have hgb : ‖g (cuntzCutoff b δ) - g b‖ < ε/2 := by
    simpa only [dist_eq_norm] using hclose hdist
  have hab : ‖a - g (cuntzCutoff b δ)‖ < ε := by
    have hv' : ‖a - g b‖ < ε/2 := hv
    have ht : ‖a - g (cuntzCutoff b δ)‖ ≤ ‖a - g b‖ + ‖g b - g (cuntzCutoff b δ)‖ := by
      simpa only [dist_eq_norm] using dist_triangle a (g b) (g (cuntzCutoff b δ))
    rw [norm_sub_rev (g b)] at ht
    linarith
  have hsa : IsSelfAdjoint (g (cuntzCutoff b δ)) := by
    have hs : (CStarMatrix.ofMatrix.symm (cuntzCutoff b δ)).conjTranspose =
        CStarMatrix.ofMatrix.symm (cuntzCutoff b δ) :=
      (cuntzCutoff_nonneg b δ).isSelfAdjoint.star_eq
    change (v * CStarMatrix.ofMatrix.symm (cuntzCutoff b δ) * v.conjTranspose).conjTranspose =
      v * CStarMatrix.ofMatrix.symm (cuntzCutoff b δ) * v.conjTranspose
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hs, Matrix.mul_assoc]
  refine ⟨δ, hδ, (cuntzLE_cutoff_of_norm_sub_lt ha hsa hab).trans ?_⟩
  exact CuntzLE.exact _ v

/-- The cutoff quantifiers characterize the original norm-closure relation. -/
theorem cuntzLE_iff_cutoff_comparison (a b : CuntzPositiveMatrix A) :
    CuntzLE a.matrix b.matrix ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      CuntzLE (a.cutoff ε).matrix (b.cutoff δ).matrix := by
  constructor
  · intro h ε hε
    exact h.exists_cutoff a.nonneg b.nonneg hε
  · intro h
    apply (cuntzLE_iff_all_cutoffs (CStarMatrix.ofMatrix a.matrix) a.nonneg
      (CStarMatrix.ofMatrix b.matrix)).mpr
    intro ε hε
    obtain ⟨δ, hδ, hc⟩ := h ε hε
    exact hc.trans (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_le b.nonneg hδ.le))

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Regularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Regularized dimensions, cutoff calculus, and topological regularization. -/

open scoped Matrix CStarAlgebra Topology

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace CuntzDimensionState

/-- Cutoff regularization of the constructed dimension state, as a finite real supremum. -/
def regularized (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : ℝ :=
  sSup ((fun ε : ℝ => d.value (a.cutoff ε)) '' Set.Ioi 0)

theorem cutoff_values_nonempty (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    ((fun ε : ℝ => d.value (a.cutoff ε)) '' Set.Ioi 0).Nonempty :=
  ⟨_, ⟨1, by norm_num, rfl⟩⟩

theorem cutoff_values_bddAbove (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    BddAbove ((fun ε : ℝ => d.value (a.cutoff ε)) '' Set.Ioi 0) := by
  refine ⟨d.value a, ?_⟩
  rintro _ ⟨ε, hε, rfl⟩
  exact d.cutoff_value_le a hε.le

theorem cutoff_value_le_regularized (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {ε : ℝ} (hε : 0 < ε) : d.value (a.cutoff ε) ≤ d.regularized a :=
  le_csSup (d.cutoff_values_bddAbove a) ⟨ε, hε, rfl⟩

theorem regularized_le (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {r : ℝ} (h : ∀ ε : ℝ, 0 < ε → d.value (a.cutoff ε) ≤ r) : d.regularized a ≤ r := by
  apply csSup_le (d.cutoff_values_nonempty a)
  rintro _ ⟨ε, hε, rfl⟩
  exact h ε hε

theorem regularized_le_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.regularized a ≤ d.value a := d.regularized_le a fun _ hε => d.cutoff_value_le a hε.le

theorem regularized_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    0 ≤ d.regularized a :=
  (d.value_nonneg (a.cutoff 1)).trans (d.cutoff_value_le_regularized a (by norm_num))

/-- Cuntz monotonicity is proved using the two-cutoff comparison theorem. -/
theorem regularized_mono (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzLE a.matrix b.matrix) : d.regularized a ≤ d.regularized b := by
  apply d.regularized_le a
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := (cuntzLE_iff_cutoff_comparison a b).mp h ε hε
  exact (d.value_mono (a := a.cutoff ε) (b := b.cutoff δ) hc).trans
    (d.cutoff_value_le_regularized b hδ)

theorem regularized_eq (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzEquivalent a.matrix b.matrix) : d.regularized a = d.regularized b :=
  le_antisymm (d.regularized_mono h.1) (d.regularized_mono h.2)

theorem regularized_zero (d : CuntzDimensionState A) : d.regularized .zero = 0 :=
  le_antisymm ((d.regularized_le_value .zero).trans_eq d.value_zero) (d.regularized_nonneg .zero)

/-- Every number strictly below the supremum is exceeded by one actual cutoff value. -/
theorem exists_lt_cutoff_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {r : ℝ} (h : r < d.regularized a) : ∃ ε : ℝ, 0 < ε ∧ r < d.value (a.cutoff ε) := by
  by_contra! hn
  exact (not_le_of_gt h) (d.regularized_le a hn)

end CuntzDimensionState

theorem cuntzCutoff_one_half : cuntzCutoff (1 : A) (1/2) = (1/2 : ℝ) • (1 : A) := by
  unfold cuntzCutoff
  have he := cfc_algebraMap (A := A) (1 : ℝ) (fun t : ℝ => max (t-1/2) 0)
  norm_num [Algebra.algebraMap_eq_smul_one] at he ⊢

/-- Regularization preserves the value of every finite identity matrix. -/
theorem CuntzDimensionState.regularized_unit (d : CuntzDimensionState A) (n : ℕ) :
    d.regularized (.unit n) = (n : ℝ) := by
  apply le_antisymm ((d.regularized_le_value _).trans_eq (d.value_unit n))
  have he : d.value ((CuntzPositiveMatrix.unit (A := A) n).cutoff (1/2)) = d.value (.unit n) := by
    apply d.value_eq
    change CuntzEquivalent (CStarMatrix.ofMatrix.symm
      (cuntzCutoff (1 : CStarMatrix (Fin n) (Fin n) A) (1/2))) (1 : Matrix (Fin n) (Fin n) A)
    rw [cuntzCutoff_one_half]
    exact cuntzEquivalent_pos_smul 1 (by norm_num)
  rw [← d.value_unit n, ← he]
  exact d.cutoff_value_le_regularized _ (by norm_num)


/-- A norm neighborhood controls one fixed cutoff by the regularized value. -/
theorem CuntzDimensionState.cutoff_value_le_regularized_of_norm {n : ℕ}
    (d : CuntzDimensionState A) {a b : CStarMatrix (Fin n) (Fin n) A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) (hab : ‖a-b‖ < ε/2) :
    d.value ((⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ : CuntzPositiveMatrix A).cutoff ε) ≤
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  have hn : ‖a - cuntzCutoff b (ε/2)‖ < ε := by
    have ht : ‖a - cuntzCutoff b (ε/2)‖ ≤ ‖a-b‖ + ‖b - cuntzCutoff b (ε/2)‖ := by
      simpa only [dist_eq_norm] using dist_triangle a b (cuntzCutoff b (ε/2))
    have he := norm_sub_cuntzCutoff_le hb (half_pos hε).le
    linarith
  have hc := cuntzLE_cutoff_of_norm_sub_lt ha (cuntzCutoff_nonneg b (ε/2)).isSelfAdjoint hn
  exact (d.value_mono (a := (⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ : CuntzPositiveMatrix A).cutoff ε)
    (b := (⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ : CuntzPositiveMatrix A).cutoff (ε/2)) hc).trans
    (d.cutoff_value_le_regularized _ (half_pos hε))

/-- Lower semicontinuity on the full positive cone in each actual matrix norm. -/
theorem CuntzDimensionState.regularized_lowerSemicontinuous (d : CuntzDimensionState A)
    (n : ℕ) : LowerSemicontinuous (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) := by
  intro a r hr
  obtain ⟨ε, hε, he⟩ := d.exists_lt_cutoff_value _ hr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε/2, half_pos hε, ?_⟩
  intro b hb
  have hdist : ‖a.val-b.val‖ < ε/2 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hb
  exact he.trans_le (d.cutoff_value_le_regularized_of_norm a.property b.property hε hdist)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

local instance matrixRealFunctionalCalculus {ν : Type*} [Fintype ν] [DecidableEq ν] :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ν ν A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance productMatrixRealFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A × CStarMatrix κ κ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The genuine block-diagonal unital star homomorphism. -/
def cuntzBlockHom : (CStarMatrix ι ι A × CStarMatrix κ κ A) →⋆ₐ[ℂ]
    CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A where
  toFun p := CStarMatrix.ofMatrix (cuntzBlock p.1 p.2)
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := by exact Matrix.fromBlocks_one
  map_add' p q := by
    ext i j
    cases i <;> cases j <;> first | rfl | exact (zero_add (0 : A)).symm
  map_mul' p q := by
    change cuntzBlock (CStarMatrix.ofMatrix.symm p.1 * CStarMatrix.ofMatrix.symm q.1)
      (CStarMatrix.ofMatrix.symm p.2 * CStarMatrix.ofMatrix.symm q.2) =
      cuntzBlock (CStarMatrix.ofMatrix.symm p.1) (CStarMatrix.ofMatrix.symm p.2) *
        cuntzBlock (CStarMatrix.ofMatrix.symm q.1) (CStarMatrix.ofMatrix.symm q.2)
    simp only [cuntzBlock, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
  map_star' p := by
    ext i j
    cases i <;> cases j <;> first | rfl | exact (star_zero A).symm
  commutes' c := by
    classical
    simp only [Algebra.algebraMap_eq_smul_one]
    change Matrix.fromBlocks (c • (1 : Matrix ι ι A)) 0 0 (c • (1 : Matrix κ κ A)) = c • (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) A)
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp only [smul_zero]

theorem cuntzCutoff_block (a : CStarMatrix ι ι A) (b : CStarMatrix κ κ A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ε : ℝ) :
    cuntzCutoff (CStarMatrix.ofMatrix (cuntzBlock a b)) ε =
      CStarMatrix.ofMatrix (cuntzBlock (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε)) (CStarMatrix.ofMatrix.symm (cuntzCutoff b ε))) := by
  let φ := cuntzBlockHom (A := A) (ι := ι) (κ := κ)
  have h := φ.map_cfc (fun t : ℝ => max (t-ε) 0) (a,b)
    (ha := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)
    (hφa := (cuntzBlock_nonneg _ _ ha hb).isSelfAdjoint)
  rw [cfc_map_prod (S := ℂ) (fun t : ℝ => max (t-ε) 0) a b
    (ha := ha.isSelfAdjoint) (hb := hb.isSelfAdjoint)
    (hab := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)] at h
  exact h.symm

theorem cuntzCutoff_reindex (a : CStarMatrix ι ι A) (ha : 0 ≤ a) (e : κ ≃ ι) (ε : ℝ) :
    cuntzCutoff (CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm a).submatrix e e)) ε =
      CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm (cuntzCutoff a ε)).submatrix e e) := by
  let φ := (CStarMatrix.reindexₐ ℂ A e.symm).toStarAlgHom
  exact (φ.map_cfc (fun t : ℝ => max (t-ε) 0) a
    (ha := ha.isSelfAdjoint) (hφa := (cuntzSubmatrix_nonneg _ e ha).isSelfAdjoint)).symm

theorem CuntzPositiveMatrix.cutoff_add (a b : CuntzPositiveMatrix A) (ε : ℝ) :
    (a.add b).cutoff ε = (a.cutoff ε).add (b.cutoff ε) := by
  cases a with
  | mk n a ha =>
    cases b with
    | mk m b hb =>
      simp only [CuntzPositiveMatrix.add, CuntzPositiveMatrix.cutoff]
      congr 1
      have he := cuntzCutoff_reindex (CStarMatrix.ofMatrix (cuntzBlock a b))
        (cuntzBlock_nonneg _ _ ha hb) finSumFinEquiv.symm ε
      have hh : cuntzCutoff (CStarMatrix.ofMatrix (cuntzBlock a b)) ε =
          CStarMatrix.ofMatrix (cuntzBlock
            (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a) ε))
            (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix b) ε))) :=
        cuntzCutoff_block (CStarMatrix.ofMatrix a) (CStarMatrix.ofMatrix b) ha hb ε
      rw [hh] at he
      exact congrArg CStarMatrix.ofMatrix.symm he

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Squares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Square approximation, square swap, and orthogonal additivity. -/

section
open scoped CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The scalar error estimate underlying approximate comparison of xx* and x*x. -/
theorem squareSwap_scalar_error {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) :
    |t - (Real.sqrt (t+δ))⁻¹ * t * t * (Real.sqrt (t+δ))⁻¹| ≤ δ := by
  have hd : 0 < t+δ := add_pos_of_nonneg_of_pos ht hδ
  have hs : Real.sqrt (t+δ) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have he : t - (Real.sqrt (t+δ))⁻¹ * t * t * (Real.sqrt (t+δ))⁻¹ = t*δ/(t+δ) := by
    field_simp
    rw [Real.sq_sqrt hd.le]
    ring
  rw [he, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- A concrete functional-calculus approximation. No polar decomposition
or square-swap property of dimension functions is assumed. -/
theorem exists_squareSwap_approx (x : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖x * star x - v * (star x * x) * star v‖ < ε := by
  let b := x * star x
  have hb : 0 ≤ b := mul_star_self_nonneg x
  have hbsa : IsSelfAdjoint b := hb.isSelfAdjoint
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let f : ℝ → ℝ := fun t => (Real.sqrt (t+δ))⁻¹
  have hf : ContinuousOn f (spectrum ℝ b) := by
    apply ContinuousOn.inv₀ ((continuousOn_id.add continuousOn_const).sqrt)
    intro t ht
    exact (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hb ht) hδ)).ne'
  let L := cfc f b
  have hL : star L = L := (cfc_predicate f b : IsSelfAdjoint L).star_eq
  have he : cfc (fun t => t - f t * t * t * f t) b = b - L * b * b * L := by
    rw [cfc_sub (fun t : ℝ => t) (fun t => f t * t * t * f t) b continuousOn_id (((hf.mul continuousOn_id).mul continuousOn_id).mul hf)]
    rw [cfc_mul (fun t => f t * t * t) f b ((hf.mul continuousOn_id).mul continuousOn_id) hf]
    rw [cfc_mul (fun t => f t * t) (fun t : ℝ => t) b (hf.mul continuousOn_id) continuousOn_id]
    rw [cfc_mul f (fun t : ℝ => t) b hf continuousOn_id, cfc_id' ℝ b]
  refine ⟨L*x, ?_⟩
  have hn : ‖cfc (fun t => t - f t * t * t * f t) b‖ ≤ δ := by
    apply norm_cfc_le hδ.le
    intro t ht
    exact squareSwap_scalar_error (spectrum_nonneg_of_nonneg hb ht) hδ
  have he' : x * star x - (L*x) * (star x*x) * star (L*x) = b - L*b*b*L := by
    simp only [star_mul, hL, b, mul_assoc]
  rw [he', ← he]
  exact hn.trans_lt (half_lt_self hε)

end Kaplansky

end

section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Cuntz square swapping is proved by norm approximants. -/
theorem cuntzLE_mul_star_self [DecidableEq ι] (x : CStarMatrix ι ι A) :
    CuntzLE (CStarMatrix.ofMatrix.symm (x * star x))
      (CStarMatrix.ofMatrix.symm (star x * x)) := by
  apply (CuntzLE.iff_approx _ _).mpr
  intro ε hε
  obtain ⟨v, hv⟩ := exists_squareSwap_approx x ε hε
  exact ⟨CStarMatrix.ofMatrix.symm v, hv⟩

theorem cuntzEquivalent_square_swap [DecidableEq ι] (x : CStarMatrix ι ι A) :
    CuntzEquivalent (CStarMatrix.ofMatrix.symm (x * star x))
      (CStarMatrix.ofMatrix.symm (star x * x)) := by
  refine ⟨cuntzLE_mul_star_self x, ?_⟩
  simpa only [star_star] using cuntzLE_mul_star_self (star x)

/-- Rectangular Gram matrices of different sizes have the same Cuntz class. -/
theorem cuntzEquivalent_rectangular_gram (v : Matrix ι κ A) :
    CuntzEquivalent (v * v.conjTranspose) (v.conjTranspose * v) := by
  classical
  let X : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A := CStarMatrix.ofMatrix (Matrix.fromBlocks 0 v 0 0)
  have hleft : CStarMatrix.ofMatrix.symm (X * star X) =
      cuntzBlock (v * v.conjTranspose) (0 : Matrix κ κ A) := by
    change Matrix.fromBlocks 0 v 0 0 * (Matrix.fromBlocks 0 v 0 0).conjTranspose = _
    simp [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  have hright : CStarMatrix.ofMatrix.symm (star X * X) =
      cuntzBlock (0 : Matrix ι ι A) (v.conjTranspose * v) := by
    change (Matrix.fromBlocks 0 v 0 0).conjTranspose * Matrix.fromBlocks 0 v 0 0 = _
    simp [cuntzBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  have h := cuntzEquivalent_square_swap X
  rw [hleft, hright] at h
  exact (cuntzEquivalent_block_zero _).symm.trans
    (h.trans ((cuntzEquivalent_block_comm _ _).trans (cuntzEquivalent_block_zero _)))

end Kaplansky

end

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- Orthogonality passes to actual positive square roots. -/
theorem sqrt_mul_sqrt_eq_zero_of_mul_eq_zero {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a*b = 0) : CFC.sqrt a * CFC.sqrt b = 0 := by
  have hsa : star a = a := ha.isSelfAdjoint.star_eq
  have hsb : star (CFC.sqrt b) = CFC.sqrt b := (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have h1 : a * CFC.sqrt b = 0 := by
    apply (CStarRing.mul_star_self_eq_zero_iff _).mp
    calc
      (a * CFC.sqrt b) * star (a * CFC.sqrt b) = a * b * a := by
        simp only [star_mul, hsa, hsb, mul_assoc]
        rw [← mul_assoc (CFC.sqrt b), CFC.sqrt_mul_sqrt_self b hb]
      _ = 0 := by rw [hab, zero_mul]
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hsa' : star (CFC.sqrt a) = CFC.sqrt a := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  calc
    star (CFC.sqrt a * CFC.sqrt b) * (CFC.sqrt a * CFC.sqrt b) = CFC.sqrt b * (a * CFC.sqrt b) := by
      simp only [star_mul, hsa', hsb, mul_assoc]
      rw [← mul_assoc (CFC.sqrt a), CFC.sqrt_mul_sqrt_self a ha]
    _ = 0 := by rw [h1, mul_zero]

/-- Orthogonal positive addition agrees with block addition in the Cuntz monoid. -/
theorem cuntzEquivalent_orthogonal_add {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b = 0) :
    CuntzEquivalent (CStarMatrix.ofMatrix.symm (a+b))
      (cuntzBlock (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)) := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) A) :=
    CStarAlgebra.instNonnegSpectrumClass'
  let S := CFC.sqrt a
  let T := CFC.sqrt b
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hT : star T = T := (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have hST : S*T = 0 := sqrt_mul_sqrt_eq_zero_of_mul_eq_zero ha hb hab
  have hTS : T*S = 0 := by simpa only [star_mul, hS, hT, star_zero] using congrArg star hST
  let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
  have hl : v * v.conjTranspose = CStarMatrix.ofMatrix.symm (a+b) := by
    dsimp [v]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
    change S*star S + T*star T = a+b
    rw [hS, hT, CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]
  have hr : v.conjTranspose * v =
      cuntzBlock (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) := by
    dsimp [v]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols]
    change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (star S * S))
      (CStarMatrix.ofMatrix.symm (star S * T)) (CStarMatrix.ofMatrix.symm (star T * S))
      (CStarMatrix.ofMatrix.symm (star T * T)) = _
    rw [hS, hT, hST, hTS, CFC.sqrt_mul_sqrt_self a ha, CFC.sqrt_mul_sqrt_self b hb]
    rfl
  simpa only [hl, hr] using cuntzEquivalent_rectangular_gram v

theorem CuntzDimensionState.value_orthogonal_add (d : CuntzDimensionState A) (n : ℕ)
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b = 0) :
    d.value ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ =
      d.value ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.value ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  let pa : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩
  let pb : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩
  rw [← d.value_add pa pb]
  exact d.value_eq ((cuntzEquivalent_orthogonal_add a b ha hb hab).trans
    (CuntzPositiveMatrix.add_equiv pa pb).symm)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_RegularizedState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Regularized dimension states and subadditivity. -/

section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace CuntzDimensionState

/-- A common smaller cutoff controls two independent cutoff thresholds. -/
theorem cutoff_value_add_le_regularized (d : CuntzDimensionState A)
    (a b : CuntzPositiveMatrix A) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    d.value (a.cutoff ε) + d.value (b.cutoff δ) ≤ d.regularized (a.add b) := by
  have hp := lt_min hε hδ
  calc
    _ ≤ d.value (a.cutoff (min ε δ)) + d.value (b.cutoff (min ε δ)) :=
      add_le_add (d.cutoff_value_antitone a (min_le_left _ _))
        (d.cutoff_value_antitone b (min_le_right _ _))
    _ = d.value ((a.add b).cutoff (min ε δ)) := by rw [CuntzPositiveMatrix.cutoff_add, d.value_add]
    _ ≤ _ := d.cutoff_value_le_regularized _ hp

theorem regularized_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) :
    d.regularized (a.add b) = d.regularized a + d.regularized b := by
  apply le_antisymm
  · apply d.regularized_le
    intro ε hε
    rw [CuntzPositiveMatrix.cutoff_add, d.value_add]
    exact add_le_add (d.cutoff_value_le_regularized a hε) (d.cutoff_value_le_regularized b hε)
  · apply (le_sub_iff_add_le).mp
    apply d.regularized_le a
    intro ε hε
    apply (le_sub_iff_add_le).mpr
    apply (le_sub_iff_add_le').mp
    apply d.regularized_le b
    intro δ hδ
    apply (le_sub_iff_add_le').mpr
    exact d.cutoff_value_add_le_regularized a b hε hδ

/-- The regularization descends to an additive, normalized monotone state
on the actual Cuntz monoid. -/
def regularize (d : CuntzDimensionState A) : CuntzDimensionState A where
  state := {
    toFun := Quotient.lift d.regularized (fun _ _ h => d.regularized_eq h)
    map_zero' := d.regularized_zero
    map_add' := by
      intro a b
      induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
      exact d.regularized_add a b }
  monotone := by
    intro a b h
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    exact d.regularized_mono ((cuntzClass_le a b).mp h)
  normalized := by
    change d.regularized (.unit 1) = 1
    exact_mod_cast d.regularized_unit 1

@[simp] theorem regularize_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.regularize.value a = d.regularized a := rfl

end CuntzDimensionState
end Kaplansky

end

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The row of two identities compresses the diagonal block to the ordinary sum. -/
theorem cuntzLE_sum_block {n : ℕ} (a b : Matrix (Fin n) (Fin n) A) :
    CuntzLE (a+b) (cuntzBlock a b) := by
  let v := Matrix.fromCols (1 : Matrix (Fin n) (Fin n) A) (1 : Matrix (Fin n) (Fin n) A)
  have h : v * cuntzBlock a b * v.conjTranspose = a+b := by
    simp [v, cuntzBlock, Matrix.fromCols_mul_fromBlocks,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  simpa only [h] using CuntzLE.exact (cuntzBlock a b) v

namespace CuntzDimensionState

/-- Dimension is subadditive for positive sums, without a commutation hypothesis. -/
theorem value_sum_le (d : CuntzDimensionState A) {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    d.value ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ ≤
      d.value ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.value ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  let pa : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩
  let pb : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩
  rw [← d.value_add pa pb]
  apply d.value_mono
  exact (cuntzLE_sum_block _ _).trans (CuntzPositiveMatrix.add_equiv pa pb).symm.1

theorem regularized_sum_le (d : CuntzDimensionState A) {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    d.regularized ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ ≤
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ :=
  d.regularize.value_sum_le a b ha hb

theorem regularized_orthogonal_add (d : CuntzDimensionState A) {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b=0) :
    d.regularized ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ =
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ :=
  d.regularize.value_orthogonal_add n a b ha hb hab

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Spectral distributions, integrals, and scalar covariance. -/

open scoped Matrix CStarAlgebra
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- A positive cutoff vanishes above the actual spectral norm bound. -/
theorem cuntzCutoff_eq_zero_of_norm_le {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : ‖a‖ ≤ ε) :
    cuntzCutoff a ε = 0 := by
  nontriviality A
  change cfc (fun t : ℝ => max (t-ε) 0) a = 0
  rw [← cfc_zero ℝ a]
  apply cfc_congr
  intro t ht
  have h : t ≤ ε := by
    simpa only [Real.norm_of_nonneg (spectrum_nonneg_of_nonneg ha ht)] using
      (spectrum.norm_le_norm_of_mem ht).trans hε
  exact max_eq_right (sub_nonpos.mpr h)

namespace CuntzDimensionState

theorem regularized_of_matrix_eq_zero (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (ha : a.matrix = 0) : d.regularized a = 0 := by
  rw [← d.regularized_zero]
  apply d.regularized_eq
  change CuntzEquivalent a.matrix (0 : Matrix (Fin 0) (Fin 0) A)
  rw [ha]
  exact ⟨CuntzLE.zero _, CuntzLE.zero _⟩

/-- The regularized spectral distribution attached to an actual positive matrix. -/
def distribution (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) (t : ℝ) : ℝ :=
  d.regularized (a.cutoff t)

theorem distribution_antitone (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    Antitone (d.distribution a) := by
  intro s t h
  exact d.regularized_mono (a := a.cutoff t) (b := a.cutoff s)
    (cuntzLE_of_nonneg_le (cuntzCutoff_nonneg _ _) (cuntzCutoff_antitone _ h))

theorem distribution_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) (t : ℝ) :
    0 ≤ d.distribution a t := d.regularized_nonneg _

theorem distribution_eq_zero (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {t : ℝ} (ht : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ t) : d.distribution a t = 0 := by
  apply d.regularized_of_matrix_eq_zero
  change CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a.matrix) t) = 0
  rw [cuntzCutoff_eq_zero_of_norm_le a.nonneg ht]
  rfl

theorem distribution_intervalIntegrable (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    (s t : ℝ) : IntervalIntegrable (d.distribution a) volume s t :=
  (d.distribution_antitone a).intervalIntegrable

/-- Finite layer-cake integral. This definition does not assert the quasitrace axioms. -/
def spectralValue (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : ℝ :=
  ∫ t in (0 : ℝ)..‖CStarMatrix.ofMatrix a.matrix‖, d.distribution a t

theorem spectralValue_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    0 ≤ d.spectralValue a :=
  intervalIntegral.integral_nonneg_of_forall (norm_nonneg _) (d.distribution_nonneg a)


/-- The layer-cake integral is independent of an upper endpoint past the norm. -/
theorem spectralValue_eq_integral (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {R : ℝ} (hR : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ R) :
    d.spectralValue a = ∫ t in (0 : ℝ)..R, d.distribution a t := by
  have he : (∫ t in ‖CStarMatrix.ofMatrix a.matrix‖..R, d.distribution a t) = 0 := by
    have h := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hR
      (g := fun _ : ℝ => (0 : ℝ)) (fun t ht => d.distribution_eq_zero a ht.1.le)
    simpa using h
  have h := intervalIntegral.integral_add_adjacent_intervals
    (d.distribution_intervalIntegrable a 0 ‖CStarMatrix.ofMatrix a.matrix‖)
    (d.distribution_intervalIntegrable a ‖CStarMatrix.ofMatrix a.matrix‖ R)
  rw [he, add_zero] at h
  exact h

end CuntzDimensionState

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_SquareCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Intertwining functional calculus and cutoffs of adjoint squares. -/

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] matrixRealFunctionalCalculus productMatrixRealFunctionalCalculus

section Rectangular
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Real functional calculus commutes with genuine diagonal blocks. -/
theorem cfc_cuntzBlock (a : CStarMatrix ι ι A) (b : CStarMatrix κ κ A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (CStarMatrix.ofMatrix (cuntzBlock a b)) =
      CStarMatrix.ofMatrix (cuntzBlock (CStarMatrix.ofMatrix.symm (cfc f a))
        (CStarMatrix.ofMatrix.symm (cfc f b))) := by
  let φ := cuntzBlockHom (A := A) (ι := ι) (κ := κ)
  have h := φ.map_cfc f (a,b) (hf := hf.continuousOn)
    (ha := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)
    (hφa := (cuntzBlock_nonneg _ _ ha hb).isSelfAdjoint)
  rw [cfc_map_prod (S := ℂ) f a b (hf := hf.continuousOn)
    (ha := ha.isSelfAdjoint) (hb := hb.isSelfAdjoint)
    (hab := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)] at h
  exact h.symm

/-- Intertwining positives also intertwines their continuous real functions.
The proof uses block commutation, so no polar decomposition is assumed. -/
theorem cfc_matrix_intertwine (a : CStarMatrix ι ι A) (b : CStarMatrix κ κ A)
    (x : Matrix ι κ A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : CStarMatrix.ofMatrix.symm a * x = x * CStarMatrix.ofMatrix.symm b)
    (f : ℝ → ℝ) (hf : Continuous f) :
    CStarMatrix.ofMatrix.symm (cfc f a) * x = x * CStarMatrix.ofMatrix.symm (cfc f b) := by
  let D : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A := CStarMatrix.ofMatrix (cuntzBlock a b)
  let X : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A := CStarMatrix.ofMatrix (Matrix.fromBlocks 0 x 0 0)
  have hc : Commute D X := by
    have hc' :
        (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a) 0 0 (CStarMatrix.ofMatrix.symm b) *
          Matrix.fromBlocks 0 x 0 0 : Matrix (ι ⊕ κ) (ι ⊕ κ) A) =
        Matrix.fromBlocks 0 x 0 0 *
          Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a) 0 0 (CStarMatrix.ofMatrix.symm b) := by
      simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hx]
    exact hc'
  have h := (hc.cfc_real f).eq
  rw [show cfc f D = CStarMatrix.ofMatrix (cuntzBlock
      (CStarMatrix.ofMatrix.symm (cfc f a)) (CStarMatrix.ofMatrix.symm (cfc f b))) from
    cfc_cuntzBlock a b ha hb f hf] at h
  have h' := congrArg (fun z : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A =>
    (CStarMatrix.ofMatrix.symm z).submatrix Sum.inl Sum.inr) h
  change (cuntzBlock (CStarMatrix.ofMatrix.symm (cfc f a)) (CStarMatrix.ofMatrix.symm (cfc f b)) * Matrix.fromBlocks 0 x 0 0).submatrix Sum.inl Sum.inr =
    (Matrix.fromBlocks 0 x 0 0 * cuntzBlock (CStarMatrix.ofMatrix.symm (cfc f a)) (CStarMatrix.ofMatrix.symm (cfc f b))).submatrix Sum.inl Sum.inr at h'
  ext i j
  simpa [cuntzBlock, Matrix.fromBlocks_multiply, Matrix.submatrix] using congrFun (congrFun h' i) j

end Rectangular

/-- A continuous cutoff factor, regular at zero for a strictly positive threshold. -/
def cutoffSquareFactor (ε t : ℝ) : ℝ := Real.sqrt (max (t-ε) 0 / max t ε)

theorem cutoffSquareFactor_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (cutoffSquareFactor ε) := by
  apply Continuous.sqrt
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (hε.trans_le (le_max_right t ε)).ne'

theorem cutoffSquareFactor_identity {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    cutoffSquareFactor ε t * t * cutoffSquareFactor ε t = max (t-ε) 0 := by
  have hd : 0 < max t ε := hε.trans_le (le_max_right _ _)
  have hs := Real.mul_self_sqrt (div_nonneg (le_max_right (t-ε) 0) hd.le)
  change Real.sqrt _ * t * Real.sqrt _ = _
  rw [mul_right_comm, hs]
  rcases le_total t ε with h | h
  · simp [max_eq_right (sub_nonpos.mpr h)]
  · rw [max_eq_left h, div_mul_cancel₀ _ (hε.trans_le h).ne']

/-- The actual cutoff factors as g(a) a g(a). -/
theorem cutoffSquareFactor_cfc {a : A} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    cfc (cutoffSquareFactor ε) a * a * cfc (cutoffSquareFactor ε) a =
      cuntzCutoff a ε := by
  have hf : ContinuousOn (cutoffSquareFactor ε) (spectrum ℝ a) := (cutoffSquareFactor_continuous hε).continuousOn
  have he : cfc (fun t : ℝ => cutoffSquareFactor ε t * t * cutoffSquareFactor ε t) a =
      cfc (cutoffSquareFactor ε) a * a * cfc (cutoffSquareFactor ε) a := by
    rw [cfc_mul (fun t : ℝ => cutoffSquareFactor ε t * t) (cutoffSquareFactor ε) a
      (hf.mul continuousOn_id) hf, cfc_mul (cutoffSquareFactor ε) (fun t : ℝ => t) a
      hf continuousOn_id, cfc_id' ℝ a ha.isSelfAdjoint]
  rw [← he]
  apply cfc_congr
  intro t ht
  exact cutoffSquareFactor_identity hε t

/-- Matching positive cutoffs of unequal rectangular Gram matrices are
Cuntz equivalent, proved by an exact rectangular factorization. -/
theorem cuntzEquivalent_cutoff_rectangular_gram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (x : Matrix ι κ A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) {ε : ℝ} (hε : 0 < ε) :
    CuntzEquivalent
      (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix (x*x.conjTranspose)) ε))
      (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix (x.conjTranspose*x)) ε)) := by
  classical
  let a := CStarMatrix.ofMatrix (x*x.conjTranspose)
  let b := CStarMatrix.ofMatrix (x.conjTranspose*x)
  let L := cfc (cutoffSquareFactor ε) a
  let R := cfc (cutoffSquareFactor ε) b
  have hL : star L = L := (cfc_predicate _ _ : IsSelfAdjoint L).star_eq
  have hR : star R = R := (cfc_predicate _ _ : IsSelfAdjoint R).star_eq
  have hx : CStarMatrix.ofMatrix.symm L * x = x * CStarMatrix.ofMatrix.symm R :=
    cfc_matrix_intertwine a b x ha hb (Matrix.mul_assoc _ _ _) _
      (cutoffSquareFactor_continuous hε)
  let y := CStarMatrix.ofMatrix.symm L * x
  have hy : y = x * CStarMatrix.ofMatrix.symm R := hx
  have hl : y*y.conjTranspose = CStarMatrix.ofMatrix.symm (cuntzCutoff a ε) := by
    dsimp only [y]
    rw [Matrix.conjTranspose_mul]
    change CStarMatrix.ofMatrix.symm L * x * (x.conjTranspose * CStarMatrix.ofMatrix.symm (star L)) = _
    rw [hL]
    have he := cutoffSquareFactor_cfc ha hε
    change L * a * L = _ at he
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm L * (x*x.conjTranspose) * CStarMatrix.ofMatrix.symm L = _ at he'
    simpa only [Matrix.mul_assoc] using he'
  have hr : y.conjTranspose*y = CStarMatrix.ofMatrix.symm (cuntzCutoff b ε) := by
    rw [hy, Matrix.conjTranspose_mul]
    change CStarMatrix.ofMatrix.symm (star R) * x.conjTranspose * (x * CStarMatrix.ofMatrix.symm R) = _
    rw [hR]
    have he := cutoffSquareFactor_cfc hb hε
    change R * b * R = _ at he
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm R * (x.conjTranspose*x) * CStarMatrix.ofMatrix.symm R = _ at he'
    simpa only [Matrix.mul_assoc] using he'
  rw [← hl, ← hr]
  exact cuntzEquivalent_rectangular_gram y

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Spectral candidates on squares, orthogonal elements, and complex elements. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

local instance matrixNonUnitalRealFunctionalCalculus {ν : Type*} [Fintype ν] [DecidableEq ν] :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ν ν A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance matrixNonnegSpectrum {ν : Type*} [Fintype ν] [DecidableEq ν] :
    NonnegSpectrumClass ℝ (CStarMatrix ν ν A) := CStarAlgebra.instNonnegSpectrumClass'

namespace CuntzDimensionState

/-- The spectral distributions of rectangular Gram matrices agree at
all strictly positive thresholds, not just on the uncut matrices. -/
theorem distribution_rectangular_gram (d : CuntzDimensionState A) {n m : ℕ}
    (x : Matrix (Fin n) (Fin m) A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) {t : ℝ} (ht : 0 < t) :
    d.distribution ⟨n, x*x.conjTranspose, ha⟩ t =
      d.distribution ⟨m, x.conjTranspose*x, hb⟩ t :=
  d.regularized_eq (cuntzEquivalent_cutoff_rectangular_gram x ha hb ht)

/-- The spectral integral satisfies square swapping in unequal sizes. -/
theorem spectralValue_rectangular_gram (d : CuntzDimensionState A) {n m : ℕ}
    (x : Matrix (Fin n) (Fin m) A) (ha : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose))
    (hb : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x)) :
    d.spectralValue ⟨n, x*x.conjTranspose, ha⟩ =
      d.spectralValue ⟨m, x.conjTranspose*x, hb⟩ := by
  let a : CuntzPositiveMatrix A := ⟨n, x*x.conjTranspose, ha⟩
  let b : CuntzPositiveMatrix A := ⟨m, x.conjTranspose*x, hb⟩
  let R := ‖CStarMatrix.ofMatrix a.matrix‖ + ‖CStarMatrix.ofMatrix b.matrix‖
  have hR : ‖CStarMatrix.ofMatrix a.matrix‖ ≤ R := le_add_of_nonneg_right (norm_nonneg _)
  have hR' : ‖CStarMatrix.ofMatrix b.matrix‖ ≤ R := le_add_of_nonneg_left (norm_nonneg _)
  rw [d.spectralValue_eq_integral a hR, d.spectralValue_eq_integral b hR']
  apply intervalIntegral.integral_congr_Ioo_of_le (le_trans (norm_nonneg _) hR)
  intro t ht
  exact d.distribution_rectangular_gram x ha hb ht.1

/-- In particular, the original square-swap axiom holds on the positive squares. -/
theorem spectralValue_square_swap (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (x*star x), mul_star_self_nonneg x⟩ =
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (star x*x), star_mul_self_nonneg x⟩ :=
  d.spectralValue_rectangular_gram (CStarMatrix.ofMatrix.symm x) _ _

end CuntzDimensionState

namespace CuntzDimensionState

/-- The spectral value in a fixed matrix size, on the genuine positive cone. -/
def positiveValue (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) : ℝ :=
  d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩

@[simp] theorem positiveValue_zero (d : CuntzDimensionState A) (n : ℕ) :
    d.positiveValue (0 : CStarMatrix (Fin n) (Fin n) A) le_rfl = 0 := by
  simp [positiveValue, spectralValue]

/-- The same positive construction gives a canonical signed value by positive
and negative parts. Additivity on general commuting elements is not assumed. -/
def signedValue (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : ℝ :=
  d.positiveValue a⁺ (CFC.posPart_nonneg a) - d.positiveValue a⁻ (CFC.negPart_nonneg a)

theorem signedValue_of_nonneg (d : CuntzDimensionState A) {n : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) :
    d.signedValue a = d.positiveValue a ha := by
  unfold signedValue
  simp only [(CFC.posPart_eq_self a).mpr ha, (CFC.negPart_eq_zero_iff a ha.isSelfAdjoint).mpr ha,
    d.positiveValue_zero, sub_zero]

@[simp] theorem signedValue_zero (d : CuntzDimensionState A) (n : ℕ) :
    d.signedValue (0 : CStarMatrix (Fin n) (Fin n) A) = 0 := by
  rw [d.signedValue_of_nonneg le_rfl, d.positiveValue_zero]

@[simp] theorem signedValue_neg (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : d.signedValue (-a) = -d.signedValue a := by
  simp only [signedValue, CFC.posPart_neg, CFC.negPart_neg, neg_sub]


/-- A single complex-valued extension of the spectral construction in every
finite matrix size. Abelian linearity is not asserted by this definition. -/
def complexValue (d : CuntzDimensionState A) {n : ℕ}
    (a : CStarMatrix (Fin n) (Fin n) A) : ℂ :=
  (d.signedValue (ℜ a : CStarMatrix (Fin n) (Fin n) A) : ℂ) +
    Complex.I * (d.signedValue (ℑ a : CStarMatrix (Fin n) (Fin n) A) : ℂ)

theorem complexValue_selfAdjoint (d : CuntzDimensionState A) {n : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : IsSelfAdjoint a) :
    d.complexValue a = (d.signedValue a : ℂ) := by
  simp [complexValue, ha.coe_realPart, ha.imaginaryPart]

theorem complexValue_of_nonneg (d : CuntzDimensionState A) {n : ℕ}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : 0 ≤ a) :
    d.complexValue a = (d.positiveValue a ha : ℂ) := by
  rw [d.complexValue_selfAdjoint ha.isSelfAdjoint, d.signedValue_of_nonneg ha]

@[simp] theorem complexValue_zero (d : CuntzDimensionState A) (n : ℕ) :
    d.complexValue (0 : CStarMatrix (Fin n) (Fin n) A) = 0 := by
  simp [complexValue]

/-- The original real/imaginary axiom, without assuming that h and k commute. -/
theorem complexValue_real_imag (d : CuntzDimensionState A) {n : ℕ}
    (h k : CStarMatrix (Fin n) (Fin n) A) (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k) :
    d.complexValue (h + Complex.I • k) = d.complexValue h + Complex.I * d.complexValue k := by
  rw [d.complexValue_selfAdjoint hh, d.complexValue_selfAdjoint hk]
  simp [complexValue, map_add, hh.coe_realPart, hh.imaginaryPart, hk.coe_realPart, hk.imaginaryPart]

/-- Nonnegativity of squares for the single whole-matrix construction. -/
theorem complexValue_square_nonneg (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) : 0 ≤ d.complexValue (star x*x) := by
  rw [d.complexValue_of_nonneg (star_mul_self_nonneg x)]
  exact_mod_cast d.spectralValue_nonneg ⟨n, CStarMatrix.ofMatrix.symm (star x*x), star_mul_self_nonneg x⟩

/-- Square swapping for the same whole-matrix construction. -/
theorem complexValue_square_swap (d : CuntzDimensionState A) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) :
    d.complexValue (star x*x) = d.complexValue (x*star x) := by
  rw [d.complexValue_of_nonneg (star_mul_self_nonneg x), d.complexValue_of_nonneg (mul_star_self_nonneg x)]
  exact congrArg (fun r : ℝ => (r : ℂ)) (d.spectralValue_square_swap x).symm

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Real functional calculus and signed and complex spectral measures. -/

open scoped Matrix CStarAlgebra ComplexOrder
open Set MeasureTheory TopologicalSpace

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {X : Type*} [TopologicalSpace X]

/-- Real continuous functions viewed inside the complex function algebra. -/
def continuousRealInclusion : C(X, ℝ) →⋆ₐ[ℝ] C(X, ℂ) where
  toFun f := ⟨fun x => (f x : ℂ), by fun_prop⟩
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' f g := by ext x; simp
  map_mul' f g := by ext x; simp
  commutes' r := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' f := by ext x; simp

@[simp] theorem continuousRealInclusion_apply (f : C(X, ℝ)) (x : X) :
    continuousRealInclusion f x = (f x : ℂ) := rfl

variable [CompactSpace X]

local instance continuousMapRealFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ C(X, ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

theorem continuous_continuousRealInclusion : Continuous (continuousRealInclusion (X := X)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(X, ℝ) × X => (p.1 p.2 : ℂ))
  fun_prop

theorem continuousRealInclusion_cutoff (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    cuntzCutoff (continuousRealInclusion f) t =
      continuousRealInclusion (continuousDimensionCutoff f t) := by
  ext x
  have hsa : IsSelfAdjoint (continuousRealInclusion f) := (map_nonneg continuousRealInclusion hf).isSelfAdjoint
  have hsax : IsSelfAdjoint (continuousRealInclusion f x) := by
    change star (f x : ℂ) = (f x : ℂ)
    simp
  have h := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc
    (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f) (ha := hsa) (hφa := hsax)
  change (cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)) x = _ at h
  change (cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)) x = _
  rw [h]
  exact cfc_algebraMap (A := ℂ) (f x) (fun s : ℝ => max (s-t) 0)

variable {A : Type*} [CStarAlgebra A] {n : ℕ}

/-- The real function algebra mapped into the ambient finite matrix algebra. -/
def realFunctionHom (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) :
    C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A :=
  (ψ.restrictScalars ℝ).comp continuousRealInclusion

theorem realFunctionHom_continuous (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) :
    Continuous (realFunctionHom ψ) := by
  have hψ : Continuous ψ := by fun_prop
  exact hψ.comp continuous_continuousRealInclusion

/-- Genuine CFC naturality identifies the image of a scalar cutoff. -/
theorem realFunctionHom_cutoff (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    realFunctionHom ψ (continuousDimensionCutoff f t) = cuntzCutoff (realFunctionHom ψ f) t := by
  change ψ (continuousRealInclusion (continuousDimensionCutoff f t)) = _
  rw [← continuousRealInclusion_cutoff f hf t]
  exact ψ.map_cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)
    (ha := (map_nonneg continuousRealInclusion hf).isSelfAdjoint)
    (hφa := (map_nonneg ψ (map_nonneg continuousRealInclusion hf)).isSelfAdjoint)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_OpenUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Vanishing of homology under open unions and finite covers. -/

section
open CategoryTheory Limits HomologicalComplex
variable {X : Type} [TopologicalSpace X]

/-- Remove a redundant enclosing subtype without changing its topology. -/
def subspaceSubsetHomeomorph (U W : Set X) (h : U ⊆ W) :
    (Subtype.val ⁻¹' U : Set W) ≃ₜ U where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end

open CategoryTheory Limits Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_ProjectiveClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Localization, top homology, and the fundamental class of projective products. -/

section
open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {ι : Type} (K : ι → ℕ)

def coordinatePunctureDimensions (T : Finset ι) (i : ι) : ℕ := by
  classical
  exact if i ∈ T then K i - 1 else K i

end ComplexGrassmann

end

open CategoryTheory Limits

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.IntegralHomology_AffineAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky

/-! Affine-avoidance covers and convex product-pair homology. -/

section
open Set
variable {E F J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype J]

/-- The complement of finitely many affine zero sets, including dependent
or zero affine maps. No general-position or nonempty assumption is made. -/
def affineAvoidanceSet (l : J → E →L[ℝ] F) (c : J → F) : Set E := {x | ∀ j, l j x + c j ≠ 0}

end

open CategoryTheory Limits Set

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert shifts, their relations, and block operator bounds. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem block_norm_le_of_column (T : Fin n → E →L[ℂ] F)
    (hcol : ∑ i, (T i).adjoint.comp (T i) = ContinuousLinearMap.id ℂ E) (i : Fin n) :
    ‖T i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have he : ∑ j, ‖T j v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := congrArg (fun W : E →L[ℂ] E => RCLike.re (inner ℂ v (W v))) hcol
    simpa only [sum_apply, ContinuousLinearMap.comp_apply,
      inner_sum, map_sum, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.id_apply, inner_self_eq_norm_sq] using h
  have hi : ‖T i v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← he]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖T j v‖) (Finset.mem_univ i)
  have hn := norm_nonneg v
  have hni := norm_nonneg (T i v)
  nlinarith

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Words
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky.NormalizedHermitianTuple
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

local instance instCompleteSpace_rb740ec_1 : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance instCompleteSpace_1 : CompleteSpace F := FiniteDimensional.complete ℂ F

end Kaplansky.NormalizedHermitianTuple

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open TopologicalSpace
open scoped Pointwise
namespace Kaplansky

variable {A : Type*} [CStarAlgebra A]

/-- The actual unital closed C*-subalgebra generated by the specified set. -/
def generatedAlgebra (s : Set A) : StarSubalgebra ℂ A :=
  (StarAlgebra.adjoin ℂ s).topologicalClosure

def generatedGenerator {N : ℕ} (x : Fin N → A) (k : Fin N) :
    generatedAlgebra (Set.range x) :=
  ⟨x k, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨k,rfl⟩)⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_BundlePolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Bundle matrix polynomial evaluation, Hilbert isometries, and polynomial action. -/

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

/-- One term of a rectangular star polynomial, with its actual word and
its degree bound. Zero coefficients and empty words are allowed. -/
structure BoundedMatrixTerm (m n R : ℕ) where
  row : Fin m
  col : Fin n
  coeff : ℂ
  word : List (Bool × Fin 24)
  degree_le : word.length ≤ R

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner-compatible two-quasitraces on the usual CStarMatrix algebra and the fixed-pair counterexample proposition. -/

section

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

/-- A single matrix entry with the C*-matrix norm. -/
def entry (i j : n) (a : A) : CStarMatrix n n A := CStarMatrix.ofMatrix (Matrix.single i j a)
def corner (i : n) (a : A) : CStarMatrix n n A := entry i i a

omit [Fintype n] in
@[simp] theorem entry_star (i j : n) (a : A) :
    star (entry i j a) = entry j i (star a) := by
  change (Matrix.single i j a).conjTranspose = Matrix.single j i (star a)
  exact Matrix.conjTranspose_single i j a

@[simp] theorem entry_mul (i j k : n) (a b : A) :
    entry i j a * entry j k b = entry i k (a * b) := by
  change Matrix.single i j a * Matrix.single j k b = Matrix.single i k (a * b)
  simp

omit [Fintype n] in
@[simp] theorem corner_star (i : n) (a : A) : star (corner i a) = corner i (star a) := entry_star i i a
@[simp] theorem corner_mul (i : n) (a b : A) : corner i a * corner i b = corner i (a*b) := entry_mul i i i a b

omit [Fintype n] in
theorem corner_selfAdjoint (i : n) {a : A} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (corner i a) := by
  change star (corner i a) = corner i a
  rw [corner_star, ha.star_eq]

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix order and the normalization of genuine corner extensions. -/

section

noncomputable section
open scoped ComplexOrder BigOperators CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

omit [Fintype n] in
@[simp] theorem corner_add (i : n) (a b : A) : corner i (a+b) = corner i a + corner i b := by
  change Matrix.single i i (a+b) = Matrix.single i i a + Matrix.single i i b
  exact Matrix.single_add i i a b
omit [Fintype n] in
@[simp] theorem corner_sub (i : n) (a b : A) : corner i (a-b) = corner i a - corner i b := by
  change Matrix.single i i (a-b) = Matrix.single i i a - Matrix.single i i b
  simp only [sub_eq_add_neg, Matrix.single_add, Matrix.single_neg]
omit [Fintype n] in
@[simp] theorem corner_smul (i : n) (c : ℂ) (a : A) : corner i (c • a) = c • corner i a := by
  change Matrix.single i i (c • a) = c • Matrix.single i i a
  simp
omit [Fintype n] in
@[simp] theorem corner_zero (i : n) : corner i (0 : A) = 0 := by
  change Matrix.single i i (0 : A) = 0
  simp

end Kaplansky

end
end

section

noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

@[simp] theorem upperLeft_eq_corner (a : A) : upperLeft a = corner (0 : Fin 2) a := by
  ext i j
  change (if i = 0 ∧ j = 0 then a else 0) = (if 0 = i ∧ 0 = j then a else 0)
  simp only [eq_comm]

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_ActualAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The actual M48 algebra, its fixed defect pair, and its Cuntz dimension state. -/

namespace Kaplansky

section
open scoped BigOperators
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

abbrev ActualDefectIndex := Fin 24 ⊕ Fin 24

end

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed quasitrace constraints and compactness of normalized two-quasitraces. -/

section

noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable (A : Type*) [CStarAlgebra A]

abbrev QuasitraceCandidate := (A → ℂ) × (CStarMatrix (Fin 2) (Fin 2) A → ℂ)

end Kaplansky

end
end

end OAI
end


