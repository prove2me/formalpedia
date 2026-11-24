-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_KillingFormDiffCartanInvolution
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_KillingFormDiffCartanInvolution
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:02:14.485274+00:00
-- url     : https://prove2.me/theorems/7bccf427-60bd-4c09-b2bd-3dde665050c1
-- title:
--   Killing Form Diff Cartan Involution
-- statement:
--   Definitions and structural lemmas for Killing Form Diff Cartan Involution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/KillingFormDiffCartanInvolution.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_star_PhiGL
import Theorems.Thm_GlobalTheory_Tw_thetaGL_mul
import Theorems.Thm_GlobalTheory_Tw_thetaGL_thetaGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Topology
open scoped Kronecker ContDiff
noncomputable section
namespace GlobalTheory.Tw
abbrev GP (a b : ℕ) (R : Type) [CommRing R] : Type := GL (Fin a) R × GL (Fin b) R
section Alg
variable {a b : ℕ} {R : Type} [CommRing R] [StarRing R]
def PhiG (a b : ℕ) (R : Type) [CommRing R] : GP a b R := (PhiGL a R, PhiGL b R)
def th0 : MulAut (GP a b R) where
  toFun g := star g⁻¹
  invFun g := star g⁻¹
  left_inv g := by simp [star_inv]
  right_inv g := by simp [star_inv]
  map_mul' g h := by simp
def thetaG : MulAut (GP a b R) where
  toFun g := (thetaGL g.1, thetaGL g.2)
  invFun g := (thetaGL g.1, thetaGL g.2)
  left_inv _ := Prod.ext (thetaGL_thetaGL _) (thetaGL_thetaGL _)
  right_inv _ := Prod.ext (thetaGL_thetaGL _) (thetaGL_thetaGL _)
  map_mul' _ _ := Prod.ext (thetaGL_mul _ _) (thetaGL_mul _ _)
theorem cartan_involution_apply (g : GP a b R) : th0 g = star g⁻¹ := rfl
@[simp] theorem cartan_involution_involutive (g : GP a b R) : th0 (th0 g) = g := by
  rw [cartan_involution_apply, cartan_involution_apply, star_inv, star_star, inv_inv]
@[simp] theorem thetaG_thetaG (g : GP a b R) : thetaG (thetaG g) = g := by
  exact Prod.ext (thetaGL_thetaGL g.1) (thetaGL_thetaGL g.2)
theorem cartan_involution_frobenius : th0 (PhiG a b R) = PhiG a b R := by
  rw [cartan_involution_apply]
  refine Prod.ext ?_ ?_ <;> simp [PhiG, star_inv, star_PhiGL]
def twAct (x δ y : GP a b R) : GP a b R := x * δ * thetaG y
def toTh0 (g : GP a b R) : GP a b R := g * PhiG a b R
def nrmG (δ : GP a b R) : GP a b R := δ * thetaG δ
def twConjG (x δ : GP a b R) : GP a b R := x⁻¹ * δ * thetaG x
def RegG (δ : GP a b R) : Prop := Reg δ.1.val ∧ Reg δ.2.val
def AdG (δ : GP a b R) : MulAut (GP a b R) := MulAut.conj δ * thetaG
def centG (δ : GP a b R) : Subgroup (GP a b R) where
  carrier := {g | g * δ = δ * thetaG g}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [map_mul, mul_assoc, hh, ← mul_assoc, hg, mul_assoc]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, ← hg, inv_mul_cancel_left]
def IsTwRep {M : Type} [Monoid M] (H : Subgroup (GP a b R)) (Ht : Set (GP a b R)) (π : H →* M) (πt : GP a b R → M) : Prop :=
  ∀ δ ∈ Ht, IsUnit (πt δ) ∧ ∀ h₁ h₂ : H, πt (twAct h₁ δ h₂) = π h₁ * πt δ * π h₂
end Alg
abbrev GR (a b : ℕ) : Type := GP a b ℂ
abbrev LieG (a b : ℕ) : Type := Matrix (Fin a) (Fin a) ℂ × Matrix (Fin b) (Fin b) ℂ
variable {a b : ℕ}
instance secondCountable_GLC (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) :=
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
instance locallyCompact_GLC (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) :=
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  inferInstance
instance measurableSpace_GR : MeasurableSpace (GR a b) := borel _
instance borelSpace_GR : BorelSpace (GR a b) := ⟨rfl⟩
def mat : GR a b →* LieG a b := (Units.coeHom _).prodMap (Units.coeHom _)
theorem mat_apply (g : GR a b) : mat g = (g.1.val, g.2.val) := rfl
theorem mat_star (g : GR a b) : mat (star g) = star (mat g) := rfl
theorem mat_injective : Function.Injective (mat : GR a b → LieG a b) := by
  intro g h e
  rw [mat_apply, mat_apply, Prod.mk.injEq] at e
  exact Prod.ext (Units.ext e.1) (Units.ext e.2)
@[simp] theorem mat_mul_inv (g : GR a b) : mat g * mat g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]
@[simp] theorem mat_inv_mul (g : GR a b) : mat g⁻¹ * mat g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]
def expG (X : LieG a b) : GR a b := ((Matrix.isUnit_exp X.1).unit, (Matrix.isUnit_exp X.2).unit)
def KR (a b : ℕ) : Subgroup (GR a b) := (th0 : MulAut (GR a b)).toMonoidHom.eqLocus (MonoidHom.id _)
theorem mem_KR {k : GR a b} : k ∈ KR a b ↔ th0 k = k := by
  exact Iff.rfl
theorem mem_KR_iff_star {k : GR a b} : k ∈ KR a b ↔ star k = k⁻¹ := by
  rw [mem_KR, cartan_involution_apply, star_inv, inv_eq_iff_eq_inv]
theorem mem_KR_iff_mat {k : GR a b} : k ∈ KR a b ↔ mat k * star (mat k) = 1 := by
  rw [mem_KR_iff_star, eq_comm, ← mul_eq_one_iff_inv_eq, ← mat_injective.eq_iff, map_mul, map_one, mat_star]
theorem mem_KR_iff_unitary {k : GR a b} :
    k ∈ KR a b ↔ k.1.val ∈ unitaryGroup (Fin a) ℂ ∧ k.2.val ∈ unitaryGroup (Fin b) ℂ := by
  rw [mem_KR_iff_mat, mat_apply, Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_star, Prod.snd_star, Prod.fst_one, Prod.snd_one]
theorem PhiG_mem_KR : PhiG a b ℂ ∈ KR a b := by
  exact mem_KR.2 cartan_involution_frobenius
theorem isCompact_unitary_GL (n : ℕ) : IsCompact {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
  have hU : IsCompact (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have hcl : IsClosed (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      have e : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
          (fun A : Matrix (Fin n) (Fin n) ℂ => A * star A) ⁻¹' {1} := by
        ext A; exact Matrix.mem_unitaryGroup_iff
      rw [e]
      exact isClosed_singleton.preimage (continuous_id.mul continuous_star)
    have hbd : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1 := by
      intro A hA i _ j _
      have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hA) i) i
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
      simp only [Matrix.star_apply, Complex.star_def, Complex.mul_conj] at h
      have h2 : ∑ k, Complex.normSq (A i k) = 1 := by exact_mod_cast h
      have h3 : Complex.normSq (A i j) ≤ 1 :=
        h2 ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (A i k)) (Finset.mem_univ j)
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Complex.normSq_eq_norm_sq] at h3
      nlinarith [norm_nonneg (A i j)]
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset hcl hbd
  have : CompactSpace (unitaryGroup (Fin n) ℂ) := isCompact_iff_compactSpace.1 hU
  let φ : unitaryGroup (Fin n) ℂ → GL (Fin n) ℂ := fun u =>
    ⟨u.1, star u.1, Unitary.mul_star_self_of_mem u.2, Unitary.star_mul_self_of_mem u.2⟩
  have hφ : Continuous φ :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range φ = {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
    ext k
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hk
      exact ⟨⟨k.val, hk⟩, Units.ext rfl⟩
  rw [← hr]
  exact isCompact_range hφ
theorem isCompact_KR : IsCompact (KR a b : Set (GR a b)) := by
  have e : (KR a b : Set (GR a b)) = {k : GL (Fin a) ℂ | k.val ∈ unitaryGroup (Fin a) ℂ} ×ˢ
      {k : GL (Fin b) ℂ | k.val ∈ unitaryGroup (Fin b) ℂ} := by
    ext k
    exact mem_KR_iff_unitary
  rw [e]
  exact (isCompact_unitary_GL a).prod (isCompact_unitary_GL b)
instance compactSpace_KR : CompactSpace (KR a b) := isCompact_iff_compactSpace.1 isCompact_KR
def haarK (a b : ℕ) : Measure (KR a b) := Measure.haarMeasure ⊤
instance : (haarK a b).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
instance : IsProbabilityMeasure (haarK a b) := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
def pSp (a b : ℕ) : Submodule ℝ (LieG a b) := selfAdjoint.submodule ℝ (LieG a b)
def kSp (a b : ℕ) : Submodule ℝ (LieG a b) := skewAdjoint.submodule ℝ (LieG a b)
theorem mem_pSp {X : LieG a b} : X ∈ pSp a b ↔ star X = X := by
  exact selfAdjoint.mem_iff
def BForm (a b : ℕ) : LinearMap.BilinForm ℝ (LieG a b) :=
  LinearMap.mk₂ ℝ (fun X Y => ((X.1 * Y.1).trace + (X.2 * Y.2).trace).re)
    (fun X X' Y => by simp [add_mul]; ring) (fun c X Y => by simp; ring)
    (fun X Y Y' => by simp [mul_add]; ring) (fun c X Y => by simp; ring)
def AdLie (g : GR a b) : LieG a b →ₗ[ℝ] LieG a b := LinearMap.mulLeftRight ℝ (mat g, mat g⁻¹)
theorem AdLie_apply (g : GR a b) (X : LieG a b) : AdLie g X = mat g * X * mat g⁻¹ := rfl
def dth0 : LieG a b →ₗ[ℝ] LieG a b where
  toFun X := -star X
  map_add' X Y := by rw [star_add, neg_add]
  map_smul' c X := by simp
theorem diff_cartan_involution_apply (X : LieG a b) : dth0 X = -star X := rfl
def dtheta : LieG a b →ₗ[ℝ] LieG a b := AdLie (PhiG a b ℂ) ∘ₗ dth0
def AdT (δ : GR a b) : LieG a b →ₗ[ℝ] LieG a b := AdLie δ ∘ₗ dtheta
theorem AdLie_mul (g h : GR a b) : AdLie (g * h) = AdLie g ∘ₗ AdLie h := by
  refine LinearMap.ext fun X => ?_
  simp only [LinearMap.comp_apply, AdLie_apply, map_mul, _root_.mul_inv_rev, mul_assoc]
@[simp] theorem AdLie_one : AdLie (1 : GR a b) = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp [AdLie_apply]
theorem AdT_eq (δ : GR a b) : AdT δ = AdLie (toTh0 δ) ∘ₗ dth0 := by
  simp only [AdT, dtheta, toTh0, AdLie_mul, LinearMap.comp_assoc]
theorem AdLie_mem_pSp {k : GR a b} (hk : k ∈ KR a b) {X : LieG a b} (hX : X ∈ pSp a b) : AdLie k X ∈ pSp a b := by
  rw [mem_pSp] at hX ⊢
  have hk' := mem_KR_iff_star.1 hk
  have e1 : star (mat k) = mat k⁻¹ := by rw [← mat_star, hk']
  have e2 : star (mat k⁻¹) = mat k := by rw [← mat_star, star_inv, hk', inv_inv]
  rw [AdLie_apply, star_mul, star_mul, e1, e2, hX, mul_assoc]
theorem AdT_mem_pSp {k : GR a b} (hk : k ∈ KR a b) {X : LieG a b} (hX : X ∈ pSp a b) : AdT k X ∈ pSp a b := by
  rw [AdT_eq, LinearMap.comp_apply]
  apply AdLie_mem_pSp (mul_mem hk PhiG_mem_KR)
  rw [diff_cartan_involution_apply, mem_pSp.1 hX]
  exact neg_mem hX
def AdLiep (k : KR a b) : pSp a b →ₗ[ℝ] pSp a b := (AdLie k.1).restrict fun _ hX => AdLie_mem_pSp k.2 hX
def AdTp (k : KR a b) : pSp a b →ₗ[ℝ] pSp a b := (AdT k.1).restrict fun _ hX => AdT_mem_pSp k.2 hX
def distinguishedElementKR (a b : ℕ) : KR a b := ⟨(PhiG a b ℂ)⁻¹, inv_mem PhiG_mem_KR⟩
end GlobalTheory.Tw


