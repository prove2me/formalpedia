-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
-- name    : GroundTheory_AutomorphicForms_SphericalSatake
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:28.392293+00:00
-- url     : https://prove2.me/theorems/fb5cd5bf-8080-4d00-9609-f399ff68e207
-- title:
--   Spherical Satake
-- statement:
--   Definitions and structural lemmas for Spherical Satake, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalSatake.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalPrincipal
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_diagGL_mul_mul_inv_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_exists_eq_mul_torusPow_iwasawaExponent
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_eq
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_mul_of_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_mul_of_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Measures_modularCharacter_eq_one_of_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_Spherical_eq_of_forall_evalAt
import Theorems.Thm_GroundTheory_Automorphic_Spherical_evalAt_single
import Theorems.Thm_GroundTheory_Automorphic_Spherical_monomialChar_add
import Theorems.Thm_GroundTheory_Automorphic_Spherical_sphericalCharacter_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_integral_eq_smul_finsum_coset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped ValuativeRel
namespace Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
theorem torusPow_add (l l' : Fin n → ℤ) :
    torusPow F n (l + l') = torusPow F n l * torusPow F n l' := by
  rw [torusPow, torusPow, torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]
theorem torusPow_zero : torusPow F n 0 = 1 := by
  rw [torusPow, ← map_one (diagGL F n)]
  congr 1
  funext i
  simp
theorem diagGL_mul_comm (a b : Fin n → Fˣ) : diagGL F n a * diagGL F n b = diagGL F n b * diagGL F n a := by
  rw [← map_mul, ← map_mul, mul_comm]
theorem iwasawaExponent_one : iwasawaExponent F n (1 : GL (Fin n) F) = 0 := by
  simpa [torusPow_zero] using
    iwasawaExponent_eq F n (unipotent F n).one_mem (integralGL F n).one_mem (l := (0 : Fin n → ℤ))
theorem exists_diagGL_eq_torusPow_mul (d : Fin n → Fˣ) :
    ∃ l : Fin n → ℤ, ∃ e : Fin n → (𝒪[F])ˣ,
      diagGL F n d = torusPow F n l * diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i) := by
  choose l e he using fun i => exists_zpow_mul_unit F (d i).ne_zero
  refine ⟨l, e, ?_⟩
  rw [torusPow, ← map_mul]
  congr 1
  funext i
  ext
  simp [he i, Units.val_zpow_eq_zpow_val, Units.coe_map]
def diagUnits {b : GL (Fin n) F} (hb : b ∈ borel F n) : Fin n → Fˣ :=
  fun i => Units.mk0 (b i i) (apply_self_ne_zero_of_mem_borel F n hb i)
theorem mul_inv_diagUnits_mem_unipotent {b : GL (Fin n) F} (hb : b ∈ borel F n) :
    b * (diagGL F n (diagUnits hb))⁻¹ ∈ unipotent F n := by
  have hDinv : (diagGL F n (diagUnits hb))⁻¹ ∈ borel F n :=
    (borel F n).inv_mem (diagGL_mem_borel F n _)
  refine ⟨(borel F n).mul_mem hb hDinv, fun i => ?_⟩
  rw [mul_apply_self_of_mem_borel F n hb hDinv, ← map_inv, coe_diagGL, diagonal_apply_eq]
  simp [diagUnits, apply_self_ne_zero_of_mem_borel F n hb i]
theorem iwasawaExponent_mul_of_mem_borel {b : GL (Fin n) F} (hb : b ∈ borel F n)
    (g : GL (Fin n) F) :
    iwasawaExponent F n (b * g) = iwasawaExponent F n b + iwasawaExponent F n g := by
  obtain ⟨l, e, hde⟩ := exists_diagGL_eq_torusPow_mul (diagUnits hb)
  set D := diagGL F n (diagUnits hb)
  set E : GL (Fin n) F := diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i)
  have hE : E ∈ integralGL F n := diagGL_map_mem_integralGL F n e
  have hu := mul_inv_diagUnits_mem_unipotent hb
  have key : ∀ g : GL (Fin n) F, iwasawaExponent F n (b * g) = l + iwasawaExponent F n g := by
    intro g
    obtain ⟨u', hu', k', hk', hg⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
    set lg := iwasawaExponent F n g with hlg
    have hcomm : E * torusPow F n lg = torusPow F n lg * E :=
      diagGL_mul_comm _ _
    have hD : D⁻¹ * torusPow F n l = E⁻¹ := by
      rw [hde, _root_.mul_inv_rev, inv_mul_cancel_right]
    have : b * g = (b * D⁻¹ * (D * u' * D⁻¹)) * torusPow F n (l + lg) * (E * k') := by
      rw [torusPow_add]
      conv_lhs => rw [hg]
      calc b * (u' * torusPow F n lg * k')
          = b * u' * (E⁻¹ * (E * torusPow F n lg)) * k' := by group
        _ = b * u' * (E⁻¹ * (torusPow F n lg * E)) * k' := by rw [hcomm]
        _ = b * u' * ((D⁻¹ * torusPow F n l) * (torusPow F n lg * E)) * k' := by
            rw [hD]
        _ = _ := by group
    rw [this]
    refine iwasawaExponent_eq F n ((unipotent F n).mul_mem hu ?_) ((integralGL F n).mul_mem hE hk')
    exact diagGL_mul_mul_inv_mem_unipotent F n hu' _
  have hb1 := key 1
  rw [mul_one, iwasawaExponent_one, add_zero] at hb1
  rw [key, hb1]
def unramifiedChar (w : Fin n → ℂˣ) : levi F n (id : Fin n → Fin n) →* ℂ where
  toFun t := monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t)
  map_one' := by simp [iwasawaExponent_one]
  map_mul' t t' := by
    have ht : (t : GL (Fin n) F) ∈ borel F n := levi_le_blockUpper t.2
    simp only [Subgroup.coe_mul, iwasawaExponent_mul_of_mem_borel ht, monomialChar_add, map_mul]
    ring
theorem invSqrtModular_eq_one {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : invSqrtModular F n id p = 1 := by
  have h := sqrtModular_mul_invSqrtModular p
  have hs : sqrtModular F n id p = 1 := by
    show ((NNReal.sqrt (Measure.modularCharacter p) : ℝ) : ℂ) = 1
    rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
    simp
  rwa [hs, one_mul] at h
theorem isUnramified_unramifiedChar (w : Fin n → ℂˣ) : IsUnramified (unramifiedChar (F := F) w) := by
  intro t ht
  show monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t) = 1
  have h0 : iwasawaExponent F n (t : GL (Fin n) F) = 0 := by
    simpa [iwasawaExponent_one] using iwasawaExponent_mul_of_mem_integralGL F n 1 ht
  rw [h0, monomialChar_zero, invSqrtModular_eq_one ht, one_mul]
theorem iwasawaExponent_leviProj (b : blockUpper F n (id : Fin n → Fin n)) :
    iwasawaExponent F n ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      iwasawaExponent F n (b : GL (Fin n) F) := by
  have hb : (b : GL (Fin n) F) ∈ borel F n := b.2
  have hD : ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      diagGL F n (diagUnits hb) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_diagGL, leviProj_apply]
    by_cases hij : i = j
    · subst hij
      simp [diagUnits]
    · simp [hij, diagonal_apply_ne _ hij]
  rw [hD]
  conv_rhs => rw [show (b : GL (Fin n) F) = (b * (diagGL F n (diagUnits hb))⁻¹) *
    diagGL F n (diagUnits hb) by group]
  rw [iwasawaExponent_mul_of_mem_unipotent F n (mul_inv_diagUnits_mem_unipotent hb)]
theorem borelChar_unramifiedChar (w : Fin n → ℂˣ) (b : blockUpper F n (id : Fin n → Fin n)) :
    borelChar (unramifiedChar w) b = monomialChar (iwasawaExponent F n (b : GL (Fin n) F)) w := by
  rw [borelChar_apply]
  change sqrtModular F n id b * (monomialChar (iwasawaExponent F n
    ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F)) w *
      invSqrtModular F n id (leviIncl (leviProj F n id b))) = _
  rw [iwasawaExponent_leviProj]
  have : invSqrtModular F n id (leviIncl (leviProj F n id b)) = invSqrtModular F n id b := by
    show (sqrtModular F n id (leviIncl (leviProj F n id b)))⁻¹ = (sqrtModular F n id b)⁻¹
    rw [sqrtModular_leviProj]
  rw [this, mul_left_comm, sqrtModular_mul_invSqrtModular, mul_one]
theorem sphericalFun_unramifiedChar (w : Fin n → ℂˣ) (g : GL (Fin n) F) :
    sphericalFun (unramifiedChar w) g = monomialChar (iwasawaExponent F n g) w := by
  obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
  rw [sphericalFun_mul (isUnramified_unramifiedChar w) b hk, borelChar_unramifiedChar,
    iwasawaExponent_mul_of_mem_integralGL F n _ hk]
variable (F n) in

def integralOpen : OpenSubgroup (GL (Fin n) F) := ⟨integralGL F n, isOpen_integralGL F n⟩
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
def cosetSupport (h : SphericalHecke μ (F := F) (n := n)) :
    Finset (GL (Fin n) F ⧸ integralGL F n) :=
  (finite_image_mk_tsupport (integralOpen F n) (h : HeckeAlgebra μ).mem.2).toFinset
theorem apply_out_eq_zero {h : SphericalHecke μ (F := F) (n := n)}
    {x : GL (Fin n) F ⧸ integralGL F n} (hx : x ∉ cosetSupport h) :
    (h : HeckeAlgebra μ) x.out = 0 := by
  by_contra h0
  exact hx ((Set.Finite.mem_toFinset _).mpr ⟨x.out, subset_tsupport _ h0, QuotientGroup.out_eq' x⟩)
theorem sphericalEigen_unramifiedChar (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalEigen (unramifiedChar w) μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h, (h : HeckeAlgebra μ) x.out *
        monomialChar (iwasawaExponent F n x.out) w := by
  have hf : HasCompactSupport fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g :=
    (h : HeckeAlgebra μ).mem.2.mul_right
  have hK : ∀ g, ∀ k ∈ integralOpen F n,
      (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) (g * k) =
        (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) g := by
    intro g k hk
    simp only [sphericalFun_unramifiedChar, iwasawaExponent_mul_of_mem_integralGL F n g hk]
    rw [(HeckeAlgebraLevel.val_mem _ _ h k hk g).2]
  rw [sphericalEigen, integral_eq_smul_finsum_coset μ (integralOpen F n)
    (isCompact_integralGL F n) hf hK, Complex.real_smul]
  congr 1
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n,
    (h : HeckeAlgebra μ) x.out * sphericalFun (unramifiedChar w) x.out) = _
  rw [finsum_eq_sum_of_support_subset (s := cosetSupport h)]
  · simp only [sphericalFun_unramifiedChar]
  · intro x hx
    by_contra hxs
    exact hx (by simp [apply_out_eq_zero hxs])
variable (μ) in

def satake (h : SphericalHecke μ (F := F) (n := n)) : LaurentRing n :=
  (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
    ∑ x ∈ cosetSupport h, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out)
theorem evalAt_satake (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt w (satake μ h) = sphericalCharacter μ (isUnramified_unramifiedChar w) h := by
  rw [sphericalCharacter_apply, satake, map_smul, map_sum, sphericalEigen_unramifiedChar,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [evalAt_single]
variable (μ) in

def satakeHom : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] LaurentRing n where
  toFun := satake μ
  map_one' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_one]
  map_mul' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_mul]
  map_zero' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_zero]
  map_add' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_add]
  commutes' c := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, AlgHom.commutes]
end Spherical
end GroundTheory.Automorphic


