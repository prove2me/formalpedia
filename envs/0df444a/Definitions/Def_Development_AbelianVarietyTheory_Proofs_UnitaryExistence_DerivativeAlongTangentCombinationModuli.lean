-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuli
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuli
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:05.537905+00:00
-- url     : https://prove2.me/theorems/9ad857b7-2d1b-44ac-8e59-691067d1510c
-- title:
--   Derivative Along Tangent Combination Moduli
-- statement:
--   Definitions and structural lemmas for Derivative Along Tangent Combination Moduli, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DerivativeAlongTangentCombinationModuli.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_TanMod_unit_of_smT_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TanDeriv
section SlopeTestRemainingChoices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.TanMod
def evAt {R : Type} [CommRing R] {Y : Scheme.{0}} (W : Sp R ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U)
    (f : Γ(Y, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((W.appLE U ⊤ h).hom f)
theorem evAt_congr {R : Type} [CommRing R] {Y : Scheme.{0}} {W W' : Sp R ⟶ Y} (e : W = W') (U : Y.Opens)
    (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ W' ⁻¹ᵁ U) (f : Γ(Y, U)) : evAt W U h f = evAt W' U h' f := by
  subst e; rfl
theorem evAt_comp {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ W) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evAt (spMap φ ≫ W) U h' f = φ (evAt W U h f) := by
  have h1 : (spMap φ ≫ W).appLE U ⊤ h' = W.appLE U ⊤ h ≫ (spMap φ).appTop := by
    have : (spMap φ).appTop = (spMap φ).appLE ⊤ ⊤ le_top := (Scheme.Hom.app_eq_appLE (spMap φ))
    rw [this]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) W U ⊤ ⊤ h le_top).symm
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h3 := congrArg (fun ψ => ψ.hom ((W.appLE U ⊤ h).hom f)) h2
  unfold evAt
  rw [h1]
  exact h3
theorem top_le_of_comp {R A : Type} [CommRing R] [CommRing A] (p : R →+* A)
    (hs : Function.Surjective p) (hn : ∀ x, p x = 0 → x * x = 0) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U) : ⊤ ≤ W ⁻¹ᵁ U := by
  intro x _
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap p) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have h3 : a * a ∈ (show PrimeSpectrum R from x).asIdeal := by
      rw [hn a ha]; exact Ideal.zero_mem _
    exact ((show PrimeSpectrum R from x).isPrime.mem_or_mem h3).elim id id
  obtain ⟨y, hy⟩ := hx
  have h4 : (show Sp A from y) ∈ (spMap p ≫ W) ⁻¹ᵁ U := h trivial
  have h5 : spMap p (show Sp A from y) = x := hy
  rw [← h5]
  exact h4
theorem comp_top_le {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) {Y : Scheme.{0}} (W : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ W ⁻¹ᵁ U) : ⊤ ≤ (spMap p ≫ W) ⁻¹ᵁ U :=
  fun y _ => h (show spMap p y ∈ (⊤ : (Sp R).Opens) from trivial)
variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]
theorem snd_evAt_mul (u v : overAt x0 (DualNumber S) ⟶ G) (hu0 : smT x0 0 u = 1) (hv0 : smT x0 0 v = 1)
    (U : G.left.Opens) (hu : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from u.left) ⁻¹ᵁ U)
    (hv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from v.left) ⁻¹ᵁ U)
    (huv : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (u * v).left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt (R := DualNumber S) (u * v).left U huv f).snd =
      (evAt (R := DualNumber S) u.left U hu f).snd + (evAt (R := DualNumber S) v.left U hv f).snd := by
  have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
  let P : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G :=
    (homAt x0 (tm (LinearMap.inl S S S)) ≫ u) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)
  have e1 : homAt x0 (tm (LinearMap.fst S S S)) ≫ P = u := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change _ * smT x0 0 v = _
    rw [hv0, _root_.mul_one]
  have e2 : homAt x0 (tm (LinearMap.snd S S S)) ≫ P = v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change smT x0 0 u * _ = _
    rw [hu0, _root_.one_mul]
  have e3 : homAt x0 (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S)) ≫ P = u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
      Category.id_comp]
  have f1 : spMap (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = u.left :=
    congrArg (fun φ => φ.left) e1
  have f2 : spMap (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = v.left :=
    congrArg (fun φ => φ.left) e2
  have f3 : spMap (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = (u * v).left :=
    congrArg (fun φ => φ.left) e3
  have hP : ⊤ ≤ (show Sp (TrivSqZeroExt S (S × S)) ⟶ G.left from P.left) ⁻¹ᵁ U := by
    refine top_le_of_comp (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ?_ ?_ _ U ?_
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · exact f1 ▸ hu
  rw [← evAt_congr f1 U (comp_top_le _ _ U hP) hu, ← evAt_congr f2 U (comp_top_le _ _ U hP) hv,
    ← evAt_congr f3 U (comp_top_le _ _ U hP) huv, evAt_comp _ _ U hP, evAt_comp _ _ U hP, evAt_comp _ _ U hP]
  simp
variable [IsCommMonObj G]
theorem tan_top_le (U : G.left.Opens)
    (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U) (m : TanSp x0 G) :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from m.pt.left) ⁻¹ᵁ U := by
  refine top_le_of_comp (TrivSqZeroExt.fstHom S S S).toRingHom ?_ ?_ _ U ?_
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]
  · exact (unit_of_smT_zero x0 _ m.tan).symm ▸ h1
def derivAt (U : G.left.Opens) (h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U)
    (f : Γ(G.left, U)) : TanSp x0 G →ₗ[S] S where
  toFun m := (evAt (R := DualNumber S) m.pt.left U (tan_top_le U h1 m) f).snd
  map_add' m n := snd_evAt_mul m.pt n.pt m.tan n.tan U _ _ _ f
  map_smul' a m := by
    have := evAt_comp (epsMul a) (show Sp (DualNumber S) ⟶ G.left from m.pt.left) U (tan_top_le U h1 m)
      (tan_top_le U h1 (a • m)) f
    refine (congrArg TrivSqZeroExt.snd this).trans ?_
    simp [epsMul]
end SlopeTestRemainingChoices
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
end GlobalTheory.TanDeriv


