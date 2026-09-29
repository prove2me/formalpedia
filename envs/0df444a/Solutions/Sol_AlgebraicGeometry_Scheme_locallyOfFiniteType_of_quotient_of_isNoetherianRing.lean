-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.locallyOfFiniteType_of_quotient_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0e22abd3-d508-5880-86f8-9fb0875fb560

import Mathlib
import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace QuotLftNoethGC3

theorem appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

end QuotLftNoethGC3

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪)) (hlft : LocallyOfFiniteType fM)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ p ⁻¹ᵁ V = U) :
    LocallyOfFiniteType f := by
  classical
  haveI := hint; haveI := haff; haveI := hlft

  apply HasRingHomProperty.of_iSup_eq_top (P := @LocallyOfFiniteType) (fun V : X.affineOpens => V) (iSup_affineOpens_eq_top X)
  intro V

  have hU : IsAffineOpen (p ⁻¹ᵁ (V : X.Opens)) := V.2.preimage p
  have hUst : ∀ g : G, (ρ g).hom ⁻¹ᵁ (p ⁻¹ᵁ (V : X.Opens)) = p ⁻¹ᵁ (V : X.Opens) := fun g => by
    rw [← Scheme.Hom.comp_preimage, hρp g]
  let Aring : Type := Γ(X, (V : X.Opens))
  let Bring : Type := Γ(M, p ⁻¹ᵁ (V : X.Opens))
  let Rring : Type := Γ(Spec (CommRingCat.of 𝒪), (⊤ : (Spec (CommRingCat.of 𝒪)).Opens))

  letI algRA : Algebra Rring Aring := (f.appLE ⊤ (V : X.Opens) le_top).hom.toAlgebra
  letI algAB : Algebra Aring Bring := (p.app (V : X.Opens)).hom.toAlgebra
  letI algRB : Algebra Rring Bring := (fM.appLE ⊤ (p ⁻¹ᵁ (V : X.Opens)) le_top).hom.toAlgebra
  haveI : IsScalarTower Rring Aring Bring := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show (fM.appLE ⊤ (p ⁻¹ᵁ (V : X.Opens)) le_top) r = (p.app (V : X.Opens)) ((f.appLE ⊤ (V : X.Opens) le_top) r)
    rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      QuotLftNoethGC3.appLE_congr_hom hp]
  haveI : FaithfulSMul Aring Bring := (faithfulSMul_iff_algebraMap_injective Aring Bring).mpr (hsec V)
  haveI : IsNoetherianRing Rring := isNoetherianRing_of_ringEquiv 𝒪 (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).symm.commRingCatIsoToRingEquiv

  haveI : Algebra.FiniteType Rring Bring := by
    have := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) fM hlft ⟨⊤, isAffineOpen_top _⟩ ⟨_, hU⟩ le_top
    exact RingHom.finiteType_algebraMap.mp this

  let θ : G →* (Bring →+* Bring) :=
    { toFun := fun g => ((ρ g⁻¹).hom.appLE (p ⁻¹ᵁ (V : X.Opens)) (p ⁻¹ᵁ (V : X.Opens)) (by rw [hUst])).hom
      map_one' := by
        have h1 : (ρ (1 : G)⁻¹).hom = 𝟙 M := by rw [inv_one, map_one]; rfl
        apply RingHom.ext; intro s
        show ((ρ (1 : G)⁻¹).hom.appLE _ _ _) s = s
        rw [QuotLftNoethGC3.appLE_congr_hom h1]
        erw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
        rfl
      map_mul' := fun g h => by
        have hm : (ρ (g * h)⁻¹).hom = (ρ g⁻¹).hom ≫ (ρ h⁻¹).hom := by rw [mul_inv_rev, map_mul, CategoryTheory.Aut.Aut_mul_def]; rfl
        apply RingHom.ext; intro s
        show ((ρ (g * h)⁻¹).hom.appLE _ _ _) s = ((ρ g⁻¹).hom.appLE _ _ _) (((ρ h⁻¹).hom.appLE _ _ _) s)
        rw [QuotLftNoethGC3.appLE_congr_hom hm, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] }
  letI : MulSemiringAction G Bring := MulSemiringAction.compHom Bring θ
  have hsmul : ∀ (g : G) (s : Bring), g • s = ((ρ g⁻¹).hom.appLE (p ⁻¹ᵁ (V : X.Opens)) (p ⁻¹ᵁ (V : X.Opens)) (by rw [hUst])) s :=
    fun _ _ => rfl
  haveI : Algebra.IsInvariant Aring Bring G := by
    refine ⟨fun b hb => ?_⟩
    have : b ∈ Set.range (p.app (V : X.Opens)) := by
      rw [hinv V]
      intro g
      have := hb g⁻¹
      rw [hsmul, inv_inv] at this
      exact this
    exact this

  have hft : Algebra.FiniteType Rring Aring :=
    (Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType Rring Aring Bring G).2
  exact RingHom.finiteType_algebraMap.mpr hft

end S_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing (solution)
