-- Prove2me | solution 1 for AlgebraicGeometry.finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f3bd4dbc-66dc-5404-88d1-9531f5be6eee

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import Theorems.Thm_AlgebraicGeometry_exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two
import Theorems.Thm_AlgebraicGeometry_subsingleton_fppfH1_constantZMod_specZ_of_prime
import Theorems.Thm_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two
p2m_attr_erase "simp" "Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false
open AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k)) :
    Finite (fppfCohomology specInt L 1) := by
  classical
  obtain ⟨C, iC, f, hf⟩ :=
    AlgebraicGeometry.exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two
      p q hq2 K ‹_› ‹_› ‹_› ‹_› hff hgenq hgal L e hnat
  have hc := AlgebraicGeometry.natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
    (FppfKummerSES.sheafULift.{0}.obj (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} q)) C iC
  haveI := AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime q
  have h1 : Nat.card (FppfCohomologyLES.FppfH
      (FppfKummerSES.sheafULift.{0}.obj (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} q)) 1) = 1 :=
    Nat.card_unique
  haveI : Finite (fppfCohomology specInt C 1) :=
    Nat.finite_of_card_ne_zero (by rw [hc, h1]; exact one_ne_zero)
  exact Finite.of_injective _ hf

end S_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two
end P2MW
export P2MW.S_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisInvariant_of_ne_two (solution)
