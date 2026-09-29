-- Prove2me | solution 1 for AlgebraicGeometry.finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/88f3880c-919c-5589-b7ed-11a208628e15

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicGeometry_exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two
import Theorems.Thm_AlgebraicGeometry_subsingleton_fppfH1_Gm_specZ
import Theorems.Thm_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
import Theorems.Thm_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false
open AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (dt : ℕ) (hKA : Nat.card (K →ₐ[ℤ] ↥A) = q ^ dt) :
    Finite (fppfCohomology specInt L 1) := by
  classical
  obtain ⟨dk, -, C, iC, f, hker⟩ :=
    AlgebraicGeometry.exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two
      p q hq2 K ‹_› ‹_› ‹_› ‹_› hff hgenq hgal L e hnat A hA dt hKA
  have hq : q.Prime := Fact.out
  have hc := AlgebraicGeometry.natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
    (FppfKummerSES.muPAbelianSheafLifted.{0} q) C iC
  haveI := AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ
  have hGm : Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1 :=
    Nat.card_unique
  have hmu : Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} q) 1) = 1 :=
    AlgebraicGeometry.fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial q hq (hq.odd_of_ne_two hq2) hGm
  have hC1 : Nat.card (fppfCohomology specInt C 1) = 1 := by rw [hc, hmu]
  haveI : Subsingleton (fppfCohomology specInt C 1) := (Nat.card_eq_one_iff_unique.mp hC1).1
  have htop : (fppfCohomologyMap specInt f 1).ker = ⊤ := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_top, iff_true]
    exact Subsingleton.elim _ _
  have hfin : Finite ↥(fppfCohomologyMap specInt f 1).ker :=
    Nat.finite_of_card_ne_zero (by rw [hker]; exact pow_ne_zero _ hq.ne_zero)
  rw [htop] at hfin
  exact Finite.of_equiv _ (AddSubgroup.topEquiv : (⊤ : AddSubgroup (fppfCohomology specInt L 1)) ≃+ _).toEquiv

end S_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two
end P2MW
export P2MW.S_AlgebraicGeometry_finite_fppfCohomology_one_of_sectionsEquiv_algHom_of_natCard_eq_prime_of_galoisCyclotomic_of_ne_two (solution)
