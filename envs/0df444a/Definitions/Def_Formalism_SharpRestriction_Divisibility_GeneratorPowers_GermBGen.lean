-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:03.05324+00:00
-- url     : https://prove2.me/theorems/b5708b3a-6b04-4f6e-8ed9-dc76510101e1
-- title:
--   Germ BGen
-- statement:
--   Definitions and structural lemmas for Germ BGen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Jet
variable {S ι : Type} [CommRing S]
theorem jet_exists_nil (m : ℕ) (a : Jet S ι m) : ∃ c : S, IsNilpotent (a - algebraMap S (Jet S ι m) c) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨MvPolynomial.constantCoeff p, m + 1, ?_⟩
  have h : Ideal.Quotient.mk (orig S ι ^ (m + 1)) p - algebraMap S (Jet S ι m) (MvPolynomial.constantCoeff p) =
      Ideal.Quotient.mk _ (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) := by
    rw [map_sub]
    rfl
  rw [h, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (sub_const_mem_orig p) _
instance jet_isLocalRing [IsLocalRing S] (m : ℕ) : IsLocalRing (Jet S ι m) := by
  have : Nontrivial (Jet S ι m) := (jetAug : Jet S ι m →ₐ[S] S).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨c, hc⟩ := jet_exists_nil (ι := ι) m a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
  · left
    have := hc.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    simpa using this
  · right
    have := hc.neg.isUnit_add_left_of_commute (h.map (algebraMap S (Jet S ι m))) (Commute.all _ _)
    convert this using 1
    rw [map_sub, map_one]
    ring
end Jet
section Gen
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
def cgen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j0 : K → L.ι) (h0 : LB.wchart L φ j0 = ⊤) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res (le_inf le_rfl (by rw [h0]; exact le_top) : LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j0)
    ((LB.LinComb L φ ε).g j j0)⟩
def cv {Z : Scheme.{0}} (i0 : L.ι) (z : Z) (J : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U i0) (L.g (J ψ) i0)
def divLin (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε'))) :
    LB.Gen (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε fun k => -ε' k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩ :
    LB.wchart L (Sum.elim φ φ') j ≤ (LB.div (LB.LinComb L φ ε) (LB.LinComb L φ' ε')).U (j ∘ Sum.inl, j ∘ Sum.inr))
    (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩
end Gen
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB


