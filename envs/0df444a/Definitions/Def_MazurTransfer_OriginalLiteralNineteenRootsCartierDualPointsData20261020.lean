-- Prove2me | Definitions.Def_MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
-- name    : MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T22:20:22.513008+00:00
-- url     : https://prove2.me/theorems/da117c09-25db-477f-a2b0-947990755a01
-- title:
--   Original Cartier dual point group and fixed cyclic equivalence for a given literal-root Hopf model
-- statement:
--   Retain the same given literal-root Hopf model, original Cartier dual points, original commutative group with inverse given by the eighteenth power, and original chosen cyclic and group-algebra equivalences. All four complete original constructor types and whole values, three scoped provider types and two whole values, every private helper type and nonproof value, and all original root and Cartier dual contexts are independently checked. Named downstream consumer: normalized literal mu19 classification of the same selected integral pi quotient and its norm Kummer unit conditions.
-- source:
--   MazurTheorem LiteralNineteenRootsCartierDualPoints by Vas and contributors; same given Hopf model and original chosen cyclic equivalence, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
import Definitions.Def_MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
import Theorems.Thm_GaloisRep_cartierDual_points_of_galoisCyclotomic
import Theorems.Thm_MazurTransfer_original_nineteen_roots_cyclotomic_power
import Theorems.Thm_MazurTransfer_original_finite_free_hopf_arithmetic_point_rank
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the Cartier-dual field points of the SAME given literal-root
Hopf model have order nineteen, exponent nineteen, and trivial Galois action.
The cyclic equivalence retains the original convolution monoid definitionally.
Named downstream consumer: normalized literal-mu19 classification of the
PREVIOUSLY SELECTED actual pi quotient and its Kummer unit condition.
-/

noncomputable section
namespace MazurTransfer.LiteralNineteenRootsCartierDualPoints
open NineteenRootsGaloisRepresentation NineteenRootsCyclotomicPower
local notation "K" => AlgebraicClosure ℚ
local notation "R" => GaloisRep.ratLocalizedAt 19
local instance instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
local instance instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Roots K)) :=
  RepresentationCanonicalDistribMulAction.ofRepresentation (rootsRepresentation K)
variable (H : Type) [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
variable (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K))
variable (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)),
  (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f))

abbrev DualPoints := WithConv (CartierDual R H →ₐ[R] K)

include e he_add he_act in
private theorem dual_points_fixed_pow_card :
    (∀ (σ : K ≃ₐ[ℚ] K) (ψ : DualPoints H) (θ : CartierDual R H), σ (ψ θ) = ψ θ) ∧
    (∀ ψ : DualPoints H, ψ ^ 19 = 1) ∧ Nat.card (DualPoints H) = 19 := by
  have hcard := MazurTransfer.original_finite_free_hopf_arithmetic_point_rank H K e
  have h := GaloisRep.cartierDual_points_of_galoisCyclotomic 19 H e he_add he_act 1
    (fun m => by simpa only [pow_one] using MazurTransfer.original_nineteen_roots_cyclotomic_power.2.2.1 K m) (exponent K)
    (fun σ ζ hζ => MazurTransfer.original_nineteen_roots_cyclotomic_power.1 K σ ζ (by simpa only [pow_one] using hζ))
    (fun σ m => MazurTransfer.original_nineteen_roots_cyclotomic_power.2.1 K σ m) hcard.symm
  exact ⟨h.1, fun ψ => by simpa only [pow_one] using h.2.1 ψ,
    h.2.2.trans (hcard.trans (roots_card K))⟩

abbrev dualPointGroup : CommGroup (DualPoints H) where
  __ := (inferInstance : CommMonoid (DualPoints H))
  inv ψ := ψ ^ 18
  inv_mul_cancel ψ := by
    rw [← pow_succ]
    exact (dual_points_fixed_pow_card H e he_add he_act).2.1 ψ



def cyclicEquiv : DualPoints H ≃* Multiplicative (ZMod 19) := by
  letI := dualPointGroup H e he_add he_act
  have hcard := (dual_points_fixed_pow_card H e he_add he_act).2.2
  letI : IsCyclic (DualPoints H) := isCyclic_of_prime_card hcard
  exact mulEquivOfCyclicCardEq (by
    change Nat.card (DualPoints H) = Nat.card (ZMod 19)
    simpa only [Nat.card_zmod] using hcard)

def cyclicAlgebraEquiv : MonoidAlgebra R (DualPoints H) ≃ₐc[R]
    MonoidAlgebra R (Multiplicative (ZMod 19)) :=
  MonoidAlgebra.domCongrBialgEquiv R R (cyclicEquiv H e he_add he_act)

end MazurTransfer.LiteralNineteenRootsCartierDualPoints
#print axioms MazurTransfer.LiteralNineteenRootsCartierDualPoints.DualPoints
#print axioms MazurTransfer.LiteralNineteenRootsCartierDualPoints.dualPointGroup
#print axioms MazurTransfer.LiteralNineteenRootsCartierDualPoints.cyclicEquiv
#print axioms MazurTransfer.LiteralNineteenRootsCartierDualPoints.cyclicAlgebraEquiv
#print axioms MazurTransfer.LiteralNineteenRootsCartierDualPoints.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints
#print axioms MazurTransfer.LiteralNineteenRootsCartierDualPoints.instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints
#print axioms MazurTransfer.LiteralNineteenRootsCartierDualPoints.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints


