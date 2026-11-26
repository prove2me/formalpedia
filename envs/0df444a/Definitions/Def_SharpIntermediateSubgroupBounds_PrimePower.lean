-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
-- name    : SharpIntermediateSubgroupBounds_PrimePower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:40:59.412303+00:00
-- url     : https://prove2.me/theorems/d571d505-f36d-4f45-80fe-4ef9839c8527
-- title:
--   Prime Power
-- statement:
--   Definitions and structural lemmas for Prime Power, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
noncomputable local instance subgroupCarrierFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H
noncomputable local instance subgroupIntervalFintype (H : Subgroup G) : Fintype (Set.Ici H) :=
  Fintype.ofFinite (Set.Ici H)
abbrev CoatomFiber (M V : Subgroup G) :=
  {Q : Subgroup G // Q ⊓ M = V ∧ ¬ Q ≤ M}
noncomputable local instance coatomFiberFintype (M V : Subgroup G) :
    Fintype (CoatomFiber M V) := Fintype.ofFinite _
def primePowerLayer (p k : ℕ) (T P : Subgroup G) : Finset (Subgroup G) :=
  by
    classical
    exact Finset.univ.filter fun Q ↦ T ≤ Q ∧ Q ≤ P ∧ Q.relIndex P = p ^ k
@[simp]
theorem mem_primePowerLayer {p k : ℕ} {T P Q : Subgroup G} :
    Q ∈ primePowerLayer p k T P ↔ T ≤ Q ∧ Q ≤ P ∧ Q.relIndex P = p ^ k := by
  simp [primePowerLayer]
def intermediateSubgroups (H : Subgroup G) : Finset (Subgroup G) :=
  by
    classical
    exact Finset.univ.filter fun K ↦ H ≤ K
@[simp] theorem mem_intermediateSubgroups {H K : Subgroup G} :
    K ∈ intermediateSubgroups H ↔ H ≤ K := by
  simp [intermediateSubgroups]
def elementarySubgroupSubmoduleIso (p a : ℕ) :
    Subgroup (Multiplicative (Fin a → ZMod p)) ≃o
      Submodule (ZMod p) (Fin a → ZMod p) :=
  AddSubgroup.toSubgroup.symm.trans (AddSubgroup.toZModSubmodule p)
def elementaryCarrierEquiv (p a : ℕ)
    (Q : Subgroup (Multiplicative (Fin a → ZMod p))) :
    Q ≃ elementarySubgroupSubmoduleIso p a Q where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
universe u v
noncomputable def productTopBotQuotientEquiv (H₀ : Type u) (E : Type v)
    [Group H₀] [Group E] :
    ((H₀ × E) ⧸ ((⊤ : Subgroup H₀).prod (⊥ : Subgroup E))) ≃* E :=
  (QuotientGroup.prodMulEquiv (⊤ : Subgroup H₀) (⊥ : Subgroup E)).trans
    { toFun := fun q ↦ QuotientGroup.quotientBot q.2
      invFun := fun e ↦ (1, QuotientGroup.quotientBot.symm e)
      left_inv := by
        intro q
        apply Prod.ext
        · exact QuotientGroup.subsingleton_quotient_top.elim _ _
        · exact QuotientGroup.quotientBot.symm_apply_apply q.2
      right_inv := QuotientGroup.quotientBot.apply_symm_apply
      map_mul' := by
        intro x y
        exact QuotientGroup.quotientBot.map_mul x.2 y.2 }
end
end SharpIntermediateSubgroupBounds


