-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:02.348811+00:00
-- url     : https://prove2.me/theorems/590e10d4-a7be-43f3-8448-5265bfbc5896
-- title:
--   Psb Lb
-- statement:
--   Definitions and structural lemmas for Psb Lb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
namespace LB
variable {X Y Z : Scheme.{u}}
abbrev triv (X : Scheme.{u}) : LB X where
  ι := PUnit.{u+1}
  U := fun _ => ⊤
  g := fun _ _ => 1
def dg (M L : LB X) (p q : M.ι × L.ι) : Γ(X, M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2))ˣ :=
  res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
    (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
lemma wchart_inter_le (φ : K → (Y ⟶ X)) (j j' : K → L.ι) (k : K) :
    wchart L φ j ⊓ wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
  le_inf (inf_le_left.trans (wchart_le L φ j k)) (inf_le_right.trans (wchart_le L φ j' k))
def lcg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) :
    Γ(Y, wchart L φ j ⊓ wchart L φ j')ˣ :=
  ∏ k, (res (wchart_inter_le L φ j j' k) (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)
def ts {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : Gen (LinComb L φ ε)) (j : K → L.ι) :
    Γ(Y, wchart L φ j)ˣ :=
  t.s j
lemma wchart_comp_le (h : Z ⟶ Y) (φ : K → (Y ⟶ X)) (j : K → L.ι) :
    wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ wchart L φ j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
lemma wchart_comp_le₂ (h : Z ⟶ Y) (φ : K → (Y ⟶ X)) (i j : K → L.ι) :
    wchart L (fun k => h ≫ φ k) i ⊓ wchart L (fun k => h ≫ φ k) j ≤
      h ⁻¹ᵁ (wchart L φ i ⊓ wchart L φ j) :=
  fun _ hy => ⟨wchart_comp_le L h φ i hy.1, wchart_comp_le L h φ j hy.2⟩
lemma wchart_inl_le (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ≤ wchart L φ (j ∘ Sum.inl) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
lemma wchart_inr_le (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ≤ wchart L φ' (j ∘ Sum.inr) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
lemma wchart_inl_le₂ (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j j' : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ⊓ wchart L (Sum.elim φ φ') j' ≤
      wchart L φ (j ∘ Sum.inl) ⊓ wchart L φ (j' ∘ Sum.inl) :=
  inf_le_inf (wchart_inl_le L φ φ' j) (wchart_inl_le L φ φ' j')
lemma wchart_inr_le₂ (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j j' : K ⊕ K' → L.ι) :
    wchart L (Sum.elim φ φ') j ⊓ wchart L (Sum.elim φ φ') j' ≤
      wchart L φ' (j ∘ Sum.inr) ⊓ wchart L φ' (j' ∘ Sum.inr) :=
  inf_le_inf (wchart_inr_le L φ φ' j) (wchart_inr_le L φ φ' j')
lemma wchart_pu_le (M : LB X) (f : Y ⟶ X) (i j : PUnit.{u+1} → M.ι) :
    wchart M (K := PUnit) (fun _ => f) i ⊓ wchart M (K := PUnit) (fun _ => f) j ≤
      f ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
  wchart_inter_le M (K := PUnit) (fun _ => f) i j PUnit.unit
end LB
end
end ReciprocityTheory.ChartRestriction.G.Semi


