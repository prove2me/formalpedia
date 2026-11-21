-- Prove2me | Definitions.Def_RiemannMasullo_RestrictedProductSplittings
-- name    : RiemannMasullo_RestrictedProductSplittings
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:28:26.953217+00:00
-- url     : https://prove2.me/theorems/14d1dc25-bf26-4318-9afe-be827380e304
-- title:
--   Finite changes and finite factor splittings of restricted products
-- statement:
--   Two explicit continuous multiplicative equivalences used in Appendix A.1.1. The first identifies restricted products whose distinguished subgroups agree outside a finite set by the identity on coordinates. The second splits off a prescribed finite family of factors, assuming eventual openness of the distinguished subgroups. Its inverse glues the two coordinate families.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean#L129-L220

import Mathlib
import Theorems.Thm_RiemannMasullo_continuous_restrictedProduct_of_uniform
import Theorems.Thm_RiemannMasullo_isOpen_restrictedProduct_forall_mem

namespace RiemannMasullo

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

variable [∀ i, Group (G i)] {K L : (i : ι) → Subgroup (G i)}

/-- Paper: Lemma A.1.1.2(2), p. 539. Changing finitely many distinguished subgroups gives a
continuous multiplicative equivalence acting as the identity on coordinates.
Deviation: This construction needs no compactness or openness hypotheses. -/
def restrictedProductCongr (h : ∀ᶠ i in cofinite, K i = L i) :
    (Πʳ i, [G i, K i]) ≃ₜ* (Πʳ i, [G i, L i]) where
  toFun := map (fun _ ↦ id) (h.mono fun _ hi ↦ hi ▸ mapsTo_id _)
  invFun := map (fun _ ↦ id) (h.mono fun _ hi ↦ hi ▸ mapsTo_id _)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := mapAlong_continuous G G id tendsto_id _
    (h.mono fun _ hi ↦ hi ▸ mapsTo_id _) (fun _ ↦ continuous_id)
  continuous_invFun := mapAlong_continuous G G id tendsto_id _
    (h.mono fun _ hi ↦ hi ▸ mapsTo_id _) (fun _ ↦ continuous_id)

/-- Paper: Lemma A.1.1.2(4), p. 539. Split the restricted product at a finite set of indices
by restricting each tuple to that set and its complement.
Deviation: Only eventual openness of the distinguished subgroups is needed. -/
noncomputable def restrictedProductSplitFinset (hK : ∀ᶠ i in cofinite, IsOpen (K i : Set (G i)))
    (J : Finset ι) :
    (Πʳ i, [G i, K i]) ≃ₜ* (((j : J) → G j) × (Πʳ j : {i // i ∉ J}, [G j, K j])) := by
  classical
  let F := (j : J) → G j
  let T := Πʳ j : {i // i ∉ J}, [G j, K j]
  let P := Πʳ i, [G i, K i]
  have extend {p : ι → Prop} (hp : ∀ᶠ j : {i // i ∉ J} in cofinite, p j) :
      ∀ᶠ i in cofinite, p i := by
    filter_upwards [J.eventually_cofinite_notMem,
      eventually_comap.mp (hp.filter_mono (comap_cofinite_le Subtype.val))] with i hi h
    exact h ⟨i, hi⟩ rfl
  let glue (z : F × T) (i : ι) : G i := if hi : i ∈ J then z.1 ⟨i, hi⟩ else z.2 ⟨i, hi⟩
  let join (z : F × T) : P := ⟨glue z, extend (by
    filter_upwards [z.2.2] with j hj
    change glue z j ∈ K j
    simp only [glue, dif_neg j.2]
    exact hj)⟩
  let tail : P → T := mapAlong G _ Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ id) (.of_forall fun _ ↦ mapsTo_id _)
  have htail : Continuous tail := mapAlong_continuous G _ Subtype.val
    Subtype.val_injective.tendsto_cofinite _ (.of_forall fun _ ↦ mapsTo_id _)
    (fun _ ↦ continuous_id)
  refine {
    toFun := fun x ↦ (fun j ↦ x j, tail x)
    invFun := join
    left_inv := ?_
    right_inv := ?_
    map_mul' := fun _ _ ↦ rfl
    continuous_toFun := (continuous_pi fun j ↦ continuous_eval j.val).prodMk htail
    continuous_invFun := ?_ }
  · intro x
    apply RestrictedProduct.ext
    intro i
    change glue _ i = x i
    by_cases hi : i ∈ J <;> simp [glue, hi]
    rfl
  · intro z
    apply Prod.ext
    · funext j
      simp [join, glue, j.2]
    · apply RestrictedProduct.ext
      intro j
      change glue z j = z.2 j
      simp [glue, j.2]
  · apply continuous_iff_continuousAt.mpr
    intro z
    -- Around z, the complementary factor lies uniformly in K on this cofinite set.
    let s := {j : {i // i ∉ J} | IsOpen (K j : Set (G j)) ∧ z.2 j ∈ K j}
    let V := {w : F × T | ∀ j ∈ s, w.2 j ∈ K j}
    have hV : IsOpen V := (isOpen_restrictedProduct_forall_mem s (fun j hj ↦ hj.1)).preimage
      continuous_snd
    apply ContinuousOn.continuousAt (s := V) _ (hV.mem_nhds fun j hj ↦ hj.2)
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_restrictedProduct_of_uniform
    · intro i
      change Continuous (fun w : V ↦ glue w.val i)
      by_cases hi : i ∈ J
      · simp only [glue, dif_pos hi]
        exact (continuous_apply (⟨i, hi⟩ : J)).comp (continuous_fst.comp continuous_subtype_val)
      · simp only [glue, dif_neg hi]
        exact (continuous_eval (⟨i, hi⟩ : {i // i ∉ J})).comp
          (continuous_snd.comp continuous_subtype_val)
    · apply extend
      filter_upwards [Subtype.val_injective.tendsto_cofinite.eventually hK, z.2.2] with j ho hz w
      simpa [domRestrict, join, glue, j.2] using w.2 j ⟨ho, hz⟩

end RiemannMasullo


