-- Prove2me | solution 1 for AlgebraicGeometry.exists_forall_le_closeds_eq_of_monotone_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9f482182-4261-5e23-a6c7-e490335fb265

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_forall_le_closeds_eq_of_monotone_of_isIrreducible

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry Topology

theorem solution
    {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) {ι : Type v} [Preorder ι] [Nonempty ι]
    (Z : ι → TopologicalSpace.Closeds X) (hZ : ∀ i, IsIrreducible (Z i : Set X)) (hx : ∀ i, x ∈ Z i)
    (hmono : Monotone Z) :
    ∃ i₀ : ι, ∀ i : ι, i₀ ≤ i → Z i = Z i₀ := by
  classical

  have hgen : ∀ i, IsGenericPoint (hZ i).genericPoint (Z i : Set X) :=
    fun i => (hZ i).isGenericPoint_genericPoint (Z i).isClosed
  have hsp : ∀ i, (hZ i).genericPoint ⤳ x := fun i => by
    rw [specializes_iff_mem_closure, (hgen i).def]; exact hx i

  have hmem : ∀ i, (hZ i).genericPoint ∈ Set.range (X.fromSpecStalk x) := fun i => by
    rw [Scheme.range_fromSpecStalk]; exact hsp i
  choose q hq using hmem
  let p : ι → PrimeSpectrum (X.presheaf.stalk x) := fun i => q i

  have hanti : ∀ i i', i ≤ i' → p i' ≤ p i := fun i i' h => by
    rw [PrimeSpectrum.le_iff_specializes]
    have hs : q i' ⤳ q i := by
      rw [← (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff, hq, hq, specializes_iff_mem_closure, (hgen i').def]
      have hmemi : (hZ i).genericPoint ∈ (Z i : Set X) := by
        have hcl : (hZ i).genericPoint ∈ closure ({(hZ i).genericPoint} : Set X) := subset_closure (Set.mem_singleton _)
        rwa [(hgen i).def] at hcl
      exact hmono h hmemi
    exact hs

  have hfin : ∀ i, Order.height (p i) < ⊤ := fun i => by
    have h1 : (Order.height (p i) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum (X.presheaf.stalk x)) :=
      Order.height_le_krullDim (p i)
    have h2 : Order.krullDim (PrimeSpectrum (X.presheaf.stalk x)) < ⊤ := ringKrullDim_lt_top
    have h3 := lt_of_le_of_lt h1 h2
    rw [← WithBot.coe_top, WithBot.coe_lt_coe] at h3
    exact h3

  refine ⟨Function.argmin (fun i => Order.height (p i)), fun i hi => ?_⟩
  have hle : p i ≤ p (Function.argmin fun i => Order.height (p i)) := hanti _ _ hi
  have heq : p i = p (Function.argmin fun i => Order.height (p i)) := by
    by_contra hne
    exact Function.not_lt_argmin (fun i => Order.height (p i)) i (Order.height_strictMono (lt_of_le_of_ne hle hne) (hfin i))
  have hζ : (hZ i).genericPoint = (hZ (Function.argmin fun i => Order.height (p i))).genericPoint := by
    rw [← hq i, ← hq (Function.argmin fun i => Order.height (p i))]
    exact congrArg (X.fromSpecStalk x) heq
  apply TopologicalSpace.Closeds.ext
  rw [← (hgen i).def, ← (hgen (Function.argmin fun i => Order.height (p i))).def, hζ]

end S_AlgebraicGeometry_exists_forall_le_closeds_eq_of_monotone_of_isIrreducible
end P2MW
export P2MW.S_AlgebraicGeometry_exists_forall_le_closeds_eq_of_monotone_of_isIrreducible (solution)
