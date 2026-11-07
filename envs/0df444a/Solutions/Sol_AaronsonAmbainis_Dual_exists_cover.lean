-- Prove2me | solution 1 for AaronsonAmbainis.Dual.exists_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:45.935249+00:00
-- url     : https://prove2.me/submissions/260f7cc7-3262-4901-9551-39193bff488a

import Definitions.Def_AaronsonAmbainis_Dual_Sets
import Definitions.Def_AaronsonAmbainis_Dual_Functional
import Definitions.Def_AaronsonAmbainis_Dual_Core
import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Theorems.Thm_AaronsonAmbainis_Dual_coeff_nonneg
import Theorems.Thm_AaronsonAmbainis_Dual_functional_eq_sum
import Theorems.Thm_AaronsonAmbainis_Dual_no_separator
import Theorems.Thm_AaronsonAmbainis_Dual_orthant_convex
import Theorems.Thm_AaronsonAmbainis_Dual_orthant_isClosed
import Theorems.Thm_AaronsonAmbainis_Dual_slackImage_convex
import Theorems.Thm_AaronsonAmbainis_Dual_slackImage_isCompact


set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Dual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (t : Finset ι → ℝ) (K : ℝ)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i := by
  -- the zero packing gives `0 ≤ K`
  have hK : 0 ≤ K := by
    have h := hpack 0 (fun _ => le_rfl) (fun i => by simp)
    simpa using h
  by_contra hne
  -- the set `Q` of slack vectors misses the orthant
  have hdisj : Disjoint (slack t '' massSet ι K) (orthant ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ⟨ha0, haK⟩, rfl⟩ hv
    refine hne ⟨a, ha0, haK, fun S => ?_⟩
    have h : 0 ≤ ∑ i ∈ S, a i - t S := hv S
    linarith
  -- strict separation of the compact convex `Q` from the closed convex orthant
  obtain ⟨φ, u, r, hQ, hur, hV⟩ :=
    geometric_hahn_banach_compact_closed (slackImage_convex t K)
      (slackImage_isCompact t K) orthant_convex orthant_isClosed hdisj
  -- `0` lies in the orthant, so `r < 0`
  have hr : r < 0 := by
    have h0 := hV 0 (fun _ => le_rfl)
    rwa [map_zero] at h0
  -- the coefficients of `φ` are nonnegative
  have hκ : ∀ S : Finset ι, 0 ≤ φ (Pi.single S 1) :=
    fun S => coeff_nonneg φ r hV S
  -- the finite core
  refine no_separator t K hK hpack (fun S => φ (Pi.single S 1)) hκ (fun a ha0 haK => ?_)
  have h1 : φ (slack t a) < u := hQ (slack t a) ⟨a, ⟨ha0, haK⟩, rfl⟩
  rw [functional_eq_sum φ (slack t a)] at h1
  have h2 : ∑ S, φ (Pi.single S 1) * slack t a S
      = ∑ S, φ (Pi.single S 1) * (∑ i ∈ S, a i - t S) := rfl
  rw [h2] at h1
  linarith
end AaronsonAmbainis.Dual
