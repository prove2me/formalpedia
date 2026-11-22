-- Prove2me | Definitions.Def_SumProduct_Boxes
-- name    : SumProduct_Boxes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:45:07.278664+00:00
-- url     : https://prove2.me/theorems/d6bdd230-1020-495d-aa06-e4531d4f1557
-- title:
--   Boxes
-- statement:
--   Definitions and structural lemmas for Boxes, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Boxes.lean

import Mathlib
set_option autoImplicit true
open scoped NumberField
open Pointwise
namespace SumProduct
def boxAddSet (K : Type*) [Field K] [NumberField K] (X : ℝ) : Set (𝓞 K) :=
  {α | ∀ w : NumberField.InfinitePlace K, w (α : K) ≤ X}
theorem boxAddSet_finite (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    (boxAddSet K X).Finite := by
  refine Set.Finite.of_finite_image (f := fun α : 𝓞 K => (α : K)) ?_
    (fun a _ b _ hab => NumberField.RingOfIntegers.coe_injective hab)
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ X).subset ?_
  rintro x ⟨α, hα, rfl⟩
  exact ⟨NumberField.RingOfIntegers.isIntegral_coe α, fun φ => by
    rw [← NumberField.InfinitePlace.apply φ]; exact hα (NumberField.InfinitePlace.mk φ)⟩
noncomputable def boxAdd (K : Type*) [Field K] [NumberField K] (X : ℝ) : Finset (𝓞 K) :=
  (boxAddSet_finite K X).toFinset
@[simp] theorem mem_boxAdd {K : Type*} [Field K] [NumberField K] {X : ℝ} {α : 𝓞 K} :
    α ∈ boxAdd K X ↔ ∀ w : NumberField.InfinitePlace K, w (α : K) ≤ X :=
  Set.Finite.mem_toFinset _
def boxMultSet (K : Type*) [Field K] [NumberField K] (Y : ℝ) : Set (𝓞 K)ˣ :=
  {u | ∀ w : NumberField.InfinitePlace K, |Real.log (w ((u : 𝓞 K) : K))| ≤ Y}
theorem boxMultSet_finite (K : Type*) [Field K] [NumberField K] (Y : ℝ) :
    (boxMultSet K Y).Finite := by
  refine Set.Finite.of_finite_image (f := fun u : (𝓞 K)ˣ => ((u : 𝓞 K) : K)) ?_
    (fun a _ b _ hab => Units.ext (NumberField.RingOfIntegers.coe_injective hab))
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ (Real.exp Y)).subset ?_
  rintro x ⟨u, hu, rfl⟩
  refine ⟨NumberField.RingOfIntegers.isIntegral_coe _, fun φ => ?_⟩
  rw [← NumberField.InfinitePlace.apply φ]
  have hpos : 0 < (NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K) :=
    NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u)
  have hlog : Real.log ((NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K)) ≤ Y :=
    le_trans (le_abs_self _) (hu (NumberField.InfinitePlace.mk φ))
  calc (NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K)
      = Real.exp (Real.log ((NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K))) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp Y := Real.exp_le_exp.mpr hlog
noncomputable def boxMult (K : Type*) [Field K] [NumberField K] (Y : ℝ) : Finset (𝓞 K)ˣ :=
  (boxMultSet_finite K Y).toFinset
open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  NumberField.InfinitePlace in
/-- The region in `logSpace K` (`≅ ℝ^{d-1}`) corresponding to `B^×(r)` under `logEmbedding`:
the dropped coordinate `w₀` reappears as the sum constraint, because
`∑_w log w(u) = log |N(u)| = 0`, so `|log w₀(u)| = |∑_{w ≠ w₀} log w(u)|`. -/
def unitBox (K : Type*) [Field K] [NumberField K] (r : ℝ) : Set (logSpace K) :=
  {y | (∀ w, |y w| ≤ r) ∧ |∑ w, y w| ≤ r}
end SumProduct


