-- Prove2me | solution 1 for AlonTarsi.alon_tarsi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:39.10427+00:00
-- url     : https://prove2.me/submissions/1da12633-4a53-4b34-926d-eba37a52f792

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Definitions.Def_AlonTarsiLib_PlanarSparse
public import Definitions.Def_AlonTarsiLib_AlonTarsi
public import Theorems.Thm_AlonTarsi_exists_eval_graphPoly_ne_zero
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_ConnSet_mono
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_mono
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
attribute [local simp] LeanPool.K5MinorFreeChoosability.dartSymm_apply
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AlonTarsi
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace AlonTarsi
theorem _root_.solution {Color : Type*} (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (hEO : eulerianCount D 0 ≠ eulerianCount D 1)
    (L : V → Finset Color) (hL : ∀ v, #{w | D v w} < (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by
  classical
  set A : Finset (V × V) := univ.filter fun p : V × V => D p.1 p.2 with hAdef
  have hsum : ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}),
      (-1 : ℤ) ^ #t = (eulerianCount D 0 : ℤ) - eulerianCount D 1 := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun t : Finset (V × V) => #t % 2 = 0)]
    rw [sub_eq_add_neg]
    congr 1
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)), Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.filter_filter]
      · unfold eulerianCount
        congr 2
      · intro t ht
        rw [Finset.mem_filter] at ht
        exact Even.neg_one_pow (Nat.even_iff.2 ht.2)
    · rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ)), Finset.sum_const, nsmul_eq_mul,
        mul_neg_one, Finset.filter_filter]
      · unfold eulerianCount
        congr 3
        ext t
        simp only [A, Finset.mem_filter, Nat.mod_two_ne_zero]
      · intro t ht
        rw [Finset.mem_filter] at ht
        exact Odd.neg_one_pow (Nat.odd_iff.2 (Nat.mod_two_ne_zero.1 ht.2))
  have hne : ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}),
      (-1 : ℤ) ^ #t ≠ 0 := by
    rw [hsum, sub_ne_zero]
    exact fun h => hEO (by exact_mod_cast h)
  set U : Finset Color := univ.biUnion L
  let ι : Color → ℤ := fun c => if h : c ∈ U then ((U.equivFin ⟨c, h⟩ : ℕ) : ℤ) else 0
  have hinj : Set.InjOn ι U := by
    intro c hc c' hc' h
    simp only [ι, Finset.mem_coe.1 hc, Finset.mem_coe.1 hc', ↓reduceDIte] at h
    have := U.equivFin.injective (Fin.ext (by exact_mod_cast h))
    exact congrArg Subtype.val this
  have hLU : ∀ v, L v ⊆ U := fun v c hc => Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, hc⟩
  have hout : ∀ v, #{a ∈ A | a.1 = v} = #{w | D v w} := by
    intro v
    refine Finset.card_bij' (fun a _ => a.2) (fun w _ => (v, w)) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [← ha.2]; exact ha.1
    · intro w hw
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      simpa using hw
    · intro a ha
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [← ha.2]
    · intro w _
      rfl
  obtain ⟨x, hx, hxne⟩ := exists_eval_graphPoly_ne_zero A hne (fun v => (L v).image ι)
    (fun v => by
      rw [hout, Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast hLU v))]
      exact hL v)
  have hpick : ∀ v, ∃ c ∈ L v, ι c = x v := fun v => Finset.mem_image.1 (hx v)
  choose f hfL hfx using hpick
  refine ⟨f, hfL, fun u v huv hf => ?_⟩
  have hxe : x u = x v := by rw [← hfx u, ← hfx v, hf]
  rcases hD.2.1 u v huv with h | h
  · exact hxne (u, v) (by simp [A, h]) hxe
  · exact hxne (v, u) (by simp [A, h]) hxe.symm
end AlonTarsi
