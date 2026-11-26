-- Prove2me | solution 1 for AlonTarsi.exists_eval_graphPoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:30.381421+00:00
-- url     : https://prove2.me/submissions/99ffabd0-1aeb-48fd-8a1a-5c6f1c567bc2

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Theorems.Thm_AlonTarsi_outExp_apply
public import Theorems.Thm_AlonTarsi_degree_outExp
public import Theorems.Thm_AlonTarsi_totalDegree_graphPoly
public import Theorems.Thm_AlonTarsi_eval_graphPoly
public import Theorems.Thm_AlonTarsi_coeff_outExp_graphPoly

set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}
namespace AlonTarsi
theorem _root_.solution [DecidableEq V] [Fintype V] (A : Finset (V × V))
    (hA : ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}),
      (-1 : ℤ) ^ #t ≠ 0)
    (S : V → Finset ℤ) (hS : ∀ v, #{a ∈ A | a.1 = v} < #(S v)) :
    ∃ x : V → ℤ, (∀ v, x v ∈ S v) ∧ ∀ a ∈ A, x a.1 ≠ x a.2 := by
  have hc : (graphPoly A).coeff (outExp A) ≠ 0 := by rwa [coeff_outExp_graphPoly]
  have hdeg : (graphPoly A).totalDegree = (outExp A).degree := by
    refine le_antisymm ((totalDegree_graphPoly A).trans (degree_outExp A).ge) ?_
    have := le_totalDegree (mem_support_iff.2 hc)
    rw [Finsupp.degree_apply]
    exact this
  obtain ⟨x, hx, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero (graphPoly A)
    (outExp A) hc hdeg S (fun v => by rw [outExp_apply]; exact hS v)
  refine ⟨x, hx, fun a ha h => hne ?_⟩
  rw [eval_graphPoly]
  exact Finset.prod_eq_zero ha (by rw [h, sub_self])
end AlonTarsi
