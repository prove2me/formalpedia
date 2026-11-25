-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:54.415845+00:00
-- url     : https://prove2.me/theorems/0f634109-02ba-43f2-83df-bba58600e681
-- title:
--   Constant Coeff Rho One Canon Monomial
-- statement:
--   Definitions and structural lemmas for Constant Coeff Rho One Canon Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/ConstantCoeffRhoOneCanonMonomial.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_constantCoeff_rho_one_word_monomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_constantCoeff_rho_one_word_of_lt
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_toFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_length_expand
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_span_canon_eq_top
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_toFinsupp_expand
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
noncomputable def transposeExp (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.mapDomain Prod.swap m
theorem transposeExp_injective : Function.Injective (transposeExp (n := n)) :=
  Finsupp.mapDomain_injective Prod.swap_injective
theorem toFinsupp_map_swap (w : List (Fin n × Fin n)) :
    Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) =
      transposeExp (Multiset.toFinsupp (w : Multiset (Fin n × Fin n))) := by
  induction w with
  | nil => simp [transposeExp]
  | cons a w ih =>
    rw [List.map_cons,
      show ((Prod.swap a :: w.map Prod.swap : List _) : Multiset _) =
        {Prod.swap a} + ((w.map Prod.swap : List _) : Multiset _) by simp,
      show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset _) by simp,
      Multiset.toFinsupp_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      Multiset.toFinsupp_singleton, ih, transposeExp, transposeExp, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single]
theorem degree_transposeExp (m : Fin n × Fin n →₀ ℕ) :
    (transposeExp m).degree = m.degree := by
  have h1 := degree_toFinsupp ((expand m).map Prod.swap)
  rw [toFinsupp_map_swap, toFinsupp_expand, List.length_map, length_expand] at h1
  exact h1
theorem constantCoeff_rho_one_canon_monomial (m s : Fin n × Fin n →₀ ℕ) (h : m.degree = s.degree) :
    constantCoeff (rho 1 (canon m) (monomial s 1)) ≠ 0 ↔ transposeExp m = s := by
  rw [canon, constantCoeff_rho_one_word_monomial _ _ (by rw [length_expand, h]),
    toFinsupp_map_swap, toFinsupp_expand]
theorem coeff_eq_zero_of_rho_one (s : Finset (Fin n × Fin n →₀ ℕ)) (c : (Fin n × Fin n →₀ ℕ) → ℂ)
    (h : rho 1 (∑ m ∈ s, c m • canon m) = 0) : ∀ m ∈ s, c m = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨m, hms, hm⟩ := hne
  set s' := s.filter fun m => c m ≠ 0
  have hne' : s'.Nonempty := ⟨m, Finset.mem_filter.2 ⟨hms, hm⟩⟩
  obtain ⟨m₀, hm₀, hmax⟩ := s'.exists_max_image Finsupp.degree hne'
  rw [Finset.mem_filter] at hm₀
  set N := transposeExp m₀
  have hN : N.degree = m₀.degree := degree_transposeExp m₀
  have hhom : (monomial N (1 : ℂ)).IsHomogeneous m₀.degree := by
    rw [← hN]; exact isHomogeneous_monomial _ rfl
  have key : ∀ m ∈ s, m ≠ m₀ → c m * constantCoeff (rho 1 (canon m) (monomial N 1)) = 0 := by
    intro m hm hne
    by_cases hc : c m = 0
    · rw [hc, zero_mul]
    have hdeg : m.degree ≤ m₀.degree := hmax m (Finset.mem_filter.2 ⟨hm, hc⟩)
    rcases hdeg.lt_or_eq with hlt | heq
    · rw [canon, constantCoeff_rho_one_word_of_lt _ _ _ hhom (by rw [length_expand]; exact hlt),
        mul_zero]
    · have : ¬ constantCoeff (rho 1 (canon m) (monomial N 1)) ≠ 0 := by
        rw [constantCoeff_rho_one_canon_monomial _ _ (by rw [heq, hN])]
        exact fun h' => hne (transposeExp_injective h')
      rw [not_not.1 this, mul_zero]
  have hsum := congrArg (fun T : Module.End ℂ (Poly n) => constantCoeff (T (monomial N 1))) h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C] at hsum
  rw [Finset.sum_eq_single m₀ (fun m hm hne => key m hm hne) (fun h' => absurd hm₀.1 h')] at hsum
  have h0 : constantCoeff (rho 1 (canon m₀) (monomial N 1)) ≠ 0 :=
    (constantCoeff_rho_one_canon_monomial _ _ hN.symm).2 rfl
  exact hm₀.2 ((mul_eq_zero.1 hsum).resolve_right h0)
theorem linearIndependent_canon : LinearIndependent ℂ (canon (n := n)) := by
  rw [linearIndependent_iff']
  intro s c hs
  exact coeff_eq_zero_of_rho_one s c (by rw [hs, map_zero])
noncomputable def pbw : Module.Basis (Fin n × Fin n →₀ ℕ) ℂ (U n) :=
  Module.Basis.mk linearIndependent_canon span_canon_eq_top.ge
end GroundTheory.Automorphic.HarishChandra


