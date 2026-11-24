-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:46.996932+00:00
-- url     : https://prove2.me/theorems/e1b959b0-4244-451b-b981-31492e41a630
-- title:
--   Weight Comp Apply
-- statement:
--   Definitions and structural lemmas for Weight Comp Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
theorem single_comp_emb (e : Fin n ↪o Fin r) (a : Fin n) :
    (Pi.single (e a) (1 : ℤ) : Fin r → ℤ) ∘ e = Pi.single a 1 := by
  funext c
  simp only [Function.comp_apply, Pi.single_apply, e.injective.eq_iff]
theorem weight_comp (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (m : Fin N × Fin r →₀ ℕ) :
    Finsupp.weight (fun x => (wv LL j x) ∘ e) m = (Finsupp.weight (wv LL j) m) ∘ e := by
  funext a
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
theorem weight_comp_apply (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (m : Fin N × Fin r →₀ ℕ) (a : Fin n) :
    Finsupp.weight (fun x => (wv LL j x) ∘ e) m a = wt LL j (e a) m := by
  rw [weight_comp, Function.comp_apply, weight_wv]
open Formalism.GM.FrozenVariableComponents in
theorem glAct_whe (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (a b : Fin n) {ν : Fin n → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (fun x => (wv LL j x) ∘ e) ν) :
    glAct p LL j (e a) (e b) x ∈ weightedHomogeneousSubmodule ℚ_[p] (fun x => (wv LL j x) ∘ e) (ν + dl a b) := by
  classical
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdw : Finsupp.weight (fun x => (wv LL j x) ∘ e) d = ν := hx (mem_support_iff.mp hd)
  rw [glAct_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hij : (i : ℕ) < j
  · rw [if_pos hij]
    by_cases hv : LL.vec i
    · rw [if_pos hv]
      have := wh_XD (K := ℚ_[p]) (fun x => (wv LL j x) ∘ e) (i, e b) (i, e a) d (coeff d x)
      have e' : ν + dl a b = Finsupp.weight (fun x => (wv LL j x) ∘ e) d - (wv LL j (i, e b)) ∘ e
          + (wv LL j (i, e a)) ∘ e := by
        rw [hdw]; simp only [wv, hij, hv, if_true, dl, single_comp_emb]; abel
      rw [e']; exact this
    · rw [if_neg hv]
      refine Submodule.neg_mem _ ?_
      have := wh_XD (K := ℚ_[p]) (fun x => (wv LL j x) ∘ e) (i, e a) (i, e b) d (coeff d x)
      have hn : ∀ c : Fin n, (-(Pi.single (e c) (1 : ℤ) : Fin r → ℤ)) ∘ e = -Pi.single c 1 := by
        intro c; rw [← single_comp_emb e c]; rfl
      have e' : ν + dl a b = Finsupp.weight (fun x => (wv LL j x) ∘ e) d - (wv LL j (i, e a)) ∘ e
          + (wv LL j (i, e b)) ∘ e := by
        rw [hdw]; simp only [wv, hij, hv, if_true, if_false, Bool.false_eq_true, dl, hn]; abel
      rw [e']; exact this
  · rw [if_neg hij]; exact Submodule.zero_mem _
noncomputable def GAe (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    GlW ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) n where
  E := fun a b => glAct p LL j (e a) (e b)
  comm := fun a b c d x => by
    have := glAct_comm (p := p) LL j (e a) (e b) (e c) (e d) x
    simpa only [e.injective.eq_iff] using this
  comp := fun μ => weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ
  dec := by
    classical
    intro x
    refine ⟨x.support.image (Finsupp.weight (fun x => (wv LL j x) ∘ e)), fun μ hμ => ?_⟩
    apply weightedHomogeneousComponent_eq_zero'
    intro d hd h
    exact hμ (Finset.mem_image.mpr ⟨d, hd, h⟩)
  sum_comp := by
    classical
    intro x S hS
    ext d
    rw [coeff_sum]
    simp only [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have := congrArg (coeff d) (hS _ h)
      rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
      exact this.symm
  idem := by
    classical
    intro μ ν x
    ext d
    by_cases h : μ = ν
    · subst h; simp only [if_true, coeff_weightedHomogeneousComponent]; split_ifs <;> rfl
    · simp only [if_neg h, coeff_zero, coeff_weightedHomogeneousComponent]
      split_ifs with h1 h2 <;> first | rfl | (exfalso; exact h (h1.symm.trans h2))
  diag := by
    classical
    intro c μ x
    rw [weightedHomogeneousComponent_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [glAct_diag_monomial, ← weight_comp_apply, (Finset.mem_filter.mp hd).2]
  shift := by
    classical
    intro a b μ x
    have hx : x = ∑ ν ∈ x.support.image (Finsupp.weight (fun x => (wv LL j x) ∘ e)),
        weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) ν x := by
      ext d
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hne
        exact h (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hne, rfl⟩)
    conv_lhs => rw [hx]
    rw [map_sum, map_sum]
    have e' : ∀ ν, weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ
        (glAct p LL j (e a) (e b) (weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) ν x)) =
        if ν = μ - dl a b then
          glAct p LL j (e a) (e b) (weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) ν x) else 0 := by
      intro ν
      rw [weightedHomogeneousComponent_of_mem (glAct_whe LL j e a b (weightedHomogeneousComponent_mem _ x ν))]
      congr 1
      apply propext; constructor <;> intro h <;> subst h <;> simp
    simp only [e', Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [weightedHomogeneousComponent_eq_zero', map_zero]
      intro d hd h'
      exact h (Finset.mem_image.mpr ⟨d, hd, h'⟩)
noncomputable def enumC (Cs : Finset (Fin r)) : Fin Cs.card ↪o Fin r := Cs.orderEmbOfFin rfl
end Formalism.InvariantFactorPaths.PW


