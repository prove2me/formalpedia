-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:44.380258+00:00
-- url     : https://prove2.me/theorems/2ac12983-c3c2-4599-8dd7-83a2d42ccd56
-- title:
--   Weight Space Dimension Monotone
-- statement:
--   Definitions and structural lemmas for Weight Space Dimension Monotone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_eq_top
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_top_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_top_comm
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
namespace Formalism.GM.DimensionMonotonicity
open Finset
def dl {r : ℕ} (a b : Fin r) : Fin r → ℤ := Pi.single a 1 - Pi.single b 1
lemma dl_apply {r : ℕ} (a b c : Fin r) :
    dl a b c = (if c = a then 1 else 0) - (if c = b then 1 else 0) := by
  unfold dl
  rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]
structure GlW (K : Type) (V : Type) [Field K] [AddCommGroup V] [Module K V] (r : ℕ) where
  E : Fin r → Fin r → V →ₗ[K] V
  comm : ∀ a b c d x, E a b (E c d x) - E c d (E a b x) =
    (if b = c then E a d x else 0) - (if d = a then E c b x else 0)
  comp : (Fin r → ℤ) → V →ₗ[K] V
  dec : ∀ x, ∃ S : Finset (Fin r → ℤ), ∀ μ ∉ S, comp μ x = 0
  sum_comp : ∀ x (S : Finset (Fin r → ℤ)), (∀ μ ∉ S, comp μ x = 0) → ∑ μ ∈ S, comp μ x = x
  idem : ∀ μ ν x, comp μ (comp ν x) = if μ = ν then comp ν x else 0
  diag : ∀ c μ x, E c c (comp μ x) = ((μ c : ℤ) : K) • comp μ x
  shift : ∀ a b μ x, comp μ (E a b x) = E a b (comp (μ - dl a b) x)
namespace GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
def Stable (U : Submodule K V) : Prop := ∀ a b, ∀ x ∈ U, G.E a b x ∈ U
def Graded (U : Submodule K V) : Prop := ∀ μ, ∀ x ∈ U, G.comp μ x ∈ U
def Raising (U : Submodule K V) : Prop := ∀ a b, a < b → ∀ x ∈ U, G.E a b x ∈ U
def FinW (U : Submodule K V) : Prop := ∃ S : Finset (Fin r → ℤ), ∀ x ∈ U, ∀ μ ∉ S, G.comp μ x = 0
def gS (s : Set V) : Submodule K V := sInf {U | s ⊆ U ∧ G.Stable U}
def IsWt (μ : Fin r → ℤ) (x : V) : Prop := G.comp μ x = x
def IsHW (μ : Fin r → ℤ) (x : V) : Prop := G.IsWt μ x ∧ ∀ a b, a < b → G.E a b x = 0
def Cas : V →ₗ[K] V := ∑ a, ∑ b, G.E a b ∘ₗ G.E b a
def casI (μ : Fin r → ℤ) : ℤ :=
  ∑ a, ∑ b, (if a = b then μ a * μ a else if a < b then μ a - μ b else 0)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
def psum {r : ℕ} (μ : Fin r → ℤ) (k : ℕ) : ℤ := ∑ c : Fin r, if (c : ℕ) < k then μ c else 0
def Dle {r : ℕ} (μ ν : Fin r → ℤ) : Prop := (∀ k, psum μ k ≤ psum ν k) ∧ ∑ c, μ c = ∑ c, ν c
def DomW {r : ℕ} (μ : Fin r → ℤ) : Prop := ∀ a b : Fin r, a < b → μ b ≤ μ a
variable {r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
def Low (la : Fin r → ℤ) : Submodule K V where
  carrier := {x | ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν x = 0}
  add_mem' := by
    intro x y hx hy ν hν
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx ν hν, hy ν hν, add_zero]
  zero_mem' := by intro ν _; simp
  smul_mem' := by
    intro c x hx ν hν
    simp only [Set.mem_ofPred_eq] at hx
    rw [map_smul, hx ν hν, smul_zero]
def Lw (v : V) : Submodule K V := sInf {U | v ∈ U ∧ ∀ a b, b < a → ∀ x ∈ U, G.E a b x ∈ U}
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
def ht (μ : Fin r → ℤ) : ℤ := ∑ c : Fin r, (-(c : ℤ)) * μ c
def cprod : List ℤ → V →ₗ[K] V
  | [] => LinearMap.id
  | c :: cs => (G.Cas - ((c : ℤ) : K) • LinearMap.id) ∘ₗ cprod cs
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section Ops
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ]
theorem pderiv_comm_lemma (y y' : σ) (F : MvPolynomial σ K) :
    pderiv y (pderiv y' F) = pderiv y' (pderiv y F) := by
  refine MvPolynomial.induction_on' F ?_ ?_
  · intro u a
    rw [pderiv_monomial, pderiv_monomial, pderiv_monomial, pderiv_monomial]
    by_cases h : y = y'
    · subst h
      rfl
    · rw [tsub_right_comm]
      congr 1
      simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), tsub_zero]
      ring
  · intro p q hp hq
    rw [map_add, map_add, hp, hq, map_add, map_add]
theorem XD_comm (x y x' y' : σ) (F : MvPolynomial σ K) :
    X x * pderiv y (X x' * pderiv y' F) - X x' * pderiv y' (X x * pderiv y F) =
      (if y = x' then X x * pderiv y' F else 0) - (if y' = x then X x' * pderiv y F else 0) := by
  rw [Derivation.leibniz, Derivation.leibniz, pderiv_X, pderiv_X, pderiv_comm_lemma y y' F]
  simp only [smul_eq_mul, Pi.single_apply, @eq_comm _ x' y, @eq_comm _ x y']
  split_ifs <;> ring
end Ops
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
open Formalism.GM.FrozenVariableComponents in
theorem top_self_comm (LL : Letters N) (i : Fin N) (a b c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    top p LL i a b (top p LL i c d F) - top p LL i c d (top p LL i a b F) =
      (if b = c then top p LL i a d F else 0) - (if d = a then top p LL i c b F else 0) := by
  simp only [top_apply]
  by_cases hv : LL.vec i
  · simp only [hv, if_true]
    rw [XD_comm]
    simp only [Prod.mk.injEq, true_and]
  · simp only [hv, if_false, Bool.false_eq_true]
    simp only [map_neg, mul_neg, neg_neg, sub_neg_eq_add]
    have := XD_comm (K := ℚ_[p]) (i, b) (i, a) (i, d) (i, c) F
    simp only [Prod.mk.injEq, true_and, @eq_comm _ a d, @eq_comm _ c b] at this
    rw [this]
    split_ifs <;> (try simp) <;> abel
open Formalism.GM.FrozenVariableComponents in
theorem glAct_comm (LL : Letters N) (j : ℕ) (a b c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j a b (glAct p LL j c d F) - glAct p LL j c d (glAct p LL j a b F) =
      (if b = c then glAct p LL j a d F else 0) - (if d = a then glAct p LL j c b F else 0) := by
  classical
  set T : Fin N → Fin r → Fin r → (MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    fun i a b => if (i : ℕ) < j then top p LL i a b else 0 with hT
  have hg : ∀ a b, glAct p LL j a b = ∑ i, T i a b := fun a b => glAct_eq_top p LL j a b
  have key : glAct p LL j a b * glAct p LL j c d - glAct p LL j c d * glAct p LL j a b =
      (if b = c then glAct p LL j a d else 0) - (if d = a then glAct p LL j c b else 0) := by
    rw [hg a b, hg c d, hg a d, hg c b, Finset.sum_mul_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm (f := fun i i' => T i c d * T i' a b), ← Finset.sum_sub_distrib]
    have e1 : ∀ i, ∑ i', T i a b * T i' c d - ∑ i', T i' c d * T i a b =
        T i a b * T i c d - T i c d * T i a b := by
      intro i
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · intro i' _ hi'
        simp only [hT]
        split_ifs
        · rw [sub_eq_zero]; refine LinearMap.ext fun G => ?_; exact top_comm p LL i i' (Ne.symm hi') a b c d G
        all_goals simp
      · simp
    simp only [e1]
    have e2 : ∀ i, T i a b * T i c d - T i c d * T i a b =
        (if b = c then T i a d else 0) - (if d = a then T i c b else 0) := by
      intro i
      simp only [hT]
      by_cases hi : (i : ℕ) < j
      · simp only [hi, if_true]
        refine LinearMap.ext fun G => ?_
        simp only [LinearMap.sub_apply, Module.End.mul_apply, top_self_comm]
        split_ifs <;> simp
      · simp [hi]
    simp only [e2, Finset.sum_sub_distrib]
    split_ifs <;> simp
  have := congrArg (fun T => T F) key
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, apply_ite (fun T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] _ => T F),
    LinearMap.zero_apply] using this
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section W
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ] {M : Type} [AddCommGroup M]
theorem XD_monomial (x y : σ) (d : σ →₀ ℕ) (a : K) :
    X y * pderiv x (monomial d a) = monomial (d - Finsupp.single x 1 + Finsupp.single y 1) (a * d x) := by
  rw [pderiv_monomial, show (X y : MvPolynomial σ K) = monomial (Finsupp.single y 1) 1 from rfl, monomial_mul,
    one_mul, add_comm (Finsupp.single y 1)]
theorem wh_XD (w : σ → M) (x y : σ) (d : σ →₀ ℕ) (a : K) :
    X y * pderiv x (monomial d a) ∈ weightedHomogeneousSubmodule K w (Finsupp.weight w d - w x + w y) := by
  rw [XD_monomial, mem_weightedHomogeneousSubmodule]
  by_cases h : d x = 0
  · rw [h, Nat.cast_zero, mul_zero, monomial_zero]
    intro m hm
    rw [coeff_zero] at hm
    exact absurd rfl hm
  · apply isWeightedHomogeneous_monomial
    have e : d - Finsupp.single x 1 + Finsupp.single x 1 = d := by
      ext z
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hz
      · subst hz
        omega
      · omega
    have hs : ∀ z : σ, Finsupp.weight w (Finsupp.single z 1) = w z := fun z => by
      rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp), one_smul]
    have h2 : Finsupp.weight w (d - Finsupp.single x 1) = Finsupp.weight w d - w x := by
      conv_rhs => rw [← e]
      rw [map_add, hs, add_sub_cancel_right]
    rw [map_add, h2, hs]
theorem XD_diag (x : σ) (d : σ →₀ ℕ) (a : K) :
    X x * pderiv x (monomial d a) = (d x : K) • monomial d a := by
  rw [pderiv_monomial, show (X x : MvPolynomial σ K) = monomial (Finsupp.single x 1) 1 from rfl, monomial_mul,
    one_mul, smul_monomial, smul_eq_mul]
  by_cases h : d x = 0
  · simp [h]
  · have e : Finsupp.single x 1 + (d - Finsupp.single x 1) = d := by
      ext z
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hz
      · subst hz
        omega
      · omega
    rw [e, mul_comm]
end W
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def wv (LL : Letters N) (j : ℕ) : Fin N × Fin r → (Fin r → ℤ) := fun x =>
  if (x.1 : ℕ) < j then (if LL.vec x.1 then Pi.single x.2 1 else -Pi.single x.2 1) else 0
theorem weight_wv (LL : Letters N) (j : ℕ) (m : Fin N × Fin r →₀ ℕ) (c : Fin r) :
    Finsupp.weight (wv LL j) m c = wt LL j c m := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_prod_type]
  unfold wt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < j <;> by_cases h2 : LL.vec i <;> simp [wv, h1, h2, Pi.single_apply]
open Formalism.GM.FrozenVariableComponents in
theorem glAct_diag_monomial (LL : Letters N) (j : ℕ) (c : Fin r) (d : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    glAct p LL j c c (monomial d a) = ((wt LL j c d : ℤ) : ℚ_[p]) • monomial d a := by
  unfold glAct wt
  rw [LinearMap.sum_apply, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2 <;> simp [XD_diag] <;> rw [← pderiv_monomial, XD_diag]
open Formalism.GM.FrozenVariableComponents in
theorem glAct_wh (LL : Letters N) (j : ℕ) (a b : Fin r) {ν : Fin r → ℤ} {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL j) ν) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL j) (ν + dl a b) := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight (wv LL j) d = ν := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have h3 := wh_XD (K := ℚ_[p]) (wv LL j) (i, b) (i, a) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL j) d - wv LL j (i, b) + wv LL j (i, a) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [e]
    exact h3
  · have h3 := wh_XD (K := ℚ_[p]) (wv LL j) (i, a) (i, b) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL j) d - wv LL j (i, a) + wv LL j (i, b) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _
noncomputable def GA (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) :
    GlW ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) r where
  E := glAct p LL j
  comm := fun a b c d x => glAct_comm LL j a b c d x
  comp := fun μ => weightedHomogeneousComponent (wv LL j) μ
  dec := by
    classical
    intro x
    refine ⟨x.support.image (Finsupp.weight (wv LL j)), fun μ hμ => ?_⟩
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
    rw [glAct_diag_monomial, ← weight_wv, (Finset.mem_filter.mp hd).2]
  shift := by
    classical
    intro a b μ x
    have hx : x = ∑ ν ∈ x.support.image (Finsupp.weight (wv LL j)), weightedHomogeneousComponent (wv LL j) ν x := by
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
    have e : ∀ ν, weightedHomogeneousComponent (wv LL j) μ (glAct p LL j a b (weightedHomogeneousComponent (wv LL j) ν x)) =
        if ν = μ - dl a b then glAct p LL j a b (weightedHomogeneousComponent (wv LL j) ν x) else 0 := by
      intro ν
      rw [weightedHomogeneousComponent_of_mem (glAct_wh LL j a b (weightedHomogeneousComponent_mem _ x ν))]
      congr 1
      apply propext; constructor <;> intro h <;> subst h <;> simp
    simp only [e, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [weightedHomogeneousComponent_eq_zero', map_zero]
      intro d hd h'
      exact h (Finset.mem_image.mpr ⟨d, hd, h'⟩)
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def wL (N r : ℕ) : Fin N × Fin r → (Fin N → ℤ) := fun x => Pi.single x.1 1
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def midAct (p : ℕ) [Fact p.Prime] (LL : Letters N) (J j0 : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ∑ i : Fin N, if J ≤ (i : ℕ) ∧ (i : ℕ) < j0 then Formalism.GM.FrozenVariableComponents.top p LL i c d else 0
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def wOut (N r : ℕ) (i0 : Fin N) : Fin N × Fin r → ℤ := fun v => if v.1 = i0 then 0 else 1
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def ιF (N K : ℕ) [NeZero N] : Fin (K + 1) → Fin N :=
  fun a => if h : (a : ℕ) < N then ⟨a, h⟩ else ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
lemma hK_of_adm (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) : T.pos i + 1 + 1 ≤ N := by
  obtain ⟨h, -⟩ := hadm.2.1 i; omega
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Comparison₂
section Tie2
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
def Lz (LL : Letters N) (j0 : ℕ) : Letters N where
  vec := LL.vec
  deg := fun a => if (a : ℕ) < j0 then LL.deg a else 0
end Tie2
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM
end Formalism.GM


