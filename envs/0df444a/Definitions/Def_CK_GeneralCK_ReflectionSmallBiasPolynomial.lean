-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPolynomial
-- name    : CK_GeneralCK_ReflectionSmallBiasPolynomial
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:43:47.838908+00:00
-- url     : https://prove2.me/theorems/e6e5bfc9-43cd-4d79-85fd-b7a0d4973b63
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasPolynomial` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasPolynomial` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasPolynomial` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasPolynomial (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasPolynomial.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasComplexDomain
import Mathlib.Analysis.Asymptotics.Lemmas

-- ===== source module GeneralCK.ReflectionSmallBiasPolynomial =====
section

/-!
# Truncated sparse Laurent polynomials for the reflection Taylor certificate

The first two variables have positive Taylor degree. The nonzero entropy
constant is a parameter and may occur with an integer exponent.
-/

namespace GeneralCK.Reflection.SmallBiasPolynomial

open Filter Asymptotics
open scoped Topology

structure Term where
  a : ℕ
  b : ℕ
  k : ℤ
  c : ℚ
  deriving DecidableEq, Repr

noncomputable def evalTerm (k : ℂ) (t : Term) (p : ℂ × ℂ) : ℂ :=
  (t.c : ℂ) * k ^ t.k * p.1 ^ t.a * p.2 ^ t.b

noncomputable def eval (k : ℂ) : List Term → ℂ × ℂ → ℂ
  | [], _ => 0
  | t :: ts, p => evalTerm k t p + eval k ts p

def insertTerm (p : Term) : List Term → List Term
  | [] => if p.c = 0 then [] else [p]
  | q :: qs =>
    if p.c = 0 then q :: qs
    else if p.a = q.a ∧ p.b = q.b ∧ p.k = q.k then
      if p.c + q.c = 0 then qs
      else {q with c := p.c + q.c} :: qs
    else q :: insertTerm p qs

def normalize : List Term → List Term
  | [] => []
  | p :: ps => insertTerm p (normalize ps)

def add (p q : List Term) : List Term := normalize (p ++ q)

def scale (c : ℚ) (p : List Term) : List Term := p.map fun t => {t with c := c * t.c}

def mulTerm (p q : Term) : Term := ⟨p.a + q.a, p.b + q.b, p.k + q.k, p.c * q.c⟩

def rawMul : List Term → List Term → List Term
  | [], _ => []
  | p :: ps, q => q.map (mulTerm p) ++ rawMul ps q

def mul (p q : List Term) : List Term := normalize (rawMul p q)

def truncate (n : ℕ) (p : List Term) : List Term := p.filter fun t => t.a + t.b < n

/- Truncate before normalization so discarded terms never undergo rational
arithmetic or coefficient collection during kernel replay. -/
def mulTrunc (n : ℕ) (p q : List Term) : List Term :=
  normalize (truncate n (rawMul p q))

theorem eval_append (k : ℂ) (p q : List Term) (z : ℂ × ℂ) :
    eval k (p ++ q) z = eval k p z + eval k q z := by
  induction p with
  | nil => simp [eval]
  | cons t ts ih => simp [eval, ih, add_assoc]

theorem eval_insertTerm (k : ℂ) (p : Term) (q : List Term) (z : ℂ × ℂ) :
    eval k (insertTerm p q) z = evalTerm k p z + eval k q z := by
  induction q with
  | nil =>
    by_cases hz : p.c = 0
    · simp [insertTerm, hz, eval, evalTerm]
    · simp [insertTerm, hz, eval]
  | cons x xs ih =>
    by_cases hz : p.c = 0
    · simp [insertTerm, hz, eval, evalTerm]
    · by_cases h : p.a = x.a ∧ p.b = x.b ∧ p.k = x.k
      · rcases h with ⟨ha, hb, hk⟩
        by_cases hs : p.c + x.c = 0
        · have hc : (p.c : ℂ) + (x.c : ℂ) = 0 := by exact_mod_cast hs
          simp [insertTerm, hz, ha, hb, hk, hs, eval, evalTerm]
          have hc' : (p.c : ℂ) = -(x.c : ℂ) := eq_neg_of_add_eq_zero_left hc
          rw [hc']
          ring
        · simp [insertTerm, hz, ha, hb, hk, hs, eval, evalTerm]
          ring
      · simp [insertTerm, hz, h, eval, ih, add_left_comm]

theorem eval_normalize (k : ℂ) (p : List Term) (z : ℂ × ℂ) :
    eval k (normalize p) z = eval k p z := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp [normalize, eval_insertTerm, eval, ih]

theorem eval_add (k : ℂ) (p q : List Term) (z : ℂ × ℂ) :
    eval k (add p q) z = eval k p z + eval k q z := by
  simp [add, eval_normalize, eval_append]

theorem eval_scale (k : ℂ) (c : ℚ) (p : List Term) (z : ℂ × ℂ) :
    eval k (scale c p) z = (c : ℂ) * eval k p z := by
  induction p with
  | nil => simp [scale, eval]
  | cons t ts ih =>
    simp [scale, eval, evalTerm] at *
    rw [ih]
    ring

theorem eval_mulTerm {k : ℂ} (hk : k ≠ 0) (p q : Term) (z : ℂ × ℂ) :
    evalTerm k (mulTerm p q) z = evalTerm k p z * evalTerm k q z := by
  simp only [evalTerm, mulTerm, Rat.cast_mul, pow_add, zpow_add₀ hk]
  ring

theorem eval_map_mulTerm {k : ℂ} (hk : k ≠ 0) (p : Term) (q : List Term) (z : ℂ × ℂ) :
    eval k (q.map (mulTerm p)) z = evalTerm k p z * eval k q z := by
  induction q with
  | nil => simp [eval]
  | cons t ts ih => simp [eval, eval_mulTerm hk, ih, mul_add]

theorem eval_rawMul {k : ℂ} (hk : k ≠ 0) (p q : List Term) (z : ℂ × ℂ) :
    eval k (rawMul p q) z = eval k p z * eval k q z := by
  induction p with
  | nil => simp [rawMul, eval]
  | cons t ts ih => simp [rawMul, eval_append, eval_map_mulTerm hk, eval, ih, add_mul]

theorem eval_mul {k : ℂ} (hk : k ≠ 0) (p q : List Term) (z : ℂ × ℂ) :
    eval k (mul p q) z = eval k p z * eval k q z := by
  rw [mul, eval_normalize, eval_rawMul hk]

theorem analyticAt_evalTerm (k : ℂ) (t : Term) (p : ℂ × ℂ) :
    AnalyticAt ℂ (evalTerm k t) p :=
  ((analyticAt_const.mul analyticAt_const).mul (analyticAt_fst.pow t.a)).mul (analyticAt_snd.pow t.b)

theorem analyticAt_eval (k : ℂ) (ts : List Term) (p : ℂ × ℂ) :
    AnalyticAt ℂ (eval k ts) p := by
  induction ts with
  | nil => exact analyticAt_const
  | cons t ts ih => exact (analyticAt_evalTerm k t p).add ih

theorem norm_evalTerm_le (k : ℂ) (t : Term) (p : ℂ × ℂ) :
    ‖evalTerm k t p‖ ≤ ‖(t.c : ℂ) * k ^ t.k‖ * ‖p‖ ^ (t.a + t.b) := by
  unfold evalTerm
  rw [norm_mul, norm_mul, norm_pow, norm_pow, pow_add]
  have ha := norm_fst_le p
  have hb := norm_snd_le p
  calc
    _ ≤ ‖(t.c : ℂ) * k ^ t.k‖ * ‖p‖ ^ t.a * ‖p‖ ^ t.b := by gcongr
    _ = _ := by ring

theorem evalTerm_isBigO {n : ℕ} (k : ℂ) (t : Term) (hn : n ≤ t.a + t.b) :
    evalTerm k t =O[𝓝 (0 : ℂ × ℂ)] (fun p => ‖p‖ ^ n) := by
  refine isBigO_iff.mpr ⟨‖(t.c : ℂ) * k ^ t.k‖, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ × ℂ) (by norm_num : (0 : ℝ) < 1)] with p hp
  have hp1 : ‖p‖ ≤ 1 := (show ‖p‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using hp).le
  have hn' := pow_le_pow_of_le_one (norm_nonneg p) hp1 hn
  have hh := (norm_evalTerm_le k t p).trans (mul_le_mul_of_nonneg_left hn' (norm_nonneg _))
  simpa only [norm_pow, norm_norm] using hh

/-- Truncation deletes only terms of order at least n. -/
theorem eval_sub_truncate_isBigO (k : ℂ) (ts : List Term) (n : ℕ) :
    (fun p => eval k ts p - eval k (truncate n ts) p)
      =O[𝓝 (0 : ℂ × ℂ)] (fun p => ‖p‖ ^ n) := by
  induction ts with
  | nil => simpa [eval, truncate] using (isBigO_zero (fun p : ℂ × ℂ => ‖p‖ ^ n) (𝓝 0) :
      (fun _ : ℂ × ℂ => (0 : ℂ)) =O[𝓝 0] (fun p => ‖p‖ ^ n))
  | cons t ts ih =>
    by_cases ht : t.a + t.b < n
    · simpa only [truncate, List.filter_cons, decide_eq_true ht, if_true, eval,
        add_sub_add_left_eq_sub] using ih
    · have hh := (evalTerm_isBigO k t (Nat.le_of_not_gt ht)).add ih
      simpa [truncate, ht, eval, add_sub_assoc] using hh

end GeneralCK.Reflection.SmallBiasPolynomial

end


