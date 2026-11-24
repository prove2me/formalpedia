-- Prove2me | Definitions.Def_HLambdaG_Main_Supplement_LittleLaw
-- name    : HLambdaG_Main_Supplement_LittleLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:58:18.959451+00:00
-- url     : https://prove2.me/theorems/0077efac-425f-42d9-a2f3-0cf5bc8c94c8
-- title:
--   §1.2, pp. 636, 640 — the L = λW sample path: T_n, D_n, W_n, F_k of (7), queue length Q(t)
-- statement:
--   **The $L=\lambda W$ framework (§1.2).** Customer $n\ge1$ arrives at epoch $T_n$ and departs at epoch $D_n$, with
--   $$
--   T_n\le D_n,\qquad 0=T_0\le T_n\le T_{n+1}<\infty,\qquad T_n\to\infty .
--   $$
--   Here $T_0=0$ is not the arrival of a 0th customer. The waiting time (time in system) of customer $n$ is $W_n=D_n-T_n$. The setting becomes a special case of §1.1 with
--   $$
--   F_k(t)=\int_0^t 1_{[T_k,D_k]}(s)\,ds=\bigl(\min(t,D_k)-T_k\bigr)^+,\qquad t\ge0. \tag{7}
--   $$
--   This is the time customer $k$ has spent in the system by time $t$. Then $G(n)=n^{-1}\sum_{k=1}^nW_k$ and $H(t)=t^{-1}\sum_{k\ge1}F_k(t)$ is the time-average number in system. The **queue length** is
--   $$
--   Q(t)=\sum_{k=1}^{\infty}1_{[T_k,D_k]}(t)=\#\{k\ge1:\ T_k\le t\le D_k\}.
--   $$
--
--   These objects state Theorem 5, the converse ($\lambda$ and $L$ give $W$) of the sample-path $L=\lambda W$.
--
--   **Formalization Note** $F_k$ is written in the closed form $\max\{0,\min(t,D_k)-T_k\}$. Because $T_k\ge0$, this equals the integral (7). The instance of the §1.1 setting proves its fields: $F_k\ge0$, $F_k$ nondecreasing, $F_k\le W_k$, and only finitely many $F_k(t)\ne0$, since $F_k(t)=0$ once $T_k\ge t$. $F_0=0$ and $D_0$ is an unused dummy. $Q(t)$ is the cardinality of a finite set, finite because $T_k\to\infty$.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 636, §1.2 display (7); p. 640, §4.1 (definition of Q(t)); https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- The `L = λW` sample path of §1.2 (p. 636): arrival epochs `T n` and departure epochs
`D n` of customer `n ≥ 1`, with `0 = T₀ ≤ T_n ≤ T_{n+1} < ∞`, `T_n → ∞` and `T_n ≤ D_n`.
`D 0` is a dummy value (there is no 0th customer). -/
structure LWSetting where
  T : ℕ → ℝ≥0
  D : ℕ → ℝ≥0
  T_zero : T 0 = 0
  T_mono : Monotone T
  T_tendsto : Tendsto T atTop atTop
  T_le_D : ∀ n, 1 ≤ n → T n ≤ D n

/-- The waiting time (time in system) `W_n = D_n − T_n` of customer `n ≥ 1`. -/
def LWSetting.W (L : LWSetting) (n : ℕ) : ℝ := (L.D n : ℝ) - L.T n

/-- (7): `F_k(t) = ∫₀ᵗ 1_{[T_k, D_k]}(s) ds`, the time customer `k` has spent in the system
by time `t`; in closed form `(min(t, D_k) − T_k)⁺`. `F_0 = 0`. -/
noncomputable def LWSetting.F (L : LWSetting) (k : ℕ) (t : ℝ≥0) : ℝ :=
  if k = 0 then 0 else max 0 (min (t : ℝ) (L.D k) - L.T k)

lemma LWSetting.F_nonneg (L : LWSetting) (k : ℕ) (t : ℝ≥0) : 0 ≤ L.F k t := by
  unfold LWSetting.F; split_ifs <;> simp

lemma LWSetting.F_eq_zero_of_le (L : LWSetting) (k : ℕ) (t : ℝ≥0) (h : t ≤ L.T k) :
    L.F k t = 0 := by
  unfold LWSetting.F
  split_ifs
  · rfl
  · have : min (t : ℝ) (L.D k) ≤ L.T k := le_trans (min_le_left _ _) (by exact_mod_cast h)
    simp [this]

/-- The §1.2 sample path as an instance of the §1.1 setting, with `F_k` of (7). -/
noncomputable def LWSetting.toDiscrete (L : LWSetting) : DiscreteSetting where
  F := L.F
  T := L.T
  F_zero := fun t => by simp [LWSetting.F]
  F_nonneg := L.F_nonneg
  F_mono := by
    intro k t t' h
    unfold LWSetting.F
    split_ifs
    · exact le_rfl
    · exact max_le_max le_rfl (sub_le_sub_right (min_le_min_right _ (by exact_mod_cast h)) _)
  F_bdd := by
    intro k
    refine ⟨max 0 ((L.D k : ℝ) - L.T k), ?_⟩
    rintro _ ⟨t, rfl⟩
    unfold LWSetting.F
    split_ifs
    · exact le_max_left _ _
    · exact max_le_max le_rfl (sub_le_sub_right (min_le_right _ _) _)
  F_summable := by
    intro t
    obtain ⟨N, hN⟩ := (L.T_tendsto.eventually_ge_atTop t).exists_forall_of_atTop
    refine summable_of_ne_finset_zero (s := Finset.range N) ?_
    intro k hk
    exact L.F_eq_zero_of_le k t (hN k (by simpa using hk))
  T_zero := L.T_zero
  T_mono := L.T_mono
  T_tendsto := L.T_tendsto

/-- The queue length `Q(t) = Σ_{k ≥ 1} 1_{[T_k, D_k]}(t)` (p. 641), the number of customers
`k ≥ 1` with `T_k ≤ t ≤ D_k`; the set is finite because `T_k → ∞`. -/
noncomputable def LWSetting.Q (L : LWSetting) (t : ℝ≥0) : ℕ :=
  Set.ncard {k : ℕ | 1 ≤ k ∧ L.T k ≤ t ∧ t ≤ L.D k}

end HLambdaG.Main.Supplement


