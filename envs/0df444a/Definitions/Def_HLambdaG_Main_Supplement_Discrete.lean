-- Prove2me | Definitions.Def_HLambdaG_Main_Supplement_Discrete
-- name    : HLambdaG_Main_Supplement_Discrete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:57:17.275145+00:00
-- url     : https://prove2.me/theorems/2cd91c81-7f2c-41ca-af2a-4abbac75b2a6
-- title:
--   §1.1, §3, pp. 636, 640 — one discrete variable: F_k, T_k, embedding (5), N(t) of (6), conditions (17) and (18), U_n and T₂ of (19)
-- statement:
--   **The setting with one discrete variable (§1.1).** Customers are numbered $k=1,2,\dots$. Customer $k$ carries a nonnegative, nondecreasing, bounded function $F_k$ on $[0,\infty)$, with finite limit $F_k(\infty)=\lim_{t\to\infty}F_k(t)$, and $\sum_{k\ge1}F_k(t)<\infty$ for every $t$. The epochs $T_0=0\le T_1\le T_2\le\cdots<\infty$ satisfy $T_k\to\infty$. The averages of interest are
--   $$
--   G(n)=n^{-1}\sum_{k=1}^{n}F_k(\infty),\qquad H(t)=t^{-1}\sum_{k=1}^{\infty}F_k(t). \tag{4}
--   $$
--   The setting is embedded in the general framework by
--   $$
--   F(s,t)=\sum_{k=1}^{[s]}F_k(t),\qquad T_1(s)=T_{[s]},\qquad s\ge0, \tag{5}
--   $$
--   where $[s]$ is the integer part of $s$. $F$ is a cumulative input and $T_1$ a time change in the sense of §1, so the general marginal averages $G(s)=s^{-1}F(s,\infty)$ and $H(t)=t^{-1}F(\infty,t)$ apply; at $s=n$ they are exactly (4). The counting function is
--   $$
--   N(t)=\max\{k\ge0:\ T_k\le t\},\qquad t\ge0. \tag{6}
--   $$
--
--   **Conditions of §3.** Condition (17) is
--   $$
--   n^{-1}\sum_{k=n+1}^{\infty}F_k(T_n)\to0\qquad(n\to\infty),
--   $$
--   with lower summation index $n+1$. For a nonnegative finite sequence $\{S_k\}$, condition (18) is
--   $$
--   \frac{S_n}{T_n}\to0\quad\text{and}\quad n^{-1}\sum_{k=1}^{n}\bigl[F_k(\infty)-F_k(T_k+S_k)\bigr]\to0\qquad(n\to\infty).
--   $$
--   From such a sequence, (19) forms the running maximum $U_n=\max\{S_k:1\le k\le n\}$ (with $U_0=0$) and the second time change
--   $$
--   T_2(s)=T_{[s]}+U_{[s]},\qquad s\ge0.
--   $$
--
--   These objects state Theorems 2–4 of the paper, which reduce the general conditions (14) and (15) to the sequence conditions (17) and (18).
--
--   **Formalization Note** Indices are natural numbers. $F_0$ is a dummy fixed to $0$, since there is no 0th customer; $T_0=0$ is kept as an epoch. Time and the index $s$ range over $\mathbb R_{\ge0}$, and $[s]$ is `Nat.floor`. $F_k(\infty)$ is the supremum of the bounded nondecreasing $F_k$. The embedding builds the published `HLambdaG.Main.CumulativeInput` (monotonicity and finite marginal limits are proved from the fields), and the step functions $T_1$, $T_2$ are built as the published `HLambdaG.Main.TimeChange`. Right-continuity holds because both are constant on each $[n,n+1)$. $N(t)$ is the natural-number supremum of $\{k: T_k\le t\}$; this set contains $0$ and is finite, so the supremum is the maximum. The printed (17) has lower index $k=n$. The index $n+1$ used here is the sum computed in the proof of Theorem 2; see that item. In (18), $S_n/T_n$ uses Lean's division, which is $0$ when $T_n=0$. Since $T_n\to\infty$, this affects only finitely many $n$ and no limit.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 636, §1.1 displays (4)–(6); p. 640, §3 displays (17)–(19); https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology

/-- The §1.1 setting with one discrete variable (p. 636). Customers are `k = 1, 2, …`;
`F k` is the input of customer `k`, and index `0` is a dummy with `F 0 = 0` (there is no
0th customer). `T k` are the epochs, with `T 0 = 0`. The finiteness of `F_k(∞)` and of
`Σ_k F_k(t)` are the general framework's finite limits `F(s, ∞)` and `F(∞, t)` (p. 635). -/
structure DiscreteSetting where
  F : ℕ → ℝ≥0 → ℝ
  T : ℕ → ℝ≥0
  F_zero : ∀ t, F 0 t = 0
  F_nonneg : ∀ k t, 0 ≤ F k t
  F_mono : ∀ k, Monotone (F k)
  F_bdd : ∀ k, BddAbove (Set.range (F k))
  F_summable : ∀ t, Summable (fun k => F k t)
  T_zero : T 0 = 0
  T_mono : Monotone T
  T_tendsto : Tendsto T atTop atTop

/-- The step time change `s ↦ T_{[s]}` of a nondecreasing sequence tending to infinity;
it is constant on each `[n, n + 1)`, hence right-continuous. -/
noncomputable def stepTC (T : ℕ → ℝ≥0) (hmono : Monotone T) (htend : Tendsto T atTop atTop) :
    TimeChange where
  T := fun s => T ⌊s⌋₊
  mono := hmono.comp (fun _ _ h => Nat.floor_le_floor h)
  rcont := by
    intro s
    refine (continuousWithinAt_const (b := T ⌊s⌋₊)).congr_of_eventuallyEq ?_ rfl
    have hlt : s < (⌊s⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one s
    filter_upwards [Ico_mem_nhdsGE hlt] with x hx
    have hx' : x ∈ Set.Ico ((⌊s⌋₊ : ℕ) : ℝ≥0) ((⌊s⌋₊ : ℝ≥0) + 1) :=
      ⟨le_trans (Nat.floor_le s.2) hx.1, hx.2⟩
    show T ⌊x⌋₊ = T ⌊s⌋₊
    rw [Nat.floor_eq_on_Ico ⌊s⌋₊ x hx']
  tendsto := htend.comp tendsto_nat_floor_atTop

/-- The time change `T₁(s) = T_{[s]}` of (5). -/
noncomputable def DiscreteSetting.T1 (D : DiscreteSetting) : TimeChange :=
  stepTC D.T D.T_mono D.T_tendsto

/-- `F_k(∞)`, the finite limit of the nondecreasing bounded function `F_k`. -/
noncomputable def DiscreteSetting.Finf (D : DiscreteSetting) (k : ℕ) : ℝ := ⨆ t, D.F k t

/-- The cumulative input (5): `F(s, t) = Σ_{k=1}^{[s]} F_k(t)`. -/
noncomputable def DiscreteSetting.input (D : DiscreteSetting) : CumulativeInput where
  F := fun s t => ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k t
  mono_s := by
    intro t s s' h
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor h)) (fun k _ _ => D.F_nonneg k t)
  mono_t := by
    intro s t t' h
    exact Finset.sum_le_sum (fun k _ => D.F_mono k h)
  bdd_t := by
    intro s
    refine ⟨∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.Finf k, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact Finset.sum_le_sum (fun k _ => le_ciSup (D.F_bdd k) t)
  bdd_s := by
    intro t
    refine ⟨∑' k, D.F k t, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (D.F_summable t).sum_le_tsum _ (fun k _ => D.F_nonneg k t)

/-- The counting function (6): `N(t) = max {k ≥ 0 : T_k ≤ t}`. The set contains `0` and is
finite because `T_k → ∞`, so the supremum is a maximum. -/
noncomputable def DiscreteSetting.N (D : DiscreteSetting) (t : ℝ≥0) : ℕ := sSup {k | D.T k ≤ t}

/-- Condition (17) with lower summation index `n + 1`:
`n⁻¹ Σ_{k=n+1}^∞ F_k(T_n) → 0` as `n → ∞`. -/
def DiscreteSetting.Cond17 (D : DiscreteSetting) : Prop :=
  Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * ∑' j : ℕ, D.F (n + 1 + j) (D.T n)) atTop (𝓝 0)

/-- Condition (18) for a given nonnegative finite sequence `S`:
`S_n / T_n → 0` and `n⁻¹ Σ_{k=1}^n [F_k(∞) − F_k(T_k + S_k)] → 0`. -/
def DiscreteSetting.Cond18 (D : DiscreteSetting) (S : ℕ → ℝ≥0) : Prop :=
  Tendsto (fun n : ℕ => (S n : ℝ) / (D.T n : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ *
      ∑ k ∈ Finset.Icc 1 n, (D.Finf k - D.F k (D.T k + S k))) atTop (𝓝 0)

/-- (19): `U_n = max {S_k : 1 ≤ k ≤ n}`, with `U_0 = 0` (empty maximum). -/
def U (S : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := (Finset.Icc 1 n).sup S

lemma U_mono (S : ℕ → ℝ≥0) : Monotone (U S) :=
  fun _ _ h => Finset.sup_mono (Finset.Icc_subset_Icc le_rfl h)

/-- The time change `T₂(s) = T_{[s]} + U_{[s]}` of (19). -/
noncomputable def DiscreteSetting.T2 (D : DiscreteSetting) (S : ℕ → ℝ≥0) : TimeChange :=
  stepTC (fun n => D.T n + U S n) (D.T_mono.add (U_mono S))
    (tendsto_atTop_mono (fun n => le_add_of_nonneg_right (by positivity)) D.T_tendsto)

end HLambdaG.Main.Supplement


