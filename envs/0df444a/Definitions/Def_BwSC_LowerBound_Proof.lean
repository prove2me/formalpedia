-- Prove2me | Definitions.Def_BwSC_LowerBound_Proof
-- name    : BwSC_LowerBound_Proof
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:10.702427+00:00
-- url     : https://prove2.me/theorems/5585a858-b8e2-44c6-929d-1f83ff6420f9
-- title:
--   App. J, pp. 18, 60–74 — time grids t^(1), t^(2), stopping time τ, risky events E^(1), E^(2), alternative environments, R_bad, stopped artificial measures
-- statement:
--   The objects of the RECAP proof of Theorem 2 (Appendix J). Write $q=q(S,K)$, $r=r(S,K)$, $a(q)=1/(2-2^{-q})$.
--
--   1. **Time grids** (Algorithm 2, p. 18): $t^{(1)}_0=t^{(2)}_0=0$ and
--   $$t^{(1)}_j=\Big\lfloor (K-r)^{1-\frac{2-2^{1-j}}{2-2^{-q}}}\,T^{\frac{2-2^{1-j}}{2-2^{-q}}}\Big\rfloor,\qquad t^{(2)}_j=\Big\lfloor K^{1-\frac{2-2^{1-j}}{2-2^{-q-1}}}\,T^{\frac{2-2^{1-j}}{2-2^{-q-1}}}\Big\rfloor .$$
--   2. **Stopping time** (p. 60): $\tau=\min\{t\in[T]:S(1:t)=S\}$, and $\tau=\infty$ if no such round exists.
--   3. **First class of risky events** (p. 60), $k\in[K]$, $m=\lfloor (t^{(1)}_q+T)/2\rfloor$: $E^{(1)}_{j,k}$ = "action $k$ is not chosen in period $[t^{(1)}_{j-1}:t^{(1)}_j]$" for $j\in[q]$; $E^{(1)}_{q+1,k}$ = "$k$ is not chosen in $[t^{(1)}_q:m]$"; $E^{(1)}_{q+2,k}=\{\tau\le m,\ a_\tau=k,\ k\text{ not chosen in }[t^{(1)}_q:\tau-1]\}$.
--   4. **Second class** (p. 60): $E^{(2)}_{j,k}$ = "action $k$ is not chosen in period $[t^{(2)}_{j-1}:t^{(2)}_j]$", $j\in[q+2]$.
--   5. **Gaps and alternative environments** (pp. 65, 68–69): $\Delta^{(1)}_1=1$, $\Delta^{(1)}_j=\frac{1}{2(q+2)}\sqrt{(K-r)/t^{(1)}_{j-1}}$ for $j\in[2:q+1]$, $\Delta^{(1)}_{q+2}=-\frac{1}{2(q+2)}\sqrt{(K-r)/t^{(1)}_q}$; $\Delta^{(2)}_1=1$, $\Delta^{(2)}_j=\frac1{2(q+2)}\sqrt{K/t^{(2)}_{j-1}}$ for $j\in[2:q+2]$. The environment $\mu^{(c)}_{j,k}$ has mean $\Delta^{(c)}_j$ on arm $k$ and $0$ elsewhere; the reference environment is $\mathbf 0$ and $\mathbb Q=\mathbb P^\pi_{\mathbf 0}$.
--   6. **Bad-event regrets** (pp. 66, 69): $R_{\rm bad}=\frac{K-r}{8(q+2)}\big(\frac{T}{K-r}\big)^{a(q)}$ and $R_{\rm bad2}=\frac{K}{4(q+2)}\big(\frac TK\big)^{a(q+1)}$; the pseudo-regret of a history under $\mu$ is $T\max_i\mu_i-\sum_{t=1}^T\mu_{a_t}$.
--   7. **Artificial measures** (pp. 71–74, repaired). For a window $[lo:hi]$ — $[1:t^{(1)}_1]$, $[t^{(1)}_{j-1}:t^{(1)}_j]$ ($j\in[2:q]$), $[t^{(1)}_q:m]$ ($j\in\{q+1,q+2\}$) for the first class, $[t^{(2)}_{j-1}:t^{(2)}_j]$ for the second — the *stopped record* of a history keeps every round before $lo$, keeps the rounds of the window before the first pull of arm $k$ in the window, and records that first pull and every later round as $(k,0)$. $\mathbb P'_{j,k}$, $\mathbb Q'_{j,k}$ (resp. $\mathbb P''_{j,k}$, $\mathbb Q''_{j,k}$) are the laws of the stopped record under $\mu^{(1)}_{j,k}$ and $\mathbf 0$ (resp. $\mu^{(2)}_{j,k}$ and $\mathbf 0$).
--   8. **Averages** ((43), p. 69; p. 70): $\overline{p^{(c)}}=\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}\mathbb P^\pi_{\mu^{(c)}_{j,k}}(E^{(c)}_{j,k})$ and $\overline{q^{(c)}}$ the same average under $\mathbb Q$.
--
--   These are the shared objects of Lemmas 6–13 and (46)–(47).
--
--   **Formalization Note** Rounds are 1-based as on the page: entry $s$ of a history $h\in(\{1,\dots,K\}\times\mathbb R)^T$ is round $s+1$, and a period $[n_1:n_2]$ is the set of rounds $t$ with $n_1\le t\le n_2$ and $1\le t\le T$. $\tau=\infty$ is encoded as $T+1$; since no round $T+1$ exists, $a_\tau=k$ fails there. At $q=0$ the clauses $j=1$ and $j=q+1$ of item 3 collide; the clauses $j=q+2$, then $j=q+1$, take precedence. Floors are `Nat.floor` of real numbers. **Repair of (45):** the printed artificial measures hide arm $k$'s rewards inside the window but keep all actions, which may depend on the hidden rewards; then the divergence identity of p. 72 fails. The records here stop at the first pull of $k$ in the window, which keeps the risky events decided by the record and gives the divergence $(\Delta^2/2)\,\mathbb E_{\mathbf 0}[N_k(lo-1)]$ intended on p. 72. The stopped-record map is proved measurable in this file, so its push-forward measures are genuine laws. $\Delta^{(1)}_{q+2}$ divides by $t^{(1)}_0=0$ when $q=0$ (value $0$ in Lean); the paper leaves that case undefined and the statements using it assume $q\ge1$.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 18 (Algorithm 2 initialization), p. 60 (App. J.1), pp. 65, 68–69 (App. J.3), pp. 69–70 ((43)), pp. 71–74 (App. J.4, (45))

import Mathlib
import Definitions.Def_BwSC_LowerBound_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound

/-- The first time grid of Algorithm 2, p. 18: `t^{(1)}_0 = 0` and, for `j ≥ 1`,
`t^{(1)}_j = ⌊(K - r)^{1 - (2 - 2^{1-j})/(2 - 2^{-q})} T^{(2 - 2^{1-j})/(2 - 2^{-q})}⌋`
with `q = q(S,K)`, `r = r(S,K)`. The paper uses `j = 0, …, q + 1`. -/
noncomputable def t1 (S K T j : ℕ) : ℕ :=
  if j = 0 then 0 else
    ⌊((K : ℝ) - (rIdx S K : ℝ)) ^ (1 - (2 - (2 : ℝ) ^ (1 - (j : ℝ))) * aExp (qIdx S K)) *
      (T : ℝ) ^ ((2 - (2 : ℝ) ^ (1 - (j : ℝ))) * aExp (qIdx S K))⌋₊

/-- The second time grid of Algorithm 2, p. 18: `t^{(2)}_0 = 0` and, for `j ≥ 1`,
`t^{(2)}_j = ⌊K^{1 - (2 - 2^{1-j})/(2 - 2^{-q-1})} T^{(2 - 2^{1-j})/(2 - 2^{-q-1})}⌋`.
The paper uses `j = 0, …, q + 2`. -/
noncomputable def t2 (S K T j : ℕ) : ℕ :=
  if j = 0 then 0 else
    ⌊(K : ℝ) ^ (1 - (2 - (2 : ℝ) ^ (1 - (j : ℝ))) * aExp (qIdx S K + 1)) *
      (T : ℝ) ^ ((2 - (2 : ℝ) ^ (1 - (j : ℝ))) * aExp (qIdx S K + 1))⌋₊

/-- The stopping time `τ = min{t ∈ [T] : S(1 : t) = S}` of App. J.1, item 2, p. 60, the first
round at which the total switching cost reaches the budget `S`. The value `τ = ∞` (empty set)
is encoded by the sentinel `T + 1`, which exceeds every round, and `act h (T + 1) = none`. -/
noncomputable def stopTime {K T : ℕ} (S : ℕ) (h : BanditHistory K T) : ℕ :=
  if hne : ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).Nonempty then
    ((Finset.Icc 1 T).filter (fun t => switchCost h 1 t = S)).min' hne
  else T + 1

/-- "Action `k` is not chosen in period `[n₁ : n₂]`": no 1-based round `t` with
`n₁ ≤ t ≤ n₂` (and `1 ≤ t ≤ T`) plays arm `k`. -/
def notChosen {K T : ℕ} (h : BanditHistory K T) (k : Fin K) (n₁ n₂ : ℕ) : Prop :=
  ∀ t, n₁ ≤ t → t ≤ n₂ → act h t ≠ some k

/-- The midpoint `⌊(t^{(1)}_{q(S,K)} + T)/2⌋` of App. J.1, item 3, p. 60. -/
noncomputable def mid1 (S K T : ℕ) : ℕ := (t1 S K T (qIdx S K) + T) / 2

/-- The first class of risky events `E^{(1)}_{j,k}`, `j ∈ [q + 2]` (App. J.1, item 3, p. 60):
* `j ∈ [1 : q]`: action `k` is not chosen in period `[t^{(1)}_{j-1} : t^{(1)}_j]`
  (for `j = 1` this is `[1 : t^{(1)}_1]`, since `t^{(1)}_0 = 0`);
* `j = q + 1`: action `k` is not chosen in `[t^{(1)}_q : ⌊(t^{(1)}_q + T)/2⌋]`;
* `j = q + 2`: `τ ≤ ⌊(t^{(1)}_q + T)/2⌋`, `a_τ = k`, and action `k` is not chosen in
  `[t^{(1)}_q : τ - 1]`.
The clauses `j = q + 2` and `j = q + 1` take precedence (they collide with `j = 1` when
`q = 0`). -/
noncomputable def E1 (S K T j : ℕ) (k : Fin K) : Set (BanditHistory K T) :=
  if j = qIdx S K + 2 then
    {h | stopTime S h ≤ mid1 S K T ∧ act h (stopTime S h) = some k ∧
      notChosen h k (t1 S K T (qIdx S K)) (stopTime S h - 1)}
  else if j = qIdx S K + 1 then
    {h | notChosen h k (t1 S K T (qIdx S K)) (mid1 S K T)}
  else
    {h | notChosen h k (t1 S K T (j - 1)) (t1 S K T j)}

/-- The second class of risky events `E^{(2)}_{j,k}`, `j ∈ [q + 2]` (App. J.1, item 4, p. 60):
action `k` is not chosen in period `[t^{(2)}_{j-1} : t^{(2)}_j]` (`[1 : t^{(2)}_1]` for
`j = 1`). -/
noncomputable def E2 (S K T j : ℕ) (k : Fin K) : Set (BanditHistory K T) :=
  {h | notChosen h k (t2 S K T (j - 1)) (t2 S K T j)}

/-- The reward gap `Δ^{(1)}_j` of App. J.3.1, p. 65: `1` for `j = 1`,
`(1/(2(q+2)))·√((K - r)/t^{(1)}_{j-1})` for `j ∈ [2 : q + 1]`, and
`-(1/(2(q+2)))·√((K - r)/t^{(1)}_q)` for `j = q + 2`. -/
noncomputable def Δ1 (S K T j : ℕ) : ℝ :=
  if j = 1 then 1
  else if j = qIdx S K + 2 then
    -(1 / (2 * ((qIdx S K : ℝ) + 2)) *
      Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T (qIdx S K) : ℝ)))
  else
    1 / (2 * ((qIdx S K : ℝ) + 2)) *
      Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T (j - 1) : ℝ))

/-- The reward gap `Δ^{(2)}_j` of App. J.3.2, p. 68: `1` for `j = 1` and
`(1/(2(q+2)))·√(K/t^{(2)}_{j-1})` for `j ∈ [2 : q + 2]`. -/
noncomputable def Δ2 (S K T j : ℕ) : ℝ :=
  if j = 1 then 1
  else 1 / (2 * ((qIdx S K : ℝ) + 2)) * Real.sqrt ((K : ℝ) / (t2 S K T (j - 1) : ℝ))

/-- The alternative environment `μ^{(1)}_{j,k}` (p. 65): mean `Δ^{(1)}_j` on arm `k`, `0` on
every other arm. -/
noncomputable def envAlt1 (S K T j : ℕ) (k : Fin K) : Fin K → ℝ :=
  Function.update (0 : Fin K → ℝ) k (Δ1 S K T j)

/-- The alternative environment `μ^{(2)}_{j,k}` (p. 69): mean `Δ^{(2)}_j` on arm `k`, `0` on
every other arm. -/
noncomputable def envAlt2 (S K T j : ℕ) (k : Fin K) : Fin K → ℝ :=
  Function.update (0 : Fin K → ℝ) k (Δ2 S K T j)

/-- `R_bad(S,K,T) = ((K - r)/(8(q+2)))·(T/(K - r))^{1/(2 - 2^{-q})}` (Lemma 8, p. 66). -/
noncomputable def Rbad (S K T : ℕ) : ℝ :=
  ((K : ℝ) - (rIdx S K : ℝ)) / (8 * ((qIdx S K : ℝ) + 2)) *
    ((T : ℝ) / ((K : ℝ) - (rIdx S K : ℝ))) ^ aExp (qIdx S K)

/-- `R_bad2(S,K,T) = (K/(4(q+2)))·(T/K)^{1/(2 - 2^{-q-1})}` (Lemma 10, p. 69). -/
noncomputable def Rbad2 (S K T : ℕ) : ℝ :=
  (K : ℝ) / (4 * ((qIdx S K : ℝ) + 2)) * ((T : ℝ) / (K : ℝ)) ^ aExp (qIdx S K + 1)

/-- The pseudo-regret of a history under the mean vector `μ`:
`T·max_i μ_i - Σ_{t=1}^T μ_{a_t}` (the integrand of R^π_μ(T), p. 59). -/
noncomputable def regretOf {K T : ℕ} (μvec : Fin K → ℝ) (h : BanditHistory K T) : ℝ :=
  (T : ℝ) * (⨆ i, μvec i) - ∑ t, μvec (h t).1

/-- The window `[lo, hi]` of the first-class artificial measures (p. 71): `[1 : t^{(1)}_1]`
for `j = 1` (encoded with `t^{(1)}_0 = 0`), `[t^{(1)}_{j-1} : t^{(1)}_j]` for `j ∈ [2 : q]`,
and `[t^{(1)}_q : ⌊(t^{(1)}_q + T)/2⌋]` for `j ∈ {q + 1, q + 2}`. -/
noncomputable def lo1 (S K T j : ℕ) : ℕ :=
  if qIdx S K + 1 ≤ j then t1 S K T (qIdx S K) else t1 S K T (j - 1)

/-- Right end of the first-class window, see `lo1`. -/
noncomputable def hi1 (S K T j : ℕ) : ℕ :=
  if qIdx S K + 1 ≤ j then mid1 S K T else t1 S K T j

/-- The window `[t^{(2)}_{j-1} : t^{(2)}_j]` of the second-class artificial measures (p. 73). -/
noncomputable def lo2 (S K T j : ℕ) : ℕ := t2 S K T (j - 1)

/-- Right end of the second-class window. -/
noncomputable def hi2 (S K T j : ℕ) : ℕ := t2 S K T j

/-- Whether entry `i` (1-based round `i + 1`) of an action vector is recorded unchanged by the
stopped record of window `[lo, hi]` and arm `k`: the round precedes the window, or it lies in
the window, plays an arm other than `k`, and no round of the window before it plays `k`. -/
def keepRound {K T : ℕ} (lo hi : ℕ) (k : Fin K) (a : Fin T → Fin K) (i : Fin T) : Prop :=
  i.val + 1 < lo ∨
    (i.val + 1 ≤ hi ∧ a i ≠ k ∧ ∀ s ∈ Finset.Ico lo (i.val + 1), actA a s ≠ some k)

open Classical in
/-- The stopped record of a history for window `[lo, hi]` and arm `k` (the repaired form of the
artificial measures (45), p. 71): rounds before `lo` are kept as `(a_t, X_t)`; rounds of the
window before the first pull of arm `k` in the window are kept; the first pull of `k` in the
window and every later round (in the window or after `hi`) are recorded as the constant
`(k, 0)`. -/
noncomputable def stopCensor {K T : ℕ} (lo hi : ℕ) (k : Fin K) (h : BanditHistory K T) :
    BanditHistory K T :=
  fun i => if keepRound lo hi k (actions h) i then h i else (k, 0)

lemma measurable_actions {K T : ℕ} :
    Measurable (actions : BanditHistory K T → Fin T → Fin K) :=
  measurable_pi_lambda _ (fun s => measurable_fst.comp (measurable_pi_apply s))

lemma measurable_stopCensor {K T : ℕ} (lo hi : ℕ) (k : Fin K) :
    Measurable (stopCensor lo hi k : BanditHistory K T → BanditHistory K T) := by
  rw [measurable_pi_iff]
  intro i
  classical
  have hset : MeasurableSet {h : BanditHistory K T | keepRound lo hi k (actions h) i} :=
    measurable_actions ((Set.toFinite {a : Fin T → Fin K | keepRound lo hi k a i}).measurableSet)
  exact Measurable.ite hset (measurable_pi_apply i) measurable_const

/-- The artificial measure `P'_{j,k}` (p. 71, repaired): the law of the stopped record, for the
first-class window of `j`, of the history under the alternative environment `μ^{(1)}_{j,k}`. -/
noncomputable def artP1 {K : ℕ} (π : BanditPolicy K) (S T j : ℕ) (k : Fin K) :
    Measure (BanditHistory K T) :=
  (banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T).map
    (stopCensor (lo1 S K T j) (hi1 S K T j) k)

/-- The artificial reference measure `Q'_{j,k}` (pp. 71–72, repaired): the same stopped record
under the reference environment `0`. -/
noncomputable def artQ1 {K : ℕ} (π : BanditPolicy K) (S T j : ℕ) (k : Fin K) :
    Measure (BanditHistory K T) :=
  (banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T).map
    (stopCensor (lo1 S K T j) (hi1 S K T j) k)

/-- The artificial measure `P''_{j,k}` (p. 73, repaired): the stopped record, for the
second-class window of `j`, under the alternative environment `μ^{(2)}_{j,k}`. -/
noncomputable def artP2 {K : ℕ} (π : BanditPolicy K) (S T j : ℕ) (k : Fin K) :
    Measure (BanditHistory K T) :=
  (banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T).map
    (stopCensor (lo2 S K T j) (hi2 S K T j) k)

/-- The artificial reference measure `Q''_{j,k}` (pp. 73–74, repaired). -/
noncomputable def artQ2 {K : ℕ} (π : BanditPolicy K) (S T j : ℕ) (k : Fin K) :
    Measure (BanditHistory K T) :=
  (banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T).map
    (stopCensor (lo2 S K T j) (hi2 S K T j) k)

/-- `p̄^{(1)}` (p. 69, (43)): the average over `j ∈ [q+2]`, `k ∈ [K]` of the probability of
`E^{(1)}_{j,k}` under its alternative measure `P^{(1)}_{j,k}`. -/
noncomputable def pbar1 {K : ℕ} (π : BanditPolicy K) (S T : ℕ) : ℝ :=
  1 / (((qIdx S K : ℝ) + 2) * K) *
    ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
      ((banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k)).toReal

/-- `q̄^{(1)}` (p. 70): the same average under the reference measure `ℚ = P^π_0`. -/
noncomputable def qbar1 {K : ℕ} (π : BanditPolicy K) (S T : ℕ) : ℝ :=
  1 / (((qIdx S K : ℝ) + 2) * K) *
    ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
      ((banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E1 S K T j k)).toReal

/-- `p̄^{(2)}`: the average probability of `E^{(2)}_{j,k}` under `P^{(2)}_{j,k}`. -/
noncomputable def pbar2 {K : ℕ} (π : BanditPolicy K) (S T : ℕ) : ℝ :=
  1 / (((qIdx S K : ℝ) + 2) * K) *
    ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
      ((banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k)).toReal

/-- `q̄^{(2)}`: the average probability of `E^{(2)}_{j,k}` under `ℚ`. -/
noncomputable def qbar2 {K : ℕ} (π : BanditPolicy K) (S T : ℕ) : ℝ :=
  1 / (((qIdx S K : ℝ) + 2) * K) *
    ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
      ((banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E2 S K T j k)).toReal

end BwSC.LowerBound


