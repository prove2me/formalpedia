-- Prove2me | Definitions.Def_DynDoubleAuction_TwoSided_Model
-- name    : DynDoubleAuction_TwoSided_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:03.648389+00:00
-- url     : https://prove2.me/theorems/41bead9f-c5dd-4dd6-b3d9-8c8ef49747b2
-- title:
--   §2 and §5.1 — the two-sided market and coupled mechanism
-- statement:
--   A market has one seller, $n\ge1$ buyers, a joint distribution $F$ of their values, a value bound $\bar v$, a reserve price $r$, and buyer weights $\alpha_i$. Values in different periods are independent draws from $F$; agents' values within a period may be correlated. Let $\underline w_0=\mathbb E[(\max_{i\ge1}v_i-v_0)^+]$ and $\mu=\mathbb E[(r-v_0)^+]$. The standing assumptions include support on $[0,\bar v]^{n+1}$ and Assumption 5.1's equalities, weight bound, and $0<\mu\le\underline w_0$.
--
--   The mechanism maps current promises and reports to allocation probabilities, expected transfers, and next promises. In the medium region, it trades with the lexicographically first highest buyer at their value and pays the seller their cost. In the boundary regions, it uses reserve $r$, buyer weights $\alpha_i$, and the per-agent throttles $\min(1,w_i/\mu)$. The definitions also specify the state recursion, the iid value law, expected profit $\Pi$, expected welfare $S$, the first-best benchmark $\Pi^{\mathrm{FB}}=T\underline w_0$, and first-exit times.
--
--   These definitions fix the market and the exact mechanism studied in Lemma 5.2 and Theorem 5.3.
--
--   **Formalization Note** Agents are `Fin (n+1)` with seller zero; periods are one-based in prose and zero-based in the recursive state. Equality at either medium-region boundary uses the boundary rule.
-- source:
--   Balseiro, Mirrokni, Paes Leme & Zuo, Dynamic Double Auctions: Towards First Best, SSRN 3213460 (version of November 15, 2018), pp. 6–10, 24–25, 29–30, §2, §5.1, Assumption 5.1, proof of Theorem 5.3

import Mathlib

namespace DynDoubleAuction.TwoSided

open MeasureTheory Filter Topology

/-- One seller, numbered zero, and `n` buyers, numbered one through `n`. -/
structure Market (n : ℕ) where
  F : Measure (Fin (n + 1) → ℝ)
  vbar : ℝ
  r : ℝ
  α : Fin (n + 1) → ℝ

/-- The largest buyer value; the empty-buyer branch only makes the function total. -/
noncomputable def maxBuyer {n : ℕ} (v : Fin (n + 1) → ℝ) : ℝ := by
  classical
  exact if h : (Finset.univ.erase (0 : Fin (n + 1))).Nonempty then
    (Finset.univ.erase (0 : Fin (n + 1))).sup' h v
  else 0

/-- Lexicographically first buyer attaining the highest value and meeting the seller's cost. -/
def isWinner {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Prop :=
  i ≠ 0 ∧ v 0 ≤ v i ∧ v i = maxBuyer v ∧
    ∀ j : Fin (n + 1), j ≠ 0 → j < i → v j < v i

noncomputable def wlow {n : ℕ} (M : Market n) : ℝ :=
  ∫ v, max (maxBuyer v - v 0) 0 ∂M.F

noncomputable def mu {n : ℕ} (M : Market n) : ℝ :=
  ∫ v, max (M.r - v 0) 0 ∂M.F

/-- Remaining reserve surplus at the start of period `t`, with periods numbered from one. -/
noncomputable def wbar {n : ℕ} (M : Market n) (T t : ℕ) : ℝ :=
  ((T : ℝ) - (t : ℝ) + 1) * mu M

/-- The paper's support restriction and Assumption 5.1. -/
def Standing {n : ℕ} (M : Market n) : Prop :=
  1 ≤ n ∧ IsProbabilityMeasure M.F ∧ 0 < M.vbar ∧
  (∀ᵐ v ∂M.F, ∀ j, v j ∈ Set.Icc 0 M.vbar) ∧
  M.r ∈ Set.Icc 0 M.vbar ∧
  (∀ i, i ≠ 0 → M.α i ∈ Set.Icc 0 1) ∧
  (∀ i, i ≠ 0 → M.α i * (∫ v, v i * (if v 0 ≤ M.r then 1 else 0) ∂M.F) = mu M) ∧
  (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i) ≤ 1 ∧
  mu M ≤ wlow M ∧ 0 < mu M

/-- Boundary points belong to the low or high rule. -/
def Medium {n : ℕ} (M : Market n) (T t : ℕ) (w0 : ℝ) : Prop :=
  wlow M < w0 ∧ w0 < wbar M T t - M.vbar

/-- Allocation probabilities, expected transfers, and next-period promises. -/
structure Outcome (n : ℕ) where
  q : Fin (n + 1) → ℝ
  z : Fin (n + 1) → ℝ
  u : Fin (n + 1) → ℝ

/-- The coupled mechanism of §5.1. The allocation is a probability, not a random draw. -/
noncomputable def rule {n : ℕ} (M : Market n) (T t : ℕ)
    (w v : Fin (n + 1) → ℝ) : Outcome n := by
  classical
  if Medium M T t (w 0) then
    let q : Fin (n + 1) → ℝ := fun i =>
      if i = 0 then (if v 0 ≤ maxBuyer v then 1 else 0)
      else (if isWinner v i then 1 else 0)
    exact {
      q := q
      z := fun i => v i * q i
      u := fun i => w i + max (maxBuyer v - v 0) 0 - wlow M
    }
  else
    let q : Fin (n + 1) → ℝ := fun i =>
      if i = 0 then min 1 (w 0 / mu M) * (if v 0 ≤ M.r then 1 else 0)
      else M.α i * min 1 (w i / mu M) * (if v 0 ≤ M.r then 1 else 0)
    exact {
      q := q
      z := fun i => if i = 0 then M.r * q 0 else 0
      u := fun i => max (w i - mu M) 0
    }

/-- Period utility at true value `x` when the outcome was computed from reports. -/
noncomputable def periodUtility {n : ℕ} (o : Outcome n) (j : Fin (n + 1)) (x : ℝ) : ℝ :=
  if j = 0 then o.z 0 - x * o.q 0 else x * o.q j - o.z j

/-- The state before period `k + 1`; `state ... 0` is the initial promise. -/
noncomputable def state {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) : ℕ → Fin (n + 1) → ℝ
  | 0 => fun _ => w1
  | k + 1 => (rule M T (k + 1) (state M T w1 vs k) (vs k)).u

noncomputable def periodOutcome {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) (k : ℕ) : Outcome n :=
  rule M T (k + 1) (state M T w1 vs k) (vs k)

noncomputable def profitPath {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range T,
    ((∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (periodOutcome M T w1 vs k).z i) -
      (periodOutcome M T w1 vs k).z 0)

noncomputable def welfarePath {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range T,
    ((∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
      vs k i * (periodOutcome M T w1 vs k).q i) -
      vs k 0 * (periodOutcome M T w1 vs k).q 0)

/-- Independent periods with arbitrary within-period correlation. -/
noncomputable def valueLaw {n : ℕ} (M : Market n) :
    Measure (ℕ → Fin (n + 1) → ℝ) :=
  Measure.infinitePi (fun _ => M.F)

noncomputable def expectedProfit {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ) : ℝ :=
  ∫ vs, profitPath M T w1 vs ∂valueLaw M

noncomputable def expectedWelfare {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ) : ℝ :=
  ∫ vs, welfarePath M T w1 vs ∂valueLaw M

noncomputable def firstBest {n : ℕ} (M : Market n) (T : ℕ) : ℝ :=
  (T : ℝ) * wlow M

noncomputable def initialPromise {n : ℕ} (M : Market n) (T : ℕ) : ℝ :=
  wlow M + M.vbar * Real.sqrt (8 * (T : ℝ) * Real.log T)

/-- First period in the low or high region; `T+1` means no exit during the horizon. -/
noncomputable def exitTime {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) : ℕ := by
  classical
  exact if h : ∃ t ∈ Finset.Icc 1 T,
      ¬ Medium M T t (state M T w1 vs (t - 1) 0) then
    Nat.find h
  else T + 1

noncomputable def tauLow {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) : ℕ := by
  classical
  exact if h : ∃ t ∈ Finset.Icc 1 T,
      state M T w1 vs (t - 1) 0 ≤ wlow M then Nat.find h else T + 1

noncomputable def tauHigh {n : ℕ} (M : Market n) (T : ℕ) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) : ℕ := by
  classical
  exact if h : ∃ t ∈ Finset.Icc 1 T,
      wbar M T t - M.vbar ≤ state M T w1 vs (t - 1) 0 then Nat.find h else T + 1

/-- Centered first-best surplus walk, indexed so `mart 0 = w^1`. -/
noncomputable def mart {n : ℕ} (M : Market n) (w1 : ℝ)
    (vs : ℕ → Fin (n + 1) → ℝ) : ℕ → ℝ
  | 0 => w1
  | k + 1 => mart M w1 vs k + max (maxBuyer (vs k) - vs k 0) 0 - wlow M

noncomputable def Tstar {n : ℕ} (M : Market n) (T : ℕ) : ℝ :=
  (T : ℝ) + 1 -
    (M.vbar + wlow M + 2 * M.vbar * Real.sqrt (8 * (T : ℝ) * Real.log T)) / mu M

end DynDoubleAuction.TwoSided


