-- Prove2me | Definitions.Def_BwSC_LowerBound_Supplement_AdaLS
-- name    : BwSC_LowerBound_Supplement_AdaLS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:42:53.556646+00:00
-- url     : https://prove2.me/theorems/79d30b14-2383-465c-aff4-58605efbb294
-- title:
--   Algorithm 2 (boundary-completed) — full finite-seed AdaLS replay and canonical history kernels
-- statement:
--   This is the full AdaLS algorithm, with tuning parameter $\lambda=1/2$, on the published bandit model. Its two time grids are the published $t^{(1)}_j,t^{(2)}_j$. Let $q=q(S,K)$, $r=r(S,K)$ and $\widehat r=\max\{r+1-q,0\}$. Initialization uniformly chooses a subset $A^{(2)}_1$ of $\widehat r$ arms without replacement and then uniformly chooses $a_0$ outside that subset; $A^{(1)}_1$ is its complement.
--
--   For each epoch $l=1,\ldots,q$, the operational replay executes all of Lines 2–12: class-2 blocks; the class-1 loop, starting at the previous epoch's last arm when still in that class; the initial $n_l^{(2)}$ pulls and their checkpoints $T_{l,i}^{(1)}$; the confidence test and additional pulls; actual endpoints $T_l^{(2)},T_l^{(1)}$; and elimination in each class using both of the specified observation times. It then executes all of Lines 13–16: final class-2 exploration, final elimination and commitment to an empirical maximizer in the printed $A_l$.
--
--   The confidence radius for a sampled arm is
--   $$\sqrt{\frac{6\log T}{N_i(t)}}.$$
--   Every unobserved empirical mean is $-\infty$. An unobserved arm receives confidence bounds $[-\infty,+\infty]$, explicitly completing the source's undefined zero-sample confidence formula. Empty loops do nothing, counts use the source's nonnegative floor convention, and blocks stop at the horizon. The zero-budget branch plays $a_0$ throughout; the one-arm branch always plays its sole arm. Iteration uses increasing labels, with the required previous-arm priority. Final ties prefer the previous arm when it is an empirical maximizer, then the least label.
--
--   The history kernel is specified from the finite initial seeds. Given a history, replay each seed on its observed reward tape, retain exactly the seeds whose predicted past actions match that history, and choose the next action uniformly over those compatible seeds. For $n<T$,
--   $$\pi_n(\cdot\mid h)=\frac1{|\mathcal S(h)|}\sum_{s\in\mathcal S(h)}\delta_{a_{n+1}(s,h)}.$$
--   An impossible history with no compatible seeds selects the first arm. Kernels after $T$ are unrestricted. Existence of a canonical Markov-kernel policy realizing these equations is an explicit conclusion of each upper-bound theorem, rather than a premise or a regret condition hidden in the definition.
--
--   **Formalization Note** This replay is a specification of the concrete algorithm, not an arbitrary policy meeting the desired bound. A tape position $t$ is reward from round $t+1$; endpoints count completed rounds. Future tape entries are zero, and the sequential replay consults only entries preceding each decision. `EpochLog` preserves every actual endpoint. The only infinite confidence values occur in explicit no-sample branches, avoiding arithmetic with indeterminate infinities. The source's final elimination is recorded, and commitment still maximizes over $A_l$, as printed. The one-arm and zero-sample completions add no restrictions on $S,K,T$ or environments.
-- source:
--   Simchi-Levi & Xu, arXiv:1905.10825v4, p. 18, Algorithm 2; p. 14, eq. (4); pp. 17–19; Appendix F, pp. 45–52

import Mathlib
import Definitions.Def_BwSC_LowerBound_Supplement_Environment
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.Supplement

noncomputable section

/-- Each log records the actual endpoints T_l^(2), T_l^(1) and T_(l,i)^(1).
The integers count completed rounds; the first round is 1. -/
structure EpochLog (K : ℕ) where
  start : ℕ
  endTwo : ℕ
  checkOne : Fin K → ℕ
  endOne : ℕ

/-- Operational state, with a_0 held in `last` before the first actual play. -/
structure ReplayState (K : ℕ) where
  trace : List (Fin K)
  last : Fin K
  activeOne : Finset (Fin K)
  activeTwo : Finset (Fin K)
  logs : List (EpochLog K)

/-- Completed pulls among the first t rounds of a replay trace. -/
def replayCount {K : ℕ} (a : List (Fin K)) (i : Fin K) (t : ℕ) : ℕ :=
  ((Finset.range (min t a.length)).filter (fun s => a[s]? = some i)).card

/-- Sample mean; −∞ for every unobserved arm, agreeing with μbar_i(0)=−∞
on p. 14. Rewards are indexed from zero in the tape. -/
def replayMean {K : ℕ} (a : List (Fin K)) (x : ℕ → ℝ) (i : Fin K) (t : ℕ) : EReal :=
  if replayCount a i t = 0 then ⊥ else
    (((∑ s ∈ (Finset.range (min t a.length)).filter (fun s => a[s]? = some i), x s) /
      (replayCount a i t : ℝ) : ℝ) : EReal)

/-- Eq. (4), p. 14. Unobserved arms have the full confidence interval;
this explicit boundary completion avoids the undefined −∞+∞ expression. -/
def replayUCB {K : ℕ} (T : ℕ) (a : List (Fin K)) (x : ℕ → ℝ) (i : Fin K) (t : ℕ) : EReal :=
  if replayCount a i t = 0 then ⊤ else
    replayMean a x i t + (Real.sqrt (6 * Real.log T / replayCount a i t) : ℝ)

def replayLCB {K : ℕ} (T : ℕ) (a : List (Fin K)) (x : ℕ → ℝ) (i : Fin K) (t : ℕ) : EReal :=
  if replayCount a i t = 0 then ⊥ else
    replayMean a x i t - (Real.sqrt (6 * Real.log T / replayCount a i t) : ℝ)

/-- Append only as many consecutive plays as remain in the horizon.
A zero count leaves the last actually played arm unchanged. -/
def playBlock {K : ℕ} (T : ℕ) (i : Fin K) (n : ℕ) (s : ReplayState K) : ReplayState K :=
  let m := min n (T - s.trace.length)
  {s with trace := s.trace ++ List.replicate m i, last := if m = 0 then s.last else i}

/-- Fixed causal iteration order: increasing labels, except that the arm at
T_(l−1)^(1) comes first in the class-1 loop when still active (Lines 3–10). -/
def classOneOrder {K : ℕ} (A : Finset (Fin K)) (previous : Fin K) : List (Fin K) :=
  if previous ∈ A then previous :: (A.erase previous).sort (· ≤ ·) else A.sort (· ≤ ·)

/-- At the moment after the initial n_l^(2) pulls of i (Line 6). -/
def continuationTest {K : ℕ} (T : ℕ) (A : Finset (Fin K)) (x : ℕ → ℝ)
    (i : Fin K) (s : ReplayState K) : Prop :=
  ∀ j ∈ A, replayLCB T s.trace x j s.trace.length ≤
    replayUCB T s.trace x i s.trace.length

/-- Lines 5–7 for one class-1 arm, including the data-dependent extra pulls
and its own checkpoint T_(l,i)^(1). -/
def visitOne {K : ℕ} (T n₂ extra : ℕ) (A : Finset (Fin K)) (x : ℕ → ℝ)
    (acc : ReplayState K × (Fin K → ℕ)) (i : Fin K) :
    ReplayState K × (Fin K → ℕ) := by
  classical
  let s := playBlock T i n₂ acc.1
  let checks := Function.update acc.2 i s.trace.length
  exact (if continuationTest T A x i s then playBlock T i extra s else s, checks)

/-- A complete epoch l≤q: Lines 2–12 of Algorithm 2. The two grids are
parameters so Algorithm 6 can reuse the identical adaptive logic. -/
def replayEpoch {K : ℕ} (T : ℕ) (g₁ g₂ : ℕ → ℕ) (l : ℕ) (x : ℕ → ℝ)
    (s : ReplayState K) : ReplayState K := by
  classical
  let A := s.activeOne ∪ s.activeTwo
  let start := s.trace.length
  let previous := s.last
  let n₂ := (g₂ l - start) / A.card
  let s₂ := (s.activeTwo.sort (· ≤ ·)).foldl (fun z i => playBlock T i n₂ z) s
  let endTwo := s₂.trace.length
  let extra := (⌊((g₁ l : ℝ) / 2 - (endTwo : ℝ)) / (s.activeOne.card : ℝ)⌋₊) - n₂
  let visited := (classOneOrder s.activeOne previous).foldl
    (visitOne T n₂ extra A x) (s₂, fun _ => endTwo)
  let z := visited.1
  let checks := visited.2
  let finish := z.trace.length
  let one := s.activeOne.filter (fun i => ∀ j ∈ A,
    replayLCB T z.trace x j finish ≤ replayUCB T z.trace x i finish ∧
    replayLCB T z.trace x j (checks i) ≤ replayUCB T z.trace x i finish)
  let two := s.activeTwo.filter (fun i => ∀ j ∈ A,
    replayLCB T z.trace x j finish ≤ replayUCB T z.trace x i finish ∧
    replayLCB T z.trace x j endTwo ≤ replayUCB T z.trace x i finish)
  exact {z with activeOne := one, activeTwo := two, logs := z.logs ++ [⟨start, endTwo, checks, finish⟩]}

/-- Least empirical maximizer, preferring the previous arm when it is a
maximizer. In particular an entirely unobserved final epoch keeps a_0. -/
def empiricalChoice {K : ℕ} (A : Finset (Fin K)) (x : ℕ → ℝ)
    (s : ReplayState K) : Fin K := by
  classical
  let best := A.filter (fun i => ∀ j ∈ A,
    replayMean s.trace x j s.trace.length ≤ replayMean s.trace x i s.trace.length)
  exact if s.last ∈ best then s.last else
    if hn : best.Nonempty then best.min' hn else s.last

/-- Lines 13–16: the final class-2 exploration, its elimination, and
commitment to an empirical maximizer in A_l (as printed in Line 16).
The eliminated set is recorded even though there is no next epoch. -/
def finalEpoch {K : ℕ} (T : ℕ) (g₂ : ℕ → ℕ) (l : ℕ) (x : ℕ → ℝ)
    (s : ReplayState K) : ReplayState K := by
  classical
  let A := s.activeOne ∪ s.activeTwo
  let start := s.trace.length
  let n₂ := (g₂ l - start) / A.card
  let z := (s.activeTwo.sort (· ≤ ·)).foldl (fun z i => playBlock T i n₂ z) s
  let finish := z.trace.length
  let next := A.filter (fun i => ∀ j ∈ A,
    replayLCB T z.trace x j finish ≤ replayUCB T z.trace x i finish)
  let chosen := empiricalChoice A x z
  let out := playBlock T chosen (T - finish) z
  exact {out with activeOne := next, activeTwo := ∅, logs := out.logs ++ [⟨start, finish, fun _ => finish, T⟩]}

/-- rhat=max(r+1−q,0), with signed r, so S=0 gives rhat=0. -/
def classTwoSize (S K : ℕ) : ℕ :=
  ((rIdx S K + 1 - (qIdx S K : ℤ)) : ℤ).toNat

/-- Uniform seeds are pairs (class-2 subset, a_0 outside it). Uniform pairs
are exactly uniform sampling without replacement followed by uniform a_0.
The one-arm branch avoids dividing by K−1 or forming a nonexistent gap. -/
def initialSeeds (S K : ℕ) : Finset (Finset (Fin K) × Fin K) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.1.card = (if K = 1 then 0 else classTwoSize S K) ∧ p.2 ∉ p.1)

/-- Entire finite execution with fixed seed and reward tape. It executes
all q ordinary epochs and the last epoch, including empty loops, with
λ=1/2. Every block is clipped to the remaining horizon. -/
def replayRun {K : ℕ} (S T : ℕ) (g₁ g₂ : ℕ → ℕ)
    (seed : Finset (Fin K) × Fin K) (x : ℕ → ℝ) : ReplayState K := by
  classical
  let init : ReplayState K := ⟨[], seed.2, Finset.univ \ seed.1, seed.1, []⟩
  exact if K = 1 ∨ S = 0 then playBlock T seed.2 T init else
    let s := (List.range (qIdx S K)).foldl
      (fun s j => replayEpoch T g₁ g₂ (j + 1) x s) init
    finalEpoch T g₂ (qIdx S K + 1) x s

/-- Replay on an observed history: unavailable future rewards are set to
zero. Every decision at round n+1 uses only rewards with indices <n. -/
def historyTape {K n : ℕ} (h : BanditHistory K n) (t : ℕ) : ℝ :=
  if ht : t < n then (h ⟨t, ht⟩).2 else 0

/-- Replay action, with its seed's a_0 as the totalization beyond T. -/
def replayAction {K : ℕ} (S T : ℕ) (g₁ g₂ : ℕ → ℕ)
    (seed : Finset (Fin K) × Fin K) {n : ℕ} (h : BanditHistory K n) (t : ℕ) : Fin K :=
  ((replayRun S T g₁ g₂ seed (historyTape h)).trace[t]?).getD seed.2

/-- Seeds compatible with all actions already observed. Conditional on a
history, compatible seeds have equal weights: reward likelihoods depend
only on observed actions and rewards, not on the private seed. -/
def compatibleSeeds {K n : ℕ} (S T : ℕ) (g₁ g₂ : ℕ → ℕ) (h : BanditHistory K n) :
    Finset (Finset (Fin K) × Fin K) := by
  classical
  exact (initialSeeds S K).filter (fun seed =>
    ∀ t : Fin n, replayAction S T g₁ g₂ seed h t = (h t).1)

/-- The precise finite-seed conditional action law. An incompatible history
has probability zero and is completed with the deterministic first arm.
No regret or switching guarantee is included in this definition. -/
def replayChoice {K n : ℕ} (hK : 0 < K) (S T : ℕ) (g₁ g₂ : ℕ → ℕ)
    (h : BanditHistory K n) : Measure (Fin K) := by
  classical
  let seeds := compatibleSeeds S T g₁ g₂ h
  exact if seeds = ∅ then Measure.dirac ⟨0, hK⟩ else
    ((seeds.card : ℝ≥0∞)⁻¹) •
      ∑ seed ∈ seeds, Measure.dirac (replayAction S T g₁ g₂ seed h n)

/-- A canonical history-kernel policy realizing the specified replay
algorithm. Existence is asserted by each upper-bound theorem, never assumed.
Kernels after the horizon are irrelevant and unrestricted. -/
def IsReplayPolicy {K : ℕ} (hK : 0 < K) (S T : ℕ) (g₁ g₂ : ℕ → ℕ)
    (π : BanditPolicy K) : Prop :=
  ∀ n, n < T → ∀ h : BanditHistory K n, π.select n h = replayChoice hK S T g₁ g₂ h

/-- Algorithm 2, p. 18, with its published grids and λ=1/2. -/
def IsAdaLS {K : ℕ} (hK : 0 < K) (S T : ℕ) (π : BanditPolicy K) : Prop :=
  IsReplayPolicy hK S T (t1 S K T) (t2 S K T) π

end

end BwSC.LowerBound.Supplement


