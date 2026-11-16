-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold
-- name    : SampleCRS_AlmostGreedy_Supplement_threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:34:38.381888+00:00
-- url     : https://prove2.me/theorems/72df5cfd-d122-4dc8-9f64-7dafada2e6ab
-- title:
--   Algorithms 2 and 3: actual threshold laws and strict-threshold run
-- statement:
--   A threshold has a before-first value and one value at each arrival position. Algorithm 2 uses two sample rows. For their first success set $S$, it returns before-first if $S$ is empty. For a singleton $\{j\}$ it returns $j$ unless the second sample at $j$ is active, in which case it chooses before-first or $j$ fairly. When $|S|\ge2$, it first chooses before-first with probability $1/2$; otherwise it chooses $J$ uniformly from $S$, keeps $J$ if its second sample is inactive, and otherwise chooses uniformly from $S\setminus\{J\}$. The conditional weights explicitly sum these actual random choices.
--
--   Algorithm 3 returns before-first on an empty success set, chooses fairly between before-first and its unique member on a singleton, and chooses uniformly from $S$ otherwise. Both sample-induced threshold laws are independent of online activations. The threshold run accepts the first active arrival strictly after its threshold and stops. For arrival $\ell$,
--   $$g_\ell(t)=\begin{cases}\prod_{t<j<\ell}(1-p_j)&t<\ell,\\0&t\ge\ell,\end{cases}
--   \qquad \varepsilon_i=p_i/2-\Pr[T=i].$$
--   This product definition does not impose any mass restriction on $p$. The actual-run acceptance probability is defined separately from $g$, so it does not assume any desired guarantee.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Algorithms 2,3 and g, pp.10–13

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_onlineKernel

open Classical

namespace SampleCRS.AlmostGreedy.Supplement

/-- `none` is the paper's threshold 0, before every element. `some i` is
the threshold at the arrival with zero-based label i. -/
abbrev Threshold (n : ℕ) := Option (Fin n)

def sampleSet {n : ℕ} (Y : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Y i = true)

/-- Distribution of the actual random choices of Algorithm 2, conditional on
both sample rows. Each inner sum is the stated independent uniform choice. -/
noncomputable def threshold2Weight {n : ℕ} (Y Z : Fin n → Bool) (t : Threshold n) : ℝ :=
  let S := sampleSet Y
  if S.card = 0 then (if t = none then 1 else 0)
  else if S.card = 1 then
    ∑ j ∈ S, if Z j = true then
      (if t = none then (1 : ℝ) / 2 else 0) + (if t = some j then (1 : ℝ) / 2 else 0)
    else (if t = some j then 1 else 0)
  else (if t = none then (1 : ℝ) / 2 else 0) +
    (1 / 2 : ℝ) * (∑ j ∈ S,
      if Z j = true then (∑ j' ∈ S.erase j, if t = some j' then (1 : ℝ) else 0) /
        ((S.erase j).card : ℝ)
      else (if t = some j then 1 else 0)) / (S.card : ℝ)

/-- Distribution of Algorithm 3's threshold conditional on its sample row. -/
noncomputable def threshold3Weight {n : ℕ} (Y : Fin n → Bool) (t : Threshold n) : ℝ :=
  let S := sampleSet Y
  if S.card = 0 then (if t = none then 1 else 0)
  else if S.card = 1 then
    (if t = none then (1 : ℝ) / 2 else 0) +
      ∑ j ∈ S, if t = some j then (1 : ℝ) / 2 else 0
  else (∑ j ∈ S, if t = some j then (1 : ℝ) else 0) / (S.card : ℝ)

noncomputable def threshold2Law {n : ℕ} (p : Fin n → ℝ) (t : Threshold n) : ℝ :=
  ∑ Y, ∑ Z, activationWeight p Y * activationWeight p Z * threshold2Weight Y Z t

noncomputable def threshold3Law {n : ℕ} (p : Fin n → ℝ) (t : Threshold n) : ℝ :=
  ∑ Y, activationWeight p Y * threshold3Weight Y t

def afterThreshold {n : ℕ} (t : Threshold n) (i : Fin n) : Prop :=
  match t with | none => True | some j => j < i

noncomputable def thresholdRun {n : ℕ} (t : Threshold n) (X : Fin n → Bool) : Finset (Fin n) :=
  (List.ofFn (fun i : Fin n => i)).foldl (fun A i =>
    if A.card = 0 ∧ afterThreshold t i ∧ X i = true then insert i A else A) ∅

/-- The threshold is independent of all online activations: its law multiplies
the entire online product law, rather than depending on that vector. -/
noncomputable def thresholdC {n : ℕ} (p : Fin n → ℝ) (w : Threshold n → ℝ)
    (i : Fin n) : ℝ :=
  (∑ t, w t * activationE p (fun X => if i ∈ thresholdRun t X then 1 else 0)) / p i

noncomputable def g {n : ℕ} (p : Fin n → ℝ) (ell : Fin n) (t : Threshold n) : ℝ :=
  if afterThreshold t ell then
    ∏ j ∈ Finset.univ.filter (fun j => afterThreshold t j ∧ j < ell), (1 - p j)
  else 0

noncomputable def thresholdError {n : ℕ} (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  p i / 2 - threshold3Law p (some i)

def ThresholdFeasible (n : ℕ) : Prop :=
  ∀ (t : Threshold n) (X : Fin n → Bool),
    (thresholdRun t X).card ≤ 1 ∧ ∀ i ∈ thresholdRun t X, X i = true

end SampleCRS.AlmostGreedy.Supplement


