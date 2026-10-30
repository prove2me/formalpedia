-- Prove2me | Definitions.Def_SimchiLeviAddOn_Learning_Online
-- name    : SimchiLeviAddOn_Learning_Online
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:59:04.834271+00:00
-- url     : https://prove2.me/theorems/dcc63a43-f452-46d9-944b-d885786c3d2a
-- title:
--   Algorithm 2: four counters, trajectory law, episodes, events and regret
-- statement:
--   Histories record posted policies, primary Bernoulli purchases, observed add-on outcomes and the controller's private episode-end decisions. Primary counters count periods using their price; add-on counters count core-purchase opportunities under the relevant selected or ordinary price. Means and counters initialize at zero. At episode start t each positive-count UCB is min(1, empirical mean + sqrt(2 log(t)/count)), with arbitrary causal [0,1] completions at zero counts. Algorithm 1 uses K=ceil(sqrt(t)/epsilon). Its output is held until a positive-start associated counter reaches or exceeds twice its start value, or a causal zero-start completion ends the episode. The latter must terminate almost surely after positive time, with no assumed moment bound. Conditional independent Bernoulli observations and randomized history-dependent actions construct a finite trajectory law. Regret is expected cumulative benchmark minus actual revenue. The literal bad event has radius 2 log(t)/count, without a square root, with arbitrary history-dependent Boolean completions at zero counts. Contributions use the event at the actual episode start and truncate at T. Expected full episode length is an extended nonnegative tail sum.
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Sections 4.1-4.2, pp. 14-19 (same PDF pages), Algorithm 2, equations (6), (8)-(10)

import Definitions.Def_SimchiLeviAddOn_Learning_Offline

open scoped BigOperators ENNReal
open Filter

namespace SimchiLeviAddOn.Learning

/-- Only observed add-on outcomes are stored. Entries without a core purchase are false. -/
structure Observation (X : Market) where
  core : Fin X.N → Bool
  primary : Fin X.M → Bool
  addon : Fin X.N → Fin X.M → Bool
  deriving DecidableEq, Fintype

structure Record (X : Market) where
  policy : Policy X
  observation : Observation X
  stop : Bool
  deriving DecidableEq, Fintype

abbrev History (X : Market) := List (Record X)

def bit (b : Bool) : ℕ := if b then 1 else 0

def corePurchases {X : Market} (o : Observation X) : ℕ := ∑ n, bit (o.core n)

def associated {X : Market} (p : Policy X) : Parameter X → Prop
  | .core n q => p.core n = q
  | .primary m q => p.original m = q
  | .discounted m q => p.selected m = true ∧ p.discount m = q
  | .ordinary m q => p.selected m = false ∧ p.original m = q

noncomputable def opportunities {X : Market} (r : Record X) : Parameter X → ℕ := by
  classical
  exact fun k => if associated r.policy k then
    match k with
    | .core _ _ => 1
    | .primary _ _ => 1
    | .discounted _ _ => corePurchases r.observation
    | .ordinary _ _ => corePurchases r.observation
    else 0

noncomputable def successes {X : Market} (r : Record X) : Parameter X → ℕ := by
  classical
  exact fun k => if associated r.policy k then
    match k with
    | .core n _ => bit (r.observation.core n)
    | .primary m _ => bit (r.observation.primary m)
    | .discounted m _ => ∑ n, if r.observation.core n then bit (r.observation.addon n m) else 0
    | .ordinary m _ => ∑ n, if r.observation.core n then bit (r.observation.addon n m) else 0
    else 0

noncomputable def count {X : Market} (h : History X) (k : Parameter X) : ℕ :=
  (h.map (fun r => opportunities r k)).sum

noncomputable def empirical {X : Market} (h : History X) (k : Parameter X) : ℝ :=
  if count h k = 0 then 0 else ((h.map (fun r => successes r k)).sum : ℝ) / count h k

/-- Length of the prefix through the last completed episode, zero if none has ended. -/
def lastStop {X : Market} (h : History X) : ℕ :=
  ((h.zipIdx.filter (fun r => r.1.stop)).map (fun r => r.2 + 1)).foldl max 0

def episodeBase {X : Market} (h : History X) : History X := h.take (lastStop h)

def episodeStart {X : Market} (h : History X) : ℕ := lastStop h + 1

/-- Number of episodes intersecting a finite history (a stop at its final period adds none). -/
def episodeCount {X : Market} (h : History X) : ℕ :=
  if h.isEmpty then 0 else 1 + (h.dropLast.map (fun r => bit r.stop)).sum

/-- Length of the episode starting at zero-based position s, truncated at this history's end. -/
def truncatedLength {X : Market} (h : History X) (s : ℕ) : ℕ :=
  min (h.length - s) (1 + ((h.drop s).takeWhile (fun r => !r.stop)).length)

noncomputable def resolution (ε : ℝ) (t : ℕ) : ℕ := ⌈Real.sqrt t / ε⌉₊

/-- All positive-count formulas are literal. Every [0,1] value is admitted at count zero. -/
def UCBCompatible (X : Market) (h : History X) (u : Tables X) : Prop :=
  IsDemand X u ∧ ∀ k, 0 < count h k →
    u k = min 1 (empirical h k + Real.sqrt (2 * Real.log (h.length + 1) / count h k))

/-- New policies come from Algorithm 1; between episode starts the last policy is held. -/
def AllowedPolicy (X : Market) (ε : ℝ) (h : History X) (p : Policy X) : Prop :=
  if lastStop h = h.length then
    ∃ u : Tables X, UCBCompatible X h u ∧
      IsOfflineOutput X u (resolution ε (h.length + 1)) p
  else ∀ r ∈ h.getLast?, p = r.policy

noncomputable def positiveDoubled (X : Market) (h : History X)
    (p : Policy X) (o : Observation X) : Prop :=
  ∃ k, associated p k ∧ 0 < count (episodeBase h) k ∧
    2 * count (episodeBase h) k ≤ count (h ++ [⟨p, o, false⟩]) k

noncomputable def zeroAssociated (X : Market) (h : History X) (p : Policy X) : Prop :=
  ∃ k, associated p k ∧ count (episodeBase h) k = 0

/-- Independent private action and stopping randomization, conditional on observed history.
PMF is Mathlib's general probability-mass object, not a paper-specific replacement. -/
structure Controller (X : Market) where
  action : History X → PMF (Policy X)
  endProbability : History X → Policy X → Observation X → Set.Icc (0 : ℝ) 1

noncomputable def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Fresh independent primary samples followed by one independent add-on sample per core purchase.
The deterministic false marker carries no unobserved outcome to the controller. -/
noncomputable def observationMass (X : Market) (d : Tables X) (p : Policy X)
    (o : Observation X) : ℝ :=
  (∏ n, bernoulliMass (d (.core n (p.core n))) (o.core n)) *
  (∏ m, bernoulliMass (d (.primary m (p.original m))) (o.primary m)) *
  ∏ n, ∏ m, if o.core n then
    bernoulliMass (if p.selected m then d (.discounted m (p.discount m))
      else d (.ordinary m (p.original m))) (o.addon n m)
    else if o.addon n m then 0 else 1

/-- The finite one-step kernel includes the post-observation episode decision. -/
noncomputable def stepMass (X : Market) (d : Tables X) (A : Controller X)
    (h : History X) (r : Record X) : ℝ :=
  (A.action h r.policy).toReal * observationMass X d r.policy r.observation *
    bernoulliMass (A.endProbability h r.policy r.observation).val r.stop

noncomputable def extensionMass (X : Market) (d : Tables X) (A : Controller X) :
    History X → History X → ℝ
  | _, [] => 1
  | h, r :: rs => stepMass X d A h r * extensionMass X d A (h ++ [r]) rs

/-- Expectation under the recursively constructed finite-history law. All sums are finite. -/
noncomputable def expectFrom (X : Market) (d : Tables X) (A : Controller X)
    (h : History X) (T : ℕ) (f : History X → ℝ) : ℝ :=
  ∑ z : Fin T → Record X, extensionMass X d A h (List.ofFn z) * f (h ++ List.ofFn z)

/-- Survival for k more periods without ending the current episode. -/
noncomputable def survival (X : Market) (d : Tables X) (A : Controller X)
    (h : History X) (k : ℕ) : ℝ := by
  classical
  exact expectFrom X d A h k (fun h' =>
    if ∀ r ∈ h'.drop h.length, r.stop = false then 1 else 0)

/-- Operational constraints only: no optimism, concentration, approximation or regret guarantees.
The limit asserts a.s. finite positive stopping, and imposes no moment bound. -/
def IsAlgorithm (X : Market) (d : Tables X) (ε : ℝ) (A : Controller X) : Prop :=
  (∀ h p, p ∈ (A.action h).support → AllowedPolicy X ε h p) ∧
  (∀ h p o, p ∈ (A.action h).support →
    (positiveDoubled X h p o → (A.endProbability h p o).val = 1) ∧
    (¬positiveDoubled X h p o → ¬zeroAssociated X h p →
      (A.endProbability h p o).val = 0)) ∧
  (∀ h, 0 < extensionMass X d A [] h →
    Tendsto (survival X d A h) atTop (nhds 0))

/-- All history-measurable Boolean completions of the undefined count-zero comparison. -/
abbrev EventCompletion (X : Market) := History X → Parameter X → Bool

noncomputable def badEvent (X : Market) (d : Tables X) (e : EventCompletion X)
    (h : History X) : Prop :=
  ∃ k, if count h k = 0 then e h k = true else
    |empirical h k - d k| > 2 * Real.log (h.length + 1) / count h k

/-- Signed expected pseudo-regret, evaluated on the algorithm's actual menu tuples. -/
noncomputable def regret (X : Market) (d : Tables X) (A : Controller X) (T : ℕ) : ℝ :=
  expectFrom X d A [] T (fun h =>
    (h.map (fun r => optimum X d - revenue X d r.policy)).sum)

/-- Indicator-weighted episode regret. Grouping periods with the same episode start gives
(R* - R(Pi_tau)) times the truncated episode length, with its start-history event. -/
noncomputable def eventRegret (X : Market) (d : Tables X) (A : Controller X)
    (e : EventCompletion X) (bad : Bool) (T : ℕ) : ℝ := by
  classical
  exact expectFrom X d A [] T (fun h =>
    ∑ i : Fin T,
      if decide (badEvent X d e (episodeBase (h.take i.val))) = bad then
        match h[i.val]? with
        | some r => optimum X d - revenue X d r.policy
        | none => 0
      else 0)

/-- Conditional expected length of a fresh episode after observed starting history h.
Tail-sum expectation in ENNReal retains a possible infinite mean. -/
noncomputable def expectedLength (X : Market) (d : Tables X) (A : Controller X)
    (h : History X) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (survival X d A h k)

end SimchiLeviAddOn.Learning


