-- Prove2me | Definitions.Def_AggCG_Supplement_matchLoss
-- name    : AggCG_Supplement_matchLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:23:22.010364+00:00
-- url     : https://prove2.me/theorems/1c780f56-1ad0-4c5d-8024-0be766730548
-- title:
--   Normalized regret of the dyadic online-matching policy
-- statement:
--   The online-arrival-weighted matching instance has $T$ prefix arrivals of weight $1/T$ with neighbor pair $\{A_j,B_j\}$ and one final probe of weight one. A dyadic score-mixture policy uses its scalar parameter to choose a prefix bit at each stage, then matches the probe to a free neighbor if possible.
--
--   Its loss is normalized regret $1-\mathrm{ALG}_\theta/\mathrm{OPT}$.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), §G.1.1–G.1.3, pp.40–41, PDF pp.41–42

import Mathlib

namespace AggCG.Supplement

/-- An instance of online-arrival-weighted bipartite matching over the offline vertex set `V`
(Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and
Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §G.1.1, p.40, PDF p.41):
`k` online vertices arriving in order `0, …, k − 1`, each with a neighbourhood and a weight. -/
structure OnlineInst (V : Type) where
  /-- Number of online arrivals. -/
  k : ℕ
  /-- Neighbourhood of each arrival. -/
  nbr : Fin k → Finset V
  /-- Weight of each arrival. -/
  w : Fin k → ℝ

namespace OnlineInst

variable {V : Type}

/-- A matching: each online vertex is matched to at most one neighbour, and no offline vertex twice. -/
def IsMatching (I : OnlineInst V) (μ : Fin I.k → Option V) : Prop :=
  (∀ i v, μ i = some v → v ∈ I.nbr i) ∧ ∀ i i' v, μ i = some v → μ i' = some v → i = i'

/-- The reward of a matching: the total weight of the matched online vertices. -/
noncomputable def reward (I : OnlineInst V) (μ : Fin I.k → Option V) : ℝ :=
  ∑ i, if (μ i).isSome then I.w i else 0

/-- `OPT(x)`: the largest reward of a matching (p.40: "the weight of the maximum offline matching").

**Formalization Note** For a finite `V` the set of rewards is finite and contains `0` (the empty
matching), so this supremum is a maximum. -/
noncomputable def opt (I : OnlineInst V) : ℝ :=
  sSup {r | ∃ μ, I.IsMatching μ ∧ r = I.reward μ}

end OnlineInst

/-- The offline vertices `A_0, B_0, …, A_{T−1}, B_{T−1}` of §G.1.1: `(j, true)` is `A_j` and
`(j, false)` is `B_j` (the paper's `A_{j+1}, B_{j+1}`). -/
abbrev Offline (T : ℕ) := Fin T × Bool

/-- The evaluation instance with probe neighbourhood `S` (§G.1.1, p.40): prefix arrivals `u_j` with
`N(u_j) = {A_j, B_j}` and weight `1/T`, then one final arrival of weight `1` with neighbourhood `S`. -/
noncomputable def probeInst (T : ℕ) (S : Finset (Offline T)) : OnlineInst (Offline T) where
  k := T + 1
  nbr := fun i => if h : i.val < T then {(⟨i.val, h⟩, true), (⟨i.val, h⟩, false)} else S
  w := fun i => if i.val < T then 1 / (T : ℝ) else 1

/-- The dyadic interval `[L, R]` maintained by the policy before arrival `u_j` (§G.1.2, p.40): it starts
at `[0, 1]`; at stage `j` the scores are `s_θ(A_j) = (1 − θ)·0 + θ·1` and `s_θ(B_j) = (1 − θ)m_j + θ m_j`
with `m_j = (L + R)/2`; the policy takes `A_j` iff its score is larger (ties to `B_j`) and moves to the
upper half after `A_j`, the lower half after `B_j`. -/
noncomputable def dyadicInterval (θ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | j + 1 =>
    let LR := dyadicInterval θ j
    let m := (LR.1 + LR.2) / 2
    if (1 - θ) * m + θ * m < (1 - θ) * 0 + θ * 1 then (m, LR.2) else (LR.1, m)

/-- The decision bit of stage `j`: `true` iff the policy matches `u_j` to `A_j`, i.e. iff
`(1 − θ)·0 + θ·1 > m_j` (ties to `B_j`). -/
noncomputable def takesA (θ : ℝ) (j : ℕ) : Bool :=
  let LR := dyadicInterval θ j
  let m := (LR.1 + LR.2) / 2
  decide ((1 - θ) * m + θ * m < (1 - θ) * 0 + θ * 1)

open Classical in
/-- The matching produced by the policy with parameter `θ` on `probeInst T S` (§G.1.2): `u_j` is matched
to `A_j` or `B_j` by `takesA θ j`, and the final arrival to a free neighbour if one exists (p.41: "matched
to any free neighbor"). -/
noncomputable def policyMatching (T : ℕ) (θ : ℝ) (S : Finset (Offline T)) :
    Fin (T + 1) → Option (Offline T) :=
  fun i =>
    if h : i.val < T then some (⟨i.val, h⟩, takesA θ i.val)
    else
      let free := S.filter fun v => v.2 ≠ takesA θ v.1.val
      if hf : free.Nonempty then some hf.choose else none

/-- The normalized regret `f_θ(x) = 1 − ALG_θ(x)/OPT(x)` of the policy on `probeInst T S`
(§G.1.1, p.40). -/
noncomputable def matchLoss (T : ℕ) (θ : ℝ) (S : Finset (Offline T)) : ℝ :=
  1 - (probeInst T S).reward (policyMatching T θ S) / (probeInst T S).opt

/-- The instance domain `X_T` of Theorem G.1 (p.41): a nonempty probe neighbourhood with at most three
offline vertices and at most one from each pair `{A_j, B_j}`. -/
def ValidProbe (T : ℕ) (S : Finset (Offline T)) : Prop :=
  S.Nonempty ∧ S.card ≤ 3 ∧ ∀ j : Fin T, ¬ ((j, true) ∈ S ∧ (j, false) ∈ S)

/-- The class `F_T = {x ↦ f_θ(x) : θ ∈ [0, 1]}` on `X_T`. -/
def matchClass (T : ℕ) : Set ({S : Finset (Offline T) // ValidProbe T S} → ℝ) :=
  {g | ∃ θ ∈ Set.Icc (0 : ℝ) 1, ∀ S, g S = matchLoss T θ S.1}

end AggCG.Supplement


