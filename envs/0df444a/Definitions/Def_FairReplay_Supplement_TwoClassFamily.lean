-- Prove2me | Definitions.Def_FairReplay_Supplement_TwoClassFamily
-- name    : FairReplay_Supplement_TwoClassFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:47:31.73807+00:00
-- url     : https://prove2.me/theorems/42ece711-fc52-4b0c-bf2e-7d03561f29f6
-- title:
--   Declared two-class partial-replay family (P19)
-- statement:
--   A **declared two-class family** consists of vertices, each low or high; a set $A$ of high candidate vertices; legal replay groups $S_1,\dots,S_k$, each with at least two vertices; and declared group costs $c_i>0$.
--
--   For $p,s,\tau,d>0$ with $p+s+\tau+d<1$: under the **simple null** all old thresholds equal $p$, low new thresholds equal $p+s$ and high new thresholds equal $p+s+\tau$; the **alternative $x\in A$** raises only $x$'s new threshold by $d$. A query of group $S_i$ draws one tape $U\sim\mathrm{Unif}[0,1]$ and reveals the ordered raw old/new outputs $\big((P_0(v;U),P_1(v;U))\big)_{v\in S_i}$; queries use independent tapes.
--
--   **Formalization Note** The first $k$ actions are the legal groups and one deterministic zero-cost idle action represents making no query, so the zero-query tester remains expressible when $k=0$. Coordinates of vertices outside the queried group are constant.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10.5, pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_thresholdOut
import Definitions.Def_FairReplay_uniformTape
import Definitions.Def_FairReplay_obsCode

open MeasureTheory

namespace FairReplay.Supplement

/-- **The declared two-class partial-replay topology** (Sah, Zhang, Lian, *Testing Fairness of
Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, §10.5, pp.18–19 (PDF pp.20–21)): "Here C records which legal groups provide
same-background control observations and R records boundary-only observations, with positive
declared group costs c. Every legal group has at least two vertices and reveals its ordered raw
old/new transcript under one common tape".

A `TwoClassFamily` consists of `n` vertices, each low or high (`high`), a set `A` of high candidate
vertices, `k` legal groups `S i` (each with at least two vertices) and their declared costs `c i > 0`.

**Formalization Note** Groups are finite sets of vertices; two groups may coincide. -/
structure TwoClassFamily where
  /-- Number of vertices. -/
  n : ℕ
  /-- Number of legal replay groups. -/
  k : ℕ
  /-- The class of each vertex (`true` = high). -/
  high : Fin n → Bool
  /-- The candidate set: the vertices that an alternative may change. -/
  A : Finset (Fin n)
  /-- The legal replay groups. -/
  S : Fin k → Finset (Fin n)
  /-- The declared group costs. -/
  c : Fin k → ℝ
  /-- Candidates are high vertices. -/
  A_high : ∀ x ∈ A, high x = true
  /-- Every legal group has at least two vertices. -/
  S_card : ∀ i, 2 ≤ (S i).card
  /-- Declared costs are positive. -/
  c_pos : ∀ i, 0 < c i

namespace TwoClassFamily

/-- New threshold of vertex `v` in the P19 family: `p + s` for a low vertex, `p + s + τ` for a high
vertex, plus `d` at the changed candidate `x` when `alt = some x`. -/
def newThr (F : TwoClassFamily) (p s τ d : ℝ) (alt : Option (Fin F.n)) (v : Fin F.n) : ℝ :=
  p + s + (if F.high v then τ else 0) + (if alt = some v then d else 0)

/-- The ordered raw old/new outputs of one query of group `i` on the tape value `U`: coordinate
`finProdFinEquiv (v, j)` is `Pj(v;U)` for `v ∈ S i` (old threshold `p`, new threshold `newThr`), and
the constant `false` for `v ∉ S i`. -/
noncomputable def groupObs (F : TwoClassFamily) (p s τ d : ℝ) (alt : Option (Fin F.n))
    (i : Fin F.k) (U : ℝ) : Fin (F.n * 2) → Bool := fun j =>
  if (finProdFinEquiv.symm j).1 ∈ F.S i then
    (if (finProdFinEquiv.symm j).2 = 0 then thresholdOut p U
      else thresholdOut (F.newThr p s τ d alt (finProdFinEquiv.symm j).1) U)
  else false

lemma measurable_groupObs (F : TwoClassFamily) (p s τ d : ℝ) (alt : Option (Fin F.n))
    (i : Fin F.k) : Measurable (fun U : ℝ => F.groupObs p s τ d alt i U) := by
  rw [measurable_pi_iff]
  intro j
  simp only [groupObs]
  split_ifs <;> first | exact measurable_thresholdOut _ | exact measurable_const

/-- The law of the coded observation of one query of group `i`. -/
noncomputable def groupLaw (F : TwoClassFamily) (p s τ d : ℝ) (alt : Option (Fin F.n))
    (i : Fin F.k) : Measure ℝ :=
  uniformTape.map (fun U => obsCode (F.groupObs p s τ d alt i U))

instance groupLaw.instIsProbabilityMeasure (F : TwoClassFamily) (p s τ d : ℝ)
    (alt : Option (Fin F.n)) (i : Fin F.k) : IsProbabilityMeasure (F.groupLaw p s τ d alt i) :=
  Measure.isProbabilityMeasure_map
    (measurable_obsCode.comp (F.measurable_groupObs p s τ d alt i)).aemeasurable

/-- **The P19 partial-replay model** (§10.5, pp.18–19): "Under the simple null all old thresholds
equal p, low new thresholds equal p + s, and high new thresholds equal p + s + τ; alternative x
raises only high candidate x by d."

`F.groupModel p s τ d alt` is the sequential-sampling environment whose first `F.k` actions are the
legal groups; querying group `i` reveals the coded ordered old/new transcript of its members on one
fresh uniform tape. The final action is a deterministic idle action. It makes the sequential model
inhabited when the legal-group family is empty and carries no information or declared cost.
`alt = none` is the simple null and `alt = some x` the alternative changing `x`.

**Formalization Note** The theorems use alternatives `some x` with `x ∈ A` only. The idle action
represents making no group query; it is needed only to encode the zero-query tester when `k = 0`. -/
noncomputable def groupModel (F : TwoClassFamily) (p s τ d : ℝ) (alt : Option (Fin F.n)) :
    BanditAlgorithm.StochasticBandit (F.k + 1) where
  P i := if h : (i : ℕ) < F.k then F.groupLaw p s τ d alt ⟨i, h⟩ else Measure.dirac 0
  prob i := by
    split <;> infer_instance

end TwoClassFamily

end FairReplay.Supplement


