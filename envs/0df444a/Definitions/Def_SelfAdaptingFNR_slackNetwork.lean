-- Prove2me | Definitions.Def_SelfAdaptingFNR_slackNetwork
-- name    : SelfAdaptingFNR_slackNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:38:34.591522+00:00
-- url     : https://prove2.me/theorems/5dfcfda9-0dfd-457a-827f-be0795f29b01
-- title:
--   The slack set $\mathscr F^V_t$ and the slack network
-- statement:
--   For a period $t$, a WDP pair $(s,a)$ with component-feasible actions and $j=2,\dots,J+1$, let $u_{t,k,j}=b_k-\sum_{j'=1}^{j-1}C_{t,k,j'}(s_{j'},a_{j'})$ be the remaining capacity (**slack**) of the $k$-th linking constraint after fixing the first $j-1$ component pairs, and $u_{t,k,1}=b_k$. The **extended slack set** is
--   $$\mathscr F^V_t=\Big\{(u,s,a)\in\mathbb R^{K\times(J+1)}\times\mathcal S_t\times\textstyle\times_j\mathcal A_{t,j}(s_j):\ u_{t,k,1}=b_k,\ u_{t,k,j+1}=u_{t,k,j}-C_{t,k,j}(s_j,a_j),\ u_{t,k,J+1}\ge0\ \ \forall k,j\Big\}.$$
--
--   The **slack network** of period $t$ has, in layer $j$, one node for each distinct value of the slack vector $u_{t,j}=(u_{t,k,j})_{k\in\mathcal K}$ over the feasible pairs $\mathscr F_t$ (the first layer is $\{b\}$), and an arc labelled $(s_j,a_j)$, $a_j\in\mathcal A_{t,j}(s_j)$, from the node $u_{t,j}$ to the node $u_{t,j+1}$ exactly when $u_{t,k,j+1}=u_{t,k,j}-C_{t,k,j}(s_j,a_j)$ for all $k$.
--
--   Its nodes track resource availability; Corollary 1 shows that it is a feasibility network.
--
--   **Formalization Note** Slack layers are 0-based. The paper's $\mathscr F^V_t$ takes $a\in\mathcal A_t(s)$, which already contains the linking constraints; here $a$ ranges over the component action sets, the content of the proof of Proposition 1. The paper writes "$u_{t+1,j}$" for the slack of the head node; it is $u_{t,j+1}$. The first layer is $\{b\}$, which is the set of values of $u_{t,1}$ on $\mathscr F_t$ whenever $\mathscr F_t\ne\emptyset$.
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §3.1, pp.11–12, slacks $u_{t,k,j}$, (11), the slack network

import Mathlib
import Definitions.Def_SelfAdaptingFNR_FeasibilityNetwork

open scoped Classical

namespace SelfAdaptingFNR

variable {J K T : ℕ}

/-- The **extended slack set** `𝓕^V_t` of Proposition 1 (Nadarajah & Cire, SSRN 4081430,
Aug. 2023, §3.1, (11), pp.11–12): triples `(u, s, a)` with `u ∈ ℝ^{K×(J+1)}` and component-feasible
`a ∈ ×ⱼ 𝒜_{t,j}(sⱼ)` such that
`u_{t,k,1} = b_k`, `u_{t,k,j+1} = u_{t,k,j} − C_{t,k,j}(sⱼ,aⱼ)` for all `k, j`, and
`u_{t,k,J+1} ≥ 0` for all `k`.

**Formalization Note.** `u k i` is `u_{t,k,i+1}` (slack layers `Fin (J + 1)`, 0-based). The paper
prints `a ∈ 𝒜_t(s)`, which already contains the linking constraints and makes the condition
`u_{t,k,J+1} ≥ 0` redundant; here `a` ranges over the component action sets only, which is the
content the proof of Proposition 1 (p.ec5) establishes. -/
def WDP.slackSet (M : WDP J K T) (t : ℕ) :
    Set ((Fin K → Fin (J + 1) → ℝ) × ((j : Fin J) → M.S t j) × ((j : Fin J) → M.Act t j)) :=
  {q | (∀ j, q.2.2 j ∈ M.A t j (q.2.1 j)) ∧
    (∀ k, q.1 k 0 = M.b k) ∧
    (∀ k (j : Fin J), q.1 k j.succ = q.1 k j.castSucc - M.C t k j (q.2.1 j) (q.2.2 j)) ∧
    (∀ k, 0 ≤ q.1 k (Fin.last J))}

/-- The slack vector `u_{t,i} = (b_k − ∑_{j′ < i} C_{t,k,j′}(s_{j′},a_{j′}), k ∈ 𝒦)` after fixing the
first `i` component state–action pairs (p.11), for the 0-based layer `i : Fin (J + 1)`. -/
noncomputable def WDP.slackValue (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (i : Fin (J + 1)) : Fin K → ℝ :=
  fun k => M.b k - ∑ j ∈ Finset.univ.filter (fun j : Fin J => (j : ℕ) < (i : ℕ)),
    M.C t k j (s j) (a j)

/-- The node values of layer `i` of the slack network (p.12): the distinct values taken by the
slack vector `u_{t,i}` over `𝓕_t`; the first layer is `{b}` (`u_{t,k,1} := b_k`). -/
noncomputable def WDP.slackLayer (M : WDP J K T) (t : ℕ) (i : Fin (J + 1)) :
    Finset (Fin K → ℝ) :=
  if (i : ℕ) = 0 then {M.b} else
    (Finset.univ.filter fun p => p ∈ M.feasiblePairs t).image
      fun p => M.slackValue t p.1 p.2 i

/-- The **slack network** `𝒩_t` of period `t` (p.12): layer `i` consists of the distinct slack
vectors of `slackLayer`, and an arc labelled `(sⱼ, aⱼ)`, `aⱼ ∈ 𝒜_{t,j}(sⱼ)`, joins the node
`u_{t,j}` to the node `u_{t,j+1}` iff `u_{t,k,j+1} = u_{t,k,j} − C_{t,k,j}(sⱼ,aⱼ)` for all `k`.

**Formalization Note.** The paper writes "the slacks `u_{t,j}` and `u_{t+1,j}` associated with
`vⱼ` and `vⱼ₊₁`"; the head's slack is `u_{t,j+1}` (typo). The first layer is `{b}` as in the
paper's `u_{t,k,1} := b_k`; it equals the set of values of `u_{t,1}` over `𝓕_t` whenever
`𝓕_t ≠ ∅`. -/
noncomputable def WDP.slackNetwork (M : WDP J K T) (t : ℕ) : LayeredNetwork M t where
  V i := {u // u ∈ M.slackLayer t i}
  instFintypeV _ := inferInstance
  root := ⟨M.b, by simp [WDP.slackLayer]⟩
  root_unique v := by
    obtain ⟨u, hu⟩ := v
    simp only [WDP.slackLayer, Fin.val_zero, if_true, Finset.mem_singleton] at hu
    exact Subtype.ext hu
  succ j v s a :=
    if h : a ∈ M.A t j s ∧ (fun k => v.1 k - M.C t k j s a) ∈ M.slackLayer t j.succ then
      some ⟨fun k => v.1 k - M.C t k j s a, h.2⟩
    else none
  succ_feasible j v s a v' h := by
    by_contra hc
    simp [hc] at h

end SelfAdaptingFNR


