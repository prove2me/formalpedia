-- Prove2me | Definitions.Def_SelfAdaptingFNR_FNR
-- name    : SelfAdaptingFNR_FNR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:38:33.384671+00:00
-- url     : https://prove2.me/theorems/23141910-fcd1-447e-90fd-e3858f46383e
-- title:
--   The feasibility network relaxation FNR and $z^{\mathrm{FNR}}$
-- statement:
--   Let $(\mathcal N_t)_{t\in\mathcal T}$ be layered networks. For a node $v\in\mathcal V_{t,j}$ let $\mathcal E^+_t(v)$ be the set of labels $(s_j,a_j)$ of the arcs leaving $v$, $\mathcal E^-_t(v)$ the set of node–state–action triples $(v',s_{j-1},a_{j-1})$ of the arcs entering $v$, and $\mathcal V^+_{t,j}(s_j,a_j)=\{v\in\mathcal V_{t,j}:(s_j,a_j)\in\mathcal E^+_t(v)\}$.
--
--   The **feasibility network relaxation (FNR)** has the D-LAG variables $x$ and variables $y_{t,j}(v,s_j,a_j)$ for $v\in\mathcal V_{t,j}$:
--   $$\max_{x,y}\ \sum_{t\in\mathcal T}\sum_{j\in\mathcal J}\sum_{s_j\in\mathcal S_{t,j}}\sum_{a_j\in\mathcal A_{t,j}(s_j)}r_{t,j}(s_j,a_j)\,x_{t,j}(s_j,a_j)$$
--   subject to
--   1. (17) the component flow constraints (7)–(8), (10);
--   2. (18) $x_{t,j}(s_j,a_j)=\sum_{v\in\mathcal V^+_{t,j}(s_j,a_j)}y_{t,j}(v,s_j,a_j)$ for all $t,j,s_j$ and $a_j\in\mathcal A_{t,j}(s_j)$;
--   3. (19) $\sum_{(s_j,a_j)\in\mathcal E^+_t(v)}y_{t,j}(v,s_j,a_j)=\sum_{(v',s_{j-1},a_{j-1})\in\mathcal E^-_t(v)}y_{t,j-1}(v',s_{j-1},a_{j-1})$ for all $t$, $j\in\mathcal J\setminus\{1\}$, $v\in\mathcal V_{t,j}$;
--   4. (20) $y\ge0$.
--
--   $z^{\mathrm{FNR}}$ is its optimal value. FNR replaces the averaged linking constraints (9) of D-LAG by flow constraints on the networks.
--
--   **Formalization Note** The networks form a family indexed by all periods; only those with $t<T$ enter. The printed (19) has $y_{t,j}$ on the right and the printed $\mathcal E^-_t(v)$ has $a_{j-1}\in\mathcal A_{t,j}(s_{j-1})$; the incoming arcs belong to component $j-1$, so they read $y_{t,j-1}$ and $\mathcal A_{t,j-1}(s_{j-1})$. The variables $y$ are indexed by all node–state–action triples, as on p.16; a triple that carries no arc occurs only in (20). $z^{\mathrm{FNR}}$ is an `EReal` supremum.
-- source:
--   S. Nadarajah, A. A. Cire, Self-Adapting Network Relaxations for Weakly Coupled Markov Decision Processes, SSRN 4081430 (version of Aug. 2023), https://ssrn.com/abstract=4081430, §4.1, pp.16–17, $\mathcal E^\pm_t(v)$, $\mathcal V^+_{t,j}$, (FNR), (17)–(20), definition of $z^{\mathrm{FNR}}$

import Mathlib
import Definitions.Def_SelfAdaptingFNR_DLAG
import Definitions.Def_SelfAdaptingFNR_FeasibilityNetwork

open scoped Classical

namespace SelfAdaptingFNR

variable {J K T : ℕ}

/-- An **FNR arc variable** for a network family `N`: `y t j v sⱼ aⱼ = y_{t,j}(v, sⱼ, aⱼ)` for a
node `v ∈ 𝒱_{t,j}` (layer `j.castSucc`) and a component pair `(sⱼ, aⱼ)`. -/
abbrev WDP.ArcVar (M : WDP J K T) (N : (t : ℕ) → LayeredNetwork M t) : Type :=
  (t : ℕ) → (j : Fin J) → (N t).V j.castSucc → M.S t j → M.Act t j → ℝ

/-- `𝒱⁺_{t,j}(sⱼ,aⱼ) := {v ∈ 𝒱_{t,j} : (sⱼ,aⱼ) ∈ ℰ⁺_t(v)}`, the nodes with an outgoing arc
labelled `(sⱼ, aⱼ)` (p.16). -/
noncomputable def LayeredNetwork.outNodes {M : WDP J K T} {t : ℕ} (N : LayeredNetwork M t)
    (j : Fin J) (s : M.S t j) (a : M.Act t j) : Finset (N.V j.castSucc) :=
  Finset.univ.filter fun v => (N.succ j v s a).isSome

/-- Feasibility for **(FNR)**, the feasibility network relaxation of Nadarajah & Cire, SSRN 4081430
(Aug. 2023), §4.1, p.17, for the family of networks `N = (𝒩_t)_{t ∈ 𝒯}`:
* (17) the D-LAG flow constraints (7)–(8), (10) on `x`;
* (18) `x_{t,j}(sⱼ,aⱼ) = ∑_{v ∈ 𝒱⁺_{t,j}(sⱼ,aⱼ)} y_{t,j}(v,sⱼ,aⱼ)` for `t ∈ 𝒯`, `j ∈ 𝒥`,
  `sⱼ ∈ 𝒮_{t,j}`, `aⱼ ∈ 𝒜_{t,j}(sⱼ)`;
* (19) flow conservation `∑_{(sⱼ,aⱼ) ∈ ℰ⁺_t(v)} y_{t,j}(v,sⱼ,aⱼ) =
  ∑_{(v′,s_{j−1},a_{j−1}) ∈ ℰ⁻_t(v)} y_{t,j−1}(v′,s_{j−1},a_{j−1})` for `t ∈ 𝒯`, `j ∈ 𝒥 ∖ {1}`,
  `v ∈ 𝒱_{t,j}`;
* (20) `y ≥ 0`.

Here `ℰ⁺_t(v)` is the set of labels of the arcs leaving `v` and `ℰ⁻_t(v)` the set of
node–state–action triples of the arcs entering `v` (p.16).

**Formalization Note.** In (19) the paper's node layer `j ∈ {2,…,J}` is the layer `j.succ` of the
0-based component `j` with `j + 1 < J`; the outgoing arcs belong to component `j + 1`, the
incoming arcs to component `j`. The paper prints `y_{t,j}(v′, s_{j−1}, a_{j−1})` on the right of
(19) and `𝒜_{t,j}(s_{j−1})` in `ℰ⁻_t(v)`; the incoming arcs are those of component `j − 1`, so the
variable is `y_{t,j−1}` and the action set `𝒜_{t,j−1}(s_{j−1})` (typos). The variables `y` are
indexed by every node–state–action triple, as on p.16 ("for all `v ∈ 𝒱_{t,j}`, `sⱼ ∈ 𝒮_{t,j}`, and
`aⱼ ∈ 𝒜_{t,j}(sⱼ)`"); a triple that carries no arc occurs in no constraint other than (20) and in
no objective. -/
def WDP.FNRFeasible (M : WDP J K T) (N : (t : ℕ) → LayeredNetwork M t)
    (x : M.FlowVar) (y : M.ArcVar N) : Prop :=
  M.FlowConstraints x ∧
  (∀ t, t < T → ∀ j (s : M.S t j), ∀ a ∈ M.A t j s,
    x t j s a = ∑ v ∈ (N t).outNodes j s a, y t j v s a) ∧
  (∀ t, t < T → ∀ (j : Fin J) (hj : (j : ℕ) + 1 < J) (v : (N t).V j.succ),
    ∑ s : M.S t ⟨j + 1, hj⟩, ∑ a ∈ M.A t ⟨j + 1, hj⟩ s,
        (if ((N t).succ ⟨j + 1, hj⟩ v s a).isSome then y t ⟨j + 1, hj⟩ v s a else 0) =
      ∑ v' : (N t).V j.castSucc, ∑ s' : M.S t j, ∑ a' ∈ M.A t j s',
        (if (N t).succ j v' s' a' = some v then y t j v' s' a' else 0)) ∧
  (∀ t, t < T → ∀ j (v : (N t).V j.castSucc) (s : M.S t j), ∀ a ∈ M.A t j s, 0 ≤ y t j v s a)

/-- `z^FNR`, the **optimal value of FNR** (p.17) for the network family `N`: the supremum in
`EReal` of the D-LAG/FNR objective `∑_t ∑_j ∑_{sⱼ} ∑_{aⱼ} r_{t,j}(sⱼ,aⱼ) x_{t,j}(sⱼ,aⱼ)` over the
FNR feasible set. -/
noncomputable def WDP.zFNR (M : WDP J K T) (N : (t : ℕ) → LayeredNetwork M t) : EReal :=
  sSup ((fun xy : M.FlowVar × M.ArcVar N => (M.flowObjective xy.1 : EReal)) ''
    {xy | M.FNRFeasible N xy.1 xy.2})

end SelfAdaptingFNR


