-- Prove2me | Definitions.Def_LNTopology_Hermetization_hermetize
-- name    : LNTopology_Hermetization_hermetize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:48.438701+00:00
-- url     : https://prove2.me/theorems/c5136699-3f15-4c57-960b-5795695b5567
-- title:
--   Hermetization of a node set
-- statement:
--   The **hermetization** of a node set $U$ in a network with flows $\Lambda$ is the network obtained by (i) deleting all channels among nodes of $U$; (ii) adding a new node $v_0$; (iii) connecting every node of $U$ to $v_0$ with a channel that summarizes its flows towards the other nodes of $U$. Its node set is $V\cup\{v_0\}$ and its flows $\lambda'$ are
--
--   $$\lambda'_{i,j}=\begin{cases}0 & i,j\in U,\\ \lambda_{i,j} & i,j\in V,\ \text{not both in } U,\end{cases}\qquad \lambda'_{i,v_0}=-\lambda'_{v_0,i}=\begin{cases}\sum_{w\in U}\lambda_{i,w} & i\in U,\\ 0 & i\notin U,\end{cases}\qquad \lambda'_{v_0,v_0}=0.$$
--
--   Channels between $U$ and $V\setminus U$ are unchanged, and $v_0$ has channels only to nodes of $U$.
--
--   **Formalization Note** The new network lives on `Option V`, with `none` the new node $v_0$. The paper's proof writes $\lambda'_{0,l}=\sum_i\lambda_{i,l}$; here it is written $-\sum_{w\in U}\lambda_{l,w}$, the same number for an antisymmetric $\Lambda$, so that $\lambda'$ is antisymmetric for every input.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Definition 3.6, pp. 7–8 (PDF pp. 8–9), and the matrix λ′ in the proof of Lemma B.1, p. 11 (PDF p. 12)

import Mathlib

namespace LNTopology.Hermetization

/-- **Hermetization of a node set.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Definition 3.6, pp. 7–8, and the matrix λ′ in the proof of Lemma B.1, p. 11.

"The hermetization of a set of nodes U in a LN is the graph obtained by: (i) deleting all
channels among nodes in U; (ii) adding a new node v0; and (iii) connecting all nodes in U to v0
with channels that summarize their flows towards other nodes in U."

The hermetized network lives on `Option V`, where `none` is the new node `v₀`:
* for `i, j ∈ V`, the flow is `0` if both lie in `U` (step (i)), and `lam i j` otherwise
  (channels between `U` and `V ∖ U`, and outside `U`, are unchanged);
* `i ∈ U` sends `Σ_{w∈U} lam i w` to `v₀` (step (iii)), and `v₀` sends the negative back;
* `v₀` has no channel to nodes outside `U`, nor to itself.

**Formalization Note.** Encoding E2: the paper's `λ′_{0,l} = Σ_i λ_{i,l}` is written
`-(Σ_{w∈U} lam l w)`, which is the same number when `lam` is antisymmetric (`IsLN`) and keeps
the hermetized matrix antisymmetric for every input. The paper's proof sums over `j = 1, …, n`
because it treats `U` as the whole network; Definition 3.6's "towards other nodes in U" is the
sum over `U` (reading R2). -/
noncomputable def hermetize {V : Type*} [DecidableEq V] (lam : V → V → ℝ) (U : Finset V) :
    Option V → Option V → ℝ
  | some i, some j => if i ∈ U ∧ j ∈ U then 0 else lam i j
  | some i, none => if i ∈ U then ∑ w ∈ U, lam i w else 0
  | none, some j => if j ∈ U then -(∑ w ∈ U, lam j w) else 0
  | none, none => 0

end LNTopology.Hermetization


