-- Prove2me | Definitions.Def_OnlineStochMatching_TSM_Cut
-- name    : OnlineStochMatching_TSM_Cut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:34:13.026167+00:00
-- url     : https://prove2.me/theorems/2be67f64-9a51-4591-b0c7-cb89171d939a
-- title:
--   The surgered reachability cut $(S, T)$ of $G_f$ and the crossing edge set $E_\delta$ (Section 4.2.3)
-- statement:
--   Let $G = (A, I, E)$ be a finite bipartite graph, $G_f$ its boosted flow graph (source arcs of capacity 2, middle arcs of capacity 1, sink arcs of capacity 2), and $E_f \subseteq E$ the edge set of an integral maximum flow. The **residual graph** of this flow has an arc $s \to a$ when fewer than two edges of $E_f$ meet $a$, an arc $a \to i$ when $(a, i) \in E \setminus E_f$, and an arc $i \to a$ when $(a, i) \in E_f$. Let $S_0$ be the set of advertisers and impression types reachable from $s$ in it.
--
--   The cut $(S, T)$ of the paper is obtained by a "surgery": every impression type outside $S_0$ that is joined by edges of $E$ to more than one advertiser of $S_0$ is moved to the source side. Thus
--   $$A_S = A \cap S_0, \qquad I_S = (I \cap S_0) \cup \{\, i : \#\{a \in A_S : (a,i) \in E\} \ge 2 \,\},$$
--   $A_T = A \setminus A_S$ and $I_T = I \setminus I_S$. Finally,
--   $$E_\delta = \{(a, i) \in E : a \in A_S,\ i \in I_T\}$$
--   is the set of edges crossing the cut from $A_S$ to $I_T$.
--
--   The cut is the paper's tool for bounding OPT: its capacity equals $|E_f|$, and it guides a cut of the realization graph.
--
--   **Formalization Note** Reachability is defined inductively from the three arc types above. Arcs back into $s$ and the arcs at the sink are omitted: for a maximum flow the sink is not reachable from $s$, so they do not change the reachable set. All statements that use the cut assume $E_f$ is a maximum flow edge set.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 7, Section 4.2.3 (the cut (S, T), A_S, A_T, I_S, I_T, E_δ)

import Definitions.Def_OnlineStochMatching_TSM_Coloring

namespace OnlineStochMatching.TSM

open Finset

variable {A I : Type}

/-- Reachability from the source `s` in the residual graph of the boosted flow graph `G_f` left
by the integral flow with middle edge set `F ⊆ E` (Feldman, Mehta, Mirrokni, Muthukrishnan,
*Online Stochastic Matching: Beating 1-1/e*, arXiv:0905.4100v1, §4.2.3, p. 7). The residual arcs
used are: `s → a` iff `deg_F(a) < 2` (the arc `(s, a)` of capacity 2 is not saturated);
`a → i` iff `(a, i) ∈ E \ F`; `i → a` iff `(a, i) ∈ F` (reverse of a flow-carrying arc).
Arcs into `s` and the arcs at the sink `t` are omitted: when `F` is a maximum flow, `t` is not
reachable, so they do not change the set of vertices reachable from `s`. -/
inductive Reach [DecidableEq A] (E F : Finset (A × I)) : A ⊕ I → Prop
  | source (a : A) : degA F a < 2 → Reach E F (Sum.inl a)
  | forward (a : A) (i : I) :
      Reach E F (Sum.inl a) → (a, i) ∈ E → (a, i) ∉ F → Reach E F (Sum.inr i)
  | backward (a : A) (i : I) :
      Reach E F (Sum.inr i) → (a, i) ∈ F → Reach E F (Sum.inl a)

/-- `A_S = A ∩ S` (§4.2.3, p. 7): the advertisers on the source side of the cut `(S, T)`; these are
the advertisers reachable from `s` in the residual graph (the surgery moves impressions only). -/
noncomputable def cutAS [Fintype A] [DecidableEq A] (E F : Finset (A × I)) : Finset A := by
  classical
  exact Finset.univ.filter fun a => Reach E F (Sum.inl a)

/-- `A_T = A ∩ T` (§4.2.3, p. 7). -/
noncomputable def cutAT [Fintype A] [DecidableEq A] (E F : Finset (A × I)) : Finset A :=
  Finset.univ \ cutAS E F

/-- `I_S = I ∩ S` (§4.2.3, p. 7) after the "surgery": an impression type is on the source side if it
is reachable from `s` in the residual graph, or if it is incident (by an edge of `E`) to more than
one advertiser of `A ∩ S`. -/
noncomputable def cutIS [Fintype A] [DecidableEq A] [Fintype I] (E F : Finset (A × I)) :
    Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    Reach E F (Sum.inr i) ∨ 2 ≤ ((cutAS E F).filter fun a => (a, i) ∈ E).card

/-- `I_T = I ∩ T` (§4.2.3, p. 7). -/
noncomputable def cutIT [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F : Finset (A × I)) : Finset I :=
  Finset.univ \ cutIS E F

/-- `E_δ` (§4.2.3, p. 7): the edges `(a, i) ∈ E` that cross the cut from `A_S` to `I_T`. -/
noncomputable def Edelta [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F : Finset (A × I)) : Finset (A × I) := by
  classical
  exact E.filter fun e => e.1 ∈ cutAS E F ∧ e.2 ∈ cutIT E F

end OnlineStochMatching.TSM


