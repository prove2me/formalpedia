-- Prove2me | Definitions.Def_HyperCheeger_Hypergraph_conductance
-- name    : HyperCheeger_Hypergraph_conductance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:36.672324+00:00
-- url     : https://prove2.me/theorems/9d2fb484-b0f5-4997-a2a7-d5db85fb26ef
-- title:
--   Edge boundary and conductance $\phi_h(S)$, $\phi_h(H)$
-- statement:
--   For $S\subseteq V_H$ the **edge boundary** is $\partial_h(S)=\{e\in E_H: e\cap S\ne\emptyset,\ e\cap(V_H\setminus S)\ne\emptyset\}$, and the **conductance** of $S$ and of $H$ are
--
--   $$\phi_h(S)=\frac{\sum_{e\in\partial_h(S)}w_H(e)}{\min(\mathrm{vol}_H(S),\mathrm{vol}_H(V_H\setminus S))},\qquad \phi_h(H)=\min_{\emptyset\subsetneq S\subsetneq V_H}\phi_h(S).$$
--
--   For a 2-graph $G$ these are the paper's $\partial_g$, $\phi_g(S)$, $\phi_g(G)$. This is the combinatorial side of the Cheeger inequality.
--
--   **Formalization Note.** A zero denominator forces every boundary hyperedge to have weight $0$, so the quotient is $0/0$, which is $0$ in Lean. The minimum is a real infimum over the finite subtype of proper nonempty subsets, which is nonempty when $V_H$ has at least two vertices.
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), §3.1, p.6

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph

namespace HyperCheeger

namespace Hypergraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The edge boundary `∂_h(S) = {e ∈ E : e ∩ S ≠ ∅, e ∩ (V_H ∖ S) ≠ ∅}` (§3.1, p.6). -/
def boundary (H : Hypergraph V) (S : Finset V) : Finset (Finset V) :=
  H.edges.filter fun e => (e ∩ S).Nonempty ∧ (e ∩ Sᶜ).Nonempty

/-- The conductance of a set,
`φ_h(S) = ∑_{e ∈ ∂_h(S)} w_H(e) / min(vol_H(S), vol_H(V_H ∖ S))` (§3.1, p.6).

**Formalization Note.** A zero denominator occurs only when `S` or `Sᶜ` consists of zero-degree
vertices. Every boundary hyperedge then has weight `0`, so the quotient is `0/0`, which is `0` in
Lean. -/
noncomputable def conductanceSet (H : Hypergraph V) (S : Finset V) : ℝ :=
  (∑ e ∈ H.boundary S, H.w e) / min (H.vol S) (H.vol Sᶜ)

/-- The conductance `φ_h(H) = min_{∅ ⊊ S ⊊ V_H} φ_h(S)` (Kamal, Bagchi, *A Cheeger Inequality for
Hypergraphs and Its Applications*, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256
e0942b89…), §3.1, p.6).

**Formalization Note.** A real infimum over the finite subtype of proper nonempty subsets. For
`2 ≤ card V` that subtype is nonempty, so the infimum is the minimum. -/
noncomputable def conductance (H : Hypergraph V) : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ}, H.conductanceSet S

end Hypergraph

end HyperCheeger


