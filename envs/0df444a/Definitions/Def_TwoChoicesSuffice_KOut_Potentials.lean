-- Prove2me | Definitions.Def_TwoChoicesSuffice_KOut_Potentials
-- name    : TwoChoicesSuffice_KOut_Potentials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:04.712816+00:00
-- url     : https://prove2.me/theorems/4d63a05b-4017-4871-af08-2416d9067e67
-- title:
--   Bridge potential $\Psi_G(J,H)$ and component potentials $\Phi$
-- statement:
--   Let $G$ be a finite simple graph and $J\subseteq H\subseteq G$ nested spanning subgraphs. An edge of $H$ is a **bridge** of $H$ if deleting it disconnects its endpoints in $H$; write $\mathrm{Br}(H)$ for the set of bridges. The **bridge potential** is
--   $$
--   \Psi_G(J,H)=\sum_{e=uv\in\mathrm{Br}(H)\setminus E(J)}\min\{\deg_G(u),\deg_G(v)\}.
--   $$
--   For a vertex weight $w:V\to\mathbb N$ and a spanning subgraph $J$, the weighted component potential is $\sum_{C\in\mathrm{CC}(J)}\max_{v\in C}w(v)$, the sum over the connected components of $J$ of the largest weight in each. With $w=\deg_G$ this is the **max-degree component potential**
--   $$
--   \Phi_G(J)=\sum_{C\in\mathrm{CC}(J)}\max_{v\in C}\deg_G(v),
--   $$
--   all degrees measured in the original graph $G$. Merging components can only decrease these potentials.
--
--   The bridge potential bounds the inverse switchings of the paper's switching arguments, and the component potential is the quantity whose expectation is shown to be $O(n)$.
--
--   **Formalization Note** Mathlib's `IsBridge` also holds for non-edges between different components, so `bridges H` keeps only edges of `H` satisfying it. `compPotential w J` sums `sup w` over the vertex set of each component (components are nonempty); `degPotential G J` is $\Phi_G(J)$.
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), §3.1 (Bridge Potential; Max-degree Component Potential), printed p. 6, PDF p. 7; PDF pp. 7–8

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling

open scoped Classical

namespace TwoChoicesSuffice.KOut

variable {V : Type*} [Fintype V]

/-- `Br(H)`: the bridges of `H`, i.e. the edges of `H` whose deletion disconnects their
endpoints. (Mathlib's `IsBridge` alone also holds for non-edges joining two components, so
membership in the edge set of `H` is imposed explicitly.) Source: §3.1, PDF p. 7. -/
noncomputable def bridges (H : SimpleGraph V) : Finset (Sym2 V) :=
  H.edgeFinset.filter fun e => H.IsBridge e

/-- The weight `min{deg_G(u), deg_G(v)}` of an unordered pair `uv`, degrees in `G`. -/
noncomputable def minDegree (G : SimpleGraph V) (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun u v => min (G.degree u) (G.degree v), fun _ _ => min_comm _ _⟩ e

/-- Bridge potential `Ψ_G(J, H) = ∑_{e = uv ∈ Br(H) \ E(J)} min{deg_G(u), deg_G(v)}`
for nested spanning subgraphs `J ⊆ H ⊆ G`. Source: §3.1, PDF p. 7 (printed p. 6). -/
noncomputable def bridgePotential (G J H : SimpleGraph V) : ℕ :=
  ∑ e ∈ (bridges H).filter (fun e => e ∉ J.edgeFinset), minDegree G e

/-- The vertex set of the connected component `C` of `J`. -/
noncomputable def compVerts (J : SimpleGraph V) (C : J.ConnectedComponent) : Finset V :=
  Finset.univ.filter fun v => J.connectedComponentMk v = C

/-- Weighted component potential `∑_{C ∈ CC(J)} max_{v ∈ C} w(v)` for a vertex weight
`w : V → ℕ` (every component is nonempty, so the `sup` is a genuine maximum). -/
noncomputable def compPotential (w : V → ℕ) (J : SimpleGraph V) : ℕ :=
  ∑ C : J.ConnectedComponent, (compVerts J C).sup w

/-- Max-degree component potential `Φ_G(J) = ∑_{C ∈ CC(J)} max_{v ∈ C} deg_G(v)`, all
degrees measured in the original graph `G`. Source: §3.1, PDF p. 8 (printed p. 7). -/
noncomputable def degPotential (G J : SimpleGraph V) : ℕ :=
  compPotential (fun v => G.degree v) J

end TwoChoicesSuffice.KOut


