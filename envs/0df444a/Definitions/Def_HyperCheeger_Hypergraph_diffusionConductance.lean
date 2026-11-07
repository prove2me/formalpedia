-- Prove2me | Definitions.Def_HyperCheeger_Hypergraph_diffusionConductance
-- name    : HyperCheeger_Hypergraph_diffusionConductance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:33.468829+00:00
-- url     : https://prove2.me/theorems/44796cea-9c2a-4dd3-a933-9978764e5bd2
-- title:
--   Diffusion conductance $\hat\phi_h(S)$, $\hat\phi_h(H)$
-- statement:
--   The **diffusion conductance** of $S\subseteq V_H$ and of $H$ are
--
--   $$\hat\phi_h(S)=\frac{\sum_{e\in\partial_h(S)}\frac{w_H(e)}{|e|-1}\,|e\cap S|\,|e\cap(V_H\setminus S)|}{\min(\mathrm{vol}_H(S),\mathrm{vol}_H(V_H\setminus S))},\qquad \hat\phi_h(H)=\min_{\emptyset\subsetneq S\subsetneq V_H}\hat\phi_h(S).$$
--
--   It counts a crossing hyperedge by its crossing vertex pairs. It coincides with $\phi_h$ on 2-graphs, and it is the quantity that links $\phi_h$ to the spectrum of the normalized Laplacian in this paper.
--
--   **Formalization Note.** $|e|-1$ is a real subtraction; a boundary hyperedge has $|e|\ge2$. As for $\phi_h$, a zero denominator comes with a zero numerator and $0/0=0$. The minimum is a real infimum over the finite subtype of proper nonempty subsets.
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), §3.1, p.7

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_conductance

namespace HyperCheeger

namespace Hypergraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The diffusion conductance of a set,
`φ̂_h(S) = ∑_{e ∈ ∂_h(S)} (w_H(e)/(|e|−1)) |e ∩ S| |e ∩ (V_H ∖ S)| / min(vol_H(S), vol_H(V_H ∖ S))`
(§3.1, p.7).

**Formalization Note.** `|e| − 1` is a real subtraction. A boundary hyperedge has `|e| ≥ 2`. As in
`conductanceSet`, a zero denominator comes with a zero numerator, and `0/0 = 0`. -/
noncomputable def diffusionConductanceSet (H : Hypergraph V) (S : Finset V) : ℝ :=
  (∑ e ∈ H.boundary S, H.w e / ((e.card : ℝ) - 1) * ((e ∩ S).card : ℝ) * ((e ∩ Sᶜ).card : ℝ)) /
    min (H.vol S) (H.vol Sᶜ)

/-- The diffusion conductance `φ̂_h(H) = min_{∅ ⊊ S ⊊ V_H} φ̂_h(S)` (Kamal, Bagchi, *A Cheeger
Inequality for Hypergraphs and Its Applications*, STOC 2027 submission, arXiv:2609.16286 (manuscript
sha256 e0942b89…), §3.1, p.7).

**Formalization Note.** A real infimum over the finite subtype of proper nonempty subsets, which is
nonempty for `2 ≤ card V`. -/
noncomputable def diffusionConductance (H : Hypergraph V) : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ}, H.diffusionConductanceSet S

end Hypergraph

end HyperCheeger


