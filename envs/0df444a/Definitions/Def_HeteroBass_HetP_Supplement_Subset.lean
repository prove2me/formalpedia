-- Prove2me | Definitions.Def_HeteroBass_HetP_Supplement_Subset
-- name    : HeteroBass_HetP_Supplement_Subset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:27:07.309584+00:00
-- url     : https://prove2.me/theorems/129126f0-0ec1-44c9-bf22-e80076ca8449
-- title:
--   §3.1 — subset nonadoption probabilities of the published chain
-- statement:
--   Let there be $M$ consumers, with nonnegative external rates $p_i$ and directed influence rates $Q_{k,i}$ from consumer $k$ to consumer $i$. The adopter set starts empty and has the transition matrix $P_t=\exp(tG)$ of the published Bass generator. For a set $U$ of nodes, define its **subset nonadoption probability** by
--
--   $$s_U(t)=\sum_{A:\,A\cap U=\varnothing}P_t(\varnothing,A).$$
--
--   This is the probability that every consumer in $U$ is still a nonadopter. It observes the existing adoption process and supplies the quantities in the general master equations (19). The definition also has the usual empty-event extension $s_{\varnothing}(t)$, although Lemma 2 is stated only for nonempty subsets.
--
--   **Formalization Note** Nodes are `Fin M`, and sets are finite sets. The definition has a real matrix-exponential value for every real time and every real parameter array; probability interpretations and theorem statements use nonnegative time and admissible rates. No independent ODE solution is substituted for the process.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, §3.1, p. 7; Appendix A, p. 24

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

namespace HeteroBass.HetP.Supplement

/-- Probability that every node of U is a nonadopter in the published chain. -/
noncomputable def subsetNonadoption {M : ℕ} (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (U : Finset (Fin M)) (t : ℝ) : ℝ :=
  ∑ A : Finset (Fin M), if Disjoint A U then transition p Q t ∅ A else 0

end HeteroBass.HetP.Supplement


