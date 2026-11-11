-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_Mass
-- name    : PlanarMetricElections_Peer_Mass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:10.65346+00:00
-- url     : https://prove2.me/theorems/42a5b9e5-021a-4b27-9082-7f756abadddc
-- title:
--   Uniform mass of a planar set
-- statement:
--   Let $V$ be a finite set of planar voters, and let $X$ be any planar set. Define its uniform voter mass by
--
--   $$\mu_V(X)=\frac{|V\cap X|}{|V|}.$$
--
--   Each distinct voter has equal weight. This definition applies to cells, rectangles, and the witness sets in Appendix A. Every theorem that uses a normalized electorate assumes it is nonempty, either explicitly or through its quartile-grid data.
--
--   **Formalization Note** Cardinalities are converted to real numbers before division. On the unused input $V=\varnothing$, Lean's real division assigns mass zero.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Section 3 and Appendix A, pp. 4, 13 (PDF pp. 5, 14)

import Definitions.Def_PlanarMetricElections_Peer_Geometry

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer

/-- Uniform voter mass. Intended uses have V nonempty; mass of the empty electorate is 0. -/
def mass (V : Finset Plane) (X : Set Plane) : ℝ :=
  ((V.filter (fun v => v ∈ X)).card : ℝ) / (V.card : ℝ)

end PlanarMetricElections.Peer


