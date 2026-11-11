-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_RectangularNet
-- name    : PlanarMetricElections_Peer_RectangularNet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:49.500201+00:00
-- url     : https://prove2.me/theorems/0fde91a7-ebce-47c1-a7d2-4d0c3229b910
-- title:
--   Strong rectangular nets and their worst-case factors
-- statement:
--   An axis-parallel rectangle is a product $I\times J$ of two order-convex subsets of the real line. This includes open and closed boundaries, unbounded intervals, empty rectangles, lines, and points. For finite voter sets, these boundary conventions give the same incidence problem: the closed bounding box of a nonempty finite subset of a rectangle is contained in that rectangle.
--
--   Let $V$ be a finite voter set, $Q$ a finite selected set, $k\ge0$ an integer, and $\varepsilon$ real. The strong-net predicate means
--
--   $$Q\subseteq V,\quad |Q|\le k,\quad \forall R\text{ rectangular},\quad \mu_V(R)>\varepsilon\Longrightarrow R\cap Q\ne\varnothing.$$
--
--   The uncovered mass $U_V(Q)$ is the supremum of $\mu_V(R)$ over rectangles avoiding $Q$. Define
--
--   $$\varsigma_k^{\mathcal R}=\sup_{V\text{ finite, nonempty}}\ \inf_{Q\subseteq V,\,|Q|\le k} U_V(Q).$$
--
--   Empty $Q$ is allowed, as in equation (1). The avoiding family contains the empty rectangle; each mass is in $[0,1]$. The feasible family contains the empty set, is finite, and is nonempty. Consequently the inner suprema and infima are attained in their intended domains; the outer supremum over electorates is nonempty and bounded, without a claim of attainment. These definitions expose the source's optimization rather than assuming its desired bound.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Section 2, equation (1), and Section 3, p. 4 (PDF p. 5)

import Definitions.Def_PlanarMetricElections_Peer_Mass

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer

/-- All products of real intervals, including open, closed, unbounded and degenerate intervals. -/
def IsRectangle (R : Set Plane) : Prop :=
  ∃ I J : Set ℝ, Set.OrdConnected I ∧ Set.OrdConnected J ∧ R = I ×ˢ J

/-- Q is drawn from V and hits every rectangle of mass strictly greater than ε. -/
def IsStrongRectNet (V Q : Finset Plane) (k : ℕ) (ε : ℝ) : Prop :=
  Q ⊆ V ∧ Q.card ≤ k ∧
    ∀ R : Set Plane, IsRectangle R → ε < mass V R →
      ∃ q ∈ Q, q ∈ R

/-- For each avoiding rectangle take its actual uniform voter mass. -/
def rectangularWorst (V Q : Finset Plane) : ℝ :=
  sSup {r : ℝ | ∃ R : Set Plane, IsRectangle R ∧
    Disjoint R (↑Q : Set Plane) ∧ r = mass V R}

/-- Empty Q is permitted in the strong-net optimization of equation (1). -/
def rectangularInstance (V : Finset Plane) (k : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ Q : Finset Plane, Q ⊆ V ∧ Q.card ≤ k ∧
    r = rectangularWorst V Q}

def rectangularFactor (k : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ V : Finset Plane, V.Nonempty ∧ r = rectangularInstance V k}

end PlanarMetricElections.Peer


