-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_Capture
-- name    : PlanarMetricElections_Peer_Capture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:50.905933+00:00
-- url     : https://prove2.me/theorems/765bab05-d36b-429b-8fd3-372e3f5a6223
-- title:
--   Strict capture, feasible coalitions, and the strong-peer factor
-- statement:
--   Let $V$ be a finite planar voter set, $S$ a finite defending set, $c$ any real planar point, and $d$ a real-valued distance function. Feasibility at budget $k$ means $S\subseteq V$, $S\ne\varnothing$, and $|S|\le k$. Define
--
--   $$W_d(V,S,c)=\{v\in V:\forall s\in S,\ d(v,c)<d(v,s)\},\qquad P_d(V,S,c)=\frac{|W_d(V,S,c)|}{|V|}.$$
--
--   Strict inequality excludes all ties. The worst capture is $\sup_{c\in\mathbb R^2}P_d(V,S,c)$. For a positive integer $k$, the instance value minimizes this worst capture over feasible coalitions, and
--
--   $$\mathrm{PF}_d(k)=\sup_{V\text{ finite, nonempty}}\ \inf_{\varnothing\ne S\subseteq V,\,|S|\le k}\ \sup_{c\in\mathbb R^2}P_d(V,S,c).$$
--
--   The strong-peer guarantee at threshold $\varepsilon$ asserts existence of a feasible $S$ with $P_d(V,S,c)\le\varepsilon$ for every $c$. These predicates and factors supply the game model for Lemma 5.6 and Theorem 5.7. No strict-total-ranking bundle or no-tie condition is imported.
--
--   **Formalization Note** Positive budgets use $\mathbb N_{>0}$. For each fixed nonempty $V$ the feasible family contains a singleton, and all payoffs lie in a finite subset of $[0,1]$, so its inner extrema are attained. The outer supremum over electorates is nonempty and bounded in $[0,1]$; attainment is not asserted. Empty-electorate helper payoffs totalize to zero; all statements exclude that input.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Sections 2 and 4, equation (2), pp. 3–4, 6–8 (PDF pp. 4–5, 7–9)

import Definitions.Def_PlanarMetricElections_Peer_Mass

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer

def FeasibleCoalition (V S : Finset Plane) (k : ℕ) : Prop :=
  S ⊆ V ∧ S.Nonempty ∧ S.card ≤ k

/-- Ties do not count as capture. -/
def captured (d : Plane → Plane → ℝ) (V S : Finset Plane) (c : Plane) : Finset Plane :=
  V.filter (fun v => ∀ s ∈ S, d v c < d v s)

def capturePayoff (d : Plane → Plane → ℝ) (V S : Finset Plane) (c : Plane) : ℝ :=
  ((captured d V S c).card : ℝ) / (V.card : ℝ)

def worstCapture (d : Plane → Plane → ℝ) (V S : Finset Plane) : ℝ :=
  sSup (Set.range (capturePayoff d V S))

/-- Positive k ensures the feasible family is nonempty whenever V is nonempty. -/
def peerInstance (d : Plane → Plane → ℝ) (V : Finset Plane) (k : ℕ+) : ℝ :=
  sInf {r : ℝ | ∃ S : Finset Plane, FeasibleCoalition V S k ∧ r = worstCapture d V S}

def peerFactor (d : Plane → Plane → ℝ) (k : ℕ+) : ℝ :=
  sSup {r : ℝ | ∃ V : Finset Plane, V.Nonempty ∧ r = peerInstance d V k}

def StrongPeerGuarantee (d : Plane → Plane → ℝ) (V : Finset Plane) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ S : Finset Plane, FeasibleCoalition V S k ∧ ∀ c : Plane, capturePayoff d V S c ≤ ε

end PlanarMetricElections.Peer


