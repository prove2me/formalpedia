-- Prove2me | Definitions.Def_PoSUndirected_ndGame
-- name    : PoSUndirected_ndGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:32.279354+00:00
-- url     : https://prove2.me/theorems/036e8103-6854-43fe-a37a-c6e2944fbfa9
-- title:
--   The undirected network design game with equal cost sharing, and the owned-edge game
-- statement:
--   A **network design game** is specified by a finite undirected loopless multigraph $G=(V,E)$, edge costs $(c_e)_{e\in E}$ and finitely many players. Player $i$ has terminals $s_i,t_i$ and chooses **any** simple $s_i$–$t_i$ path $P_i$ of $G$. For a profile $P=(P_1,\dots,P_n)$ let $\ell_e(P)$ be the number of players using edge $e$. The payments and the social cost are
--   $$
--   c_i(P)=\sum_{e\in P_i}\frac{c_e}{\ell_e(P)},\qquad C(P)=\sum_{e:\,\ell_e(P)>0}c_e .
--   $$
--   A **weak (Nash) equilibrium** is a profile with no strictly improving unilateral move; tied deviations are allowed.
--
--   An **endpoint owner** of an edge $e=uv$ is a player with terminals $u,v$; ownership imposes no route restriction. In the **owned-edge game** every edge has exactly one player, its endpoint owner, who may use every simple path of the whole multigraph between the endpoints of her edge. Finally, an edge set $R$ is a **two-attachment region** with attachments $p,q$ if every vertex lying on an edge of $R$ and on an edge outside $R$ is $p$ or $q$; a vertex on an edge of $R$ other than $p,q$ is **strictly internal**, and an **external crosser** of $R$ is a player with no strictly internal terminal whose path uses an edge of $R$.
--
--   This is the model of all results of the paper; the owned-edge game is the class of the lower bound.
--
--   **Formalization Note** The game is the published fair cost-sharing game `fairGame` (strategy families plus equal sharing) with constant edge costs; `IsPureNash` (cost after any switch at least the current cost) is the weak equilibrium and `designCost` is $C(P)$. Positivity of the costs, looplessness and connectivity of the terminal pairs are hypotheses of the theorems that need them.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §2, pp.2–3 (PDF pp.4–5); §3, p.3 (PDF p.5); Lemma A.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PoSUndirected_IsSimplePathEdges
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

variable {V E ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- The edge sets of all simple `u`–`v` paths of the multigraph `ends`. -/
noncomputable def pathStrategies (ends : E → Sym2 V) (u v : V) : Finset (Finset E) := by
  classical exact Finset.univ.filter (fun S => IsSimplePathEdges ends u v S)

/-- The network design game of §2 (Tsoufis, preprint, sha256 c095d811…, §2, p.2 (PDF p.4)) on
the finite undirected loopless multigraph `ends : E → Sym2 V` with edge costs `c`: player `i ∈ ι`
has terminals `s i`, `t i` and may choose the edge set of **any** simple `s i`–`t i` path. Every
user of an edge `e` used by `ℓ_e(P)` players pays `c_e / ℓ_e(P)`, so player `i` pays
`cᵢ(P) = Σ_{e ∈ Pᵢ} c_e / ℓ_e(P)`.

**Formalization Note.** Built on the published `fairGame` (equal sharing of the constant cost
`c e`); `IsPureNash` of `CongestionPoA.AsymSum` is the paper's weak equilibrium (no strictly
improving unilateral move, ties allowed), and `designCost (fun e _ => c e)` is the social cost
`C(P) = Σ_{e : ℓ_e(P) > 0} c_e`. Positivity of the costs, looplessness and the connectivity of each
terminal pair are hypotheses of the statements, not part of this definition. -/
noncomputable def ndGame (ends : E → Sym2 V) (c : E → ℝ) (s t : ι → V) : CongestionGame ι E :=
  fairGame (fun i => pathStrategies ends (s i) (t i)) (fun e _ => c e)

/-- The strategies of the endpoint owner of edge `e` (§2, p.3 (PDF p.5): "An endpoint owner of
`e = uv` is a player with terminals `u, v`. Ownership specifies a demand and imposes no route
restriction"): the edge sets of all simple paths of the whole multigraph between the two
endpoints of `e`. -/
noncomputable def ownerStrategies (ends : E → Sym2 V) (e : E) : Finset (Finset E) := by
  classical exact
    Finset.univ.filter (fun S => ∃ u v : V, ends e = s(u, v) ∧ IsSimplePathEdges ends u v S)

/-- The owned-edge game (§3, p.3 (PDF p.5): "one player for every edge, and all simple paths
available to every player"): the players are the edges themselves, player `e` is the endpoint
owner of `e`, and the edge costs are shared equally.

**Formalization Note.** This is `ndGame` with `ι = E` and terminals the two endpoints of each
edge; the orientation of the endpoint pair is irrelevant, since a simple `u`–`v` path and a
simple `v`–`u` path have the same edge sets. -/
noncomputable def ownerGame (ends : E → Sym2 V) (c : E → ℝ) : CongestionGame E E :=
  fairGame (ownerStrategies ends) (fun e _ => c e)

/-- Player `i` is an endpoint owner of edge `e`: its terminal pair is the endpoint pair of `e`
(§2, p.3 (PDF p.5)). -/
def IsEndpointOwner (ends : E → Sym2 V) (s t : ι → V) (i : ι) (e : E) : Prop :=
  ends e = s(s i, t i)

/-- The edge set `R` meets the rest of the multigraph only at the vertices `p`, `q`
(a two-attachment region, Lemma A.1, p.13 (PDF p.15)): every vertex incident both to an edge of
`R` and to an edge outside `R` is `p` or `q`. -/
def IsTwoAttachment (ends : E → Sym2 V) (R : Finset E) (p q : V) : Prop :=
  ∀ (v : V) (e f : E), e ∈ R → f ∉ R → v ∈ ends e → v ∈ ends f → v = p ∨ v = q

/-- `v` is a strictly internal vertex of the region `R` with attachments `p`, `q`: it lies on an
edge of `R` and is neither attachment. -/
def IsInternalVertex (ends : E → Sym2 V) (R : Finset E) (p q : V) (v : V) : Prop :=
  (∃ e ∈ R, v ∈ ends e) ∧ v ≠ p ∧ v ≠ q

/-- Player `i` is an external crosser of the region `R` (attachments `p`, `q`) in the profile `A`:
neither terminal of `i` is strictly internal to `R`, and the path of `i` uses an edge of `R`
(Lemma A.1, p.13 (PDF p.15); "Her terminals cannot be strictly internal … every external use is a
complete attachment-to-attachment crossing"). -/
def IsCrosser (ends : E → Sym2 V) (s t : ι → V) (R : Finset E) (p q : V) (A : ι → Finset E)
    (i : ι) : Prop :=
  ¬ IsInternalVertex ends R p q (s i) ∧ ¬ IsInternalVertex ends R p q (t i) ∧ (A i ∩ R).Nonempty

end PoSUndirected


