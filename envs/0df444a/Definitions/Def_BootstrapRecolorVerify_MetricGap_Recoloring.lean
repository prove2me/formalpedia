-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Recoloring
-- name    : BootstrapRecolorVerify_MetricGap_Recoloring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:06.401697+00:00
-- url     : https://prove2.me/theorems/d6006198-c570-488f-aea3-ff407c86f2dc
-- title:
--   Uniform representatives, smooth proxy costs and simultaneous sampling
-- statement:
--   In each level-$(i+1)$ cloud choose one coordinate uniformly and independently. Recolor every vertex with its representative's original color. A map is monochromatic if it is constant within every cloud. To recolor a monochromatic map down one level, first collapse its input clouds, then recolor the preceding clouds, then project the resulting colors down one level.
--
--   For a map $\varphi_i:V(G_i)\to V(G_i)$, the proxy is
--
--   $$\overline{\operatorname{cost}}_i(\varphi_i)=\frac1{N_iL}\sum_u\rho_1(u,\varphi_i(u))+\frac1{N_i}\sum_{j=1}^{i-1}\sum_{e=\{u,v\}\in E_j(G_i)}w_e\rho_{j+1}(\varphi_i(u),\varphi_i(v)),$$
--
--   with the additional terminal-distance level-$r$ contribution when $i=r$. Every undirected edge is counted once, with multiplicity. The average over the finite representative function space is the exact product-uniform expectation.
--
--   The sampling event requires one lift array to satisfy
--
--   $$\left|\overline{\operatorname{cost}}_{i+1}^{(j)}(\sigma)-\mathbb E\overline{\operatorname{cost}}_{i+1}^{(j)}(\sigma')\right|\le\frac{2\theta M_{j+1}}{a_j}$$
--
--   simultaneously for every $1\le j\le i-1$ and every map into $G_{j+1}$. Maps into later graphs are equivalent through ancestor projection, so no coloring is omitted. The target metric is already fixed in the preceding history. Internal matchings do not occur in this event. It has no constraints for the first two stages.
--
--   These definitions specify the randomness and the common cost convention for sampling, recoloring, and bootstrapping.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Definition 4.8 p.12; §4 pp.9,12; §6.2–6.4, especially (17), p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=24; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Hierarchy

open scoped Classical

namespace BootstrapRecolorVerify.MetricGap

/-- Uniform finite expectation. All representative spaces here are finite and
nonempty for r>0, so every real cost is integrable. -/
noncomputable def average {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (Fintype.card A : ℝ)⁻¹ * ∑ a, f a

/-- Independent uniformly random representatives, one coordinate in each cloud.
The uniform distribution on this function space is exactly the product law. -/
abbrev Representatives (r i : ℕ) := Vertex r i → Fin (cloudSize r (i + 1))

/-- Recolor the entire cloud with its representative's original color (p.24). -/
def recolor {r i : ℕ} {A : Type*} (f : Vertex r (i + 1) → A)
    (z : Representatives r i) (u : Vertex r (i + 1)) : A :=
  f (u.1, z u.1)

/-- Monochromaticity is within each cloud, not across different clouds
(Definition 4.8, p.12). -/
def Monochromatic {r i : ℕ} {A : Type*} (f : Vertex r (i + 1) → A) : Prop :=
  ∀ (u : Vertex r i) (a b : Fin (cloudSize r (i + 1))), f (u, a) = f (u, b)

/-- A fixed coordinate to evaluate the common color after collapsing a cloud.
Its choice does not matter for a monochromatic input. -/
def cloudZero {r : ℕ} (hr : 0 < r) (i : ℕ) : Fin (cloudSize r (i + 1)) :=
  ⟨0, by unfold cloudSize baseSize Lambda delta L; positivity⟩

/-- Recoloring of Lemma 6.5: collapse input level-(i+2) clouds, recolor
level-(i+1) clouds, and project colors onto G_(i+1) (pp.25--26). -/
def recolorDown {r i : ℕ} (hr : 0 < r)
    (f : Vertex r (i + 2) → Vertex r (i + 2))
    (z : Representatives r i) (u : Vertex r (i + 1)) : Vertex r (i + 1) :=
  (f ((u.1, z u.1), cloudZero hr (i + 1))).1

/-- The pendant proxy term, (0), p.23. Unused level zero is explicitly zero. -/
noncomputable def vertexContribution {r i : ℕ} (H : History r i)
    (f : Vertex r i → Vertex r i) : ℝ :=
  if hi : 1 ≤ i then
    (Fintype.card (Vertex r i) * (L r : ℝ))⁻¹ *
      ∑ u, projectedRho H 1 hi u (f u)
  else 0

/-- Proxy cost from §6.2, p.23, with the definitions of §4, pp.9,12.
At the top, the terminal term B_r is retained. Lower stages omit their
last edge level. There is never a distance rho_(i+1) on G_i. -/
noncomputable def proxyCost {r i : ℕ} (H : History r i)
    (f : Vertex r i → Vertex r i) : ℝ :=
  vertexContribution H f + (Fintype.card (Vertex r i) : ℝ)⁻¹ *
    ∑ e : Edge r i,
      edgeWeight r (edgeLevel e) *
        (if hj : edgeLevel e + 1 ≤ i then
           projectedRho H (edgeLevel e + 1) hj (f (endpoints H e).1) (f (endpoints H e).2)
         else if i = r then terminalDistance H (f (endpoints H e).1) (f (endpoints H e).2)
         else 0)

/-- Normalized level-j sampled matching cost at the next stage. The target is
G_(j+1), already frozen in H. Every map into any later target factors through
this target for this cost; conversely every map here is allowed in (17). -/
noncomputable def sampledContribution {r i : ℕ} (H : History r i)
    (a : LiftArray r i) (j : ℕ) (hj : j + 1 ≤ i)
    (f : Vertex r (i + 1) → Vertex r (j + 1)) : ℝ :=
  (Fintype.card (Vertex r (i + 1)) : ℝ)⁻¹ *
    ∑ e : Edge r i, if edgeLevel e = j then
      edgeWeight r j * ∑ x : Fin (cloudSize r (i + 1)),
        rho (historyPrefix r (j + 1) hj H)
          (f ((endpoints H e).1, x)) (f ((endpoints H e).2, a e x))
    else 0

/-- Simultaneous acceptance event (17), p.24. The single matching array must
work for every older level and every coloring, before that coloring is chosen.
The quantifier is empty at stages 1 and 2; internal matchings are absent here. -/
def SamplingEvent {r i : ℕ} (H : History r i) (a : LiftArray r i) : Prop :=
  ∀ (j : ℕ) (_ : 1 ≤ j) (hj : j + 2 ≤ i + 1),
    ∀ f : Vertex r (i + 1) → Vertex r (j + 1),
      |sampledContribution H a j (by omega) f -
        average (fun z : Representatives r i =>
          sampledContribution H a j (by omega) (recolor f z))| ≤
      2 * theta r * cap r (j + 1) / scale r j

end BootstrapRecolorVerify.MetricGap


