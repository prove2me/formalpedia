-- Prove2me | Definitions.Def_SparseIncidenceHom_WidthComparison_Separators
-- name    : SparseIncidenceHom_WidthComparison_Separators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:12.765276+00:00
-- url     : https://prove2.me/theorems/6643615e-7f81-4195-a941-c1b35f64c17d
-- title:
--   Endpoint-inclusive fractional separators, integral balance, and hereditary cost
-- statement:
--   Let $H=(V,E)$ be finite and covered, let $x:V\to[0,1]$, and let $\gamma:E\to[0,1]$ be nonzero, with $\Gamma=\sum_e\gamma(e)>0$. A simple primal path has cost equal to the sum of $x$ over all vertices of its support, including both endpoints. A zero-length path at $v$ has cost $x(v)$. The untruncated distance is $+\infty$ when no path exists. Its truncated version and its extension to edges are
--   $$d_x^*(u,v)=\min\left(\{1\}\cup\left\{\sum_{z\in V(Q)}x(z):Q\text{ simple from }u\text{ to }v\right\}\right),\quad
--   d_x^*(e,f)=\min_{u\in e,v\in f}d_x^*(u,v).$$
--   For $0<\theta<1$, fractional balance means
--   $$\sum_{f\in E}\gamma(f)d_x^*(e,f)\ge(1-\theta)\Gamma\quad(e\in E).$$
--   Integral balance of $S\subseteq V$ means $\sum_{e:e\cap C\ne\varnothing}\gamma(e)\le\theta\Gamma$ for every component $C$ after deleting $S$. Original edges meeting $C$ count even when they also meet $S$.
--
--   Define the optimum and hereditary cost by
--   $$\beta_{H,\theta}(\gamma)=\min_{x\text{ fractionally balanced}}\rho_H^*(x),\qquad
--   \operatorname{fsep}_\theta(H)=\sup_{W\subseteq V,\ 0\ne\gamma:E(H[W])\to[0,1]}\beta_{H[W],\theta}(\gamma).$$
--   The hereditary supremum includes zero so that an empty family contributes zero. Every induced hypergraph and every admissible real edge weighting is included. These costs connect the source's fractional separator relaxation to independently defined widths. Infima use nonempty feasible sets on the stated source domain; the all-one vertex vector is a feasible separator. Interval-valued functions are represented by real functions with explicit coordinate bounds.
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), pp. 9–11, Section 3.1, Equations (3)–(4), beta and fsep definitions, and p. 11 path formula

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Decompositions

namespace SparseIncidenceHom.WidthComparison

/-- All endpoints in support contribute, including the singleton support of a nil walk. -/
noncomputable def pathCost {V : Type} {G : SimpleGraph V} {u v : V}
    (x : V → ℝ) (p : G.Walk u v) : ℝ := (p.support.map x).sum

/-- Untruncated distance uses +infinity for no path. Demands are nonnegative on its source domain. -/
noncomputable def vertexDistance {V : Type} (H : FiniteHypergraph V) (x : V → ℝ)
    (u v : V) : ENNReal :=
  ⨅ (p : (primal H).Walk u v) (_ : p.IsPath), ENNReal.ofReal (pathCost x p)

/-- Equivalent finite minimum from p. 11; {1} prevents an empty-infimum convention. -/
noncomputable def truncatedVertexDistance {V : Type} (H : FiniteHypergraph V) (x : V → ℝ)
    (u v : V) : ℝ :=
  sInf ({1} ∪ {c | ∃ p : (primal H).Walk u v, p.IsPath ∧ c = pathCost x p})

noncomputable def edgeDistance {V : Type} (H : FiniteHypergraph V) (x : V → ℝ)
    (e f : Edge H) : ℝ :=
  sInf {c | ∃ (u v : V), u ∈ e.val ∧ v ∈ f.val ∧ c = truncatedVertexDistance H x u v}

/-- Gamma is a nonzero [0,1]-valued edge weighting. -/
def IsEdgeWeight {V : Type} (H : FiniteHypergraph V) (γ : Edge H → ℝ) : Prop :=
  (∀ e, 0 ≤ γ e ∧ γ e ≤ 1) ∧ ∃ e, γ e ≠ 0

noncomputable def totalEdgeWeight {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (γ : Edge H → ℝ) : ℝ := ∑ e, γ e

noncomputable def IsFractionalSeparator {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (γ : Edge H → ℝ) (θ : ℝ) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧
  ∀ e, (1 - θ) * totalEdgeWeight H γ ≤ ∑ f : Edge H, γ f * edgeDistance H x e f

noncomputable def fractionalSeparators {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (γ : Edge H → ℝ) (θ : ℝ) : Set (V → ℝ) := {x | IsFractionalSeparator H γ θ x}

/-- Original edges meeting a remaining component are counted even if they also meet S. -/
noncomputable def IsIntegralSeparator {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (γ : Edge H → ℝ) (θ : ℝ) (S : Set V) : Prop := by
  classical
  exact ∀ C : Set V, IsComponentAfter H S C →
    (∑ e : Edge H, if (e.val ∩ C).Nonempty then γ e else 0) ≤ θ * totalEdgeWeight H γ

noncomputable def separatorOptimum {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (γ : Edge H → ℝ) (θ : ℝ) : ℝ :=
  sInf (coverCost H '' fractionalSeparators H γ θ)

/-- Every induced subhypergraph, with independent real nonzero edge weights; empty supremum is 0. -/
noncomputable def hereditarySeparatorCost {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (θ : ℝ) : ℝ := by
  classical
  exact sSup ({0} ∪ {c | ∃ W : Finset V, ∃ γ : Edge (induced H (W : Set V)) → ℝ,
    IsEdgeWeight (induced H (W : Set V)) γ ∧
    c = separatorOptimum (induced H (W : Set V)) γ θ})

end SparseIncidenceHom.WidthComparison


