-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_Supplement_MadParameters
-- name    : LocalOccupancyIS_Glauber_Supplement_MadParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:59:01.829009+00:00
-- url     : https://prove2.me/theorems/ac97fff6-b361-4691-92d8-b48a8e98f202
-- title:
--   Equation (19) parameters and real degree bounds
-- statement:
--   For a finite graph, a real degree upper bound $\Delta$ means $d_G(v)\le\Delta$ for every vertex; triangle freeness excludes every three-edge triangle. For $\Delta\ge1$, $a\ge0$ and $\lambda>0$, write $p=\lambda/(1+\lambda)$ and define
--
--   $$\ell=\log(1+\lambda),\quad D_{19}=\Delta(1+\lambda)^a\ell,\quad w=W(D_{19}),\quad \beta_{19}=\frac{e^w}{p(1+w)},\quad \gamma_{19}=\frac{(1+\lambda)^a\ell}{p(1+w)}.$$
--
--   Here $W$ is the published principal Lambert function on nonnegative inputs. These are computed parameters, separate from the main-text biclique-density parameters. The published predicate $\mathrm{HereditaryDensity}(G,1,a)$ is exactly the source's local maximum-average-degree bound, including empty induced neighborhoods.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), p.15, equations (19)–(20) and §5 definitions

import Definitions.Def_LocalOccupancyIS_Glauber_Parameters

namespace LocalOccupancyIS.Glauber.Supplement
noncomputable section

/-- A real upper bound; no regularity or minimum-degree restriction. -/
def RealDegreeBound {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℝ) : Prop := ∀ v, (G.degree v : ℝ) ≤ Δ

def TriangleFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v w, ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w u)

/-- Equation (19), distinct from the biclique-density parameter choice. -/
def madW (Δ a lam : ℝ) : ℝ :=
  RiskBalancingMNL.lambertW (Δ * (1+lam)^a * Real.log (1+lam))
def madBeta (Δ a lam : ℝ) : ℝ :=
  Real.exp (madW Δ a lam) / (p lam * (1 + madW Δ a lam))
def madGamma (Δ a lam : ℝ) : ℝ :=
  (1+lam)^a * Real.log (1+lam) / (p lam * (1 + madW Δ a lam))

end
end LocalOccupancyIS.Glauber.Supplement


