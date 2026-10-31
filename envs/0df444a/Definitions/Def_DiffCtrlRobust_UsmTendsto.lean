-- Prove2me | Definitions.Def_DiffCtrlRobust_UsmTendsto
-- name    : DiffCtrlRobust_UsmTendsto
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:41.205346+00:00
-- url     : https://prove2.me/theorems/1a721ff8-25b8-4ccc-ad21-3baccd36a247
-- title:
--   Convergence $v_n\to v$ in $\mathfrak U_{\mathsf{sm}}$
-- statement:
--   A sequence $v_n$ converges to $v$ in $\mathfrak U_{\mathsf{sm}}$ if and only if
--
--   $$
--   \lim_{n\to\infty}\int_{\mathbb R^d} f(x)\int_{\mathbb U} g(x,u)\,v_n(x)(\mathrm du)\,\mathrm dx=\int_{\mathbb R^d} f(x)\int_{\mathbb U} g(x,u)\,v(x)(\mathrm du)\,\mathrm dx
--   $$
--
--   for all $f\in L^1(\mathbb R^d)\cap L^2(\mathbb R^d)$ and $g\in\mathcal C_b(\mathbb R^d\times\mathbb U)$. This is the topology on Markov controls under which the costs of the paper are continuous and the limit policies of the robustness argument live.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.6

import Definitions.Def_DiffCtrlRobust_Usm

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Convergence `vₙ → v` in `𝔘sm` (arXiv:2205.05894v2, §2, p.6): for all `f ∈ L¹(ℝ^d) ∩ L²(ℝ^d)`
and `g ∈ C_b(ℝ^d × U)`,
`∫ f(x) ∫ g(x, u) vₙ(x)(du) dx → ∫ f(x) ∫ g(x, u) v(x)(du) dx`. -/
def UsmTendsto {d : ℕ} {U : Type*} [TopologicalSpace U] [MeasurableSpace U]
    (vs : ℕ → Usm d U) (v : Usm d U) : Prop :=
  ∀ f : SDEState d → ℝ, Integrable f volume → MemLp f 2 volume →
    ∀ g : BoundedContinuousFunction (SDEState d × U) ℝ,
      Tendsto (fun n => ∫ x, f x * ∫ u, g (x, u) ∂((vs n).1 x : Measure U)) atTop
        (𝓝 (∫ x, f x * ∫ u, g (x, u) ∂(v.1 x : Measure U)))

end DiffCtrlRobust


