-- Prove2me | Definitions.Def_StochHiddenConvex_Model_G
-- name    : StochHiddenConvex_Model_G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:08.379078+00:00
-- url     : https://prove2.me/theorems/d166d139-846f-454d-9c8a-b3af7cdf5790
-- title:
--   Reformulation (3): $\mathcal U$, the generalized inverse $g^{-1}$, $G$, and the projections $\Pi_{\mathcal X}$, $\Pi_{\mathcal U}$
-- statement:
--   For the model of problem (1), the reformulated problem is
--   $$\min_{u\in\mathcal U}G(u):=\mathbb E_{\xi\sim\mathbb P(\xi)}\big[f(\phi(g^{-1}(u),\xi))\big],\qquad(3)$$
--   where
--
--   1. $\mathcal U:=\{u\mid u_i\in\mathcal U_i:=[\mathbb E[\phi_i(\underline X_i,\xi_i)],\,\mathbb E[\phi_i(\bar X_i,\xi_i)]],\ i\in[d]\}$ is the image box;
--   2. $g^{-1}(u):=(g_1^{-1}(u_1),\dots,g_d^{-1}(u_d))$ with the generalized inverse $g_i^{-1}(u_i)=\inf_{x_i\in[\underline X_i,\bar X_i]}\{x_i\mid g_i(x_i)\ge u_i\}$;
--   3. $\Pi_{\mathcal X}(x):=\arg\min_{y\in\mathcal X}\|y-x\|^2$ and $\Pi_{\mathcal U}$ are the Euclidean projections onto the two boxes.
--
--   These objects are the "virtual" problem on which MSG's update mirrors a projected stochastic gradient step.
--
--   **Formalization Note** The infimum is a real `sInf`; for $u_i\in\mathcal U_i$ the set contains $\bar X_i$ and is bounded below by $\underline X_i$, so it is the paper's infimum (values outside $\mathcal U_i$ are never used). Both projections are written as coordinatewise clamping, which is the Euclidean projection onto a box.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (3), p.8; Preliminaries, p.8; Lemma 3.1, p.15

import Mathlib
import Definitions.Def_StochHiddenConvex_Model

open MeasureTheory

namespace StochHiddenConvex

namespace Model

variable {d : ℕ} (M : Model d)

/-- The image box `𝒰 := {u | uᵢ ∈ 𝒰ᵢ := [𝔼[ϕᵢ(X̲ᵢ, ξᵢ)], 𝔼[ϕᵢ(X̄ᵢ, ξᵢ)]], i ∈ [d]}`
(Chen, He, Hu & Ye, arXiv:2205.01774v3, (3), p.8). -/
def Ubox : Set (Vec d) := {u | ∀ i, M.gc i (M.lo i) ≤ u i ∧ u i ≤ M.gc i (M.hi i)}

/-- The generalized inverse `gᵢ⁻¹(uᵢ) = inf_{xᵢ∈[X̲ᵢ,X̄ᵢ]} {xᵢ | gᵢ(xᵢ) ≥ uᵢ}`
(arXiv:2205.01774v3, (3), p.8).

**Formalization Note.** A real `sInf`; for `uᵢ ∈ 𝒰ᵢ` the set contains `X̄ᵢ` and is bounded
below by `X̲ᵢ`, so this is the paper's infimum. Outside `𝒰ᵢ` the value is not used. -/
noncomputable def ginvC (i : Fin d) (u : ℝ) : ℝ :=
  sInf {y : ℝ | y ∈ Set.Icc (M.lo i) (M.hi i) ∧ u ≤ M.gc i y}

/-- `g⁻¹(u) := (g₁⁻¹(u₁), …, g_d⁻¹(u_d))` (arXiv:2205.01774v3, (3), p.8). -/
noncomputable def ginv (u : Vec d) : Vec d := WithLp.toLp 2 (fun i => M.ginvC i (u i))

/-- The reformulated objective `G(u) := 𝔼_{ξ∼ℙ(ξ)}[f(ϕ(g⁻¹(u), ξ))]` of problem (3)
(arXiv:2205.01774v3, (3), p.8). -/
noncomputable def G (u : Vec d) : ℝ := ∫ s, M.f (M.phiVec (M.ginv u) s) ∂M.P

/-- The projection `Π_𝒳(x) := arg min_{y∈𝒳} ‖y − x‖²` onto the box (arXiv:2205.01774v3,
Preliminaries, p.8).

**Formalization Note.** Written as coordinatewise clamping `max X̲ᵢ (min X̄ᵢ xᵢ)`, which is the
Euclidean projection onto a box whenever `X̲ᵢ ≤ X̄ᵢ`. -/
def projBox (x : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => max (M.lo i) (min (M.hi i) (x i)))

/-- The projection `Π_𝒰` onto the image box `𝒰` (arXiv:2205.01774v3, Lemma 3.1, p.15),
written as coordinatewise clamping to `[𝔼ϕᵢ(X̲ᵢ, ξᵢ), 𝔼ϕᵢ(X̄ᵢ, ξᵢ)]` (the Euclidean projection
onto a box). -/
noncomputable def projU (u : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => max (M.gc i (M.lo i)) (min (M.gc i (M.hi i)) (u i)))

end Model

end StochHiddenConvex


