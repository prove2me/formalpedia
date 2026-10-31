-- Prove2me | Definitions.Def_ZeroOneSCO_Semismooth
-- name    : ZeroOneSCO_Semismooth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:34.650998+00:00
-- url     : https://prove2.me/theorems/68e5ab5f-fc85-4691-8e60-4fc6038350db
-- title:
--   Semismooth and strongly semismooth maps at a point, (10) and (11)
-- statement:
--   Let $\varphi$ be a map between normed spaces, Lipschitz on a neighbourhood of $x$, with Clarke generalized Jacobian $\partial\varphi$. It is **semismooth** at $x$ if it is directionally differentiable at $x$ and, as $\Delta x\to0$, for every $H\in\partial\varphi(x+\Delta x)$,
--   $$
--   \varphi(x+\Delta x)-\varphi(x)-H\Delta x=o(\|\Delta x\|).
--   $$
--   It is **strongly semismooth** at $x$ if the same holds with $O(\|\Delta x\|^2)$ on the right.
--
--   These are the regularity notions under which a Newton step on a nonsmooth map is accurate at the required order.
--
--   **Formalization Note** The bounds are uniform in $H$, as $\forall\varepsilon>0\ \exists\delta>0$ and as $\exists C,\delta$. The platform's `NonsmoothNewton.Local.SemismoothAt` is the limit form of Qi and Sun, whose equivalence with (10) is a theorem, so this module states the paper's own definition.
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, p.5, (10), (11)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac

open Filter Topology

namespace ZeroOneSCO

/-- Semismoothness of `φ` at `x` as defined on p.5 of Zhou, Pan, Xiu & Li, arXiv:2210.11889v5,
display (10): `φ` is locally Lipschitz, directionally differentiable at `x`, and
`φ(x + Δ) − φ(x) − HΔ = o(‖Δ‖)` as `Δ → 0`, uniformly over `H ∈ ∂φ(x + Δ)`.

**Formalization Note.** The page's open set `O` is a neighbourhood of `x` on which `φ` is Lipschitz.
This is the paper's definition. The platform's `NonsmoothNewton.Local.SemismoothAt` is the limit form of
Qi–Sun, which is equivalent to this one only by a theorem. -/
def SemismoothAt10 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E → F) (x : E) : Prop :=
  (∃ (L : NNReal) (U : Set E), U ∈ 𝓝 x ∧ LipschitzOnWith L φ U) ∧
  (∀ d : E, ∃ L : F, Tendsto (fun t : ℝ => t⁻¹ • (φ (x + t • d) - φ x)) (𝓝[>] 0) (𝓝 L)) ∧
  ∀ ε > 0, ∃ δ > 0, ∀ Δ : E, ‖Δ‖ < δ → ∀ H ∈ NonsmoothNewton.Shared.clarkeJac φ (x + Δ),
    ‖φ (x + Δ) - φ x - H Δ‖ ≤ ε * ‖Δ‖

/-- Strong semismoothness of `φ` at `x`, arXiv:2210.11889v5, display (11), p.5: as `SemismoothAt10`
with `φ(x + Δ) − φ(x) − HΔ = O(‖Δ‖²)` in place of (10). -/
def StronglySemismoothAt11 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E → F) (x : E) : Prop :=
  (∃ (L : NNReal) (U : Set E), U ∈ 𝓝 x ∧ LipschitzOnWith L φ U) ∧
  (∀ d : E, ∃ L : F, Tendsto (fun t : ℝ => t⁻¹ • (φ (x + t • d) - φ x)) (𝓝[>] 0) (𝓝 L)) ∧
  ∃ C : ℝ, ∃ δ > 0, ∀ Δ : E, ‖Δ‖ < δ → ∀ H ∈ NonsmoothNewton.Shared.clarkeJac φ (x + Δ),
    ‖φ (x + Δ) - φ x - H Δ‖ ≤ C * ‖Δ‖ ^ 2

end ZeroOneSCO


