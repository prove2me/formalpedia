-- Prove2me | Definitions.Def_SybilClinch_AdmissibleAMM
-- name    : SybilClinch_AdmissibleAMM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:00.419533+00:00
-- url     : https://prove2.me/theorems/a504a87a-8d61-44b1-b907-488672c4716e
-- title:
--   Admissible AMM reserve curve $\varphi$ with initial reserve $x_0$
-- statement:
--   An automated market maker (AMM) pool holds two divisible assets $X$ and $Y$ with initial reserves $(x_0,y_0)\in\mathbb R^2_{++}$; after a batch its reserves must lie on the reserve curve $R_\varphi=\{(x,\varphi(x)):x>0\}$. The AMM is **admissible** if $\varphi:(0,\infty)\to(0,\infty)$ is continuous, strictly decreasing and convex, satisfies
--   $$\lim_{x\downarrow0}\varphi(x)=\infty,\qquad \lim_{x\uparrow\infty}\varphi(x)=0,$$
--   and is differentiable at $x_0$, where $y_0=\varphi(x_0)$.
--
--   The constant-product curve $\varphi(x)=x_0y_0/x$ is the standard example. Every result of the mission is stated for an arbitrary admissible AMM.
--
--   **Formalization Note** $\varphi$ is a total function on $\mathbb R$; all conditions are imposed on $(0,\infty)$ only. The spot price $p_0=-\varphi'(x_0)>0$ is a separate definition; its positivity follows from the other conditions.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, Definition 2.1, p.4 (PDF p.6)

import Mathlib

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2, Definition 2.1 (Admissible AMM), printed p.4 (PDF p.6).

An AMM pool with two divisible assets `X` and `Y`, initial reserves `(x₀, y₀) ∈ ℝ²₊₊` and reserve
curve `R_φ = {(x, φ x) : x > 0}`. It is *admissible* if `φ : (0, ∞) → (0, ∞)` is continuous,
strictly decreasing and convex, `φ x → ∞` as `x ↓ 0`, `φ x → 0` as `x ↑ ∞`, and `φ` is
differentiable at `x₀`; then `y₀ = φ x₀` (`AdmissibleAMM.y0`).

**Formalization Note.** `φ` is a total function `ℝ → ℝ`; every condition is imposed on the paper's
domain `(0, ∞)` only, and values of `φ` at `x ≤ 0` are never used. `y₀ = φ x₀ > 0` follows from
`pos`. The spot price `p₀ = −φ'(x₀)` is `AdmissibleAMM.p0`; its positivity, asserted in the
definition, is a consequence of strict decrease and convexity and is not a field. -/
structure AdmissibleAMM where
  /-- The reserve curve `φ`; only its values on `(0, ∞)` matter. -/
  φ : ℝ → ℝ
  /-- The initial reserve of asset `X`. -/
  x0 : ℝ
  x0_pos : 0 < x0
  pos : ∀ x, 0 < x → 0 < φ x
  continuousOn : ContinuousOn φ (Ioi 0)
  strictAntiOn : StrictAntiOn φ (Ioi 0)
  convexOn : ConvexOn ℝ (Ioi 0) φ
  tendsto_zero : Tendsto φ (𝓝[>] 0) atTop
  tendsto_atTop : Tendsto φ atTop (𝓝 0)
  differentiableAt : DifferentiableAt ℝ φ x0

end SybilClinch


