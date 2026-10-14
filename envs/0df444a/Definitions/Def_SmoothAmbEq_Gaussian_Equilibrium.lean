-- Prove2me | Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
-- name    : SmoothAmbEq_Gaussian_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:57.515199+00:00
-- url     : https://prove2.me/theorems/60fed0ce-1419-483e-bbb5-84a03270761c
-- title:
--   (2.9)–(2.10), Definition 2.1 — inside expected utility g^{z,π}, objective J, spike π_{t,h}, equilibrium strategy
-- statement:
--   This file defines the smooth-ambiguity objective and the equilibrium notion (Definition 2.1, p. 7) in the β-version of §4–§5.
--
--   1. **Inside expected utility** (p. 16):
--   $$g^{z,\pi}(t,x,\beta)=\mathbb E\big[U(X^{z,\pi}_T)\mid X^{z,\pi}_t=x,\ \beta^z_t=\beta\big],$$
--   the expected terminal utility of the wealth driven by $\pi$ under the hypothetical drift $z$, started at $(t,x,\beta)$.
--   2. **Objective** ((2.9), β-version): with the posterior $Z\mid\beta_t=\beta\sim N(\beta,\zeta(t))$ (p. 14),
--   $$J(t,x,\beta,\pi)=\mathbb E\big[\phi(g^{Z,\pi}(t,x,\beta))\mid\beta_t=\beta\big]=\int\phi\big(g^{z,\pi}(t,x,\beta)\big)\,N(\beta,\zeta(t))(dz).$$
--   3. **Spike variation.** For $\pi,\pi^*$ and $h>0$, $\pi_{t,h}=\pi$ on $[t,t+h)$ and $\pi^*$ otherwise (in time, for all $(x,\beta)$).
--   4. **Equilibrium strategy (Definition 2.1 with $\Pi$ of Definition 5.1).** $\pi^*\in\Pi$ is an equilibrium strategy if for every $(t,x,\beta)\in[0,T)\times\mathbb R^2$ and every $\pi\in\Pi$ such that $\pi_{t,h}\in\Pi$ for all sufficiently small $h>0$,
--   $$\limsup_{h\to0^+}\frac{J(t,x,\beta,\pi_{t,h})-J(t,x,\beta,\pi^*)}{h}\le0 .$$
--
--   This is the notion of subgame-perfect (first-order) optimality for the time-inconsistent smooth-ambiguity criterion; Theorem 5.5 exhibits such a $\pi^*$.
--
--   **Formalization Note** $g^{z,\pi}$ is the Bochner expectation of $U(X_T)$ for a chosen strong solution (any solution, when one exists; under Definition 5.1(i) all are indistinguishable). Since a Bochner integral of a non-integrable function is $0$ in Lean, the equilibrium predicate carries finiteness of both expectations in $J$ (integrability of $U(X^{z,\pi}_T)$ for every $z$, and of $z\mapsto\phi(g^{z,\pi})$ under $N(\beta,\zeta(t))$) for $\pi^*$ at every $(t,x,\beta)$ and for $\pi_{t,h}$ for all small $h$, as part of what is asserted: the paper treats $J$ as a real number. The $\limsup$ is written as: for every $\epsilon>0$, eventually as $h\to0^+$ the quotient is $\le\epsilon$. The posterior law is taken from Bismuth, Guéant and Pu (2019), as the paper does, not re-derived. $t$ ranges over $[0,T)$ because the spike needs $t<T$ (paper.md slip 5).
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, pp. 5–7, 12, 14, 16, (2.9)–(2.10), Definition 2.1, (2.14)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A chosen solution of the inside wealth equation (5.2) started at `(t, x, β)` (any solution
when one exists; under condition (i) of Definition 5.1 all solutions are indistinguishable). -/
noncomputable def insideWealth (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy)
    (z t x β : ℝ) : ℝ → Ω → ℝ :=
  Classical.epsilon (fun X => IsInsideWealth M P W π z t x β X)

/-- The inside expected utility (p. 16)
`g^{z,π}(t, x, β) = E[U(X^{z,π}_T) | X^{z,π}_t = x, β^z_t = β]`,
computed on the inside system started at `(t, x, β)`. -/
noncomputable def insideValue (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy)
    (z t x β : ℝ) : ℝ :=
  ∫ ω, M.U (insideWealth M P W π z t x β M.T ω) ∂P

/-- The posterior law `N(β, ζ(t))` of the drift `Z` given `β_t = β` (p. 14). -/
noncomputable def posterior (M : Model) (t β : ℝ) : Measure ℝ :=
  gaussianReal β (M.ζ t).toNNReal

/-- The smooth-ambiguity objective (2.9) in the β-version (p. 12):
`J(t, x, β, π) = E[φ(g^{Z,π}(t, x, β)) | β_t = β] = ∫ φ(g^{z,π}(t, x, β)) N(β, ζ(t))(dz)`. -/
noncomputable def J (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy)
    (t x β : ℝ) : ℝ :=
  ∫ z, M.φ (insideValue M P W π z t x β) ∂(posterior M t β)

/-- Both expectations in `J(t, x, β, π)` are finite: `U(X^{z,π}_T)` is integrable for every
`z`, and `z ↦ φ(g^{z,π}(t, x, β))` is integrable under `N(β, ζ(t))`. -/
def HasFiniteJ (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (π : Strategy)
    (t x β : ℝ) : Prop :=
  (∀ z : ℝ, Integrable (fun ω => M.U (insideWealth M P W π z t x β M.T ω)) P) ∧
  Integrable (fun z => M.φ (insideValue M P W π z t x β)) (posterior M t β)

open Classical in
/-- The spike variation of Definition 2.1 (p. 7): `π_{t,h} = π` on `[t, t + h)` (for all
`(x, β)`) and `π*` otherwise. -/
noncomputable def spike (π πs : Strategy) (t h : ℝ) : Strategy :=
  fun s x β => if s ∈ Ico t (t + h) then π s x β else πs s x β

/-- Definition 2.1 (p. 7) with the admissible class `Π` of Definition 5.1: `π*` is an
equilibrium strategy if `π* ∈ Π` and, for every `(t, x, β) ∈ [0, T) × ℝ²` and every `π ∈ Π`
such that `π_{t,h} ∈ Π` for all sufficiently small `h > 0`,
`limsup_{h → 0+} [J(t, x, β, π_{t,h}) - J(t, x, β, π*)] / h ≤ 0`.
The values `J` are real numbers: their finiteness is part of the definition (for `π*`, and
for `π_{t,h}` with `h` small). The `limsup` is written in `ε`-form. -/
def IsEquilibrium (M : Model) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (πs : Strategy) : Prop :=
  Admissible M P W πs ∧
  ∀ t ∈ Ico 0 M.T, ∀ x β : ℝ,
    HasFiniteJ M P W πs t x β ∧
    ∀ π : Strategy, Admissible M P W π →
      (∀ᶠ h in 𝓝[>] (0 : ℝ), Admissible M P W (spike π πs t h)) →
      (∀ᶠ h in 𝓝[>] (0 : ℝ), HasFiniteJ M P W (spike π πs t h) t x β) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
        (J M P W (spike π πs t h) t x β - J M P W πs t x β) / h ≤ ε

end SmoothAmbEq.Gaussian


