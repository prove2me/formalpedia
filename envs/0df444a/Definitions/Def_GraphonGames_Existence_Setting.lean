-- Prove2me | Definitions.Def_GraphonGames_Existence_Setting
-- name    : GraphonGames_Existence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:18.295262+00:00
-- url     : https://prove2.me/theorems/28fdcc29-5acd-4257-882c-9651406b6630
-- title:
--   pp. 3, 8, 10–11, 15 — graphon, operator norm ‖W‖, aggregate (6), cost J, Assumptions 1, 4, 5, best response B, Nash equilibrium (Prop. 3.6)
-- statement:
--   This file fixes the model of a static graphon game with a continuum of players, following §§2–3 of the paper.
--
--   1. **Players.** The player space is $I=[0,1]$ with Lebesgue measure $\lambda_I$. A strategy profile is a function $\alpha : I\to\mathbb R$ in $L^2(I)$ (the action set is $A=\mathbb R$); profiles are identified when they agree $\lambda_I$-almost everywhere.
--   2. **Graphon and operator.** A graphon is a symmetric, Borel-measurable, real-valued function $w$ on $I\times I$ with $\|w\|_2^2=\int_{I\times I} w(x,y)^2\,dx\,dy<\infty$. Its integral operator is $[\mathbf W g]_x=\int_I w(x,y)g(y)\,dy$, and
--   $$\|\mathbf W\| := \sup_{\varphi\in L^2(I),\ \|\varphi\|_{L^2(I)}=1}\|\mathbf W\varphi\|_{L^2(I)}.$$
--   3. **Assumption 1.** The state map $b:\mathbb R\times\mathbb R\to\mathbb R$ satisfies $|b(\alpha,z)-b(\alpha',z')|^2\le c_\alpha|\alpha-\alpha'|^2+c_z|z-z'|^2$ with $c_\alpha,c_z\ge 0$; the noise law $\mu_0$ is a probability measure on $\mathbb R$ with $\int\xi^2\,\mu_0(d\xi)<\infty$ and mean zero.
--   4. **Cost.** With the state $X_{\alpha,z,\xi}=b(\alpha,z)+\xi$, the cost of action $\alpha$ against aggregate $z$ is $J(\alpha,z)=\int f(b(\alpha,z)+\xi,\alpha,z)\,\mu_0(d\xi)$.
--   5. **Assumption 4.** For every $z$, $\alpha\mapsto J(\alpha,z)$ is $C^1$ and strongly convex with constant $\ell_c>0$:
--   $$J(\epsilon\alpha+(1-\epsilon)\alpha',z)\le\epsilon J(\alpha,z)+(1-\epsilon)J(\alpha',z)-\tfrac{\ell_c}{2}\epsilon(1-\epsilon)|\alpha-\alpha'|^2,\quad \epsilon\in[0,1],$$
--   and $|\partial_\alpha J(\alpha,z')-\partial_\alpha J(\alpha,z)|\le\ell_J|z'-z|$ with $\ell_J\ge0$.
--   6. **Assumption 5.** There is a finite constant $c_0>0$ with $|b(\alpha,z)|\le c_0$ for all $\alpha,z$.
--   7. **Aggregate.** $z\in L^2(I)$ is an aggregate of the profile $\alpha$ if $z_x=\int_I w(x,y)\,b(\alpha_y,z_y)\,dy$ for $\lambda_I$-a.e. $x$ (equation (6)); under $\sqrt{c_z}\|\mathbf W\|<1$ it is unique and is written $\mathbf Z\alpha$.
--   8. **Best response.** $[\mathbf Bz]_x$ is a minimizer of $\alpha\mapsto J(\alpha,z_x)$.
--   9. **Nash equilibrium.** $\hat\alpha\in L^2(I)$ is a Nash equilibrium if it has an aggregate $z=\mathbf Z\hat\alpha$ with $J(\hat\alpha_x,z_x)\le J(\beta,z_x)$ for $\lambda_I$-a.e. $x$ and every $\beta\in\mathbb R$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** $I$ is Mathlib's `unitInterval` with `volume`. The operator norm is an extended nonnegative real; for a graphon it is finite ($\|\mathbf W\|\le\|w\|_2$), so its real value is the paper's $\|\mathbf W\|$. The aggregate is a predicate on representatives, not a map. The best response uses Hilbert's choice operator; under Assumption 4 the minimizer exists and is unique, so the choice is never a junk value. The equilibrium is the third bullet of Proposition 3.6 (p. 11), which the paper states is equivalent under Assumption 4 to Definition 3.4 (a fixed point of the best response on a rich Fubini extension); the Fubini-extension construction is not formalized. Measurability of $b$ is not assumed, since it follows from Assumption 1. No integrability of $f$ is assumed either: the paper states Assumption 4 on $J$ itself, and every function $J$ arises as a cost with $f(x,\alpha,z)=J(\alpha,z)$, so a non-integrable $f$ (whose Lean integral is $0$) only yields another function $J$ to which the statements apply. In the equilibrium condition the quantifier order is "for a.e. $x$, for every $\beta$", the reading of Proposition 3.6.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, pp. 3, 8, 10–11, 15, Assumptions 1, 4, 5, (1), (6), (8), Proposition 3.6

import Mathlib

namespace GraphonGames.Existence

open MeasureTheory
open scoped ENNReal

/-- The player space `I = [0, 1]`, with Lebesgue measure `volume` (a probability measure). -/
abbrev I : Type := unitInterval

/-- A graphon (p. 8): a symmetric, `𝓑(I) × 𝓑(I)`-measurable, real-valued, square-integrable
function on `I × I`. -/
def IsGraphon (w : I → I → ℝ) : Prop :=
  Measurable (Function.uncurry w) ∧ (∀ x y, w x y = w y x) ∧
    MemLp (Function.uncurry w) 2 (volume : Measure (I × I))

/-- The graphon operator (p. 8): `[W g]_x = ∫_I w(x, y) g(y) dy`. -/
noncomputable def graphonApply (w : I → I → ℝ) (g : I → ℝ) : I → ℝ :=
  fun x => ∫ y, w x y * g y

/-- The operator norm `‖W‖ = sup_{φ ∈ L²(I), ‖φ‖_{L²} = 1} ‖W φ‖_{L²}` (p. 8), in `ℝ≥0∞`. -/
noncomputable def opNorm (w : I → I → ℝ) : ℝ≥0∞ :=
  ⨆ (φ : I → ℝ) (_ : MemLp φ 2 volume ∧ eLpNorm φ 2 volume = 1),
    eLpNorm (graphonApply w φ) 2 volume

/-- Assumption 1 (p. 3), with the standing mean-zero noise (pp. 3, 7). -/
def Asm1 (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ) : Prop :=
  0 ≤ cα ∧ 0 ≤ cz ∧
    (∀ a z a' z', (b a z - b a' z') ^ 2 ≤ cα * (a - a') ^ 2 + cz * (z - z') ^ 2) ∧
    IsProbabilityMeasure μ0 ∧ Integrable (fun ξ => ξ ^ 2) μ0 ∧ ∫ ξ, ξ ∂μ0 = 0

/-- The cost `J(α, z) = E[f(X_{α,z,ξ}, α, z)]` with `X = b(α, z) + ξ`, `ξ ∼ μ₀` ((1), p. 3; p. 10). -/
noncomputable def cost (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (a z : ℝ) : ℝ :=
  ∫ ξ, f (b a z + ξ) a z ∂μ0

/-- Assumption 4 (pp. 10–11) on `J : A × ℝ → ℝ` (first argument the action). -/
def Asm4 (J : ℝ → ℝ → ℝ) (ℓc ℓJ : ℝ) : Prop :=
  0 < ℓc ∧ 0 ≤ ℓJ ∧ (∀ z, ContDiff ℝ 1 (fun a => J a z)) ∧
    (∀ a a' z ε, 0 ≤ ε → ε ≤ 1 →
      J (ε * a + (1 - ε) * a') z ≤
        ε * J a z + (1 - ε) * J a' z - ℓc / 2 * ε * (1 - ε) * |a - a'| ^ 2) ∧
    (∀ a z z', |deriv (fun a => J a z') a - deriv (fun a => J a z) a| ≤ ℓJ * |z' - z|)

/-- Assumption 5 (p. 15): `|b(α, z)| ≤ c₀` for a finite positive constant `c₀`. -/
def Asm5 (b : ℝ → ℝ → ℝ) (c0 : ℝ) : Prop :=
  0 < c0 ∧ ∀ a z, |b a z| ≤ c0

/-- `z` is an aggregate of the profile `α` ((6), Proposition 3.1, p. 8):
`z ∈ L²(I)` and `z_x = ∫_I w(x, y) b(α_y, z_y) dy` for a.e. `x`. -/
def IsAggregate (w : I → I → ℝ) (b : ℝ → ℝ → ℝ) (α z : I → ℝ) : Prop :=
  MemLp z 2 volume ∧ ∀ᵐ x ∂volume, z x = ∫ y, w x y * b (α y) (z y)

/-- The best response `B z` (p. 11): for each player, a minimizer of `a ↦ J(a, z_x)`. -/
noncomputable def bestResponse (J : ℝ → ℝ → ℝ) (z : I → ℝ) : I → ℝ :=
  fun x => Classical.epsilon (fun a => ∀ β, J a (z x) ≤ J β (z x))

/-- Nash equilibrium of the graphon game, in the form of the third bullet of Proposition 3.6 (p. 11):
an `L²` profile `α` with an aggregate `z = Zα` such that for a.e. `x` and every action `β`,
`J(α_x, z_x) ≤ J(β, z_x)`. -/
def IsNash (w : I → I → ℝ) (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (α : I → ℝ) :
    Prop :=
  MemLp α 2 volume ∧ ∃ z, IsAggregate w b α z ∧
    ∀ᵐ x ∂volume, ∀ β : ℝ, cost b f μ0 (α x) (z x) ≤ cost b f μ0 β (z x)

end GraphonGames.Existence


