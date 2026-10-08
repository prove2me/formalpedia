-- Prove2me | Definitions.Def_QiNonsmoothEq_Damped_Setting
-- name    : QiNonsmoothEq_Damped_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:03.74669+00:00
-- url     : https://prove2.me/theorems/b4c0f2d4-4b52-47a9-bf37-71fb0ac1c196
-- title:
--   §§1–4, pp. 227–236 — B-differentiability (2.1), semicontinuity of degree 2 (2.5), strong BD-regularity, the norm function g, and the damped Newton method (Algorithm 4.1)
-- statement:
--   Throughout, $F:\mathbb R^n\to\mathbb R^n$ and $\mathbb R^n$ carries the Euclidean norm. $F'(x;h)=\lim_{t\downarrow 0}(F(x+th)-F(x))/t$ denotes the one-sided directional derivative and $\partial_B F(x)$ the B-subdifferential (2.12): the set of limits of Jacobians $\nabla F(x_i)$ along sequences $x_i\to x$ of points where $F$ is differentiable.
--
--   1. **Directional differentiability.** $F$ is directionally differentiable at $x$ if $F'(x;h)$ exists for every $h\in\mathbb R^n$.
--   2. **B-differentiability** (2.1). $F$ is B-differentiable at $x$ if it is directionally differentiable at $x$ and
--   $$\lim_{h\to 0}\frac{F(x+h)-F(x)-F'(x;h)}{\|h\|}=0.$$
--   3. **Semicontinuity of degree 2** (2.5). $F'(\cdot,\cdot)$ is semicontinuous of degree 2 at $x$ if there are a constant $L$ and a neighbourhood $N$ of $x$ such that $\|F'(x+h;h)-F'(x;h)\|\le L\|h\|^2$ for all $x+h\in N$.
--   4. **Nonsingularity.** A linear operator $V$ on $\mathbb R^n$ is nonsingular if it has a two-sided inverse $W$ ($WV=VW=I$).
--   5. **Strong BD-regularity** (p. 233). $F$ is strongly BD-regular at $x$ if every $V\in\partial_B F(x)$ is nonsingular.
--   6. **The norm function** (§1). $g(x)=\tfrac12 F(x)^{\mathsf T}F(x)=\tfrac12\|F(x)\|^2$.
--   7. **The Armijo test** (4.1). Given scalars $s,\beta,\sigma$, a point $y$, a direction $d$ and a nonnegative integer $m$, the test is
--   $$g(y)-g(y+\beta^m s\,d)\ \ge\ -\sigma\beta^m s\,g'(y;d).$$
--   8. **The damped Newton method** (Algorithm 4.1). Sequences $x^k$, $d^k$ and $\alpha_k$ ($k=0,1,2,\dots$) form a run with parameters $s,\beta,\sigma$ if for every $k$: $d^k$ solves the generalized Newton equation (3.12)
--   $$F(x^k)+F'(x^k;d^k)=0,$$
--   $\alpha_k=\beta^{m_k}s$ where $m_k$ is the **first** nonnegative integer $m$ for which the test (4.1) holds at $(x^k,d^k)$, and $x^{k+1}=x^k+\alpha_k d^k$.
--
--   These are the objects of §4 of the paper: the goal theorem asks when a run of Algorithm 4.1 converges to a zero of $F$ with unit steps.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so $F(x)^{\mathsf T}F(x)=\|F(x)\|^2$. The directional derivative and $\partial_B F$ are the published definitions `NonsmoothNewton.Local.dirDeriv` and `NonsmoothNewton.Shared.bJac`. The value $F'(x;h)$ (and $g'(y;d)$) is a limit that Lean evaluates to a default where it does not exist; equation (3.12) is therefore encoded as the existence statement "the directional derivative of $F$ at $x^k$ along $d^k$ exists and equals $-F(x^k)$". Nonsingularity is stated by an explicit inverse, never by Lean's total inverse. The constraints $s>0$, $\beta\in(0,1)$, $\sigma\in(0,1/2)$ and the condition $F(x^k)\ne0$ are hypotheses of the theorems, not part of the definition of a run.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 227 (§1, g = ½FᵀF), p. 229 (2.1), (2.5), p. 233 (2.12) and strong BD-regularity, p. 235 (3.12), p. 236 Algorithm 4.1 and (4.1), https://doi.org/10.1287/moor.18.1.227

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_NonsmoothNewton_Local_dirDeriv

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

/-- `F` is directionally differentiable at `x`: the one-sided directional derivative
`F'(x; h)` exists for every direction `h` (Qi 1993, §2, p. 229). -/
def DirDiffAt {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ h, ∃ d, HasDirDerivAt F x h d

/-- B-differentiability at `x`, Qi 1993, (2.1), p. 229: `F` is directionally differentiable
at `x` and `(F(x + h) - F(x) - F'(x; h)) / ‖h‖ → 0` as `h → 0`. -/
def BDiffAt {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  DirDiffAt F x ∧
    Tendsto (fun h => ‖h‖⁻¹ * ‖F (x + h) - F x - dirDeriv F x h‖) (𝓝[≠] 0) (𝓝 0)

/-- The directional derivative `F'(·, ·)` is semicontinuous of degree 2 at `x`,
Qi 1993, (2.5), p. 229: there are a constant `L` and a neighbourhood `N` of `x` with
`‖F'(x + h; h) - F'(x; h)‖ ≤ L ‖h‖²` whenever `x + h ∈ N`. (Every statement using it also
assumes directional differentiability on a neighbourhood of `x`, as the page does.) -/
def SemicontDeg2At {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ L : ℝ, ∃ N ∈ 𝓝 x, ∀ h, x + h ∈ N →
    ‖dirDeriv F (x + h) h - dirDeriv F x h‖ ≤ L * ‖h‖ ^ 2

/-- `W` is a two-sided inverse of the linear operator `V`. "`V` is nonsingular" is
`∃ W, IsInverse V W`. -/
def IsInverse {n : ℕ} (V W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  W.comp V = ContinuousLinearMap.id ℝ _ ∧ V.comp W = ContinuousLinearMap.id ℝ _

/-- Strong BD-regularity, Qi 1993, p. 233: every `V ∈ ∂_B F(x)` is nonsingular. -/
def StronglyBDRegularAt {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ V ∈ bJac F x, ∃ W, IsInverse V W

/-- The norm function `g(x) = ½ F(x)ᵀF(x) = ½ ‖F(x)‖²` of Qi 1993, §1, p. 227. -/
noncomputable def normFn {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2) * ‖F x‖ ^ 2

/-- The Armijo test (4.1) of Algorithm 4.1, Qi 1993, p. 236, at the trial index `m`:
`g(y) - g(y + β^m s d) ≥ -σ β^m s g'(y; d)`. -/
def armijoTest {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (s β σ : ℝ) (y d : EuclideanSpace ℝ (Fin n)) (m : ℕ) : Prop :=
  normFn F y - normFn F (y + (β ^ m * s) • d) ≥ -σ * β ^ m * s * dirDeriv (normFn F) y d

/-- A run of the damped Newton method, Algorithm 4.1, Qi 1993, p. 236: at every step `d k`
solves the generalized Newton equation (3.12) `F(x^k) + F'(x^k; d^k) = 0`, the step is
`α_k = β^{m_k} s` where `m_k` is the first nonnegative integer passing (4.1), and
`x^{k+1} = x^k + α_k d^k`. -/
def IsDampedNewtonRun {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (s β σ : ℝ) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) : Prop :=
  ∀ k, HasDirDerivAt F (x k) (d k) (-F (x k)) ∧
    (∃ m : ℕ, armijoTest F s β σ (x k) (d k) m ∧
      (∀ j < m, ¬ armijoTest F s β σ (x k) (d k) j) ∧ α k = β ^ m * s) ∧
    x (k + 1) = x k + α k • d k

end QiNonsmoothEq.Damped


