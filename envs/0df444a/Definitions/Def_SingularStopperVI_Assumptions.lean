-- Prove2me | Definitions.Def_SingularStopperVI_Assumptions
-- name    : SingularStopperVI_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:43.982798+00:00
-- url     : https://prove2.me/theorems/2ede40f3-91af-47cb-8eeb-a4fe682b71ae
-- title:
--   Assumptions 3.1, 3.2 and Problem A
-- statement:
--   **Assumption 3.1.** $b,\sigma$ are continuously differentiable and locally Lipschitz, $|b(x)|_d+|\sigma(x)|_{d\times d'}\le D_1(1+|x|_d)$, and $a=\sigma\sigma^\top$ is elliptic on every bounded set.
--
--   **Assumption 3.2.** $f,g,h\ge0$ on $[0,T]\times\mathbb R^d$, and for some $\alpha\in(0,1)$:
--
--   1. $f^2,g\in C^{1,2,\alpha}_{\ell oc}$ and $h\in C^{0,1,\alpha}_{\ell oc}$;
--   2. $t\mapsto f(t,x)$ is non-increasing and $f\le c(1+|x|_d^\kappa)$;
--   3. $h(t,x)-h(s,x)\le K_0(t-s)$ and $g(t,x)-g(s,x)\le K_0(t-s)$ for $s<t$;
--   4. $0\le g+h\le K_1(1+|x|_d^2)$;
--   5. $|\nabla g|_d\le f$;
--   6. $\Theta=h+\partial_tg+\mathcal Lg-rg\ge-K_2$.
--
--   **Problem A.** For $p>d+2$, find $u\in W^{1,2,p}_{\ell oc}$ of quadratic growth such that, with $\mathcal I=\{|\nabla u|_d<f\}$ and $\mathcal C=\{u>g\}$,
--
--   $$
--   \begin{cases}
--   \partial_tu+\mathcal Lu-ru=-h&\text{on }\mathcal C\cap\mathcal I,\\
--   \partial_tu+\mathcal Lu-ru\ge-h&\text{a.e. on }\mathcal C,\\
--   \partial_tu+\mathcal Lu-ru\le-h&\text{a.e. on }\mathcal I,\\
--   u\ge g,\quad |\nabla u|_d\le f&\text{everywhere},\\
--   u(T,\cdot)=g(T,\cdot).
--   \end{cases}
--   $$
--
--   The value of the game is the maximal solution of this problem.
--
--   **Formalization Note** The constants and the derivatives $J_g$ of $g$ are parameters of `Assumption32`. The exponent in (ii), printed $p$, is called $\kappa$. In Problem A, $u$ and its gradient are the continuous representatives of (2.2), and on $\mathcal C\cap\mathcal I$ the function $u$ is classically $C^{1,2}$, with the equation holding pointwise for these classical derivatives; the two a.e. lines use the weak derivatives.
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, Problem A, (3.5), p.6; Assumptions 3.1, 3.2, pp.6–7

import Mathlib
import Definitions.Def_SingularStopperVI_Game

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularStopperVI

variable {d d' : ℕ}

/-- The norm `|M|_{d×d'} = (Σ_{ij} M_{ij}²)^{1/2}`, §2, p.3. -/
noncomputable def frobNorm (M : Matrix (Fin d) (Fin d') ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The quadratic form `⟨ζ, A ζ⟩`. -/
def quadForm (A : Matrix (Fin d) (Fin d) ℝ) (ζ : Euc d) : ℝ :=
  ∑ i, ∑ j, ζ i * A i j * ζ j

/-- Assumption 3.1, p.6: `b`, `σ` are continuously differentiable and locally Lipschitz, of linear
growth, and `a = σσ^⊤` is elliptic on every bounded set, (3.6).

**Formalization Note** Bounded sets are exhausted by the balls `B̄_R`. -/
structure Assumption31 (D : Data d d') : Prop where
  b_C1 : ContDiff ℝ 1 D.b
  σ_C1 : ∀ i j, ContDiff ℝ 1 (fun x => D.σ x i j)
  b_lip : LocallyLipschitz D.b
  σ_lip : ∀ i j, LocallyLipschitz (fun x => D.σ x i j)
  growth : ∃ D1 : ℝ, 0 < D1 ∧ ∀ x, ‖D.b x‖ + frobNorm (D.σ x) ≤ D1 * (1 + ‖x‖)
  elliptic : ∀ R : ℝ, 0 < R → ∃ θ : ℝ, 0 < θ ∧ ∀ x ∈ Metric.closedBall (0 : Euc d) R, ∀ ζ : Euc d,
    θ * ‖ζ‖ ^ 2 ≤ quadForm (diffusionMatrix D x) ζ

/-- Assumption 3.2, pp.6–7, with exponent `α ∈ (0,1)`, constants `K0`, `K1`, `K2` of (3.7), (3.8),
(3.10), and `Jg` the derivatives of `g`.

**Formalization Note** The source's existential constants are parameters here, so that Lemmas 5.6
and 5.7 can name them. The exponent of (ii), written `p` on the page, is `κ`: it is unrelated to the
Sobolev `p`. (3.7) prints "all `x ∈ ℝ^{d+1}_{0,T}`" and is read `x ∈ ℝ^d`. -/
structure Assumption32 (D : Data d d') (α : ℝ) (Jg : Jet d) (K0 K1 K2 : ℝ) : Prop where
  alpha_mem : α ∈ Ioo (0 : ℝ) 1
  f_nonneg : ∀ t ∈ Icc 0 D.T, ∀ x, 0 ≤ D.f t x
  g_nonneg : ∀ t ∈ Icc 0 D.T, ∀ x, 0 ≤ D.g t x
  h_nonneg : ∀ t ∈ Icc 0 D.T, ∀ x, 0 ≤ D.h t x
  /-- (i): it is `f²`, not `f`, that lies in the class -/
  f_sq_reg : ∃ Jf : Jet d, IsC12AlphaEll D.T α (fun t x => D.f t x ^ 2) Jf
  g_reg : IsC12AlphaEll D.T α D.g Jg
  h_reg : ∃ Dh, IsC01AlphaEll D.T α D.h Dh
  /-- (ii) -/
  f_antitone : ∀ x, AntitoneOn (fun t => D.f t x) (Icc 0 D.T)
  f_growth : ∃ c κ : ℝ, 0 < c ∧ 0 < κ ∧ ∀ t ∈ Icc 0 D.T, ∀ x, D.f t x ≤ c * (1 + ‖x‖ ^ κ)
  /-- (iii), (3.7): one-sided -/
  K0_pos : 0 < K0
  h_time : ∀ s t, 0 ≤ s → s < t → t ≤ D.T → ∀ x, D.h t x - D.h s x ≤ K0 * (t - s)
  g_time : ∀ s t, 0 ≤ s → s < t → t ≤ D.T → ∀ x, D.g t x - D.g s x ≤ K0 * (t - s)
  /-- (iv), (3.8) -/
  K1_pos : 0 < K1
  sum_growth : ∀ t ∈ Icc 0 D.T, ∀ x, D.g t x + D.h t x ≤ K1 * (1 + ‖x‖ ^ 2)
  /-- (v), (3.9) -/
  grad_g : ∀ t ∈ Icc 0 D.T, ∀ x, ‖Jg.Du t x‖ ≤ D.f t x
  /-- (vi), (3.10) -/
  K2_pos : 0 < K2
  theta : ∀ t ∈ Icc 0 D.T, ∀ x, -K2 ≤ D.h t x + pdeOperator D D.g Jg t x

/-- Problem A, p.6, for a given `p`: `u ∈ W^{1,2,p}_{ℓoc}(ℝ^{d+1}_{0,T})` with quadratic growth solves
(3.5), where `I = {|∇u|_d < f}` and `C = {u > g}`.

**Formalization Note** `u` and `Du` are the continuous representatives given by (2.2), which is what
the "for all" lines refer to (p.6). The first line of (3.5) cannot be read with weak derivatives, so
on `C ∩ I` the function `u` is classically `C^{1,2}` with derivatives `K`, and the equation holds
for these at every point (proof of Theorem 6.1, p.31). -/
structure SolvesProblemA (D : Data d d') (p : ℝ) (u : ℝ → Euc d → ℝ) (J : Jet d) : Prop where
  sobolev : IsW12pLoc D.T p u J
  cont_u : ContinuousOn (fun z : ℝ × Euc d => u z.1 z.2) (stateDomain d D.T)
  cont_Du : ContinuousOn (fun z : ℝ × Euc d => J.Du z.1 z.2) (stateDomain d D.T)
  /-- line 1 of (3.5) -/
  pde_inter : ∃ K : Jet d,
    IsClassical12On D.T {z | z ∈ stateDomain d D.T ∧ D.g z.1 z.2 < u z.1 z.2 ∧
      ‖J.Du z.1 z.2‖ < D.f z.1 z.2} u K ∧
    ∀ z ∈ stateDomain d D.T, D.g z.1 z.2 < u z.1 z.2 → ‖J.Du z.1 z.2‖ < D.f z.1 z.2 →
      pdeOperator D u K z.1 z.2 = -D.h z.1 z.2
  /-- line 2 of (3.5) -/
  pde_cont : ∀ᵐ z : ℝ × Euc d, z ∈ stateDomain d D.T → D.g z.1 z.2 < u z.1 z.2 →
    -D.h z.1 z.2 ≤ pdeOperator D u J z.1 z.2
  /-- line 3 of (3.5) -/
  pde_inact : ∀ᵐ z : ℝ × Euc d, z ∈ stateDomain d D.T → ‖J.Du z.1 z.2‖ < D.f z.1 z.2 →
    pdeOperator D u J z.1 z.2 ≤ -D.h z.1 z.2
  /-- line 4 of (3.5) -/
  obstacle : ∀ z ∈ stateDomain d D.T, D.g z.1 z.2 ≤ u z.1 z.2
  /-- line 5 of (3.5) -/
  gradient_le : ∀ z ∈ stateDomain d D.T, ‖J.Du z.1 z.2‖ ≤ D.f z.1 z.2
  /-- line 6 of (3.5) -/
  terminal : ∀ x, u D.T x = D.g D.T x
  growth : ∃ c : ℝ, 0 < c ∧ ∀ z ∈ stateDomain d D.T, |u z.1 z.2| ≤ c * (1 + ‖z.2‖ ^ 2)

/-- `u` is a solution of Problem A for `p`. -/
def IsProblemASolution (D : Data d d') (p : ℝ) (u : ℝ → Euc d → ℝ) : Prop :=
  ∃ J : Jet d, SolvesProblemA D p u J

end SingularStopperVI


