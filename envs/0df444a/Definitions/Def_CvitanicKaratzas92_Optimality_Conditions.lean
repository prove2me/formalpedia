-- Prove2me | Definitions.Def_CvitanicKaratzas92_Optimality_Conditions
-- name    : CvitanicKaratzas92_Optimality_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:31:22.650507+00:00
-- url     : https://prove2.me/theorems/7e43ab3e-5811-40fa-8967-20cb70fc97e8
-- title:
--   Section 10 — conditions (A) optimality, (B) financibility, (C) minimality, (D) dual optimality, (E) parsimony; condition (12.2)
-- statement:
--   Fix an initial capital $x>0$.
--
--   **(A) Optimality of $(\hat\pi,\hat c)$.** The pair $(\hat\pi,\hat c)\in\mathcal A'(x)$, with wealth $\hat X$ in $\mathcal M$, satisfies
--   $$E\Big[\int_0^TU_1(t,c(t))\,dt+U_2(X^{x,\pi,c}(T))\Big]\le E\Big[\int_0^TU_1(t,\hat c(t))\,dt+U_2(\hat X(T))\Big]\quad\forall(\pi,c)\in\mathcal A'(x), \tag{10.1}$$
--   as well as
--   $$E\Big[\int_0^T\hat c(t)U_1'(t,\hat c(t))\,dt+\hat X(T)U_2'(\hat X(T))\Big]<\infty. \tag{10.2}$$
--
--   The remaining conditions concern a process $\lambda\in\mathcal D'$, with $y=\mathcal Y_\lambda(x)$, i.e. $\mathcal X_\lambda(y)=x$, and $c_\lambda,\xi_\lambda,X_\lambda$ of (8.17)–(8.19).
--
--   **(B) Financibility of $(c_\lambda,\xi_\lambda)$.** There exists a portfolio process $\hat\pi_\lambda$ such that $(\hat\pi_\lambda,c_\lambda)\in\mathcal A'(x)$ and
--   $$\hat\pi_\lambda(t,\omega)\in K,\qquad \delta(\lambda(t,\omega))+\hat\pi_\lambda^*(t,\omega)\lambda(t,\omega)=0,\qquad X^{x,\hat\pi_\lambda,c_\lambda}(t,\omega)=X_\lambda(t,\omega) \tag{10.3}$$
--   hold for $\ell\otimes P$-a.e. $(t,\omega)$.
--
--   **(C) Minimality of $\lambda$.** For every $\nu\in\mathcal D$,
--   $$E\Big[\int_0^TU_1(t,c_\lambda(t))\,dt+U_2(\xi_\lambda)\Big]=V_\lambda(x)\le V_\nu(x). \tag{10.4}$$
--
--   **(D) Dual optimality of $\lambda$.** For every $\nu\in\mathcal D$,
--   $$E\Big[\int_0^T\tilde U_1(t,yH_\lambda(t))\,dt+\tilde U_2(yH_\lambda(T))\Big]\le E\Big[\int_0^T\tilde U_1(t,yH_\nu(t))\,dt+\tilde U_2(yH_\nu(T))\Big],\qquad y=\mathcal Y_\lambda(x). \tag{10.5}$$
--
--   **(E) Parsimony of $\lambda$.** For every $\nu\in\mathcal D$,
--   $$E\Big[\int_0^TH_\nu(t)c_\lambda(t)\,dt+H_\nu(T)\xi_\lambda\Big]\le x. \tag{10.6}$$
--
--   **Condition (12.2).** For every $y\in(0,\infty)$ there is $\nu\in\mathcal D$ with $\tilde J(y;\nu)<\infty$.
--
--   These five conditions are the subject of Theorem 10.1.
--
--   **Formalization Note** In (A), the expectation in (10.2) is of a nonnegative quantity; at $\hat c(t)=0$ or $\hat X(T)=0$ the product is $0$. In (B), `CondBWith` states the content for a given portfolio $\hat\pi_\lambda$ and process $X$, and (B) is its existential closure. The identity $X=X_\lambda$ is required as "for every $t\le T$, $X(t)=X_\lambda(t)$ a.s.": $X_\lambda(t)$ is one conditional expectation per $t$, and for the continuous $X$ this is the paper's $\ell\otimes P$-a.e. identity. The equation $\delta(\lambda)+\hat\pi_\lambda^*\lambda=0$ is an extended-real equation, false where $\delta(\lambda)=+\infty$. (D) compares $\tilde J(y;\lambda)\le\tilde J(y;\nu)$ in the extended reals. The number $y$ standing for $\mathcal Y_\lambda(x)$ is an argument.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 785–786, Section 10, (A) (10.1)–(10.2), (B)–(E) (10.3)–(10.6); p. 791, (12.2)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Problem

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
variable (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
  (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
  (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
  (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)

/-- Condition (A), p. 785, optimality of `(π̂, ĉ)` with wealth `X̂`: the triple lies in `𝒜'(x)`,
(10.1) `J(x; π, c) ≤ J(x; π̂, ĉ)` for every `(π, c) ∈ 𝒜'(x)`, and (10.2)
`E[∫₀ᵀ ĉ(t)U₁'(t, ĉ(t)) dt + X̂(T)U₂'(X̂(T))] < ∞`. -/
def CondA (x : ℝ) (τ : Triple Ω d) : Prop :=
  τ ∈ A' P 𝓕 T I M K U1 U2 x ∧
  (∀ τ' ∈ A' P 𝓕 T I M K U1 U2 x, J P T U1 U2 τ' ≤ J P T U1 U2 τ) ∧
  ∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T,
      ENNReal.ofReal (τ.c s.toNNReal ω * deriv (U1 s.toNNReal) (τ.c s.toNNReal ω))) +
    ENNReal.ofReal (τ.X T ω * deriv U2 (τ.X T ω))) ∂P < ⊤

/-- The content of condition (B), p. 786, for a given portfolio `π̂_λ` and process `X`:
`(π̂_λ, c_λ)` with wealth `X` lies in `𝒜'(x)`, and (10.3) `π̂_λ(t, ω) ∈ K`,
`δ(λ(t, ω)) + π̂_λ*(t, ω)λ(t, ω) = 0` hold for `ℓ ⊗ P`-a.e. `(t, ω)`, and `X` is a version of
`X_λ` of (8.19) on `[0, T]` (`X(t) = X_λ(t)` a.s. for every `t ≤ T`; the page states
`X(t, ω) = X_λ(t, ω)` `ℓ ⊗ P`-a.e., the same thing for continuous `X`, since `X_λ` is defined
through one conditional expectation per `t`). Here `y` stands for `𝒴_λ(x)`. -/
def CondBWith (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y x : ℝ)
    (πhat : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ⟨πhat, cNu I M K U1 lam y, X⟩ ∈ A' P 𝓕 T I M K U1 U2 x ∧
  (∀ᵐ q ∂(lebP P T),
    πhat q.1.toNNReal q.2 ∈ K ∧
    delta K (lam q.1.toNNReal q.2) +
      ((inner ℝ (πhat q.1.toNNReal q.2) (lam q.1.toNNReal q.2) : ℝ) : EReal) = 0) ∧
  ∀ t ≤ T, ∀ᵐ ω ∂P, X t ω = XNu P 𝓕 T I M K U1 U2 lam y t ω

/-- Condition (B), p. 786, financibility of `(c_λ, ξ_λ)`: there is a portfolio `π̂_λ` (with its
wealth process `X`) satisfying `CondBWith`. Here `y` stands for `𝒴_λ(x)`. -/
def CondB (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y x : ℝ) : Prop :=
  ∃ πhat X, CondBWith P 𝓕 T I M K U1 U2 lam y x πhat X

/-- Condition (C), p. 786, minimality of `λ`: for every `ν ∈ 𝒟`, (10.4)
`E[∫₀ᵀ U₁(t, c_λ(t)) dt + U₂(ξ_λ)] = V_λ(x) ≤ V_ν(x)`. Here `y` stands for `𝒴_λ(x)`. -/
def CondC (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y x : ℝ) : Prop :=
  ∀ ν, IsD P 𝓕 T K ν →
    expUtil P T U1 U2 (cNu I M K U1 lam y) (xiNu T I M K U2 lam y) =
        Vnu P 𝓕 T I M K U1 U2 lam x ∧
      Vnu P 𝓕 T I M K U1 U2 lam x ≤ Vnu P 𝓕 T I M K U1 U2 ν x

/-- Condition (D), p. 786, dual optimality of `λ`: for every `ν ∈ 𝒟`, (10.5)
`E[∫₀ᵀ Ũ₁(t, yH_λ(t)) dt + Ũ₂(yH_λ(T))] ≤ E[∫₀ᵀ Ũ₁(t, yH_ν(t)) dt + Ũ₂(yH_ν(T))]`, i.e.
`J̃(y; λ) ≤ J̃(y; ν)`, with `y = 𝒴_λ(x)`. -/
def CondD (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y : ℝ) : Prop :=
  ∀ ν, IsD P 𝓕 T K ν → Jtilde P T I M K U1 U2 y lam ≤ Jtilde P T I M K U1 U2 y ν

/-- Condition (E), p. 786, parsimony of `λ`: for every `ν ∈ 𝒟`, (10.6)
`E[∫₀ᵀ H_ν(t)c_λ(t) dt + H_ν(T)ξ_λ] ≤ x`. Here `y` stands for `𝒴_λ(x)`. -/
def CondE (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y x : ℝ) : Prop :=
  ∀ ν, IsD P 𝓕 T K ν →
    ∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T,
        ENNReal.ofReal (HNu I M K ν s.toNNReal ω * cNu I M K U1 lam y s.toNNReal ω)) +
      ENNReal.ofReal (HNu I M K ν T ω * xiNu T I M K U2 lam y ω)) ∂P ≤ ENNReal.ofReal x

/-- (12.2), p. 791: for every `y ∈ (0, ∞)` there is `ν ∈ 𝒟` with `J̃(y; ν) < ∞`. -/
def Cond122 : Prop :=
  ∀ y > 0, ∃ ν, IsD P 𝓕 T K ν ∧ Jtilde P T I M K U1 U2 y ν < ⊤

end CvitanicKaratzas92.Optimality


