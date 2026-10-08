-- Prove2me | Definitions.Def_DataDrivenRO_Guarantee_Setting
-- name    : DataDrivenRO_Guarantee_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:25:06.594014+00:00
-- url     : https://prove2.me/theorems/11e71be9-5e04-48e2-9a8c-004878cf665e
-- title:
--   (P2)/(2), p. 2; (6), p. 10; p. 11 — VaR^ℙ_ε(v), the probabilistic guarantee, its simultaneous version, bi-affine functions
-- statement:
--   This file fixes the objects of §1, §2.1 and §3.1–3.2 of Bertsimas, Gupta and Kallus, *Data-Driven Robust Optimization*. Throughout, $\tilde{\mathbf u}$ is an uncertain parameter in $\mathbb R^d$, $\mathbb P$ is a probability measure on $\mathbb R^d$, and $\mathbf v^T\mathbf u=\sum_i v_i u_i$.
--
--   1. **Value at Risk.** For $\mathbf v\in\mathbb R^d$ and a level $\epsilon$, the Value at Risk of $\tilde{\mathbf u}^T\mathbf v$ is
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)=\inf\{t:\ \mathbb P(\tilde{\mathbf u}^T\mathbf v\le t)\ge 1-\epsilon\}.$$
--   2. **Probabilistic guarantee (P2).** A set $\mathcal U\subseteq\mathbb R^d$ *implies a probabilistic guarantee at level $\epsilon$ for $\mathbb P$* if, for every dimension $k$, every function $f(\mathbf u,\mathbf x)$ with $\mathbf x\in\mathbb R^k$ that is concave in $\mathbf u$ for each $\mathbf x$, and every $\mathbf x^*\in\mathbb R^k$,
--   $$f(\mathbf u,\mathbf x^*)\le 0\ \ \forall\mathbf u\in\mathcal U\quad\Longrightarrow\quad \mathbb P\big(f(\tilde{\mathbf u},\mathbf x^*)\le 0\big)\ge 1-\epsilon .$$
--   3. **Simultaneous guarantee.** A family $\{\mathcal U(\epsilon):0<\epsilon<1\}$ *simultaneously implies a probabilistic guarantee for $\mathbb P$* if each $\mathcal U(\epsilon)$ implies a probabilistic guarantee for $\mathbb P$ at level $\epsilon$.
--   4. **Bi-affine functions.** $f(\mathbf u,\mathbf x)$ is bi-affine if $f(\mathbf u,\mathbf x)=\mathbf u^TF\mathbf x+\mathbf f_u^T\mathbf u+\mathbf f_x^T\mathbf x+f_0$ for a matrix $F\in\mathbb R^{d\times k}$, vectors $\mathbf f_u\in\mathbb R^d$, $\mathbf f_x\in\mathbb R^k$ and a scalar $f_0$.
--
--   The support function $\delta^*(\mathbf v\mid\mathcal U)=\sup_{\mathbf u\in\mathcal U}\mathbf v^T\mathbf u$ of §2.1 is the published `RobustMDP.Shared.supportFunction`. These objects are the vocabulary of Theorem 1, which characterizes (P2) through the comparison of $\delta^*$ with VaR, and of Theorems 2 and 3, which turn it into a data-driven guarantee.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` (coordinates $0,\dots,d-1$) and $\tilde{\mathbf u}$ is the identity map. `VaR P ε v` is the published `MultistageStochastic.valueAtRisk P (u ↦ u ⬝ᵥ v) (1 - ε)`, a real infimum; every statement that uses it assumes $0<\epsilon<1$ and that $\mathbb P$ is a probability measure, under which the infimum is over a nonempty set bounded below. The probability in (P2) is compared as `ENNReal.ofReal (1 - ε) ≤ P {u | f u x* ≤ 0}`. The dimension $k$ of the decision variable is quantified universally in (P2), as the paper's "for any $\mathbf x^*\in\mathbb R^k$ and every $f$" requires; concavity is concavity on all of $\mathbb R^d$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, (P2) and (2), p. 2; bi-affine functions and δ*, §2.1, p. 7; (6), p. 10; simultaneous guarantee, p. 11

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RobustMDP_Shared_supportFunction

open MeasureTheory

namespace DataDrivenRO.Guarantee

/-- Value at Risk at level `ε` in direction `v`, display (6), p. 10 of Bertsimas–Gupta–Kallus,
arXiv:1401.0212v2: `VaR^ℙ_ε(v) = inf {t : ℙ(ũᵀv ≤ t) ≥ 1 − ε}`, where `ũ` is the identity on
`ℝᵈ = Fin d → ℝ`. It is the published `MultistageStochastic.valueAtRisk` at level `1 − ε`
applied to the linear functional `u ↦ uᵀv` (a real `sInf`; every statement using it assumes
`0 < ε < 1` and that `P` is a probability measure, under which the infimum is genuine). -/
noncomputable def VaR {d : ℕ} (P : Measure (Fin d → ℝ)) (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  MultistageStochastic.valueAtRisk P (fun u => u ⬝ᵥ v) (1 - ε)

/-- Property (P2) / implication (2), p. 2: the set `U` *implies a probabilistic guarantee at
level `ε` for `P`* if for every dimension `k` of the decision variable, every function
`f(u, x)` concave in `u` for each `x`, and every `x* ∈ ℝᵏ`, robust feasibility
`f(u, x*) ≤ 0 ∀ u ∈ U` implies `P(f(ũ, x*) ≤ 0) ≥ 1 − ε`. -/
def ImpliesGuarantee {d : ℕ} (P : Measure (Fin d → ℝ)) (U : Set (Fin d → ℝ)) (ε : ℝ) : Prop :=
  ∀ (k : ℕ) (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ),
    (∀ x, ConcaveOn ℝ Set.univ (fun u => f u x)) →
    ∀ xstar : Fin k → ℝ, (∀ u ∈ U, f u xstar ≤ 0) →
      ENNReal.ofReal (1 - ε) ≤ P {u | f u xstar ≤ 0}

/-- p. 11: a family of sets `{U(ε) : 0 < ε < 1}` *simultaneously implies a probabilistic
guarantee for `P`* if, for every `0 < ε < 1`, `U(ε)` implies a probabilistic guarantee for `P`
at level `ε`. -/
def SimultaneouslyImpliesGuarantee {d : ℕ} (P : Measure (Fin d → ℝ))
    (U : ℝ → Set (Fin d → ℝ)) : Prop :=
  ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ImpliesGuarantee P (U ε) ε

/-- §2.1, p. 7: `f(u, x)` is *bi-affine* if `f(u, x) = uᵀFx + f_uᵀu + f_xᵀx + f₀` for some
matrix `F ∈ ℝ^{d×k}`, vectors `f_u ∈ ℝᵈ`, `f_x ∈ ℝᵏ` and scalar `f₀`. -/
def IsBiaffine {d k : ℕ} (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ) : Prop :=
  ∃ (F : Matrix (Fin d) (Fin k) ℝ) (fu : Fin d → ℝ) (fx : Fin k → ℝ) (f0 : ℝ),
    ∀ u x, f u x = u ⬝ᵥ F.mulVec x + fu ⬝ᵥ u + fx ⬝ᵥ x + f0

end DataDrivenRO.Guarantee


