-- Prove2me | Definitions.Def_TeschlODE_Stability_IsMaximalFlow
-- name    : TeschlODE_Stability_IsMaximalFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:02:32.671242+00:00
-- url     : https://prove2.me/theorems/7f9102dd-0e50-4f6f-bac7-1dea0945d05b
-- title:
--   The (local) flow $\Phi$ of $\dot x = f(x)$ with maximal intervals $I_x$ (6.8)–(6.9)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}^n$. Given, for every $x$, a set of times $I_x \subseteq \mathbb{R}$ and a map $\Phi : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}^n$, we say that **$\Phi$ is the flow of $\dot x = f(x)$ on $M$ with maximal intervals $I_x$** if for every $x \in M$:
--
--   1. $t \mapsto \Phi(t, x)$ is an integral curve of (6.7) in $M$ on $I_x$ (so $I_x$ is an open interval), with $0 \in I_x$ and $\Phi(0, x) = x$;
--   2. it is the unique maximal one: every integral curve $\psi$ in $M$ on an open interval $J$ with $0 \in J$ and $\psi(0) = x$ satisfies
--   $$J \subseteq I_x \quad\text{and}\quad \psi(t) = \Phi(t, x) \ \text{ for all } t \in J .$$
--
--   Thus $I_x = (T_-(x), T_+(x))$ is the maximal interval of existence of the solution through $x$, and $\Phi$ restricted to $W = \bigcup_{x \in M} I_x \times \{x\}$ (6.8) is the map $(t, x) \mapsto \varphi(t, x)$ of (6.9). When $f \in C^1$ on an open $M$, such a pair $(I, \Phi)$ exists and is unique on $W$ (Theorem 6.1), so every statement quantifying over it is a statement about *the* flow.
--
--   **Formalization Note.** The flow is local: nothing asserts $I_x = \mathbb{R}$. The values $\Phi(t, x)$ and $I_x$ for $x \notin M$, and $\Phi(t, x)$ for $t \notin I_x$, are unconstrained and carry no meaning; every statement of the mission only reads $\Phi$ on $W$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eqs. (6.8)–(6.9)

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve

namespace TeschlODE.Stability

/-- Teschl, §6.2, p. 189, (6.8)–(6.9): `Φ` is the (local) flow of `ẋ = f(x)` on `M`, with
maximal time intervals `I x = (T₋(x), T₊(x))`. For every `x ∈ M`, the curve `t ↦ Φ t x` on
`I x` is an integral curve with `0 ∈ I x` and `Φ 0 x = x`, and it is the unique maximal one:
every integral curve `ψ` on an interval `J ∋ 0` with `ψ 0 = x` satisfies `J ⊆ I x` and agrees
with `Φ · x` on `J`. The flow's domain is `W = ⋃_{x ∈ M} I x × {x}`; values of `Φ t x` and
`I x` outside `W` (i.e. for `x ∉ M` or `t ∉ I x`) carry no meaning. -/
def IsMaximalFlow {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ M,
    IsIntegralCurve f M (I x) (fun t => Φ t x) ∧ (0 : ℝ) ∈ I x ∧ Φ 0 x = x ∧
    ∀ (J : Set ℝ) (ψ : ℝ → EuclideanSpace ℝ (Fin n)),
      IsIntegralCurve f M J ψ → (0 : ℝ) ∈ J → ψ 0 = x → J ⊆ I x ∧ ∀ t ∈ J, ψ t = Φ t x

end TeschlODE.Stability


