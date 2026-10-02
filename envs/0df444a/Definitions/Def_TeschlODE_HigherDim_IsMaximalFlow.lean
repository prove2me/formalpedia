-- Prove2me | Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
-- name    : TeschlODE_HigherDim_IsMaximalFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:02:47.983085+00:00
-- url     : https://prove2.me/theorems/5713220d-4cfa-40e6-9894-8fcd820c0ba0
-- title:
--   The (local) flow $\Phi$ of $\dot x = f(x)$ with maximal intervals $I_x$ (6.8)–(6.9)
-- statement:
--   Let $M \subseteq E$ and $f : E \to E$. Given, for every $x$, a set of times $I_x \subseteq \mathbb{R}$ and a map $\Phi : \mathbb{R} \times E \to E$, we say that **$\Phi$ is the flow of $\dot x = f(x)$ on $M$ with maximal intervals $I_x$** if for every $x \in M$:
--
--   1. $t \mapsto \Phi(t, x)$ is an integral curve of (6.7) in $M$ on $I_x$ (so $I_x$ is an open interval), with $0 \in I_x$ and $\Phi(0, x) = x$;
--   2. it is the unique maximal one: every integral curve $\psi$ in $M$ on an open interval $J$ with $0 \in J$ and $\psi(0) = x$ satisfies
--   $$J \subseteq I_x \quad\text{and}\quad \psi(t) = \Phi(t, x) \ \text{ for all } t \in J .$$
--
--   Thus $I_x = (T_-(x), T_+(x))$ is the maximal interval of existence of the solution through $x$, and $\Phi$ on $W = \bigcup_{x \in M} I_x \times \{x\}$ is the flow (6.9). For $f \in C^1$ on an open $M$ such a pair $(I, \Phi)$ exists and is unique on $W$ (Theorem 6.1), so a statement quantifying over it is a statement about *the* flow.
--
--   **Formalization Note.** The flow is local: nothing asserts $I_x = \mathbb{R}$. Chapter 8 opens by assuming the flow complete "for simplicity"; this mission keeps the local flow and states, in each theorem, exactly which points must be alive at which times, which contains the complete case. Values $\Phi(t, x)$ for $x \notin M$ or $t \notin I_x$ carry no meaning.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eqs. (6.8)–(6.9)

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve

namespace TeschlODE.HigherDim

/-- Teschl, §6.2, p. 189, (6.8)–(6.9): `Φ` is the (local) flow of `ẋ = f(x)` on `M`, with
maximal time intervals `I x = (T₋(x), T₊(x))`. For every `x ∈ M`, the curve `t ↦ Φ t x` on
`I x` is an integral curve with `0 ∈ I x` and `Φ 0 x = x`, and it is the unique maximal one:
every integral curve `ψ` on an interval `J ∋ 0` with `ψ 0 = x` satisfies `J ⊆ I x` and agrees
with `Φ · x` on `J`. Values of `Φ t x` and `I x` for `x ∉ M` or `t ∉ I x` carry no meaning. -/
def IsMaximalFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
    (M : Set E) (I : E → Set ℝ) (Φ : ℝ → E → E) : Prop :=
  ∀ x ∈ M,
    IsIntegralCurve f M (I x) (fun t => Φ t x) ∧ (0 : ℝ) ∈ I x ∧ Φ 0 x = x ∧
    ∀ (J : Set ℝ) (ψ : ℝ → E),
      IsIntegralCurve f M J ψ → (0 : ℝ) ∈ J → ψ 0 = x → J ⊆ I x ∧ ∀ t ∈ J, ψ t = Φ t x

end TeschlODE.HigherDim


