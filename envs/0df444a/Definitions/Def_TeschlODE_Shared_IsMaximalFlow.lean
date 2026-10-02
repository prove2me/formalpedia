-- Prove2me | Definitions.Def_TeschlODE_Shared_IsMaximalFlow
-- name    : TeschlODE_Shared_IsMaximalFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T17:17:00.407344+00:00
-- url     : https://prove2.me/theorems/bf634e33-0920-4000-be01-50efd43a3b4a
-- title:
--   The (local) flow $\Phi$ of $\dot x = f(x)$ with maximal intervals $I_x$ (6.8)–(6.9)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}^n$. Given a set of times $I_x \subseteq \mathbb{R}$ for every $x$ and a map $\Phi : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}^n$, we say that **$\Phi$ is the flow of $\dot x = f(x)$ on $M$ with maximal intervals $I_x$** if for every $x \in M$:
--
--   1. $t \mapsto \Phi(t, x)$ is an integral curve of (6.7) in $M$ on $I_x$, with $0 \in I_x$ and $\Phi(0, x) = x$;
--   2. it is the unique maximal one: every integral curve $\psi$ in $M$ on an open interval $J \ni 0$ with $\psi(0) = x$ satisfies
--   $$J \subseteq I_x \quad\text{and}\quad \psi(t) = \Phi(t, x) \ \text{ for all } t \in J .$$
--
--   So $I_x = (T_-(x), T_+(x))$ is the maximal interval of existence through $x$ and $\Phi$ on $W = \bigcup_{x \in M} I_x \times \{x\}$ is the map of (6.8)–(6.9). For $f \in C^1$ on an open $M$ such a pair exists and is unique on $W$ (Theorem 6.1).
--
--   This one definition serves chunk 08-hartman-grobman (Theorem 9.9, Hartman–Grobman, p. 264) and chunk 10-periodic-orbits (Lemma 12.1, p. 316; Corollary 12.3 and Theorem 12.4, p. 317; Corollary 12.5, p. 318; Lemmas 12.6 and 12.7, p. 319).
--
--   **Formalization Note.** The flow is local: nothing asserts $I_x = \mathbb{R}$. Values of $\Phi(t, x)$ and $I_x$ for $x \notin M$ or $t \notin I_x$ are unconstrained and are never read.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eqs. (6.8)–(6.9)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsIntegralCurve

namespace TeschlODE.Shared

/-- Teschl, §6.2, p. 189, (6.8)–(6.9): `Φ` is the (local) flow of `ẋ = f(x)` on `M`, with
maximal time intervals `I x = (T₋(x), T₊(x))`. For every `x ∈ M`, the curve `t ↦ Φ t x` on
`I x` is an integral curve with `0 ∈ I x` and `Φ 0 x = x`, and it is the unique maximal one:
every integral curve `ψ` on an interval `J ∋ 0` with `ψ 0 = x` satisfies `J ⊆ I x` and agrees
with `Φ · x` on `J`. Values of `Φ t x` and `I x` for `x ∉ M` or `t ∉ I x` carry no meaning. -/
def IsMaximalFlow {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ x ∈ M,
    IsIntegralCurve f M (I x) (fun t => Φ t x) ∧ (0 : ℝ) ∈ I x ∧ Φ 0 x = x ∧
    ∀ (J : Set ℝ) (ψ : ℝ → (Fin n → ℝ)),
      IsIntegralCurve f M J ψ → (0 : ℝ) ∈ J → ψ 0 = x → J ⊆ I x ∧ ∀ t ∈ J, ψ t = Φ t x

end TeschlODE.Shared


