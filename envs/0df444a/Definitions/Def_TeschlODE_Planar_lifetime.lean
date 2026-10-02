-- Prove2me | Definitions.Def_TeschlODE_Planar_lifetime
-- name    : TeschlODE_Planar_lifetime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T14:22:35.195743+00:00
-- url     : https://prove2.me/theorems/22798183-ff2b-4a0d-84cd-d88e08687f81
-- title:
--   Maximal interval of existence I_x of ẋ = f(x), Eq. (6.8)
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}^n$ (only its values on $M$ matter). An **integral curve at $x$** is a function $\varphi$ on an open interval $J \ni 0$ with $\varphi(0) = x$, $\varphi(s) \in M$ and $\dot\varphi(s) = f(\varphi(s))$ for all $s \in J$. The **maximal interval of existence** of $x$ is
--   $$I_x = \bigcup \{ J : J \text{ is the domain of an integral curve at } x \} = (T_-(x), T_+(x)).$$
--
--   For $f \in C^1(M, \mathbb{R}^n)$ with $M$ open, integral curves at $x$ are unique on common domains, so $I_x$ is the domain of the maximal integral curve of Theorem 6.1. It is the set $W$ of (6.8) sliced at $x$.
--
--   **Formalization Note.** Points are `Fin n → ℝ`. An interval is an open `Set.OrdConnected` set; derivatives are two-sided `HasDerivAt`. For $x \notin M$ the set is empty.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eq. (6.8)

import Mathlib

namespace TeschlODE.Planar

/-- Teschl, §6.2, (6.8), p. 189: the maximal interval of existence `I_x = (T₋(x), T₊(x))` of the
autonomous equation `ẋ = f(x)` on the open set `M ⊆ ℝⁿ` (points `Fin n → ℝ`). A time `t` belongs
to `lifetime f M x` iff some integral curve `φ` at `x` (`φ 0 = x`), defined on an open interval
`J ∋ 0, t`, staying in `M` and satisfying `φ'(s) = f(φ(s))` for every `s ∈ J`, is defined at `t`.
This is the union of the domains of all integral curves at `x`, i.e. the domain of the maximal
one (Theorem 2.13 / 6.1). It is empty when `x ∉ M`. -/
def lifetime {n : ℕ} (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    Set ℝ :=
  {t | ∃ (J : Set ℝ) (φ : ℝ → Fin n → ℝ), IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
    φ 0 = x ∧ ∀ s ∈ J, φ s ∈ M ∧ HasDerivAt φ (f (φ s)) s}

end TeschlODE.Planar


