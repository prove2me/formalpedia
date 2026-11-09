-- Prove2me | Definitions.Def_XorParallelRepetition_Exponential_XorGames
-- name    : XorParallelRepetition_Exponential_XorGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:29.08028+00:00
-- url     : https://prove2.me/theorems/d64ab02a-c216-4cf3-8153-1dba898679c0
-- title:
--   Definitions 1.1 and 2.1 — $k$-XOR games and generalized XOR games
-- statement:
--   Fix a prime $p$ and a finite set $\iota$ of players. A **generalized XOR game** (Definition 2.1) consists of question sets $\Sigma_i$ and a discrete law $\mu$ on tuples $(x,t)$ with $x\in\prod_i\Sigma_i$ and $t\in\mathbb F_p$. The verifier samples $(x,t)\sim\mu$, sends $x_i$ to player $i$, receives $a_i\in\mathbb F_p$, and accepts exactly when
--
--   $$
--   \sum_{i\in\iota}a_i=t.
--   $$
--
--   With no players the verifier accepts exactly when $t=0$. A **$k$-XOR game** (Definition 1.1) has a law on question tuples and a fixed target map $t:\prod_i\Sigma_i\to\mathbb F_p$; it is the generalized game whose law is the image of the question law under $x\mapsto(x,t(x))$.
--
--   The values $\operatorname{val}(\Psi)$ and $\operatorname{val}(\Psi^{\otimes n})$ are those of the corresponding games of the definition `Games`, with the target as the private coin. The module also fixes the root of unity $\omega_p=e^{2\pi i/p}$, the phase $\omega_p^{t}$ for $t\in\mathbb F_p$, the expectation of a complex function under a discrete law, and the predicate that two supported challenges have different right hand sides.
--
--   These are the games on which all statements of the mission are made.
--
--   **Formalization Note** The phase is computed through the representative of $t$ in $\{0,\dots,p-1\}$. The expectation is the series $\sum_a\mu(a)f(a)$; it is used only for bounded $f$, where it converges absolutely.
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Definition 1.1, printed p. 3, PDF p. 3; Definition 2.1, printed p. 9, PDF p. 9

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_Games

open scoped ENNReal

/-!
# XOR games over a prime field

Source: Braverman and Minzer, STOC 2027 submission #195, Definition 1.1 (printed/PDF p. 3) and
Definition 2.1 (p. 9).  The player set `ι` is any finite type; `[k]` is the case `ι = Fin k`, and
`k = 0` is the case of an empty `ι`.
-/

namespace XorParallelRepetition.Exponential

universe u

/-- The primitive root of unity `ω_p = exp(2πi/p)`. -/
noncomputable def omega (p : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / p)

/-- The phase `ω_p^t` of a field element `t ∈ F_p`, read through the representative of `t` in
`{0, …, p - 1}`. -/
noncomputable def phase (p : ℕ) (t : ZMod p) : ℂ :=
  omega p ^ t.val

/-- The expectation `E_{ω∼μ}[f(ω)]` of a complex function under a discrete law.  All functions
in this development are bounded, so the series converges absolutely. -/
noncomputable def expect {α : Type*} (μ : PMF α) (f : α → ℂ) : ℂ :=
  ∑' a, ((μ a).toReal : ℂ) * f a

/-- A generalized XOR game over `F_p` with players `ι` (Definition 2.1): question sets and a
discrete law on tuples `(x, t)` of questions and a right hand side `t ∈ F_p`. -/
structure GeneralizedXorGame (p : ℕ) (ι : Type) where
  /-- The question set of each player. -/
  Q : ι → Type u
  /-- The law of the challenge `(x₁, …, x_k, t)`. -/
  μ : PMF ((∀ i, Q i) × ZMod p)

/-- A `k`-XOR game over `F_p` (Definition 1.1): question sets, a discrete law on question tuples
and a fixed target map. -/
structure XorGame (p : ℕ) (ι : Type) where
  /-- The question set of each player. -/
  Q : ι → Type u
  /-- The law of the question tuple. -/
  μ : PMF (∀ i, Q i)
  /-- The target map `t : Σ₁ × ⋯ × Σ_k → F_p`. -/
  t : (∀ i, Q i) → ZMod p

variable {p : ℕ} {ι : Type}

namespace GeneralizedXorGame

/-- The game played by the verifier of Definition 2.1: sample `(x, t)`, send `x i` to player `i`,
receive `a i ∈ F_p` and accept exactly when `∑ i, a i = t`.  The target is the private coin, so
it is not sent to the players.  With no players the empty sum is `0`, so the verifier accepts
exactly when `t = 0`. -/
def toGame [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι) : Game.{u, 0, 0} ι where
  Question := Ψ.Q
  Answer _ := ZMod p
  Coin := ZMod p
  law := Ψ.μ
  accepts _ t a := ∑ i, a i = t

/-- The value `val(Ψ)`. -/
noncomputable def val [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι) : ℝ :=
  Ψ.toGame.val

/-- The value `val(Ψ^{⊗n})` of the `n`-fold repeated game. -/
noncomputable def repVal [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι) (n : ℕ) : ℝ :=
  (Ψ.toGame.rep n).val

/-- Two supported challenges have different right hand sides. -/
def HasTwoTargets (Ψ : GeneralizedXorGame.{u} p ι) : Prop :=
  ∃ ω₁ ∈ Ψ.μ.support, ∃ ω₂ ∈ Ψ.μ.support, ω₁.2 ≠ ω₂.2

end GeneralizedXorGame

namespace XorGame

/-- A `k`-XOR game read as a generalized XOR game: the right hand side of the sampled questions
`x` is `t x`. -/
noncomputable def toGeneralized (Ψ : XorGame.{u} p ι) : GeneralizedXorGame.{u} p ι where
  Q := Ψ.Q
  μ := Ψ.μ.map fun x => (x, Ψ.t x)

/-- The value `val(Ψ)`: the supremum over `f_i : Σ_i → F_p` of the probability, for `x ∼ μ`, that
`∑ i, f_i(x_i) = t(x)`. -/
noncomputable def val [Fintype ι] (Ψ : XorGame.{u} p ι) : ℝ :=
  Ψ.toGeneralized.val

/-- The value `val(Ψ^{⊗n})` of the `n`-fold repeated game. -/
noncomputable def repVal [Fintype ι] (Ψ : XorGame.{u} p ι) (n : ℕ) : ℝ :=
  Ψ.toGeneralized.repVal n

end XorGame

end XorParallelRepetition.Exponential


