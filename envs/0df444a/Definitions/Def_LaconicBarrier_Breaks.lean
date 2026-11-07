-- Prove2me | Definitions.Def_LaconicBarrier_Breaks
-- name    : LaconicBarrier_Breaks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:21.881408+00:00
-- url     : https://prove2.me/theorems/bf71de26-1202-476c-a7cb-33e094c72cee
-- title:
--   $\Gamma$-breaking a game; nonnegligible advantage
-- statement:
--   An advantage function $\delta : \mathbb N \to \mathbb R$ **$\Gamma$-breaks** a game if there is a polynomial $p$ such that $\delta(\lambda) > 1/p(\Gamma(\lambda))$ for infinitely many $\lambda$. With $\Gamma(\lambda) = \lambda$ this says that $\delta$ is **nonnegligible**.
--
--   **Formalization Note** The polynomial is written as $(t+2)^e$: $\delta(\lambda) > (\Gamma(\lambda)+2)^{-e}$ for some $e \in \mathbb N$ and infinitely many $\lambda$. Every positive polynomial is at most $(t+2)^e$ for some $e$, so this is the same notion, and it avoids $1/p = 1/0 = 0$ at a root of $p$.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.1, p.15

import Mathlib

namespace LaconicBarrier

/-- **Γ-breaking** (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…),
Definition 4.1, p.15): the advantage function `δ` exceeds `1/p(Γ(λ))` for some polynomial `p` and
infinitely many `λ`. With `Γ(λ) = λ` this is "`δ` is nonnegligible".

**Formalization Note** "There is a polynomial `p` with `δ(λ) > 1/p(Γ(λ))` infinitely often" is
written `δ(λ) > (Γ(λ) + 2)^{-e}` for some `e ∈ ℕ`: every positive polynomial is at most
`(t + 2)^e` for some `e`, and `(t + 2)^e` is a polynomial. This avoids `1/p = 1/0 = 0` for a
polynomial with a root. -/
def Breaks (Γ : ℕ → ℕ) (δ : ℕ → ℝ) : Prop :=
  ∃ e : ℕ, ∃ᶠ lam in Filter.atTop, (((Γ lam : ℝ) + 2) ^ e)⁻¹ < δ lam

end LaconicBarrier


