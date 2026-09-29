-- Prove2me | Definitions.Def_LanglandsFunctoriality_converse_data
-- name    : LanglandsFunctoriality_converse_data
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T15:43:24.534558+00:00
-- url     : https://prove2.me/theorems/01b8e898-d915-49bc-94c4-e145dbafac99
-- title:
--   Data for the classical converse theorems: $q$-expansions, twisted $L$-functions, Weil's conditions
-- statement:
--   This file records the classical objects appearing in the converse theorems of the survey's
--   appendix.
--
--   For a sequence $(a_n)_{n\ge1}$ of complex numbers, the attached **$q$-expansion** is
--   $f(\tau)=\sum_{n\ge1}a_n e^{2\pi i n\tau}$, a function on the upper half plane, and for a Dirichlet
--   character $\chi$ of modulus $r$ the **twisted completed $L$-function** is
--
--   $$\Lambda(s,\chi)=(2\pi)^{-s}\Gamma(s)\sum_{n\ge1}\frac{a_n\chi(n)}{n^{s}} .$$
--
--   The congruence subgroup $\Gamma_0(N)\subset SL(2,\mathbb Z)$ is recorded as a subgroup of
--   $GL(2,\mathbb R)$, the shape required to speak of cusp forms for it. The conjugate character
--   $\bar\chi$ and Weil's root number $w_\chi=i^{d}\chi(N)g(\chi)^2$, with $g(\chi)=\sum_{n\bmod r}
--   \chi(n)e^{2\pi i n/r}$ the Gauss sum, are also recorded.
--
--   Finally, **Weil's conditions (W1)–(W3)** for weight $d$ and level $N$ on a sequence $(a_n)$ are: the
--   Dirichlet series converges absolutely in a right half plane; for every primitive character $\chi$ of
--   modulus $r$ coprime to $N$ the function $\Lambda(s,\chi)$ continues to an entire function bounded on
--   vertical strips; and each satisfies
--
--   $$\Lambda(s,\chi)=w_\chi\,r^{-1}\,(r^2N)^{d/2-s}\,\Lambda(d-s,\bar\chi).$$
--
--   **Formalization Note.** The survey writes the right-hand side of (W3) with $\chi$; the conjugate
--   character $\bar\chi$ is used here, as in Weil's original statement.
-- source:
--   J.-H. Yang, Langlands Functoriality Conjecture, arXiv:0808.0917 (2008), https://arxiv.org/abs/0808.0917, p. 23, Appendix, Theorem B (Weil 1967)

import Mathlib
import Definitions.Def_LanglandsFunctoriality_automorphic_data

/-!
# Data for the classical converse theorems

This file records the classical objects used in the converse theorems of Hamburger, Hecke and
Weil: the `q`-expansion attached to a sequence of coefficients, the twisted completed
`L`-function `Λ(s, χ) = (2π)^{-s} Γ(s) ∑ aₙ χ(n) n^{-s}`, the congruence subgroup `Γ₀(N)` seen
inside `GL(2, ℝ)` (the shape Mathlib's `CuspForm` expects), and Weil's hypotheses (W1)–(W3).
-/

namespace LanglandsFunctoriality

open Complex

/-- `Γ₀(N)`, viewed inside `GL(2, ℝ)` so that Mathlib's `CuspForm` applies to it. -/
def Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map
    (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))

/-- The `q`-expansion `f(τ) = ∑_{n ≥ 1} aₙ e^{2π i n τ}` attached to a coefficient sequence. -/
noncomputable def qExpansion (a : ℕ → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' n : ℕ, a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (z : ℂ))

/-- The twisted completed `L`-function `Λ(s, χ) = (2π)^{-s} Γ(s) ∑_{n ≥ 1} aₙ χ(n) n^{-s}`. -/
noncomputable def twistedCompleted (a : ℕ → ℂ) {r : ℕ} (χ : DirichletCharacter ℂ r) (s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
    LSeries (fun n : ℕ => a n * χ (n : ZMod r)) s

/-- The complex conjugate character `χ̄`. -/
noncomputable def conjChar {r : ℕ} (χ : DirichletCharacter ℂ r) : DirichletCharacter ℂ r :=
  χ.ringHomComp (starRingEnd ℂ)

/-- Weil's root number `w_χ = i^d χ(N) g(χ)²`, where `g(χ) = ∑_{n mod r} χ(n) e^{2π i n / r}`
is the Gauss sum. -/
noncomputable def weilRootNumber (d N : ℕ) {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) : ℂ :=
  Complex.I ^ d * χ ((N : ZMod r)) * gaussSum χ ZMod.stdAddChar ^ 2

/-- Weil's hypotheses (W1)–(W3) on a coefficient sequence `a`, for weight `d` and level `N`:

* (W1) the Dirichlet series `∑ aₙ n^{-s}` converges absolutely in some right half plane;
* (W2) for every primitive character `χ` of modulus `r` coprime to `N`, the twisted completed
  `L`-function continues to an entire function bounded on vertical strips;
* (W3) each of them satisfies `Λ(s, χ) = w_χ r^{-1} (r² N)^{d/2 - s} Λ(d - s, χ̄)`. -/
def WeilConditions (d N : ℕ) (a : ℕ → ℂ) : Prop :=
  ∃ σ₀ : ℝ, (∀ s : ℂ, σ₀ < s.re → LSeriesSummable a s) ∧
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r), χ.IsPrimitive → Nat.Coprime r N →
      ∃ Λ Λc : ℂ → ℂ,
        Differentiable ℂ Λ ∧ Differentiable ℂ Λc ∧
        BoundedOnVerticalStrips Λ ∧ BoundedOnVerticalStrips Λc ∧
        (∀ s : ℂ, σ₀ < s.re → Λ s = twistedCompleted a χ s) ∧
        (∀ s : ℂ, σ₀ < s.re → Λc s = twistedCompleted a (conjChar χ) s) ∧
        (∀ s : ℂ, Λ s =
          @weilRootNumber d N r _ χ / (r : ℂ) *
            (((r : ℂ) ^ 2 * (N : ℂ)) ^ ((d : ℂ) / 2 - s)) * Λc ((d : ℂ) - s))

end LanglandsFunctoriality


