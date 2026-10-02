-- Prove2me | Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
-- name    : TeschlQM_KatoRellich_IsRelativelyBounded
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:57:38.804671+00:00
-- url     : https://prove2.me/theorems/2b7fbfa2-1053-4085-bda7-33529839a017
-- title:
--   Relatively bounded operator and its A-bound, Eq. (6.1)
-- statement:
--   Let $A$ and $B$ be linear operators in a complex Hilbert space $\mathfrak{H}$, with domains $\mathfrak{D}(A)$ and $\mathfrak{D}(B)$. The operator $B$ is **$A$ bounded** (or **relatively bounded** with respect to $A$) if $\mathfrak{D}(A) \subseteq \mathfrak{D}(B)$ and there are constants $a, b \ge 0$ such that
--   $$\|B\psi\| \le a\|A\psi\| + b\|\psi\|, \qquad \psi \in \mathfrak{D}(A). \tag{6.1}$$
--   The **$A$-bound** of $B$ is the infimum of all constants $a$ for which a corresponding $b$ exists such that (6.1) holds.
--
--   The file defines three objects: `IsRelativelyBoundedWith A B a b` (the domain inclusion, $a, b \ge 0$, and (6.1) with these constants), `IsRelativelyBounded A B` (some such $a, b$ exist), and `relativeBound A B`, the $A$-bound.
--
--   **Formalization Note.** The $A$-bound takes values in $[0, \infty]$ (`ℝ≥0∞`): it is the infimum over the admissible $a$, and equals $\infty$ exactly when $B$ is not $A$ bounded, so "the $A$-bound is less than one" already contains "$B$ is $A$ bounded". The domain inclusion $\mathfrak{D}(A) \subseteq \mathfrak{D}(B)$ is part of the definition, as in the book.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 133, Section 6.1, Eq. (6.1)

import Mathlib

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl (6.1), p. 133: `B` is `A` bounded *with constants* `a, b`: `𝔇(A) ⊆ 𝔇(B)`, `a, b ≥ 0`, and
`‖Bψ‖ ≤ a‖Aψ‖ + b‖ψ‖` for all `ψ ∈ 𝔇(A)`. The domain inclusion is part of the definition, as in the
book. -/
def IsRelativelyBoundedWith {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) (a b : ℝ) : Prop :=
  A.domain ≤ B.domain ∧ 0 ≤ a ∧ 0 ≤ b ∧
    ∀ (ψ : H) (hA : ψ ∈ A.domain) (hB : ψ ∈ B.domain),
      ‖B ⟨ψ, hB⟩‖ ≤ a * ‖A ⟨ψ, hA⟩‖ + b * ‖ψ‖

/-- Teschl, p. 133: `B` is *`A` bounded* (relatively bounded with respect to `A`) if `𝔇(A) ⊆ 𝔇(B)`
and there are constants `a, b ≥ 0` such that (6.1) holds. -/
def IsRelativelyBounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) : Prop :=
  ∃ a b : ℝ, IsRelativelyBoundedWith A B a b

/-- Teschl, p. 133: the *`A`-bound* of `B`, the infimum of all constants `a` for which a
corresponding `b` exists such that (6.1) holds. It takes values in `[0, ∞]`; it is `∞` exactly when
`B` is not `A` bounded (the infimum over the empty set), so it is never a junk `0`. -/
noncomputable def relativeBound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) : ℝ≥0∞ :=
  ⨅ (a : ℝ) (_ : ∃ b : ℝ, IsRelativelyBoundedWith A B a b), ENNReal.ofReal a

end TeschlQM.KatoRellich


