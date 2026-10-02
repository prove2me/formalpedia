-- Prove2me | Definitions.Def_TeschlQM_Shared_relativeBound
-- name    : TeschlQM_Shared_relativeBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T23:03:15.258974+00:00
-- url     : https://prove2.me/theorems/319c8cc6-b859-4202-b74a-55d61c3b095a
-- title:
--   Relatively bounded operator and its A-bound (6.1)
-- statement:
--   Let $A$ and $B$ be linear operators in a complex Hilbert space $\mathfrak H$. $B$ is **$A$ bounded with constants $a, b \ge 0$** if $\mathfrak D(A) \subseteq \mathfrak D(B)$ and
--   $$\|B\psi\| \le a\|A\psi\| + b\|\psi\|, \qquad \psi \in \mathfrak D(A).$$
--   The **$A$-bound** of $B$ is the infimum of all constants $a$ for which a corresponding $b$ exists.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `08-weyl`: p. 148, Lemma 6.22; p. 148, Lemma 6.23
--   - chunk `13-hvz`: p. 241, Theorem 11.1; p. 244, Lemma 11.5
--
--   **Formalization Note.** The $A$-bound is valued in $[0,\infty]$ (`ℝ≥0∞`); it equals $\infty$ exactly when $B$ is not $A$ bounded, so it never takes a junk value $0$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 133, Section 6.1, Eq. (6.1)

import Mathlib

namespace TeschlQM.Shared

open scoped ENNReal

/-- Teschl (6.1), p. 133: `B` is `A` bounded *with constants* `a, b`: `𝔇(A) ⊆ 𝔇(B)`, `a, b ≥ 0`, and
`‖Bψ‖ ≤ a‖Aψ‖ + b‖ψ‖` for all `ψ ∈ 𝔇(A)`. -/
def IsRelativelyBoundedWith {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) (a b : ℝ) : Prop :=
  A.domain ≤ B.domain ∧ 0 ≤ a ∧ 0 ≤ b ∧
    ∀ (ψ : H) (hA : ψ ∈ A.domain) (hB : ψ ∈ B.domain),
      ‖B ⟨ψ, hB⟩‖ ≤ a * ‖A ⟨ψ, hA⟩‖ + b * ‖ψ‖

/-- Teschl, p. 133: the **`A`-bound** of `B`, the infimum of all constants `a` for which a
corresponding `b` exists such that (6.1) holds. It takes values in `[0, ∞]` and is `∞` exactly
when `B` is not `A` bounded (the infimum over the empty set), so it is never a junk `0`. -/
noncomputable def relativeBound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) : ℝ≥0∞ :=
  ⨅ (a : ℝ) (_ : ∃ b : ℝ, IsRelativelyBoundedWith A B a b), ENNReal.ofReal a

end TeschlQM.Shared


