-- Prove2me | Definitions.Def_SumsHighPowers_PITLifting_IsHittingSet
-- name    : SumsHighPowers_PITLifting_IsHittingSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:09:45.828671+00:00
-- url     : https://prove2.me/theorems/864e8510-a848-4a48-9a33-d54dd8d5e5ca
-- title:
--   Hitting set for a class of polynomials (pp. 5, 29)
-- statement:
--   Let $F$ be a field and $D\subseteq F[x_1,\dots,x_n]$ a class of polynomials. Points $u_1,\dots,u_s\in F^n$ form a **hitting set** for $D$ if every nonzero polynomial of $D$ is nonzero at one of them:
--   $$\forall g\in D,\quad g\neq 0\ \Longrightarrow\ \exists i\in[s],\ g(u_i)\neq 0 .$$
--   A hitting set gives a black-box identity test for $D$: a member of $D$ is the zero polynomial exactly when it vanishes at every $u_i$.
--
--   **Formalization Note.** The points are a family `u : Fin s → (Fin n → F)` (the paper orders its set $\{u_i\}_{i=1}^s$ arbitrarily); repetitions are not excluded. "$g \neq 0$" is inequality of polynomials; $g(u_i)$ is `MvPolynomial.eval (u i) g`.
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 5, §1.1 (interpolating sets, equivalently hitting sets for Σ²C; the standard notion of hitting set), and p. 29, Theorem 3.1

import Mathlib

namespace SumsHighPowers.PITLifting

/-- **Hitting set** (Kaplan–Shpilka–Tal, §1.1, p. 5, and §3.1, p. 29): a finite list of points
`u₁, …, u_s ∈ Fⁿ` is a hitting set for a class `D ⊆ F[x₁, …, xₙ]` if every nonzero `g ∈ D` is
nonzero at some `uᵢ`.

**Formalization Note.** The points are a family `u : Fin s → (Fin n → F)` (the paper's set
`H = {uᵢ}_{i=1}^s`, "ordered arbitrarily"); repetitions are not excluded. Evaluation is
`MvPolynomial.eval`. -/
def IsHittingSet {F : Type*} [Field F] {n s : ℕ} (D : Set (MvPolynomial (Fin n) F))
    (u : Fin s → Fin n → F) : Prop :=
  ∀ g ∈ D, g ≠ 0 → ∃ i, MvPolynomial.eval (u i) g ≠ 0

end SumsHighPowers.PITLifting


