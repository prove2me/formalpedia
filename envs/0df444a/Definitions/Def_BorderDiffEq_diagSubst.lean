-- Prove2me | Definitions.Def_BorderDiffEq_diagSubst
-- name    : BorderDiffEq_diagSubst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:56.373554+00:00
-- url     : https://prove2.me/theorems/54d5db06-d90d-46e4-8769-ee988e31c029
-- title:
--   The substitution $(y,z)\mapsto(y+zx,0)$
-- statement:
--   For a polynomial $P(y,z,x)$ over a commutative ring $R$, the **substitution** $(y,z)\mapsto(y+zx,0)$ gives
--   $$
--   P(y+zx,\,0,\,x),
--   $$
--   obtained by first setting $z=0$ and then replacing every $y_l$ by $y_l+z\,x_l$. It is a ring homomorphism. A polynomial fixed by it depends on $y$ and $z$ only through $y+zx$.
--
--   This is the invariance in Lemma 4.5's proof (equation (15)) and in Lemma 5.1 (2) and (3).
--
--   **Formalization Note** Same encoding as `shift`: $z$ is the `Polynomial` variable, $y_l$ = `X (Sum.inl l)`, $x_l$ = `X (Sum.inr l)`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.5 proof, p.26, (15); Lemma 5.1 (2), p.31, proof p.32

import Mathlib

namespace BorderDiffEq

/-- **The substitution `(y, z) ↦ (y + z x, 0)`** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying
Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027
submission), Lemma 5.1 (2), p.31, proof p.32, and Lemma 4.5's proof, p.26, (15)): for a polynomial
`P(y, z, x)` this is `P(y + z x, 0, x)`, a ring homomorphism.

**Formalization Note.** Same encoding as `shift`: `z` is the `Polynomial` variable,
`yₗ = X (Sum.inl l)`, `xₗ = X (Sum.inr l)`. First `z := 0` (`Polynomial.eval 0`), then
`yₗ := yₗ + z·xₗ` and `xₗ := xₗ`. -/
noncomputable def diagSubst {R : Type} [CommRing R] {σ : Type}
    (P : Polynomial (MvPolynomial (σ ⊕ σ) R)) : Polynomial (MvPolynomial (σ ⊕ σ) R) :=
  MvPolynomial.aeval
    (Sum.elim
      (fun l => Polynomial.C (MvPolynomial.X (Sum.inl l)) +
        Polynomial.X * Polynomial.C (MvPolynomial.X (Sum.inr l)))
      (fun l => Polynomial.C (MvPolynomial.X (Sum.inr l))))
    (P.eval 0)

end BorderDiffEq


