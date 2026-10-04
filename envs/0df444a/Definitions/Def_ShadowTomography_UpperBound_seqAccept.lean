-- Prove2me | Definitions.Def_ShadowTomography_UpperBound_seqAccept
-- name    : ShadowTomography_UpperBound_seqAccept
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:44:33.406643+00:00
-- url     : https://prove2.me/theorems/8d34a941-bd85-404c-8b63-3904497d8255
-- title:
--   Probability that two-outcome measurements applied in succession (Lüders instruments) all accept
-- statement:
--   Let $E_1,\dots,E_M$ be two-outcome measurements and $\rho$ a state. Apply $E_1$ to $\rho$, then $E_2$ to the post-measurement state, and so on, each implemented by its **Lüders instrument**: on acceptance, the (unnormalized) state $\tau$ becomes $\sqrt{E}\,\tau\sqrt{E}$. The probability that all $M$ measurements accept is
--
--   $$
--   \Pr[\text{all accept}] = \mathrm{Tr}\!\left(A\rho A^\dagger\right), \qquad A = \sqrt{E_M}\cdots\sqrt{E_2}\sqrt{E_1}.
--   $$
--
--   For $M=0$ the product is the identity and the probability is $\mathrm{Tr}\,\rho$.
--
--   **Formalization Note** The square root is Mathlib's continuous functional calculus square root `CFC.sqrt` in the Loewner order on matrices (`open scoped MatrixOrder`). The list index `i : Fin M` is the paper's $E_{i+1}$, so `E 0` is applied first. The paper's "applied in succession" does not fix an implementation of each measurement; the Lüders instrument is the standard choice and is a convention of this formalization.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 13, Lemma 12 ("applied to ρ in succession")

import Mathlib

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound

/-- The probability that the two-outcome measurements `E 0, E 1, …, E (M-1)`, applied to `ρ` in
succession in this order (each implemented by its Lüders instrument, with Kraus operator `√E`
for acceptance), all accept: `Re Tr(A ρ A†)` with `A = √E_{M-1} ⋯ √E_1 √E_0`. -/
noncomputable def seqAccept {n : Type} [Fintype n] [DecidableEq n] {M : ℕ}
    (E : Fin M → Matrix n n ℂ) (ρ : Matrix n n ℂ) : ℝ :=
  let A : Matrix n n ℂ := ((List.finRange M).reverse.map (fun i => CFC.sqrt (E i))).prod
  (A * ρ * A.conjTranspose).trace.re

end ShadowTomography.UpperBound


