-- Prove2me | Definitions.Def_DHRUniq_schmidtCoeffs
-- name    : DHRUniq_schmidtCoeffs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:58.978301+00:00
-- url     : https://prove2.me/theorems/3df6ca1b-9fad-407d-86f8-6ed85f3e830f
-- title:
--   The non-zero Schmidt coefficients of $|\psi\rangle$
-- statement:
--   For a vector $\psi$ of $\mathbb C^a\otimes\mathbb C^b$, its **non-zero Schmidt coefficients** are the non-zero eigenvalues of $\operatorname{tr}_B|\psi\rangle\langle\psi|$, listed with multiplicity in decreasing order. They are the non-zero $p_i$ of any Schmidt decomposition $|\psi\rangle=\sum_i\sqrt{p_i}|a_i\otimes b_i\rangle$.
--
--   They appear in (P2′) and in the majorization form of (P2), which compare states on different spaces.
--
--   **Formalization Note** The eigenvalues are the roots of the characteristic polynomial, with multiplicity; the reduced operator is Hermitian, so they are real.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §2, p. 4 and (P2′), p. 9

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)
open WildeQIT (partialTraceRight)

namespace DHRUniq

/-- **The non-zero Schmidt coefficients of `|ψ⟩`** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §2, p. 4, and (P2′), p. 9), in
decreasing order, with multiplicity: the non-zero eigenvalues of `tr_B P_ψ`.

**Formalization Note** These are the `p_i` of `|ψ⟩ = ∑_i √p_i |a_i ⊗ b_i⟩` (squared amplitudes).
The eigenvalues are the roots of the characteristic polynomial with multiplicity; `tr_B P_ψ` is
Hermitian, so they are real and taking the real part loses nothing. The list has no zeros, so
two wavefunctions on different spaces can have equal lists. -/
noncomputable def schmidtCoeffs {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ψ : a × b → ℂ) : List ℝ :=
  open Classical in
  (((partialTraceRight (pureState ψ)).charpoly.roots.map Complex.re).filter (· ≠ 0)).sort (· ≥ ·)

end DHRUniq


