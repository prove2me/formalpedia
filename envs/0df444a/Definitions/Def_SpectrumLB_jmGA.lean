-- Prove2me | Definitions.Def_SpectrumLB_jmGA
-- name    : SpectrumLB_jmGA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:16.222782+00:00
-- url     : https://prove2.me/theorems/b87147c7-650e-46b6-96f3-70640bbe4eca
-- title:
--   Jucys–Murphy element $J_t$ in the group algebra $\mathbb Z[S_n]$
-- statement:
--   The Jucys–Murphy element as an element of the integral group algebra of the symmetric group:
--
--   $$
--   J_t=\sum_{1\le i<t}(i\ t)\ \in\ \mathbb Z[S_n].
--   $$
--
--   Its image under the representation on $(\mathbb C^d)^{\otimes n}$ is the operator $J_t$. Working in the group algebra makes the coefficient of each permutation in a polynomial in the $J_t$ well defined.
--
--   **Formalization Note** For $n>d$ the permutation operators on $(\mathbb C^d)^{\otimes n}$ are linearly dependent, so coefficients of permutations (Lemma 6.6) and the "identity component" of $\mathcal P_m$ (p. 24) are read in the group algebra.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §2.1, Eq. (2.7), p. 13; Lemma 6.6, p. 27

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Jucys–Murphy element in the group algebra `ℤ[S_n]`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §2.1, Eq. (2.7), p. 13 ("the Jucys–Murphy elements of the symmetric group algebra").

`jmGA t = Σ_{i < t} (i t) ∈ ℤ[S_n]`.

**Formalization Note.** The group-algebra copy of `J_t` is needed because for `n > d` the operators `π` on
`(ℂ^d)^{⊗n}` are linearly dependent, so coefficients of permutations (Lemma 6.6) and "the component of the
identity" (p. 24) are only well defined in the group algebra (paper.md reading R7). -/
noncomputable def jmGA {n : ℕ} (t : Fin n) : MonoidAlgebra ℤ (Equiv.Perm (Fin n)) :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < t), MonoidAlgebra.single (Equiv.swap i t) 1

end SpectrumLB


