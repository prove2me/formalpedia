-- Prove2me | Definitions.Def_SpectrumLB_jmCoeff
-- name    : SpectrumLB_jmCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:08.859485+00:00
-- url     : https://prove2.me/theorems/f07b2fe2-0626-44d1-87b2-f9d8be3ad81a
-- title:
--   Coefficient $A_{m,\mu}$ of a permutation in $\sum_t J_t^m$ (Lemma 6.6)
-- statement:
--   For $m\ge0$ write, in the group algebra $\mathbb Z[S_n]$,
--
--   $$
--   \sum_{t=1}^n J_t^{\,m}=\sum_{\pi\in S_n}c_\pi\,\pi .
--   $$
--
--   The coefficient $c_\pi$ counts the tuples $(t,i_1,\dots,i_m)$ with $i_j<t$ and $(i_1\,t)\cdots(i_m\,t)=\pi$. Lemma 6.6 shows that $c_\pi$ depends only on the conjugacy class $\mu$ of $\pi$, and calls it $A_{m,\mu}$; $A_{m,\varnothing}$ is the coefficient of the identity. Under the representation, $d^m\mathcal P_m=\sum_\pi c_\pi\,\pi$.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Lemma 6.6, Eq. (6.39), p. 27, and its proof, p. 28

import Mathlib
import Definitions.Def_SpectrumLB_jmGA

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Coefficient `A_{m,μ}` of a permutation in `Σ_t J_t^m`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Lemma 6.6, Eq. (6.39), p. 27, and its proof, p. 28: "Let us write d^m 𝒫_m = Σ_{π∈S_n} c_π π. …
for any fixed permutation π ∈ C_μ, we have c_π = A_{m,μ}."

`jmCoeff n m π` is the coefficient of `π` in `Σ_{t} (jmGA t)^m ∈ ℤ[S_n]`.

**Formalization Note.** Read in the group algebra (reading R7); `d^m 𝒫_m = Σ_t J_t^m` is the image of this
element under the representation `π ↦ OptimalSpectrum.Entangled.permOp π` on `(ℂ^d)^{⊗n}`. -/
noncomputable def jmCoeff (n m : ℕ) (π : Equiv.Perm (Fin n)) : ℤ :=
  (∑ t : Fin n, (jmGA t) ^ m).coeff π

end SpectrumLB


