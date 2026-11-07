-- Prove2me | Definitions.Def_SpectrumLB_jm
-- name    : SpectrumLB_jm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:23.383186+00:00
-- url     : https://prove2.me/theorems/83327c10-c3de-41ca-9111-04c4d4ef98cf
-- title:
--   Jucys–Murphy element $J_t=\sum_{i<t}(i\ t)$ on $(\mathbb C^d)^{\otimes n}$, Eq. (2.7)
-- statement:
--   For $1\le t\le n$ the $t$-th Jucys–Murphy element is the sum of the transpositions of $t$ with the earlier positions,
--
--   $$
--   J_t=\sum_{1\le i<t}(i\ t),
--   $$
--
--   acting on $(\mathbb C^d)^{\otimes n}$ through the permutation operators $\pi|j_1,\dots,j_n\rangle=|j_{\pi^{-1}(1)},\dots,j_{\pi^{-1}(n)}\rangle$ (Eq. (2.4)), and $\widetilde J_t=\frac1d J_t$. In particular $J_1=0$. The $J_t$ are Hermitian and commute, and the moments of Haar-random projections are rational functions of them (Proposition 3.2).
--
--   **Formalization Note** Positions are numbered $0,\dots,n-1$, so the paper's $J_t$ is the Lean element at position $t-1$. The permutation operators are the platform's `OptimalSpectrum.Entangled.permOp` (same orientation as Eq. (2.4)).
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §2.1, Eq. (2.7), p. 13

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_permOp

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Jucys–Murphy element `J_t` acting on `(ℂ^d)^{⊗n}`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §2.1, Eq. (2.7), p. 13: "For 1 ≤ t ≤ n, the tth Jucys–Murphy element is given by J_t = Σ_{1≤i<t} (i t)".

`jm d t = Σ_{i < t} (i t)`, each transposition acting by the platform's permutation operator
`OptimalSpectrum.Entangled.permOp` (`|y⟩ ↦ |y ∘ π⁻¹⟩`, Eq. (2.4), p. 12); the normalized element of the paper is `J̃_t = d⁻¹ J_t`.

**Formalization Note.** Positions are `Fin n` (0-indexed), so the paper's `J_1 = 0` is `jm d 0`. -/
noncomputable def jm (d : ℕ) {n : ℕ} (t : Fin n) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < t),
    OptimalSpectrum.Entangled.permOp (ι := Fin d) (Equiv.swap i t)

end SpectrumLB


