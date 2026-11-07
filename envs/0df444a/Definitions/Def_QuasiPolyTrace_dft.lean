-- Prove2me | Definitions.Def_QuasiPolyTrace_dft
-- name    : QuasiPolyTrace_dft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:06.359686+00:00
-- url     : https://prove2.me/theorems/7d69be5c-c558-400b-bb4e-2b34fd9cdcef
-- title:
--   Discrete Fourier transform of a length-$N$ sequence
-- statement:
--   For a real sequence $f=(f(0),\dots,f(N-1))$ with indices taken mod $N$, its **discrete Fourier transform** at an integer frequency $\xi$ is
--
--   $$
--   F(\xi)=\sum_{j=0}^{N-1} f(j)\,e^{2\pi i j\xi/N}.
--   $$
--
--   It is $N$-periodic in $\xi$. The paper uses it in Lemmas 11–13, where summed second and third order statistics of $f$ (autocorrelation and bispectrum) are related to $|F|^2$ and to triple products $F(\xi_1)F(\xi_2)F(-\xi_1-\xi_2)$.
--
--   **Formalization Note** The paper indexes by $\{1,\dots,N\}$; the index $N$ and the index $0$ are the same residue mod $N$ and contribute the same factor, so the transform is the same.
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), p.14 (Lemmas 11–13 use the DFT; kernel e^{2πi jξ/N} from the proof of Lemma 12)

import Mathlib

namespace QuasiPolyTrace

/-- **The discrete Fourier transform of a length-`N` sequence.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), p.14: "Lemma 13 and the
associated standard Lemmas 11 and 12 are stated for the discrete Fourier transform, mapping sequences of
length N (with indices considered mod N) to sequences of length N", with the kernel `e^{(2πi/N)·jξ}` of
the proof of Lemma 12 (p.14).

`dft N f ξ = ∑_{j} f(j) e^{2πi jξ/N}` for an integer frequency `ξ`.

**Formalization Note.** Indices run over `Fin N = {0, …, N − 1}` instead of the paper's `{1, …, N}`; the
index `N` and the index `0` are the same residue mod `N` and give the same factor `e^{2πi Nξ/N} = 1`,
so the transform is the same. Frequencies are integers (the transform is `N`-periodic in `ξ`). -/
noncomputable def dft (N : ℕ) (f : Fin N → ℝ) (ξ : ℤ) : ℂ :=
  ∑ j : Fin N, (f j : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (ξ : ℂ) / (N : ℂ))

end QuasiPolyTrace


