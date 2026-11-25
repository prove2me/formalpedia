-- Prove2me | Definitions.Def_Arxiv1904_10695_Basic
-- name    : Arxiv1904_10695_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T06:33:30.003988+00:00
-- url     : https://prove2.me/theorems/905bc624-d6d2-48b4-9f1e-901322560b10
-- title:
--   Transmission matrix, observed transmission matrix and reference-amplitude estimate
-- statement:
--   Objects of Section 1 (pp. 2-3) of Hofer and Brasselet (2019).
--
--   1. **Transmission matrix.** A transmission matrix is a complex $M\times N$ array $t=(t_{mn})$, where $m\in\{1,\dots,M\}$ indexes the SLM input pixels (or input bases) and $n\in\{1,\dots,N\}$ the camera output pixels, so that $E_{out,n}=\sum_m t_{mn}E_{in,m}$.
--   2. **Observed transmission matrix.** For an output reference field $E_{ref}=(E_{ref,n})\in\mathbb{C}^N$, the measured elements are $t_{obs,mn}=t_{mn}E_{ref,n}$.
--   3. **Average over inputs.** For real numbers $a_1,\dots,a_M$, $\langle a_m\rangle_m=\frac1M\sum_{m=1}^M a_m$. For a matrix $T$, the amplitude average at output pixel $n$ is $\langle|T_{mn}|\rangle_m$.
--   4. **Normalisation by the maximum.** For real numbers $a_1,\dots,a_N$, the normalised profile is $a_n/\max_{n'}a_{n'}$.
--
--   **Formalization Note** Indices run over $\mathrm{Fin}\,M$ and $\mathrm{Fin}\,N$. The maximum is written as a supremum over the finite set of output pixels. Lean defines division by zero as $0$. Where the statement normalises by a maximum, its hypotheses ($t\ne0$ and $E_{ref}\ne0$) make that maximum positive, so no conclusion rests on dividing by zero.
-- source:
--   Hofer and Brasselet, Manipulating the transmission matrix of scattering media for nonlinear imaging beyond the memory effect, arXiv:1904.10695v1 (2019), Section 1 (Introduction), eqs. (1)-(2), pp. 2-3

import Mathlib

/-!
Hofer and Brasselet, *Manipulating the transmission matrix of scattering media for nonlinear
imaging beyond the memory effect*, arXiv:1904.10695v1 (2019), Section 1 ("Introduction"),
pp. 2-3: the transmission matrix, the observed (reference-weighted) transmission matrix, the
average over input modes and the reference-amplitude estimate of eq. (2) with its normalisation
by the maximum.
-/

noncomputable section

namespace Arxiv1904_10695

/-- Section 1, p. 2: a transmission matrix `t_{mn}` from SLM input pixel (or basis element)
`m ∈ {1,…,M}` to camera output pixel `n ∈ {1,…,N}`, with complex entries, so that
`E_{out,n} = ∑_m t_{mn} E_{in,m}`. -/
abbrev TransmissionMatrix (M N : ℕ) : Type := Fin M → Fin N → ℂ

/-- Section 1, p. 3 (text before eq. (2)): the measured transmission-matrix elements
`t_{obs,mn} = t_{mn} E_{ref,n}`, the true elements weighted by the output reference field
`E_{ref,n}` at camera pixel `n`. -/
def obsTM {M N : ℕ} (t : TransmissionMatrix M N) (Eref : Fin N → ℂ) : TransmissionMatrix M N :=
  fun m n => t m n * Eref n

/-- Section 1, eq. (2), p. 3: the average `⟨a_m⟩_m = (1/M) ∑_{m=1}^M a_m` over the `M` input
pixels or bases. -/
def inputAvg {M : ℕ} (a : Fin M → ℝ) : ℝ := (∑ m, a m) / M

/-- Section 1, eq. (2), p. 3: the amplitude average `⟨|T_{mn}|⟩_m` over input modes of a
(transmission) matrix `T`, as a function of the output pixel `n`; applied to `T = t_obs` it is
the left-hand side of eq. (2). -/
def ampAvg {M N : ℕ} (T : TransmissionMatrix M N) (n : Fin N) : ℝ :=
  inputAvg (fun m => ‖T m n‖)

/-- Section 1, p. 3 (sentence after eq. (2)): "a normalization with its maximum value", i.e. the
profile `a_n / max_{n'} a_{n'}` of a nonnegative quantity `a` over the camera pixels. -/
def normalizeByMax {N : ℕ} (a : Fin N → ℝ) (n : Fin N) : ℝ := a n / ⨆ n', a n'

end Arxiv1904_10695


