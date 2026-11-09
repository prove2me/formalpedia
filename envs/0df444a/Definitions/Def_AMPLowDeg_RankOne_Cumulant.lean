-- Prove2me | Definitions.Def_AMPLowDeg_RankOne_Cumulant
-- name    : AMPLowDeg_RankOne_Cumulant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:08.743952+00:00
-- url     : https://prove2.me/theorems/63421691-16e4-4634-9deb-0f5b6bbb3c75
-- title:
--   Joint cumulants (2.3), conditional cumulants (2.6) and orthonormal Hermite polynomials
-- statement:
--   **Joint cumulant.** For real random variables $(B_j)_{j\in\iota}$ indexed by a finite nonempty set $\iota$ on a probability space, with the required mixed moments finite,
--
--   $$
--   \mathrm{Cum}(B_j:j\in\iota)=\sum_{\pi\in\Pi(\iota)}(-1)^{|\pi|-1}(|\pi|-1)!\prod_{A\in\pi}\mathbb E\Big[\prod_{j\in A}B_j\Big],
--   $$
--
--   where $\Pi(\iota)$ is the set of partitions of the labelled set $\iota$ into nonempty blocks and $|\pi|$ is the number of blocks. A list $B_1,\dots,B_m$ is the case $\iota=\{1,\dots,m\}$; a variable repeated $k$ times carries $k$ labels.
--
--   **Conditional cumulant.** For a sub-$\sigma$-algebra $\mathcal G$, $\mathrm{Cum}(B_j:j\in\iota\mid\mathcal G)$ is the same formula with every moment replaced by the conditional expectation $\mathbb E[\prod_{j\in A}B_j\mid\mathcal G]$; it is a random variable.
--
--   **Hermite polynomials.** $h_k=\mathrm{He}_k/\sqrt{k!}$ is the orthonormal probabilists' Hermite polynomial, where $\mathrm{He}_k$ is the monic probabilists' Hermite polynomial ($\mathrm{He}_0=1$, $\mathrm{He}_1=y$, $\mathrm{He}_2=y^2-1$, …).
--
--   The cumulants carry the whole graph expansion of the proof; the Hermite polynomials form the orthonormal basis for the Gaussian noise.
--
--   **Formalization Note** Conditional expectations are Mathlib's `condExp`, a fixed representative of an almost-everywhere defined function; all statements about conditional cumulants are therefore almost-sure statements or integrals. For $\iota$ empty the formula returns $1$; the paper never uses that case.
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 6, (2.3) and the Hermite polynomials h_k; p. 7, (2.6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- The coefficient `(−1)^{|π|−1} (|π| − 1)!` of a partition with `|π|` blocks in the
moment–cumulant formula (2.3). -/
def cumCoeff (k : ℕ) : ℝ := (-1 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ)

/-- The joint cumulant (2.3) of a finite family `(B_j)_{j ∈ ι}` of real random variables under `μ`:
`Cum(B) = Σ_{π ∈ Π(ι)} (−1)^{|π|−1}(|π|−1)! Π_{A ∈ π} E[Π_{j ∈ A} B_j]`, the sum over the set
partitions of the (labelled) index set `ι`. A list `B₁, …, B_m` is the case `ι = Fin m`; repeated
variables are repeated labels. Only nonempty `ι` occurs in the paper. -/
noncomputable def cum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (B : ι → Ω → ℝ) : ℝ :=
  ∑ P : Finpartition (Finset.univ : Finset ι),
    cumCoeff P.parts.card * ∏ A ∈ P.parts, ∫ w, ∏ j ∈ A, B j w ∂μ

/-- The conditional joint cumulant (2.6) given a sub-σ-algebra `𝒢`: the formula (2.3) with every
moment replaced by the conditional expectation `E[Π_{j ∈ A} B_j | 𝒢]` (Mathlib's `condExp`,
a fixed representative of an a.e.-defined function). -/
noncomputable def condCum {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (𝒢 : MeasurableSpace Ω) (B : ι → Ω → ℝ) : Ω → ℝ :=
  fun w => ∑ P : Finpartition (Finset.univ : Finset ι),
    cumCoeff P.parts.card * ∏ A ∈ P.parts, (μ[fun w' => ∏ j ∈ A, B j w' | 𝒢]) w

/-- The orthonormal probabilists' Hermite polynomial `h_k = He_k / √(k!)` (p. 6), where
`He_k` is Mathlib's (unnormalized) probabilists' Hermite polynomial `Polynomial.hermite k`. -/
noncomputable def hermNorm (k : ℕ) (y : ℝ) : ℝ :=
  ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval y / Real.sqrt (k.factorial)

end AMPLowDeg.RankOne


