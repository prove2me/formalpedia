-- Prove2me | Definitions.Def_TeschlQM_MinMax_eigenvalueSeq
-- name    : TeschlQM_MinMax_eigenvalueSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:01:48.756712+00:00
-- url     : https://prove2.me/theorems/6787086f-b1c2-4171-9630-63f522b3b8e8
-- title:
--   The numbers E₁ ≤ E₂ ≤ ⋯: eigenvalues below σ_ess(A) with multiplicity, then inf σ_ess(A)
-- statement:
--   Let $A$ be a self-adjoint operator on a complex Hilbert space $\mathfrak H$ and let $\Sigma = \inf \sigma_{ess}(A) \in [-\infty, +\infty]$, with $\Sigma = +\infty$ if $\sigma_{ess}(A) = \emptyset$. Let $E_1 \le E_2 \le E_3 \le \cdots$ be the eigenvalues of $A$ below the essential spectrum, counted according to their multiplicity; once there are no more eigenvalues left, $E_n = \Sigma$.
--
--   Precisely, for $x \in \mathbb R$ let $N(x)$ be the dimension (a cardinal) of the span of all eigenspaces $\operatorname{Ker}(A - \mu)$ with $\mu \le x$ and $\mu < \Sigma$; it counts the eigenvalues $\le x$ below the essential spectrum with multiplicity. Then, for $n \ge 1$,
--   $$E_n = \inf\big( \{ x \in \mathbb R \mid x < \Sigma,\ N(x) \ge n \} \cup \{ \Sigma \} \big) \in [-\infty, +\infty].$$
--   So $E_n$ is the $n$-th eigenvalue below $\Sigma$ when there are at least $n$ of them (with multiplicity), and $E_n = \Sigma$ otherwise.
--
--   **Formalization Note.** Values are in `EReal`. `infEssSpectrum A` is the `EReal` infimum of the real points of $\sigma_{ess}(A)$ (for self-adjoint $A$ all of $\sigma(A)$ is real). $N(x)$ is `Module.rank ℂ (eigenspaceBelow A x)`. Boundary values: `eigenvalueSeq A 0 = −∞` and is never used (the book indexes from $n = 1$); if $A$ is not bounded below the value is $-\infty$ for every $n$, and if $\sigma_{ess}(A) = \emptyset$ and there are fewer than $n$ eigenvalues (e.g. $\dim \mathfrak H < n$) it is $+\infty$. These are the values the right-hand side of the min-max formula takes in those cases. The numbers are defined from the spectrum and the eigenspaces only, never by the min-max expression itself.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 118–119, Section 4.3 (the E_n of Theorem 4.10)

import Mathlib
import Definitions.Def_TeschlQM_MinMax_essentialSpectrum

namespace TeschlQM.MinMax

/-- `inf σ_ess(A)` as an extended real: the infimum of the real points of the essential spectrum
(for a self-adjoint `A` every point of `σ(A)` is real). It is `+∞` when `σ_ess(A) = ∅` and `−∞`
when `σ_ess(A)` is unbounded below. -/
noncomputable def infEssSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ essentialSpectrum A})

/-- The span of the eigenvectors of `A` for the eigenvalues `μ ≤ x` lying below the essential
spectrum (`μ < inf σ_ess(A)`): the (algebraic) sum of the eigenspaces `Ker(A − μ)` over these
`μ`. Its dimension counts the eigenvalues `≤ x` below the essential
spectrum according to their multiplicity (eigenspaces of distinct eigenvalues of a
self-adjoint operator are orthogonal, Lemma 2.20). -/
noncomputable def eigenspaceBelow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (x : ℝ) : Submodule ℂ H :=
  ⨆ (μ : ℝ) (_ : (μ : EReal) < infEssSpectrum A ∧ μ ≤ x), eigenspace A (μ : ℂ)

/-- Teschl, p. 118–119 (the numbers `E_n` of Theorem 4.10): `E₁ ≤ E₂ ≤ E₃ ≤ ⋯` are the
eigenvalues of `A` below the essential spectrum, counted according to their multiplicity, and
`E_n = inf σ_ess(A)` once there are no more eigenvalues left. Encoded as
`E_n = inf ({x < inf σ_ess(A) | #{eigenvalues ≤ x below σ_ess(A), with multiplicity} ≥ n} ∪ {inf σ_ess(A)})`
in `EReal`; the multiplicity count is the (cardinal) dimension of `eigenspaceBelow A x`.
The index starts at `n = 1` as in the book (`eigenvalueSeq A 0` is `−∞` and never used).
If `A` is not bounded below the value is `−∞`; if `σ_ess(A) = ∅` and the eigenvalues run out,
the value is `+∞`. -/
noncomputable def eigenvalueSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (n : ℕ) : EReal :=
  sInf ({y : EReal | ∃ x : ℝ, y = (x : EReal) ∧ (x : EReal) < infEssSpectrum A ∧
      (n : Cardinal) ≤ Module.rank ℂ (eigenspaceBelow A x)} ∪ {infEssSpectrum A})

end TeschlQM.MinMax


