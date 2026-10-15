-- Prove2me | Definitions.Def_QAmpEst_Est_Fourier
-- name    : QAmpEst_Est_Fourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:55:50.844016+00:00
-- url     : https://prove2.me/theorems/e8a7a00e-628f-4ec0-9dc0-1ce855cfcf56
-- title:
--   §4, (13)–(14), Definitions 8–9, pp. 15–17 — F_M⁻¹, |S_M(ω)⟩, d(ω₀, ω₁), Λ_M(U) and the phase-estimation law Prob(X = x)
-- statement:
--   The general phase-estimation objects of §4 of Brassard–Høyer–Mosca–Tapp.
--
--   Fix an integer $M \ge 1$ and index the basis of $\mathbb C^M$ by $\{0, 1, \dots, M-1\}$.
--
--   1. The **quantum Fourier transform** (13) is
--   $$F_M : |x\rangle \longmapsto \frac{1}{\sqrt M}\sum_{y=0}^{M-1} e^{2\pi\imath xy/M}\,|y\rangle \qquad (0 \le x < M),$$
--   the published Fourier matrix `ShorAlgorithms.Shared.fourierMatrix M`, with $(y, x)$ entry $e^{2\pi\imath xy/M}/\sqrt M$ (the matrix is symmetric). Its inverse $F_M^{-1}$ is its conjugate transpose $F_M^\dagger$, with $(x, y)$ entry $e^{-2\pi\imath xy/M}/\sqrt M$.
--   2. For a real number $\omega$ (Definition 8),
--   $$|S_M(\omega)\rangle = \frac{1}{\sqrt M}\sum_{y=0}^{M-1} e^{2\pi\imath\omega y}\,|y\rangle ,$$
--   so that $F_M|x\rangle = |S_M(x/M)\rangle$.
--   3. For real numbers $\omega_0, \omega_1$ (Definition 9), the circular distance is
--   $$d(\omega_0,\omega_1) = \min_{z\in\mathbb Z} |z + \omega_1 - \omega_0| ;$$
--   $2\pi d(\omega_0,\omega_1)$ is the length of the shorter arc from $e^{2\pi\imath\omega_0}$ to $e^{2\pi\imath\omega_1}$.
--   4. For a square matrix $U$ on a finite-dimensional space $\mathbb C^\iota$, the controlled-power operator (14) on $\mathbb C^M \otimes \mathbb C^\iota$ is
--   $$\Lambda_M(U) : |j\rangle|y\rangle \longmapsto |j\rangle\,(U^j|y\rangle) \qquad (0 \le j < M).$$
--   5. $\mathrm{Prob}(X = x)$ in Theorem 11 is the probability $|\langle x|F_M^{-1}|S_M(\omega)\rangle|^2$ that measuring $F_M^{-1}|S_M(\omega)\rangle$ in the computational basis gives $x$.
--
--   These objects are not specific to amplitude estimation: they are the standard ingredients of quantum phase estimation, and every result of §4 is stated in their terms.
--
--   **Formalization Note** $F_M$ itself is not redefined: it is the published `ShorAlgorithms.Shared.fourierMatrix` (Shor 1997, eq. (4.1)), which is the same matrix with the same sign and normalization. The minimum in $d$ is written as an infimum over $\mathbb Z$ of a function bounded below by $0$; it is attained, so it equals the page's minimum. Integer indices are elements of `Fin M`, cast to real or complex numbers where they appear in exponents.
-- source:
--   arXiv:quant-ph/0005055v1, (13) and (14), p. 15; Definitions 8 and 9, p. 16; Theorem 11, p. 17

import Mathlib
import Definitions.Def_ShorAlgorithms_Shared_fourierMatrix

namespace QAmpEst.Est

open scoped Real

/-- The quantum Fourier transform `F_M` of (13), arXiv:quant-ph/0005055v1, p. 15, is the
published `ShorAlgorithms.Shared.fourierMatrix M`, whose `(a, c)` entry is `e^{2πıac/M} / √M`; the
matrix is symmetric, so its column `x` is `F_M|x⟩ = (1/√M) ∑_{y=0}^{M-1} e^{2πıxy/M} |y⟩`.
The inverse quantum Fourier transform `F_M⁻¹` is its conjugate transpose: entry `(x, y)` is
`e^{-2πıxy/M} / √M`. -/
noncomputable def qftInv (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  star (ShorAlgorithms.Shared.fourierMatrix M)

/-- The state `|S_M(ω)⟩ = (1/√M) ∑_{y=0}^{M-1} e^{2πıωy} |y⟩` of Definition 8, p. 16. -/
noncomputable def stateS (M : ℕ) (ω : ℝ) : Fin M → ℂ :=
  fun y => Complex.exp (2 * π * Complex.I * (ω : ℂ) * ((y : ℕ) : ℂ)) / (Real.sqrt M : ℂ)

/-- The circular distance `d(ω₀, ω₁) = min_{z ∈ ℤ} |z + ω₁ − ω₀|` of Definition 9, p. 16
(the infimum over the nonempty index set `ℤ` of a function bounded below by `0`; it is
attained). -/
noncomputable def circDist (ω0 ω1 : ℝ) : ℝ :=
  ⨅ z : ℤ, |(z : ℝ) + ω1 - ω0|

/-- The controlled-power operator `Λ_M(U) : |j⟩|y⟩ ↦ |j⟩ (U^j |y⟩)` (`0 ≤ j < M`) of (14),
p. 15, on the two-register space indexed by `Fin M × ι`. -/
def ctrlPow {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ℕ) (U : Matrix ι ι ℂ) :
    Matrix (Fin M × ι) (Fin M × ι) ℂ :=
  fun p q => if p.1 = q.1 then (U ^ (p.1 : ℕ)) p.2 q.2 else 0

/-- `Prob(X = x)` in Theorem 11, p. 17: the probability that measuring `F_M⁻¹ |S_M(ω)⟩` in the
computational basis gives `x`. -/
noncomputable def phaseProb (M : ℕ) (ω : ℝ) (x : Fin M) : ℝ :=
  Complex.normSq ((qftInv M).mulVec (stateS M ω) x)

end QAmpEst.Est


