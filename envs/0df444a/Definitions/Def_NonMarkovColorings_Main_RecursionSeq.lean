-- Prove2me | Definitions.Def_NonMarkovColorings_Main_RecursionSeq
-- name    : NonMarkovColorings_Main_RecursionSeq
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:08:41.754699+00:00
-- url     : https://prove2.me/theorems/eb7d7111-482d-4f9c-a704-cfbe13c70413
-- title:
--   The sequences $\ell_j$, $m_j$ of the proof of Proposition 5.6 and Appendix A
-- statement:
--   For a natural number $C_{cp}$ and a real $\gamma$, let $\ell_0=2$, $m_0=1$ and
--   $$\ell_{j+1}=2\ell_j+\frac{\log(200C_{cp}m_j/\gamma)}{\log 24},\qquad m_{j+1}=\frac{200C_{cp}}{\gamma}\,m_j\exp(\ell_{j+1}/96).$$
--   The paper uses $0\le j<100C_{cp}$ (p. 34, p. 71) with $\gamma=\exp(-C_{cp}^2)$.
--
--   **Formalization Note.** `ellSeq Ccp γ j`, `mSeq Ccp γ j` (real-valued, defined for every $j$); $\log$ is `Real.log`.
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 34 (proof of Proposition 5.6), p. 71 Appendix A

import Mathlib

/-!
# The sequences ℓ_j, m_j of Proposition 5.6 and Appendix A

Jain, Mizgerd, Vigoda, *Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling
and Local Uniformity*, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 34 (proof of
Proposition 5.6) and p. 71 (Appendix A).

For a natural number `C_cp` and a real `γ`: `ℓ_0 = 2`, `m_0 = 1` and
`ℓ_{j+1} = 2 ℓ_j + log(200 C_cp m_j / γ) / log 24`,
`m_{j+1} = (200 C_cp / γ) · m_j · exp(ℓ_{j+1} / 96)`.
The paper uses the recursion for `0 ≤ j < 100 C_cp`; the sequences here continue it for every `j`.
`log` is `Real.log`.
-/

namespace NonMarkovColorings.Main

noncomputable section

/-- The pair `(ℓ_j, m_j)`. -/
def ellM (Ccp : ℕ) (γ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (2, 1)
  | j + 1 =>
    let l := (ellM Ccp γ j).1
    let m := (ellM Ccp γ j).2
    let l' := 2 * l + Real.log (200 * (Ccp : ℝ) * m / γ) / Real.log 24
    (l', 200 * (Ccp : ℝ) / γ * m * Real.exp (l' / 96))

/-- `ℓ_j`. -/
def ellSeq (Ccp : ℕ) (γ : ℝ) (j : ℕ) : ℝ := (ellM Ccp γ j).1

/-- `m_j`. -/
def mSeq (Ccp : ℕ) (γ : ℝ) (j : ℕ) : ℝ := (ellM Ccp γ j).2

end

end NonMarkovColorings.Main


