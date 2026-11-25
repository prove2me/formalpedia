-- Prove2me | Definitions.Def_Arxiv2405_02007_Basic
-- name    : Arxiv2405_02007_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T16:52:18.698103+00:00
-- url     : https://prove2.me/theorems/c47bdfc0-cbe3-40c8-8ca9-9bc6d9c89846
-- title:
--   Volume and helix scattering powers of the model-free decomposition
-- statement:
--   Scattering powers of the model-free four-component decomposition of Dey et al. (2021), as used in Section 2 and Section 5.1 of Ballester-Berman (2024).
--
--   Fix a pixel with total backscattered power $\mathrm{Span}$, 3-D Barakat degree of polarisation $m_{FP}$ and scattering asymmetry parameter $\tau_{FP}$.
--
--   1. **Volume power (eq. 2).** $P_v=(1-m_{FP})\cdot\mathrm{Span}$.
--   2. **Helix power (eq. 9).** $P_c=m_{FP}\cdot\mathrm{Span}\cdot\sin(2\tau_{FP})$.
--
--   These are the two formulas through which a change of the depolarising factor $1-m_{FP}$ changes the decomposed powers.
--
--   **Formalization Note** $m_{FP}$, $\mathrm{Span}$ and $\tau_{FP}$ are real parameters. The paper defines $m_{FP}=\sqrt{1-27|\mathbf T|/\operatorname{tr}^3(\mathbf T)}$ from the coherency matrix (eq. 1) and takes $\tau_{FP}$ from Dey et al. (2021); the statements use only the numbers, with the ranges $0<\mathrm{Span}$ and $0\le m_{FP}\le1$ (or $0<m_{FP}$ where the paper divides by $m_{FP}$) written as hypotheses.
-- source:
--   J. D. Ballester-Berman, Analysing PolSAR data from vegetation by using the subaperture decomposition approach, arXiv:2405.02007v1 (2024), Section 2, eq. (2), PDF p. 2; Section 5.1, eq. (9), PDF p. 18

import Mathlib

/-!
J. D. Ballester-Berman, *Analysing PolSAR data from vegetation by using the subaperture
decomposition approach*, arXiv:2405.02007v1 (2024): the volume and helix scattering powers of the
model-free decomposition of Dey et al. (2021) as used in Section 2, eq. (2), and Section 5.1,
eq. (9), of the paper. The 3-D Barakat degree of polarisation `m_FP`, the total power `Span` and the
scattering asymmetry parameter `τ_FP` enter as real numbers.
-/

noncomputable section

namespace Arxiv2405_02007

/-- Section 2, eq. (2), PDF p. 2: the volume scattering power `P_v = (1 - m_FP) · Span`, for a degree
of polarisation `m = m_FP` and total power `span = Span`. -/
def volumePower (m span : ℝ) : ℝ := (1 - m) * span

/-- Section 5.1, eq. (9), PDF p. 18: the helix scattering power
`P_c = m_FP · Span · sin(2 τ_FP)`, for a degree of polarisation `m = m_FP`, total power
`span = Span` and scattering asymmetry parameter `tau = τ_FP`. -/
def helixPower (m span tau : ℝ) : ℝ := m * span * Real.sin (2 * tau)

end Arxiv2405_02007


