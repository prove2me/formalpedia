-- Prove2me | Definitions.Def_MatrixSpencer_Supplement_cSchur
-- name    : MatrixSpencer_Supplement_cSchur
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:29:50.177937+00:00
-- url     : https://prove2.me/theorems/270ab447-7316-40f2-ae38-e8b9a6ceea87
-- title:
--   The constant $c_{\mathrm{Schur}}=[1-\tfrac18(\Lambda^2+\Lambda^{-2})]^8$, $\Lambda=8-4\sqrt3$
-- statement:
--   Let $\Lambda=8-4\sqrt3$ and
--   $$c_{\mathrm{Schur}}=\Bigl[1-\tfrac18(\Lambda^2+\Lambda^{-2})\Bigr]^8=\Bigl(\frac{1020\sqrt3-1671}{128}\Bigr)^8\approx0.0976 .$$
--   It is the universal loss factor of one rank-one pinching (Theorem B.2); $\Lambda$ is the dimension-free upper bound on the averaged resolvent (Proposition B.3).
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), eq. (B.16), p.18 (PDF p.20); closed form p.26 (PDF p.28)

import Mathlib

namespace MatrixSpencer.Supplement

/-- `Λ = 8 − 4√3`, eq. (B.16).
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…),
Theorem B.2, eq. (B.16), p.18 (PDF p.20); also Proposition B.3, p.18. -/
noncomputable def Lam : ℝ := 8 - 4 * √3

/-- **The constant `c_Schur = [1 − ⅛(Λ² + Λ⁻²)]⁸`, `Λ = 8 − 4√3`**, eq. (B.16), p.18 (PDF p.20).
Its value is `((1020√3 − 1671)/128)⁸ ≈ 0.0976` (the last display of the proof of Theorem 1.5,
p.26, PDF p.28). -/
noncomputable def cSchur : ℝ := (1 - (Lam ^ 2 + Lam⁻¹ ^ 2) / 8) ^ 8

end MatrixSpencer.Supplement


