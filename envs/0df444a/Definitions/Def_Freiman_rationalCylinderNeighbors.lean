-- Prove2me | Definitions.Def_Freiman_rationalCylinderNeighbors
-- name    : Freiman_rationalCylinderNeighbors
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:45:34.577578+00:00
-- url     : https://prove2.me/theorems/c0fa59b9-e4f4-43dc-894e-dabe8ac376db
-- title:
--   The two endpoints adjacent to a canonical rational cylinder
-- statement:
--   The report’s two rational neighbors are (p+u)/(q+v) and (2p−u)/(2q−v), where u/v is the penultimate convergent. The names distinguish formulas; their actual numerical order depends on parity and is always handled by min/max.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §§1.1–1.3

import Definitions.Def_Freiman_continuants

namespace Freiman

noncomputable def rationalCylinderNeighborLeft (w : List ℕ+) : ℝ :=
  ((wordContinuantP w:ℝ)+(wordContinuantPrevP w:ℝ))/
    ((wordContinuantQ w:ℝ)+(wordContinuantPrevQ w:ℝ))
noncomputable def rationalCylinderNeighborRight (w : List ℕ+) : ℝ :=
  (2*(wordContinuantP w:ℝ)-(wordContinuantPrevP w:ℝ))/
    (2*(wordContinuantQ w:ℝ)-(wordContinuantPrevQ w:ℝ))

end Freiman


