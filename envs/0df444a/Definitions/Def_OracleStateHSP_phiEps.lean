-- Prove2me | Definitions.Def_OracleStateHSP_phiEps
-- name    : OracleStateHSP_phiEps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:32:12.656468+00:00
-- url     : https://prove2.me/theorems/17e4dc27-68ee-4b3a-b9e9-fc392236094a
-- title:
--   Fractional Padded Simon state $|\varphi^\varepsilon_f\rangle$ (eq. (55))
-- statement:
--   For $\varepsilon \in (0, 1]$ and a Simon function $f$,
--   $$
--   |\varphi^\varepsilon_f\rangle = \sqrt{1 - \varepsilon}\, |0\rangle |u_G\rangle + \sqrt{\varepsilon}\, |1\rangle |\varphi_f\rangle ,
--   $$
--   with the flag qubit first. These states form the Fractional Padded Simon's StateHSP family.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (55), p.39

import Mathlib
import Definitions.Def_OracleStateHSP_FlagQ
import Definitions.Def_OracleStateHSP_uG
import Definitions.Def_OracleStateHSP_phiF

namespace OracleStateHSP

/-- The input state of the Fractional Padded Simon family (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (55), p.39):
`|φ^ε_f⟩ = √(1−ε) |0⟩|u_G⟩ + √ε |1⟩|φ_f⟩`, with the flag qubit first.

**Formalization Note.** `ε` is real and `√·` is `Real.sqrt` cast to `ℂ`. -/
noncomputable def phiEps (ε : ℝ) (r : ℕ) {m : ℕ} (f : V m → V m) : EuclideanSpace ℂ (FlagQ r m) :=
  WithLp.toLp 2 fun p =>
    if p.1 = 0 then (Real.sqrt (1 - ε) : ℂ) * uG r m p.2 else (Real.sqrt ε : ℂ) * phiF r f p.2

end OracleStateHSP


