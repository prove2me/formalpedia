-- Prove2me | Definitions.Def_OracleStateHSP_fracU
-- name    : OracleStateHSP_fracU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:32:05.548457+00:00
-- url     : https://prove2.me/theorems/5cc3c6fe-ec66-4851-b541-eb7443888843
-- title:
--   State-preparation unitary $U_\varphi = O^\varepsilon_f W$
-- statement:
--   The state-preparation unitary of the Fractional Padded Simon instance is
--   $$
--   U_\varphi = O^\varepsilon_f\, W ,
--   $$
--   so that $|\varphi^\varepsilon_f\rangle = U_\varphi|0\rangle = O^\varepsilon_f W|0\rangle$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.3, p.39

import Mathlib
import Definitions.Def_OracleStateHSP_fracOracle
import Definitions.Def_OracleStateHSP_hadamardW

namespace OracleStateHSP

/-- The state-preparation unitary `U_φ = O^ε_f W` of the Fractional Padded Simon instance
(Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.39: "`|φ^ε_f⟩ = U_φ |0⟩ = O^ε_f W |0⟩`"). -/
noncomputable def fracU (ε : ℝ) (r : ℕ) {m : ℕ} (f : V m → V m) :
    Matrix (FlagQ r m) (FlagQ r m) ℂ :=
  fracOracle ε r f * hadamardW r m

end OracleStateHSP


