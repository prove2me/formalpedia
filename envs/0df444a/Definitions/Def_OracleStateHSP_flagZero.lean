-- Prove2me | Definitions.Def_OracleStateHSP_flagZero
-- name    : OracleStateHSP_flagZero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:30:35.194536+00:00
-- url     : https://prove2.me/theorems/f8b545f5-7e6a-4c4b-be1f-e6a791cb9894
-- title:
--   Basis vector $|0\rangle = |0\rangle|0,0\rangle|0\rangle$
-- statement:
--   The basis vector $|0\rangle = |0\rangle_{\mathrm{flag}}|0,0\rangle_{\mathrm{group}}|0\rangle_{\mathrm{answer}}$ of the query register, on which the preparation unitary acts: $|\varphi^\varepsilon_f\rangle = U_\varphi|0\rangle$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.3, p.39

import Mathlib
import Definitions.Def_OracleStateHSP_FlagQ

namespace OracleStateHSP

/-- The basis state `|0⟩ = |0⟩_flag |0, 0⟩_group |0⟩_answer` that the preparation unitary acts on
(Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.39: `|φ^ε_f⟩ = U_φ |0⟩`). -/
def flagZero (r m : ℕ) : FlagQ r m := (0, (0, 0))

end OracleStateHSP


