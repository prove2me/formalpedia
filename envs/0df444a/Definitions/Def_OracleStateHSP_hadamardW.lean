-- Prove2me | Definitions.Def_OracleStateHSP_hadamardW
-- name    : OracleStateHSP_hadamardW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:31:07.244088+00:00
-- url     : https://prove2.me/theorems/227ca88f-0ebf-40c8-9982-d07536cb4377
-- title:
--   Fixed gate $W = I \otimes H^{\otimes n} \otimes I$
-- statement:
--   $W$ applies Hadamard gates to the group register:
--   $$
--   W = I_{\mathrm{flag}} \otimes H^{\otimes n} \otimes I_{\mathrm{answer}}, \qquad (H^{\otimes n})_{x,y} = 2^{-n/2} (-1)^{x\cdot y}, \quad x, y \in G = \mathbb Z_2^n ,
--   $$
--   with $n = r + m$. It maps $|0\rangle$ to $|0\rangle|u_G\rangle$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.3, p.39

import Mathlib
import Definitions.Def_OracleStateHSP_FlagQ
import Definitions.Def_OracleStateHSP_dotG

namespace OracleStateHSP

/-- The fixed gate `W` of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.39 ("`W` applies Hadamard gates to the group register"):
`W = I_flag ⊗ H^{⊗n} ⊗ I_answer`, with `(H^{⊗n})_{x,y} = 2^{−n/2} (−1)^{x·y}` on
`G = Z_2^n`, `n = r + m`. -/
noncomputable def hadamardW (r m : ℕ) : Matrix (FlagQ r m) (FlagQ r m) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 ∧ p.2.2 = q.2.2 then
      ((Real.sqrt (2 ^ (r + m)))⁻¹ : ℂ) * (if dotG p.2.1 q.2.1 = 0 then 1 else -1)
    else 0

end OracleStateHSP


