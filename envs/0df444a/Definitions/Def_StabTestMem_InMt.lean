-- Prove2me | Definitions.Def_StabTestMem_InMt
-- name    : StabTestMem_InMt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:01.389188+00:00
-- url     : https://prove2.me/theorems/9fb16243-1e1b-4b28-9210-f60ee994a800
-- title:
--   Moving sector $M_t=\mathcal O_t\setminus\mathcal O_{t-1}$
-- statement:
--   Identify $\mathcal O_{t-1}$ with the matrices in $\mathcal O_t$ that fix $e_1=(1,0,\dots,0)$. The **moving sector** is
--
--   $$M_t=\mathcal O_t\setminus\mathcal O_{t-1}=\{O\in\mathcal O_t:\ Oe_1\ne e_1\}.$$
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §5.4, p. 41

import Definitions.Def_StabTestMem_IsStochOrth

namespace StabTestMem

/-- **The moving sector `M_t = O_t ∖ O_{t−1}`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §5.4, p. 41: "splitting O_t into O_{t−1} and
M_t := O_t \ O_{t−1}, where we identify O_{t−1} as all matrices that fix e_1 = (1, 0, 0, …, 0)."

`InMt O`: `O ∈ O_t` and `O e₁ ≠ e₁`, i.e. the first column of `O` is not `e₁`. -/
def InMt {t : ℕ} (O : Matrix (Fin t) (Fin t) (ZMod 2)) : Prop :=
  IsStochOrth O ∧ ∃ i j : Fin t, (j : ℕ) = 0 ∧ O i j ≠ if (i : ℕ) = 0 then 1 else 0

end StabTestMem


