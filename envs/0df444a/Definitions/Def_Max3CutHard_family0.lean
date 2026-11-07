-- Prove2me | Definitions.Def_Max3CutHard_family0
-- name    : Max3CutHard_family0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:37.080021+00:00
-- url     : https://prove2.me/theorems/d74f9c38-0893-4bc1-a715-30747e9ec61f
-- title:
--   The family $(2E,N,N)$
-- statement:
--   The family used for Max-3-Cut: the E-gadget with all weights doubled for equations of type $0$, and the N-gadget for types $1$ and $2$:
--
--   $$(I_0,I_1,I_2)=(2E,N,N).$$
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Proof of Theorem 1.1, p.6

import Mathlib
import Definitions.Def_Max3CutHard_gadgetE
import Definitions.Def_Max3CutHard_gadgetN
import Definitions.Def_Max3CutHard_Gadget_scale
import Definitions.Def_Max3CutHard_Family

namespace Max3CutHard

/-- **The family `(2E, N, N)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Proof of Theorem 1.1, p.6: "Use the family `(2E, N, N)`,
i.e. `E` with all weights doubled for type 0 and `N` for types 1, 2." -/
noncomputable def family0 : Family 3 := fun t => if t = 0 then gadgetE.scale 2 else gadgetN

end Max3CutHard


