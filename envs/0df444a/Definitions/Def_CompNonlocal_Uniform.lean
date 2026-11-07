-- Prove2me | Definitions.Def_CompNonlocal_Uniform
-- name    : CompNonlocal_Uniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:44.728089+00:00
-- url     : https://prove2.me/theorems/e02bcc08-92eb-4bd5-8868-83572e4e01d4
-- title:
--   Uniform QPT families
-- statement:
--   A family is **uniform QPT** if it has polynomial size and a classical polynomial-time machine maps $1^\kappa$ to the code of the circuit at $\kappa$. "All honest algorithms are uniform QPT."
--
--   **Formalization Note** Polynomial time is the published multi-stack Turing-machine notion `PolyTimeComputable`.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4, pp.17–18

import Mathlib
import Definitions.Def_CompNonlocal_PolySize
import Definitions.Def_CompNonlocal_encICirc
import Definitions.Def_QAlgorithms_ClassicalUnaryInput

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- Uniform quantum polynomial-time (QPT) algorithms. Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), §4, pp.17–18: "QPT denotes a uniform quantum polynomial-time algorithm … All honest
algorithms are uniform QPT."

**Formalization Note** A family is uniform QPT when it has polynomial size and a classical
polynomial-time machine (the published `PolyTimeComputable`, multi-stack Turing machines) maps
`1^κ` to the code `encICirc` of the circuit at `κ`. -/
def Uniform (F : Family) : Prop :=
  PolySize F ∧ ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ κ : ℕ, g (unary κ) = encICirc (F κ)

end CompNonlocal


