-- Prove2me | Definitions.Def_NKtLB_Supplement_UNSAT
-- name    : NKtLB_Supplement_UNSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:35:34.426407+00:00
-- url     : https://prove2.me/theorems/6b104334-8edd-422b-9b27-883afabb593d
-- title:
--   UNSAT
-- statement:
--   $\mathrm{UNSAT}$ is the set of encodings of unsatisfiable CNF formulas. Strings that encode no formula are not in UNSAT. Theorems 59 and 65 show that worst-case symmetry of information would put UNSAT outside $\mathsf{AMTIME}[2^{\log^d n}]$.
--
--   **Formalization Note** Theorem 2 (p.8) uses TAUT. Theorems 59 and 65 use UNSAT, taken here over CNF formulas.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorems 59 and 65, pp.39, 43

import Mathlib
import Definitions.Def_NKtLB_Supplement_CNF

namespace NKtLB.Supplement

/-- **UNSAT** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorems 59 and 65, pp.39, 43): the encodings of unsatisfiable CNF formulas.
Strings that encode no formula are not in UNSAT.

**Formalization Note.** The paper's Theorem 2 (p.8) uses TAUT, and Theorems 59/65 use UNSAT; UNSAT
is taken over CNF formulas under the encoding `CNF.enc`. -/
def UNSAT : Set (List Bool) := {z | ∃ φ : CNF, z = φ.enc ∧ ¬ φ.Sat}

end NKtLB.Supplement


