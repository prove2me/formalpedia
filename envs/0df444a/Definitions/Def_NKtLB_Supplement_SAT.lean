-- Prove2me | Definitions.Def_NKtLB_Supplement_SAT
-- name    : NKtLB_Supplement_SAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:34:58.575211+00:00
-- url     : https://prove2.me/theorems/5ac60fe2-dd80-413d-8a12-fa8da6f9597d
-- title:
--   SAT
-- statement:
--   $\mathrm{SAT}$ is the set of encodings of satisfiable CNF formulas. Strings that encode no formula are not in SAT.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 124, p.96; Lemma 60, p.39

import Mathlib
import Definitions.Def_NKtLB_Supplement_CNF

namespace NKtLB.Supplement

/-- **SAT** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 124, p.96, and Lemma 60, p.39): the encodings of satisfiable CNF formulas.
Strings that encode no formula are not in SAT. -/
def SAT : Set (List Bool) := {z | ∃ φ : CNF, z = φ.enc ∧ φ.Sat}

end NKtLB.Supplement


