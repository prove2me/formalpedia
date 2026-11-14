-- Prove2me | Definitions.Def_LatticePrepro_ThreeSAT
-- name    : LatticePrepro_ThreeSAT
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:47:57.289358+00:00
-- url     : https://prove2.me/theorems/dbe43228-fb3e-4576-b177-aa7172a2d76c
-- title:
--   The 3SAT language $\mathrm{SAT}_v$ (Theorem 5.1)
-- statement:
--   For a number $v$ of variables, $\mathrm{SAT}_v$ is the set of satisfiable 3SAT instances on $v$ variables:
--   $$\mathrm{SAT}_v = \{\, x : x \text{ is a 3SAT instance on } v \text{ variables and } x \text{ is satisfiable} \,\}.$$
--   An instance $x$ selects a set of clauses (one bit for each of the $(2v)^3$ possible clauses, each clause being an ordered triple of literals), and $x$ is satisfiable if some assignment $a \in \{0,1\}^v$ satisfies every clause present in $x$, i.e. every present clause contains a literal $(i, s)$ with $a_i = s$.
--
--   $\mathrm{SAT}_v$ is the language separated by the fixed codes and lattices of Theorem 5.1 in its 3SAT form (`ThreeSAT.exists_code_gap`, `ThreeSAT.exists_lattice_gap`): satisfiable instances get targets close to the code or lattice, unsatisfiable ones get targets far from it.
--
--   **Formalization Note**: `SAT v : Set (Instance v)` is `{x | Satisfiable x}`, with `Instance` and `Satisfiable` from the 3SAT verifier module. The bundle imports the whole development but defines only this set.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem 5.1 (\label{thm:approximation-hardness}); Lean: LatticePrepro/ThreeSAT.lean, LatticePrepro.ThreeSAT.SAT

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT

/-!
# Theorem 5.1 for 3SAT

The main theorems of `Main.lean` are stated for an arbitrary quadratic verifier. Instantiating
them with the verifier circuit of `Verifier/ThreeSAT.lean` (Claim 3.15 and Definition 3.14 turn
it into a quadratic verifier with the same language) gives the paper's Theorem 5.1 for 3SAT:
fixed codes and lattices of dimension `M ≤ n^C`, where `n = (2v)^3` is the instance length of
3SAT on `v` variables, with targets `t_x` such that satisfiable instances have
`dist(t_x, ·) ≤ R` and unsatisfiable ones `dist(t_x, ·) > M^{1/s - ε} · R`.
-/

namespace LatticePrepro

namespace ThreeSAT

/-- The language of satisfiable 3SAT instances on `v` variables. -/
def SAT (v : ℕ) : Set (Instance v) := {x | Satisfiable x}

end ThreeSAT

end LatticePrepro


