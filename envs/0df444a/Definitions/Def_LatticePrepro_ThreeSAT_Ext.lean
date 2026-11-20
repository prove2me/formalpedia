-- Prove2me | Definitions.Def_LatticePrepro_ThreeSAT_Ext
-- name    : LatticePrepro_ThreeSAT_Ext
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:12:25.340791+00:00
-- url     : https://prove2.me/theorems/536a42af-c1a9-4191-b640-4c7e93217cf4
-- title:
--   The quadratic verifier for 3SAT (proof of Theorem 5.1)
-- statement:
--   **The 3SAT verifier** (`ThreeSAT.verifier p v`). For a prime $p$ and a number $v$ of variables, this is the quadratic verifier over $\mathbb F_p$ obtained from the 3SAT verifier circuit `ThreeSAT.circuit v` by reading the circuit as a gate verifier (Definitions 3.13–3.14) and replacing its gates by quadratic gate equations (Claim 3.15).
--
--   Its instances are the bit strings of length $n=(2v)^{3}$, one bit for each possible clause, and its language is the set of encodings of satisfiable 3SAT instances on $v$ variables.
--
--   This is the verifier $V_n$ in the proof of Theorem 5.1.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), proof of Theorem 5.1 (\label{thm:approximation-hardness}), with Definitions 3.13–3.14 (\label{def:verifier}, \label{def:computation-assignment}) and Claim 3.15 (\label{clm:verifier-system}); Lean: LatticePrepro/ThreeSAT.lean, LatticePrepro.ThreeSAT.verifier

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
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
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT

/-! Further definitions from `LatticePrepro/ThreeSAT.lean`, continuing `Def_LatticePrepro_ThreeSAT`. -/

namespace LatticePrepro

namespace ThreeSAT

/-- The quadratic verifier of the 3SAT verifier circuit over `𝔽_p`. -/
abbrev verifier (p v : ℕ) : QuadraticVerifier p := (circuit v).toGateVerifier.toQuadratic p

end ThreeSAT

end LatticePrepro


