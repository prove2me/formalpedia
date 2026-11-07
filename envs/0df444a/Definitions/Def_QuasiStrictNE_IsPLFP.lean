-- Prove2me | Definitions.Def_QuasiStrictNE_IsPLFP
-- name    : QuasiStrictNE_IsPLFP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:25.690517+00:00
-- url     : https://prove2.me/theorems/3f5705ca-8659-4034-9083-9de6ba025225
-- title:
--   Polynomial piecewise-linear fixed-point problem
-- statement:
--   A piecewise-linear fixed-point problem is **polynomial** (Definition 6) when for every valid instance $I$:
--
--   0. $D_I$ is nonempty and bounded (so a nonempty compact convex polytope), and $F_I$ is a continuous self-map of $D_I$;
--   1. the inequalities defining $D_I$ are computed from $I$ in polynomial time;
--   2. $F_I$ is piecewise affine on $D_I$ for a collection of rational hyperplanes, with all coefficients of hyperplanes and affine formulas of encoding length polynomial in $|I|$ (condition 2);
--   3. a polynomial-time algorithm with a linear-comparison oracle for $x$ outputs No if $x\notin D_I$, and otherwise rational $C,c$ with $F_I(x)=Cx+c$.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 6, pp.8–9

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_PLFPData
import Definitions.Def_QuasiStrictNE_PLFPData_D
import Definitions.Def_QuasiStrictNE_PLCond2
import Definitions.Def_QuasiStrictNE_OracleComputesLocalFormula

namespace QuasiStrictNE

open QAlgorithms.LocalHamiltonian

/-- **Polynomial piecewise-linear fixed-point problem** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 6, pp.8–9).

`IsPLFP Φ` holds iff

0. for every valid instance `I`, `D_I` is nonempty and bounded, and `F_I` is a continuous self-map of
   `D_I` ("a continuous self-map of a nonempty compact convex domain DI");
1. the dimension and the inequalities defining `D_I` are computed from `I` in polynomial time
   ("DI is a polytope defined by a set of linear inequalities. And coefficients can be computed from
   I in polynomial time");
2. `F` satisfies condition 2 (`PLCond2`) over the valid instances, with size `|I|`;
3. a polynomial-time linear-comparison oracle algorithm outputs `No` for `x ∉ D_I` and otherwise a
   rational local affine formula `F_I(x) = Cx + c` (`OracleComputesLocalFormula`).

**Formalization Note** `D_I` is given by inequalities, so it is closed and convex; with boundedness
it is compact. The polynomial-time map of condition 1 outputs `dim I`, the number of inequalities and
the inequalities, written with the public `encBin`, `encRatVec`, `encRat`. -/
def IsPLFP (Φ : PLFPData) : Prop :=
  (∀ I, Φ.valid I → (Φ.D I).Nonempty ∧ Bornology.IsBounded (Φ.D I) ∧
    Set.MapsTo (Φ.F I) (Φ.D I) (Φ.D I) ∧ ContinuousOn (Φ.F I) (Φ.D I)) ∧
  (∃ g : List Bool → List Bool, CookPvsNP.PolyTimeComputable g ∧ ∀ I, Φ.valid I →
    g I = encBin (Φ.dim I) ++ encBin (Φ.ineqs I).length ++
      (Φ.ineqs I).flatMap (fun ab => CardinalMatching.encRatVec (Φ.dim I) ab.1 ++ encRat ab.2)) ∧
  PLCond2 (ι := {I : List Bool // Φ.valid I}) (fun I => I.1.length) (fun I => Φ.dim I.1)
    (fun I => Φ.dim I.1) (fun I => Φ.D I.1) (fun I => Φ.F I.1) ∧
  OracleComputesLocalFormula (ι := {I : List Bool // Φ.valid I}) (fun I => I.1)
    (fun I => Φ.dim I.1) (fun I => Φ.dim I.1) (fun I => Φ.D I.1) (fun I => Φ.F I.1)

end QuasiStrictNE


