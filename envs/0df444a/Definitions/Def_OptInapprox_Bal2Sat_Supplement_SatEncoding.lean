-- Prove2me | Definitions.Def_OptInapprox_Bal2Sat_Supplement_SatEncoding
-- name    : OptInapprox_Bal2Sat_Supplement_SatEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:51:48.782808+00:00
-- url     : https://prove2.me/theorems/fa91fd3f-daee-458a-a763-1fb81a8f6a3a
-- title:
--   Definition 10 and §9 — finite MAX-2SAT encoding and normalized gap
-- statement:
--   A finite MAX-2SAT input is a list of clauses, each a pair of signed variables. Repetition represents a natural-number weight. The map to the published real-weight instance gives each listed clause weight one and uses the published satisfaction predicate, optimum and balancedness. Its normalized optimum is
--
--   $$\operatorname{optFrac}(I)=\frac{\operatorname{OPT}(I)}{|I.\mathrm{clauses}|}.$$
--
--   A self-delimiting unary encoding records the variable count, clause count, variable indices and signs over the published two-symbol alphabet. Gap hardness uses the published polynomial-time many-one reductions from every NP language. Both promise sets require at least one clause; the optional balanced restriction applies to both sets. This supplies an encodable subclass of the source's nonnegative real-weight problem without encoding arbitrary real numbers.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 16,20–21, Definition 10, Definition 12 and §9

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Setting
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace OptInapprox.Bal2Sat.Supplement

/-- Unit-weight clauses with repetitions; an encodable subclass of the published instance. -/
structure SatInput where
  n : ℕ
  clauses : List (Literal n × Literal n)

namespace SatInput

def toInstance (I : SatInput) : Instance I.n where
  m := I.clauses.length
  clause := I.clauses.get
  w := fun _ => 1
  w_nonneg := fun _ => zero_le_one

noncomputable def optFrac (I : SatInput) : ℝ :=
  OPT I.toInstance / (I.clauses.length : ℝ)

def enc (I : SatInput) : List OptInapprox.MaxCut.MCSym :=
  OptInapprox.MaxCut.MCSym.unary I.n ++
  OptInapprox.MaxCut.MCSym.unary I.clauses.length ++
  I.clauses.flatMap fun C =>
    OptInapprox.MaxCut.MCSym.unary C.1.1.val ++
    OptInapprox.MaxCut.MCSym.unary (if C.1.2 then 1 else 0) ++
    OptInapprox.MaxCut.MCSym.unary C.2.1.val ++
    OptInapprox.MaxCut.MCSym.unary (if C.2.2 then 1 else 0)

end SatInput

/-- Both promise sets are restricted to balanced instances when b = true. -/
def SatGapHard (b : Bool) (c s : ℝ) : Prop :=
  OptInapprox.MaxCut.GapNPHard SatInput.enc
    (fun I => I.clauses ≠ [] ∧ (b = true → IsBalanced I.toInstance) ∧ c ≤ I.optFrac)
    (fun I => I.clauses ≠ [] ∧ (b = true → IsBalanced I.toInstance) ∧ I.optFrac ≤ s)

end OptInapprox.Bal2Sat.Supplement


