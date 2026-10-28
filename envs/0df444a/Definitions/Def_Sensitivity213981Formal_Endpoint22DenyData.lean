-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22DenyData
-- name    : Sensitivity213981Formal_Endpoint22DenyData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:53:56.642272+00:00
-- url     : https://prove2.me/theorems/fbc2e79e-56bd-4ad3-809f-2be885a9c374
-- title:
--   Endpoint22 Deny Data — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Deny Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.deny161`, `ThreeBoundMinmaxNumeric.Endpoint22.deny162`, `ThreeBoundMinmaxNumeric.Endpoint22.deny164`, `ThreeBoundMinmaxNumeric.Endpoint22.deny165`, `ThreeBoundMinmaxNumeric.Endpoint22.deny167`, `ThreeBoundMinmaxNumeric.Endpoint22.deny17`, `ThreeBoundMinmaxNumeric.Endpoint22.deny169`, `ThreeBoundMinmaxNumeric.Endpoint22.deny171`, `ThreeBoundMinmaxNumeric.Endpoint22.deny173`, `ThreeBoundMinmaxNumeric.Endpoint22.deny174`, `ThreeBoundMinmaxNumeric.Endpoint22.deny176`, `ThreeBoundMinmaxNumeric.Endpoint22.deny177`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22DenyData.lean, lines 1–259.

import Definitions.Def_Sensitivity213981Formal_Endpoint22CostValues
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankBlockedBits
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundRankAnnotated
def deny0 : ℕ:=1172812402961

def deny1 : ℕ:=4311810321

def deny2 : ℕ:=1172812402961

def deny5 : ℕ:=1104075100433

def deny7 : ℕ:=1172812402705

def deny10 : ℕ:=1099781181440







def deny17 : ℕ:=1172812402944

def deny20 : ℕ:=1168516387072



def deny24 : ℕ:=1172812337424

def deny26 : ℕ:=1172812402960



def deny29 : ℕ:=1172812337424



def deny33 : ℕ:=1172812402960

def deny35 : ℕ:=1172812337424

def deny36 : ℕ:=1172812337424

def deny37 : ℕ:=1172812337424

def deny38 : ℕ:=1172812337424



def deny44 : ℕ:=1172812337424

def deny45 : ℕ:=1172812337424

def deny46 : ℕ:=1172812337424

def deny47 : ℕ:=1172812337424

def deny48 : ℕ:=1172812398592

def deny49 : ℕ:=1172543963136

def deny50 : ℕ:=1172812398592

def deny51 : ℕ:=1172543963136

def deny52 : ℕ:=73015558144

def deny56 : ℕ:=4312858624

def deny57 : ℕ:=1172812398592



def deny61 : ℕ:=17891328

def deny62 : ℕ:=1172812402688

def deny63 : ℕ:=1099797958656

def deny64 : ℕ:=1099781181440

def deny65 : ℕ:=1172812402944



def deny67 : ℕ:=1168516387072



def deny69 : ℕ:=1172812337424





def deny73 : ℕ:=1172812337424

def deny74 : ℕ:=1172812402960

def deny76 : ℕ:=1172812337424

def deny77 : ℕ:=1172812337424

def deny78 : ℕ:=1172812337424

def deny79 : ℕ:=1172812337424

def deny80 : ℕ:=1172812337424

def deny81 : ℕ:=1172812337424

def deny82 : ℕ:=1172812337424





def deny87 : ℕ:=1172812337424

def deny88 : ℕ:=1172812337424

def deny89 : ℕ:=1172812337424



def deny91 : ℕ:=4312858624

def deny94 : ℕ:=4311810048

def deny97 : ℕ:=4311810048

def deny102 : ℕ:=17891328



def deny108 : ℕ:=1172812402688













def deny123 : ℕ:=1172812402688

def deny124 : ℕ:=1172812402688

def deny128 : ℕ:=1099780132864

def deny129 : ℕ:=1172812402944

def deny132 : ℕ:=1168516387072

def deny134 : ℕ:=1172812402960

def deny135 : ℕ:=1172812337424





def deny139 : ℕ:=1172812337424

def deny140 : ℕ:=1172812402960

def deny142 : ℕ:=1172812337424

def deny143 : ℕ:=1172812337424

def deny145 : ℕ:=1172812337424



def deny147 : ℕ:=1172812337424

def deny148 : ℕ:=1172812337424

def deny149 : ℕ:=1172812337424

def deny150 : ℕ:=1172812337424

def deny151 : ℕ:=1172812337424

def deny152 : ℕ:=1172812337424

def deny153 : ℕ:=1172812337424

def deny155 : ℕ:=1172812337424

def deny156 : ℕ:=1172812337424

def deny158 : ℕ:=1172812398592

def deny159 : ℕ:=4312858624

def deny161 : ℕ:=1172812402688

def deny162 : ℕ:=1099781181440

def deny164 : ℕ:=1172812402944

def deny165 : ℕ:=1168516387072

def deny167 : ℕ:=1172812402944

def deny169 : ℕ:=1168516387072

def deny171 : ℕ:=1172812402960



def deny173 : ℕ:=1172812402960

def deny174 : ℕ:=1172812337424

def deny176 : ℕ:=1172812402960

def deny177 : ℕ:=1172812402960

def deny178 : ℕ:=1172812337424



def deny180 : ℕ:=1172812337424

def deny182 : ℕ:=1172812337424

def deny183 : ℕ:=1172812337424



def deny186 : ℕ:=1172812337424

def deny187 : ℕ:=1172812337424

def deny188 : ℕ:=1172812337424

def deny189 : ℕ:=1172812337424

def deny190 : ℕ:=1172812337424

def deny191 : ℕ:=1172812337424



def deny195 : ℕ:=1172812402960



end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


