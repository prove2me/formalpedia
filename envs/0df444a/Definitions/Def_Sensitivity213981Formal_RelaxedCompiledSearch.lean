-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedCompiledSearch
-- name    : Sensitivity213981Formal_RelaxedCompiledSearch
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:08:46.797773+00:00
-- url     : https://prove2.me/theorems/f7be481e-b421-407b-8205-8eb3755221cb
-- title:
--   Relaxed Compiled Search — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Compiled Search in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedCompiled.Plan`, `ThreeBoundRelaxedCompiled.Int3`, `ThreeBoundRelaxedCompiled.Int3.get`, `ThreeBoundRelaxedCompiled.Job`, `ThreeBoundRelaxedCompiled.Int3.ofFn`, `ThreeBoundRelaxedCompiled.Int3.sub`, `ThreeBoundRelaxedCompiled.zero`, `ThreeBoundRelaxedCompiled.weight3`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedCompiledSearch.lean, lines 1–191.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedStateSearch
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section
/- Compile suffix options and conservation intervals once, then split the
remaining exact search at any finite frontier. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundRelaxedCompiled
open ThreeBoundQ3 ThreeBoundRelaxed

structure Int3 where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving Repr, DecidableEq

def Int3.get (x : Int3) (k : Fin 3) : ℤ :=
  if k.val=0 then x.a else if k.val=1 then x.b else x.c

def Int3.ofFn (f : Fin 3 → ℤ) : Int3 := ⟨f 0,f 1,f 2⟩



def Int3.sub (x y : Int3) : Int3 := ⟨x.a-y.a,x.b-y.b,x.c-y.c⟩



def zero : Int3 := ⟨0,0,0⟩

def weight3 (s : State) : Int3 := Int3.ofFn (weight s)











inductive Plan where
  | done : Plan
  | step (lo hi : Int3) (choices : List State) (tail : Plan) : Plan
  deriving Repr, DecidableEq









structure Job where
  plan : Plan
  pre : List State
  previous : Option State
  remaining : Int3
  deriving Repr, DecidableEq











end ThreeBoundRelaxedCompiled




end
end Sensitivity213981Formal


