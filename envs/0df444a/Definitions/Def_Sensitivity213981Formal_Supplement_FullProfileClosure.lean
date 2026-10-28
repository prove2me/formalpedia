-- Prove2me | Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
-- name    : Sensitivity213981Formal_Supplement_FullProfileClosure
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:24:33.033465+00:00
-- url     : https://prove2.me/theorems/9191adb9-03a3-4120-8c3c-d285c5a0ebfe
-- title:
--   Supplement Full Profile Closure — sensitivity certificate definitions
-- statement:
--   The definitions for Full Profile Closure in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundFullProfile.mRules`, `ThreeBoundFullProfile.pRules`, `ThreeBoundFullProfile.dRules`, `ThreeBoundFullProfile.gapRules`, `ThreeBoundFullProfile.close`, `ThreeBoundFullProfile.meet`, `ThreeBoundFullProfile.Rule.value`, `ThreeBoundFullProfile.applyRule`, `ThreeBoundFullProfile.runRules`, `ThreeBoundFullProfile.bRules`, `ThreeBoundFullProfile.aRules`, `ThreeBoundFullProfile.orderRules`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; FullProfileClosure.lean, lines 1–303.

import Definitions.Def_Sensitivity213981Formal_FullProfileClosure
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange

namespace Sensitivity213981Formal
section
/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]































def meet (v w : Profile n) : Profile n := fun c => min (v c) (w c)







def Rule.value (v : Profile n) : Rule n → ℕ
  | .aCond i j _ => v (.a (next i) j)
  | .aTarget i j _ => v (.a i (prev j))
  | .bTarget i j _ => v (.b (next i) j)
  | .bCond i j _ => v (.b i (prev j))
  | .mFromB i j _ _ => v (.b i j)
  | .mTarget i j _ _ => v (.m (next i) j)
  | .pFromA j l _ => v (.a (next j) l)
  | .pTarget j l _ => v (.p j (prev l))
  | .dFromMP i j l _ _ => v (.m i j)+v (.p j l)
  | .dDown i j l _ _ => v (.d (next i) j l)
  | .dUp i j l _ _ => v (.d i j (prev l))
  | .bPartition i j _ _ => max (v (.b i (next j))) (v (.m i j))
  | .aPartition j l _ => max (v (.a j l)) (v (.p j l))



def applyRule (tighten : Bool) (v : Profile n) (r : Rule n) : Profile n :=
  fun c => if c = r.target then
    if tighten then min (v c) (r.value v) else r.value v
    else v c



def runRules (tighten : Bool) : List (Rule n) → Profile n → Profile n
  | [], v => v
  | r::rs, v => runRules tighten rs (applyRule tighten v r)



/-- B envelopes: reverse traversal gives max of the final B bound and all
intervening M gaps. Keeping a separate envelope preserves the Python pass's
accumulator exactly, before its minimum with the original B entries. -/
def bRules (n : ℕ) : List (Rule n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).reverse.filterMap fun j =>
      if h : i ≤  j ∧ j.val+1 <  n then some (.bPartition i j h.1 h.2) else none

/-- A envelopes: forward traversal gives max of the initial A bound and all
preceding P gaps, before its minimum with the original A entries. -/
def aRules (n : ℕ) : List (Rule n) :=
  (List.finRange n).flatMap fun l =>
    (List.finRange n).filterMap fun j =>
      if h : j <  l then some (.aPartition j l h) else none

/-- Triangular A/B ordering, traversed by increasing interval length. -/
def orderRules (n : ℕ) : List (Rule n) :=
  (List.range n).flatMap fun gap =>
    (List.finRange n).flatMap fun i =>
      if h : 0 <  gap ∧ i.val+gap <  n then
        let j : Fin n := ⟨i.val+gap,h.2⟩
        have hij : i <  j := by change i.val <  i.val+gap; omega
        [.aCond i j hij,.aTarget i j hij,.bTarget i j hij,.bCond i j hij]
      else []

def mRules (j : Fin n) (hn : j.val+1 <  n) : List (Rule n) :=
  (List.finRange n).reverse.flatMap fun i =>
    if h : i ≤  j then
      [.mFromB i j h hn] ++ (if hi : i <  j then [.mTarget i j hi hn] else [])
    else []

def pRules (j : Fin n) : List (Rule n) :=
  (List.finRange n).flatMap fun l =>
    if h : j <  l then
      [.pFromA j l h] ++ (if hl : j.val+1 <  l.val then [.pTarget j l hl] else [])
    else []

def dRules (j : Fin n) : List (Rule n) :=
  (List.finRange n).reverse.flatMap fun i =>
    (List.finRange n).flatMap fun l =>
      if h : i ≤  j ∧ j <  l then
        [.dFromMP i j l h.1 h.2] ++
          (if hi : i <  j then [.dDown i j l hi h.2] else []) ++
          (if hl : j.val+1 <  l.val then [.dUp i j l h.1 hl] else [])
      else []

def gapRules (n : ℕ) : List (Rule n) :=
  (List.finRange n).flatMap fun j =>
    if hn : j.val+1 <  n then mRules j hn ++ pRules j ++ dRules j else []

/-- The complete closure procedure, in the same order as the exact verifier.
The first two passes use envelopes; all remaining updates use minima. -/
def close (v : Profile n) : Profile n :=
  let w₁ := meet v (runRules false (bRules n) v)
  let w₂ := meet w₁ (runRules false (aRules n) w₁)
  runRules true (gapRules n) (runRules true (orderRules n) w₂)





end
end ThreeBoundFullProfile




end
end Sensitivity213981Formal


