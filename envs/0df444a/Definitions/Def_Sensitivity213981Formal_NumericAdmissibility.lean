-- Prove2me | Definitions.Def_Sensitivity213981Formal_NumericAdmissibility
-- name    : Sensitivity213981Formal_NumericAdmissibility
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:17:27.397133+00:00
-- url     : https://prove2.me/theorems/2ac7949d-b3b8-4bdf-addb-b91cd1c56249
-- title:
--   Numeric Admissibility — sensitivity certificate definitions
-- statement:
--   The definitions for Numeric Admissibility in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundNumeric.instDecidableAdmissible`, `ThreeBoundNumeric.Ordered`, `ThreeBoundNumeric.BasePositive`, `ThreeBoundNumeric.instDecidableBasePositive`, `ThreeBoundNumeric.GuardOrdered`, `ThreeBoundNumeric.Admissible`, `ThreeBoundNumeric.instDecidableOrdered`, `ThreeBoundNumeric.instDecidableGuardOrdered`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; NumericAdmissibility.lean, lines 1–96.

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_FlatProfiles
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

def Ordered {n : ℕ} (v : Profile n) : Prop :=
  ∀ i j : Fin n, i< j →
    v (.a i j) ≤  v (.a (next i) j) ∧
    v (.a i j) ≤  v (.a i (prev j)) ∧
    v (.b i j) ≤  v (.b (next i) j) ∧
    v (.b i j) ≤  v (.b i (prev j))

def GuardOrdered {n : ℕ} (recipe : Fin n → Entry) (v : Profile n) : Prop :=
  ∀ i j : Fin n, i≤ j → ∀ k : Fin 9, k.val≤ (recipe j).tolerance →
    (bExpr n (recipe j).guard ((recipe j).threshold k.val)).eval v ≤ 
      (bExpr n (recipe j).guard (recipe i).guard).eval v

def Admissible {n : ℕ} (recipe : Fin n → Entry) (v : Profile n) : Prop :=
  Ordered v ∧ GuardOrdered recipe v

instance _root_.Sensitivity213981Formal.ThreeBoundNumeric.instDecidableOrdered {n : ℕ} (v : Profile n) : Decidable (Ordered v) := by unfold Ordered; infer_instance
instance _root_.Sensitivity213981Formal.ThreeBoundNumeric.instDecidableGuardOrdered {n : ℕ} (r : Fin n → Entry) (v : Profile n) : Decidable (GuardOrdered r v) := by
  unfold GuardOrdered; infer_instance
instance _root_.Sensitivity213981Formal.ThreeBoundNumeric.instDecidableAdmissible {n : ℕ} (r : Fin n → Entry) (v : Profile n) : Decidable (Admissible r v) := by
  unfold Admissible; infer_instance







def BasePositive {n : ℕ} (v : Profile n) : Prop :=
  ∀ i j : Fin n, i≤ j → 1≤ v (.a i j) ∧ 1≤ v (.b i j)

instance _root_.Sensitivity213981Formal.ThreeBoundNumeric.instDecidableBasePositive {n : ℕ} (v : Profile n) : Decidable (BasePositive v) := by
  unfold BasePositive; infer_instance



end ThreeBoundNumeric




end
end Sensitivity213981Formal


