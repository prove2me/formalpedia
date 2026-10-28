-- Prove2me | Definitions.Def_Sensitivity213303_NumericAdmissibility
-- name    : Sensitivity213303_NumericAdmissibility
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:21:10.222399+00:00
-- url     : https://prove2.me/theorems/202095f2-aa63-4f43-aece-a2c3d3fea28e
-- title:
--   Admissibility and positivity conditions for a numerical profile
-- statement:
--   Ordered(v) requires the A and B entries to respect the neighboring conditioning and target monotonicity inequalities. GuardOrdered(recipe,v) requires each relevant strong-guard-to-target B bound to be no larger than the strong-to-weak guard B bound. Admissible is their conjunction. BasePositive(v) requires every valid A and B entry to be at least one, which suffices for the initial one-bit Boolean family. All these conditions are finite and decidable for an explicit profile.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module NumericAdmissibility; source SHA256 fb7cfe1530d840838947bedc1f68aa1424bd9575e727b86a5f3a9213103420a9.

import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundProfiles
end ThreeBoundProfiles


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

def Ordered {n : ℕ} (v : Profile n) : Prop :=
  ∀ i j : Fin n, i<j →
    v (.a i j) ≤ v (.a (next i) j) ∧
    v (.a i j) ≤ v (.a i (prev j)) ∧
    v (.b i j) ≤ v (.b (next i) j) ∧
    v (.b i j) ≤ v (.b i (prev j))

def GuardOrdered {n : ℕ} (recipe : Fin n → Entry) (v : Profile n) : Prop :=
  ∀ i j : Fin n, i≤j → ∀ k : Fin 9, k.val≤(recipe j).tolerance →
    (bExpr n (recipe j).guard ((recipe j).threshold k.val)).eval v ≤
      (bExpr n (recipe j).guard (recipe i).guard).eval v

def Admissible {n : ℕ} (recipe : Fin n → Entry) (v : Profile n) : Prop :=
  Ordered v ∧ GuardOrdered recipe v

instance {n : ℕ} (v : Profile n) : Decidable (Ordered v) := by unfold Ordered; infer_instance
instance {n : ℕ} (r : Fin n → Entry) (v : Profile n) : Decidable (GuardOrdered r v) := by
  unfold GuardOrdered; infer_instance
instance {n : ℕ} (r : Fin n → Entry) (v : Profile n) : Decidable (Admissible r v) := by
  unfold Admissible; infer_instance







def BasePositive {n : ℕ} (v : Profile n) : Prop :=
  ∀ i j : Fin n, i≤j → 1≤v (.a i j) ∧ 1≤v (.b i j)

instance {n : ℕ} (v : Profile n) : Decidable (BasePositive v) := by
  unfold BasePositive; infer_instance



end ThreeBoundNumeric


