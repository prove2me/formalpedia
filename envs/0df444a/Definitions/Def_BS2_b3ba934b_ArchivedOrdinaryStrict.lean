-- Prove2me | Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryStrict
-- name    : BS2_b3ba934b_ArchivedOrdinaryStrict
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:05:43.064402+00:00
-- url     : https://prove2.me/theorems/72fffa72-8b68-46f4-a433-59c7f1c99463
-- title:
--   Sensitivity separation: ArchivedOrdinaryStrict (complete source module)
-- statement:
--   Complete Lean source module `ArchivedOrdinaryStrict` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ArchivedOrdinaryStrict.lean; original SHA-256 fd29f3853f8c9ae34a24531af3b40941b4ff27adc4efae239aa53b4de11c6fdb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryZero

open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- actual_rawA selected complete sections -/
set_option autoImplicit false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)



end Tournament









end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)

end Nesting



section JointCandidates
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)



end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]



end ZT
end
end z30

section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]



end ZT
end
end z31

section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)



end OAI.Paper320.Tournament
namespace SensitivityQ







end SensitivityQ
namespace SensitivitySourceZero






















end SensitivitySourceZero
end
end z32

section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem guardRepairs_empty_strict (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga)
    (qa q : ℕ) (hq : q < qa)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    guardRepairs T label F tb gb q x = ∅ := by
  have hempty : tolerantGuards T label F tb gb q x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact no_guard_candidate_of_strict T label F hF ta tb ga gb ht hg x hq hx hv
  simp [guardRepairs,hempty]



end ZT
end
end z33

section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z34

section z36
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace SensitivityOrdinaryGuard
end SensitivityOrdinaryGuard
end
end z36

section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





end ZT
end
end z37

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

end ZT
end
end z40

section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



end ZT
end
end z41

section z42

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 ZL

namespace ZT
variable {k : ℕ}

end ZT
end
end z42

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















end ZT
end
end z43

section z58

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivityOrdinaryGuard
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

end ZT
end
end z58

section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem ordinary_zero_strict_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga)
    (qa q : ℕ) (hq : q < qa) (a b : ℕ)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    (flipsTo (tolerantFamily T label F tb gb q) true x).card ≤
      (positiveTargets T label F tb gb q x (by decide)).card*a+
      ((tolerantTargets T label F tb gb q x).card-
        (positiveTargets T label F tb gb q x (by decide)).card)*b := by
  have hoff : tolerantFamily T label F tb gb q x = false := by
    cases hh : tolerantFamily T label F tb gb q x
    · rfl
    · have hw := family_nested T label F hF ht hg hq.le x hh
      simp [hx] at hw
  have hcover := up_subset_repairs T label F tb gb q x hoff
  rw [guardRepairs_empty_strict T label F hF ta tb ga gb ht hg qa q hq x hx,
    Finset.union_empty] at hcover
  exact (Finset.card_le_card hcover).trans
    (targetRepairs_card T label F hF ta tb ga gb ht hg qa q hq.le a b ha hb x hx)



end ZT
end
end z60

section z61

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem integer_low_eq (q m u : ℕ) :
    ((u : Int)*((m : Int)-(q : Int))+(u*(u-1)/2 : Nat)).toNat =
      (u*m+u.choose 2)-q*u := by
  have he : (u : Int)*((m : Int)-(q : Int))+(u*(u-1)/2 : Nat) =
      ((u*m+u*(u-1)/2 : Nat) : Int)-((q*u : Nat) : Int) := by
    push_cast
    ring
  rw [he]
  simp only [Int.toNat_sub,Nat.choose_two_right]



theorem caseFor_of_candidate (q m u : ℕ)
    (hc : (u+m).choose 2 ≤ q*u+(q+1)*m)
    (hu : u ≤ candidateTotalCap q m u) :
    caseFor q m u = some (booleanCase q m u) := by
  have hc' : ¬ (u+m)*(u+m-1)/2 > q*u+(q+1)*m := by
    rw [←Nat.choose_two_right]
    exact not_lt.mpr hc
  simp only [caseFor,if_neg hc']
  change (if u > candidateTotalCap q m u then none else
    some (⟨m,u,candidateTotalCap q m u,m*(q+1)-m*(m-1)/2,
      min (m*(m-1)/2) (2*m),
      ((u : Int)*((m : Int)-(q : Int))+(u*(u-1)/2 : Nat)).toNat,
      ((u : Int)*((m : Int)-(q : Int))+(u*(u-1)/2 : Nat)).toNat-u,markedCap q m⟩ : Case)) = _
  rw [if_neg (not_lt.mpr hu),integer_low_eq]
  simp only [booleanCase,Nat.choose_two_right]





end ZT
end
end z61

section z62

set_option maxHeartbeats 5000000
namespace ZT







theorem zero_strict_candidate_cases (z t u a b : ℕ)
    (hu : u ≤ 1) (ht : t ≤ 22) (hsource : u=1 → t-1 ≤ 19)
    (hraw : z ≤ u*a+(t-u)*b) : z ≤ max (22*b) (a+19*b) := by
  interval_cases u
  · norm_num at hraw
    exact (hraw.trans (Nat.mul_le_mul_right b ht)).trans (le_max_left _ _)
  · norm_num at hraw
    have hs := hsource rfl
    have hb := Nat.mul_le_mul_right b hs
    exact (by omega : z ≤ a+19*b).trans (le_max_right _ _)

end ZT
end z62

section z64

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem strict_zero_tolerance (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (qa : ℕ) (hqa : 0 < qa) (a b : ℕ)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hordinary : DefectBound T label 0 23)
    (hsource : SensitivitySourceZero.SourceBound T label 21)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    (flipsTo (tolerantFamily T label F tb gb 0) true x).card ≤ max (22*b) (a+19*b) := by
  let TC := tolerantTargets T label F tb gb 0 x
  let P := positiveTargets T label F tb gb 0 x (by decide)
  let G := tolerantGuards T label F tb gb 0 x
  let δ := (crossedTargetHeads T label F tb gb 0 x).card
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have hG : G=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact no_guard_candidate_of_strict T label F hF ta tb ga gb ht hg x hqa hx hv
  have hgcard : G.card=0 := by rw [hG]; rfl
  have hu : P.card ≤ 1 := by simpa using positiveTargets_card T label F hF tb gb hgt 0 x (by decide)
  have htcard : TC.card ≤ 22 := by
    have hh := targets_card_of_exclusion T label F hF tb gb hgt 0 23 hordinary x
    change TC.card < 23 at hh
    omega
  have hδbudget := crossedTargetHeads_budget T label F hF tb gb hgt 0 x
  change δ+((P.card*G.card+P.card.choose 2)-0*P.card) ≤ G.card*(0+1)-G.card.choose 2 at hδbudget
  have hδ : δ=0 := by rw [hgcard] at hδbudget; norm_num at hδbudget; omega
  have hsrc : P.card=1 → TC.card-1 ≤ 19 := by
    intro hpc
    have hne : (P ∪ G).Nonempty := by
      rw [hG,Finset.union_empty]
      exact Finset.card_pos.mp (by omega)
    have hh := remaining_card_source_zero T label F hF tb gb hgt 21 hsource x hne
    have hpart := remaining_targets_card T label F tb gb 0 x
    change (remainingOrdinaryTargets T label F tb gb 0 x).card+δ+P.card=TC.card at hpart
    omega
  have hraw := ordinary_zero_strict_cost T label F hF ta tb ga gb ht hg qa 0 hqa a b ha hb x hx
  exact zero_strict_candidate_cases _ TC.card P.card a b hu htcard hsrc hraw

end ZT
end
end z64


end ThreeBoundOrdinaryArchive


