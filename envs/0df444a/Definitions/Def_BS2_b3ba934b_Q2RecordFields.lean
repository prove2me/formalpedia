-- Prove2me | Definitions.Def_BS2_b3ba934b_Q2RecordFields
-- name    : BS2_b3ba934b_Q2RecordFields
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:32:33.895783+00:00
-- url     : https://prove2.me/theorems/9d4cc06d-63f8-47ae-8086-69d30b9b993c
-- title:
--   Sensitivity separation: Q2RecordFields (complete source module)
-- statement:
--   Complete Lean source module `Q2RecordFields` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Q2RecordFields.lean; original SHA-256 00882f676a90870216de7259384922917139ae5d9fd115cc2c73bcce1d414a2e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact meanings of the 29 fields of the executable q2 record. -/
import Definitions.Def_BS2_b3ba934b_Q2EnumerationBridge
import Definitions.Def_BS2_b3ba934b_Q2RawExpressions

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundRecordFields
open ThreeBoundQ2 ThreeBoundNumeric
open scoped Classical BigOperators
noncomputable section

def residual (ts : List Kind) (ds : List Bool) (v : Fin ts.length) : ℕ :=
  budget (ts.get v) - outCount (edges ts.length) ds v

def incoming (ts : List Kind) (ds : List Bool) (v : Fin ts.length) : ℕ :=
  ((directedEdges (edges ts.length) ds).filter
    fun e => isGuard (ts.get e.1) && decide (e.2 = v)).length

def typeCount (ts : List Kind) (k : Kind) : ℕ := (ts.filter fun u => u = k).length

def histogram (ts : List Kind) (ds : List Bool) (k : Kind) (hits : ℕ) : ℕ :=
  ((List.finRange ts.length).filter fun v => ts.get v = k ∧ min 2 (incoming ts ds v) = hits).length

def external (ts : List Kind) (ds : List Bool) : ℕ :=
  (((List.finRange ts.length).filter fun v => isGuard (ts.get v)).map (residual ts ds)).sum

def sortedResiduals (ts : List Kind) (ds : List Bool) : List ℕ :=
  ((List.finRange ts.length).map (residual ts ds)).mergeSort (· ≤ ·)

def residualPrefix (ts : List Kind) (ds : List Bool) (k : ℕ) : ℕ :=
  if k ≤ ts.length then ((sortedResiduals ts ds).take k).sum else 1000000

theorem record_explicit (ts : List Kind) (ds : List Bool) :
    record (ts,ds) =
    [typeCount ts 0,typeCount ts 1,typeCount ts 2,typeCount ts 3,
     typeCount ts 4,typeCount ts 5,typeCount ts 6,typeCount ts 7,
     external ts ds,
     histogram ts ds 0 1,histogram ts ds 0 2,histogram ts ds 1 1,histogram ts ds 1 2,
     histogram ts ds 2 1,histogram ts ds 2 2,histogram ts ds 3 1,histogram ts ds 3 2,
     histogram ts ds 4 1,histogram ts ds 4 2,histogram ts ds 5 1,histogram ts ds 5 2,
     histogram ts ds 6 1,histogram ts ds 6 2,histogram ts ds 7 1,histogram ts ds 7 2,
     residualPrefix ts ds 1,residualPrefix ts ds 2,residualPrefix ts ds 3,residualPrefix ts ds 4] := rfl

@[simp] theorem record_length (ts : List Kind) (ds : List Bool) : (record (ts,ds)).length = 29 := by
  rw [record_explicit]
  rfl

theorem record_type (ts : List Kind) (ds : List Bool) (k : Kind) :
    recordOfList (record (ts,ds)) k.val = typeCount ts k := by
  rw [record_explicit]
  fin_cases k <;> rfl

theorem record_external (ts : List Kind) (ds : List Bool) :
    recordOfList (record (ts,ds)) 8 = external ts ds := by
  rw [record_explicit]
  rfl

theorem record_histogram (ts : List Kind) (ds : List Bool) (k : Kind) (h : Fin 2) :
    recordOfList (record (ts,ds)) (9+2*k.val+h.val) = histogram ts ds k (h.val+1) := by
  rw [record_explicit]
  fin_cases k <;> fin_cases h <;> rfl

theorem record_prefix (ts : List Kind) (ds : List Bool) (k : Fin 4) :
    recordOfList (record (ts,ds)) (25+k.val) = residualPrefix ts ds (k.val+1) := by
  rw [record_explicit]
  fin_cases k <;> rfl

theorem typeCount_eq_card (ts : List Kind) (k : Kind) :
    typeCount ts k = ((Finset.univ : Finset (Fin ts.length)).filter fun v => ts.get v = k).card := by
  have he := length_filter_ofFn ts.get (fun u => decide (u=k))
  simpa only [typeCount,List.ofFn_get,decide_eq_true_eq] using he

theorem finRange_filter_length {m : ℕ} (p : Fin m → Bool) :
    ((List.finRange m).filter p).length =
      ((Finset.univ : Finset (Fin m)).filter fun v => p v = true).card := by
  rw [← List.countP_eq_length_filter]
  symm
  simpa using (List.nodup_finRange m).card_eq_countP (P := fun v => p v = true)

theorem histogram_eq_card (ts : List Kind) (ds : List Bool) (k : Kind) (h : ℕ) :
    histogram ts ds k h = ((Finset.univ : Finset (Fin ts.length)).filter
      fun v => ts.get v = k ∧ min 2 (incoming ts ds v) = h).card := by
  unfold histogram
  simpa only [decide_eq_true_eq] using finRange_filter_length
    (fun v : Fin ts.length => decide (ts.get v = k ∧ min 2 (incoming ts ds v) = h))

theorem incoming_orientation_eq_card (ts : List Kind)
    (R : Fin ts.length → Fin ts.length → Prop) [DecidableRel R]
    (hR : TournamentHighRows.IsTournament R) (w : Fin ts.length) :
    incoming ts (orientationBits R) w =
      ((Finset.univ : Finset (Fin ts.length)).filter fun v => isGuard (ts.get v) = true ∧ R v w).card := by
  unfold incoming
  rw [← List.countP_eq_length_filter]
  have hp : (fun e : Fin ts.length × Fin ts.length => isGuard (ts.get e.1) && decide (e.2 = w)) =
      (fun e => decide (isGuard (ts.get e.1) = true ∧ e.2 = w)) := by
    funext e
    simp
  rw [hp,← (directedEdges_nodup R).card_eq_countP]
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    obtain ⟨hed,hef⟩ := Finset.mem_filter.mp he
    have hh : isGuard (ts.get e.1) = true ∧ e.2=w := by simpa using hef
    have hr := (mem_directedEdges R hR e.1 e.2).1 (List.mem_toFinset.mp hed)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1,hh.2 ▸ hr⟩
  · intro a ha b hb hab
    have haf : isGuard (ts.get a.1) = true ∧ a.2=w := by
      simpa using (Finset.mem_filter.mp ha).2
    have hbf : isGuard (ts.get b.1) = true ∧ b.2=w := by
      simpa using (Finset.mem_filter.mp hb).2
    exact Prod.ext hab (haf.2.trans hbf.2.symm)
  · intro v hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨hg,hr⟩
    refine ⟨(v,w),Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      ((mem_directedEdges R hR v w).2 hr),?_⟩,rfl⟩
    simpa using hg

theorem external_eq_sum (ts : List Kind) (ds : List Bool) :
    external ts ds = ∑ v ∈ (Finset.univ : Finset (Fin ts.length)).filter
      (fun v => isGuard (ts.get v) = true), residual ts ds v := by
  unfold external
  have hnd : (((List.finRange ts.length).filter fun v => isGuard (ts.get v))).Nodup :=
    (List.nodup_finRange _).filter _
  rw [← List.sum_toFinset (residual ts ds) hnd]
  congr 1
  ext v
  simp

end
end ThreeBoundRecordFields

#print axioms ThreeBoundRecordFields.record_type
#print axioms ThreeBoundRecordFields.incoming_orientation_eq_card
#print axioms ThreeBoundRecordFields.external_eq_sum


