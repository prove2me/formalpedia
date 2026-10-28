-- Prove2me | Definitions.Def_BS2_b3ba934b_SaturatedOrientations
-- name    : BS2_b3ba934b_SaturatedOrientations
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:47:33.285677+00:00
-- url     : https://prove2.me/theorems/ab001d79-7d25-450d-aab6-d8d118d0f25b
-- title:
--   Sensitivity separation: SaturatedOrientations (complete source module)
-- statement:
--   Complete Lean source module `SaturatedOrientations` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/SaturatedOrientations.lean; original SHA-256 66f2e6a3df94e501149defae2124428390b7608ca35e27950cfdf259dd60c571; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Budget saturation in the exact executable orientation enumerator. -/
import Definitions.Def_BS2_b3ba934b_Q2EnumerationBridge

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace ThreeBoundSaturated
open ThreeBoundQ2
open scoped BigOperators
variable {V : Type} [DecidableEq V]

theorem orientations_sound (es : List (V × V)) (ds : List Bool) (b : V → ℕ)
    (h : ds ∈ orientations b es) : ds.length=es.length ∧ ∀ v, outCount es ds v ≤ b v := by
  induction es generalizing ds b with
  | nil =>
      have he : ds=[] := by simpa only [orientations,List.mem_singleton] using h
      subst ds
      exact ⟨rfl,fun _ => Nat.zero_le _⟩
  | cons e es ih =>
      rw [orientations,List.mem_append] at h
      rcases h with h | h
      · by_cases hp : 0<b e.1
        · rw [if_pos hp] at h
          obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp h
          obtain ⟨hlen,hb⟩ := ih rest (spend b e.1) hr
          refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ hlen,?_⟩
          intro v
          have hh := hb v
          by_cases he : v=e.1
          · subst v
            simp only [outCount,Bool.false_eq_true,if_false,ite_true,spend] at hh ⊢
            omega
          · have he' := Ne.symm he
            simpa only [outCount,Bool.false_eq_true,if_false,if_neg he',Nat.zero_add,spend,if_neg he] using hh
        · rw [if_neg hp] at h
          contradiction
      · by_cases hp : 0<b e.2
        · rw [if_pos hp] at h
          obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp h
          obtain ⟨hlen,hb⟩ := ih rest (spend b e.2) hr
          refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ hlen,?_⟩
          intro v
          have hh := hb v
          by_cases he : v=e.2
          · subst v
            simp only [outCount,if_true,ite_true,spend] at hh ⊢
            omega
          · have he' := Ne.symm he
            simpa only [outCount,if_true,if_neg he',Nat.zero_add,spend,if_neg he] using hh
        · rw [if_neg hp] at h
          contradiction

def inCount : List (V × V) → List Bool → V → ℕ
  | [], _, _ => 0
  | _::_, [], _ => 0
  | e::es, d::ds, v =>
      (if (if d then e.1 else e.2)=v then 1 else 0)+inCount es ds v

def incidentCount (es : List (V × V)) (v : V) : ℕ :=
  (es.map fun e => (if e.1=v then 1 else 0)+(if e.2=v then 1 else 0)).sum

theorem inCount_eq_countP (es : List (V × V)) (ds : List Bool) (v : V) :
    inCount es ds v=(directedEdges es ds).countP (fun e => e.2=v) := by
  induction es generalizing ds with
  | nil => simp [inCount,directedEdges]
  | cons e es ih =>
      cases ds with
      | nil => simp [inCount,directedEdges]
      | cons d ds =>
          cases d
          · change (if e.2=v then 1 else 0)+inCount es ds v=
              (e::directedEdges es ds).countP (fun e => e.2=v)
            rw [ih]
            by_cases h : e.2=v <;> simp [List.countP_cons,h,Nat.add_comm]
          · change (if e.1=v then 1 else 0)+inCount es ds v=
              (e.swap::directedEdges es ds).countP (fun e => e.2=v)
            rw [ih]
            by_cases h : e.1=v <;> simp [List.countP_cons,h,Nat.add_comm]

theorem out_add_in (es : List (V × V)) (ds : List Bool) (v : V)
    (hlen : ds.length=es.length) :
    outCount es ds v+inCount es ds v=incidentCount es v := by
  induction es generalizing ds with
  | nil => simp [outCount,inCount,incidentCount]
  | cons e es ih =>
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
          have hlen' : ds.length=es.length := by simpa using hlen
          have hh := ih ds hlen'
          cases d <;>
            simp only [outCount,inCount,incidentCount,List.map_cons,List.sum_cons,
              Bool.false_eq_true,if_false,if_true] at * <;> omega

theorem sum_outCount [Fintype V] (es : List (V × V)) (ds : List Bool)
    (hlen : ds.length=es.length) : (∑ v, outCount es ds v)=es.length := by
  induction es generalizing ds with
  | nil => simp [outCount]
  | cons e es ih =>
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
          have hlen' : ds.length=es.length := by simpa using hlen
          have hh := ih ds hlen'
          cases d <;>
            simp only [outCount,Bool.false_eq_true,if_false,if_true,Finset.sum_add_distrib,hh,List.length_cons] <;>
            simp [Nat.add_comm]

theorem saturated_outCount [Fintype V] (es : List (V × V)) (ds : List Bool)
    (q : ℕ) (hlen : ds.length=es.length) (hsize : es.length=Fintype.card V*q)
    (hb : ∀ v, outCount es ds v ≤ q) (v : V) : outCount es ds v=q := by
  have hsum : (∑ w, outCount es ds w)=∑ _w : V, q := by
    rw [sum_outCount es ds hlen,hsize]
    simp
  apply le_antisymm (hb v)
  by_contra hn
  have hlt : outCount es ds v<q := by omega
  have hh := Finset.sum_lt_sum (fun w (_ : w ∈ (Finset.univ : Finset V)) => hb w)
    ⟨v,Finset.mem_univ v,hlt⟩
  omega

theorem regular_seven (ds : List Bool)
    (h : ds ∈ orientations (fun _ : Fin 7 => 3) (edges 7)) :
    ∀ v : Fin 7, outCount (edges 7) ds v=3 ∧ inCount (edges 7) ds v=3 := by
  obtain ⟨hlen,hb⟩ := orientations_sound (edges 7) ds (fun _=>3) h
  have hsize : (edges 7).length=Fintype.card (Fin 7)*3 := by decide +kernel
  have hout := saturated_outCount (edges 7) ds 3 hlen hsize hb
  have hincident : ∀ v : Fin 7, incidentCount (edges 7) v=6 := by decide +kernel
  intro v
  have hh := out_add_in (edges 7) ds v hlen
  rw [hout v,hincident v] at hh
  exact ⟨hout v,by omega⟩

theorem regular_nine (ds : List Bool)
    (h : ds ∈ orientations (fun _ : Fin 9 => 4) (edges 9)) :
    ∀ v : Fin 9, outCount (edges 9) ds v=4 ∧ inCount (edges 9) ds v=4 := by
  obtain ⟨hlen,hb⟩ := orientations_sound (edges 9) ds (fun _=>4) h
  have hsize : (edges 9).length=Fintype.card (Fin 9)*4 := by decide +kernel
  have hout := saturated_outCount (edges 9) ds 4 hlen hsize hb
  have hincident : ∀ v : Fin 9, incidentCount (edges 9) v=8 := by decide +kernel
  intro v
  have hh := out_add_in (edges 9) ds v hlen
  rw [hout v,hincident v] at hh
  exact ⟨hout v,by omega⟩

end ThreeBoundSaturated

#print axioms ThreeBoundSaturated.orientations_sound
#print axioms ThreeBoundSaturated.regular_seven
#print axioms ThreeBoundSaturated.regular_nine


