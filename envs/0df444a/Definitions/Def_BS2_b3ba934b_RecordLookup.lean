-- Prove2me | Definitions.Def_BS2_b3ba934b_RecordLookup
-- name    : BS2_b3ba934b_RecordLookup
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:59:53.956144+00:00
-- url     : https://prove2.me/theorems/a171cb4f-8333-4a87-a553-2c37abda9d17
-- title:
--   Sensitivity separation: RecordLookup (complete source module)
-- statement:
--   Complete Lean source module `RecordLookup` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RecordLookup.lean; original SHA-256 2e5ce300e00fc4b5bff13e83e8dd316316fb7334890ab9d2559f1615c9a45952; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Verified logarithmic lookup for a finite list of exact case records. -/
import Definitions.Def_BS2_b3ba934b_CachedRawChecker

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric

inductive RecordLookup where
  | leaf : List ℕ → RecordLookup
  | branch : ℕ → RecordLookup → RecordLookup → RecordLookup

def RecordLookup.rows : RecordLookup → List (List ℕ)
  | .leaf row => [row]
  | .branch _ left right => left.rows++right.rows

def RecordLookup.get : RecordLookup → ℕ → List ℕ
  | .leaf row, _ => row
  | .branch cut left right, k => if k<cut then left.get k else right.get (k-cut)

def RecordLookup.valid : RecordLookup → Prop
  | .leaf _ => True
  | .branch cut left right => cut=left.rows.length ∧ left.valid ∧ right.valid

def RecordLookup.validDecidable : (table : RecordLookup) → Decidable table.valid
  | .leaf _ => inferInstanceAs (Decidable True)
  | .branch cut left right => by
      letI : Decidable left.valid := validDecidable left
      letI : Decidable right.valid := validDecidable right
      exact inferInstanceAs (Decidable (cut=left.rows.length ∧ left.valid ∧ right.valid))

instance (table : RecordLookup) : Decidable table.valid := table.validDecidable

theorem RecordLookup.get_correct (table : RecordLookup) (h : table.valid)
    (k : ℕ) (hk : k<table.rows.length) : table.get k=table.rows[k]?.getD [] := by
  induction table generalizing k with
  | leaf row =>
      have : k=0 := by simp only [rows,List.length_singleton] at hk; omega
      subst k
      rfl
  | branch cut left right hl hr =>
      obtain ⟨hcut,hleft,hright⟩ := h
      subst cut
      by_cases hlt : k<left.rows.length
      · rw [get,if_pos hlt,hl hleft k hlt]
        simp only [rows,List.getElem?_append_left hlt]
      · have hkr : k-left.rows.length<right.rows.length := by
          simp only [rows,List.length_append] at hk
          omega
        rw [get,if_neg hlt,hr hright (k-left.rows.length) hkr]
        simp only [rows,List.getElem?_append_right (Nat.le_of_not_gt hlt)]

def indexedFastCachedCheck (caps : Caps) (table : RecordLookup) (a c : Entry)
    (values : CostValues) (bound k : ℕ) : Bool :=
  cachedRecordCheck caps a c values bound (table.get k)

theorem rawA_le_of_fast_checks (n : ℕ) (v : ThreeBoundFullProfile.Profile n) (caps : Caps)
    (records : List (List ℕ)) (table : RecordLookup) (a c : Entry) (values : CostValues) (bound : ℕ)
    (hvalid : table.valid) (hrows : table.rows=records)
    (hpos : 0<c.tolerance) (htwo : c.tolerance≤2)
    (hc : coeffCheck n v a c values=true)
    (h : ∀ k, k<table.rows.length → indexedFastCachedCheck caps table a c values bound k=true) :
    (rawAExpr n caps records a c).eval v≤bound := by
  apply rawA_le_of_cached_checks n v caps records a c values bound hpos htwo hc
  intro k hk
  have hlen : k<table.rows.length := by simpa only [hrows] using hk
  have hh:=h k hlen
  simpa only [indexedFastCachedCheck,indexedCachedCheck,table.get_correct hvalid k hlen,hrows] using hh

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.RecordLookup.get_correct


