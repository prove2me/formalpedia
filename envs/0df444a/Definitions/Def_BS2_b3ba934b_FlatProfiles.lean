-- Prove2me | Definitions.Def_BS2_b3ba934b_FlatProfiles
-- name    : BS2_b3ba934b_FlatProfiles
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:32:26.048369+00:00
-- url     : https://prove2.me/theorems/b0cfaecf-38ca-481a-80a2-b818b6b8cecb
-- title:
--   Sensitivity separation: FlatProfiles (complete source module)
-- statement:
--   Complete Lean source module `FlatProfiles` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/FlatProfiles.lean; original SHA-256 276bf0aa1b00665f06233efe8838114a174b78aa763035615b6412c63cde2a61; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Compressed numerical profile layout and a complete coordinate checker.
The interpretation is always the named semantic A/B/M/P/D coordinate. -/
import Definitions.Def_BS2_b3ba934b_NumericExpressions

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

def valid {n : ℕ} : Coord n → Prop
  | .a i j | .b i j => i ≤ j
  | .m i j => i ≤ j ∧ j.val+1<n
  | .p j l => j<l
  | .d i j l => i≤j ∧ j<l

instance {n : ℕ} (c : Coord n) : Decidable (valid c) := by cases c <;> unfold valid <;> infer_instance

def coords (n : ℕ) : List (Coord n) :=
  ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    [.a i j,.b i j,.m i j,.p i j]) ++
  ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    (List.finRange n).map fun l => .d i j l)

theorem mem_coords {n : ℕ} (c : Coord n) : c ∈ coords n := by
  cases c with
  | a i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | b i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | m i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | p i j =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,by simp⟩⟩
  | d i j l =>
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_flatMap.mpr
        ⟨j,List.mem_finRange j,List.mem_map.mpr ⟨l,List.mem_finRange l,rfl⟩⟩⟩

def validCoords (n : ℕ) : List (Coord n) := (coords n).filter fun c => decide (valid c)

theorem mem_validCoords {n : ℕ} (c : Coord n) : c ∈ validCoords n ↔ valid c := by
  simp only [validCoords,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun h=>h.2, fun h=>⟨mem_coords c,h⟩⟩

def aIndex (n i j : ℕ) : ℕ := i*(2*n+1-i)/2+(j-i)
def bIndex (n i j : ℕ) : ℕ := n*(n+1)/2+aIndex n i j
def mIndex (n i j : ℕ) : ℕ := n*(n+1)+j*(j+1)/2+i
def pIndex (n j l : ℕ) : ℕ := n*(n+1)+n*(n-1)/2+j*(2*n-1-j)/2+(l-j-1)
def dIndex (n i j l : ℕ) : ℕ :=
  2*n*n+((List.range j).map fun k=>(k+1)*(n-k-1)).sum+i*(n-j-1)+(l-j-1)

def flatIndex {n : ℕ} : Coord n → ℕ
  | .a i j => aIndex n i.val j.val
  | .b i j => bIndex n i.val j.val
  | .m i j => mIndex n i.val j.val
  | .p j l => pIndex n j.val l.val
  | .d i j l => dIndex n i.val j.val l.val

def profileOfArray (n : ℕ) (v : Array ℕ) : Profile n := fun c => v.getD (flatIndex c) 0

/-- A balanced lookup tree gives logarithmic kernel reduction for certificates. -/
inductive NatTable where
  | leaf : ℕ → NatTable
  | branch : ℕ → NatTable → NatTable → NatTable

def NatTable.get : NatTable → ℕ → ℕ
  | .leaf v, _ => v
  | .branch cut left right, i => if i < cut then left.get i else right.get i

def profileOfTable (n : ℕ) (v : NatTable) : Profile n := fun c=>v.get (flatIndex c)

def compareProfiles {n : ℕ} (v w : Profile n) : Bool :=
  (validCoords n).all fun c=>v c ≤ w c

theorem compareProfiles_sound {n : ℕ} (v w : Profile n)
    (h : compareProfiles v w = true) : ∀ c, valid c → v c ≤ w c := by
  intro c hc
  exact of_decide_eq_true ((List.all_eq_true.mp h) c (mem_validCoords c |>.mpr hc))

theorem sem_of_not_valid {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (c : Coord n) (v : ℕ) (h : ¬valid c) :
    Sem F c v := by
  cases c with
  | a i j => exact fun hij => False.elim (h hij)
  | b i j => exact fun hij => False.elim (h hij)
  | m i j => exact fun hij hn => False.elim (h ⟨hij,hn⟩)
  | p j l => exact fun hjl => False.elim (h hjl)
  | d i j l => exact fun hij hjl => False.elim (h ⟨hij,hjl⟩)

theorem checked_upper {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (v w : Profile n) (hv : Upper F v)
    (h : compareProfiles v w = true) : Upper F w := by
  intro c
  by_cases hc : valid c
  · exact sem_mono F c _ _ (compareProfiles_sound v w h c hc) (hv c)
  · exact sem_of_not_valid F c _ hc

theorem compareProfiles_scale {n : ℕ} (v w : Profile n) (k : ℕ)
    (h : compareProfiles v w = true) :
    compareProfiles (fun c=>k*v c) (fun c=>k*w c) = true := by
  apply List.all_eq_true.mpr
  intro c hc
  exact decide_eq_true (Nat.mul_le_mul_left k
    (compareProfiles_sound v w h c (mem_validCoords c |>.mp hc)))

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.checked_upper


