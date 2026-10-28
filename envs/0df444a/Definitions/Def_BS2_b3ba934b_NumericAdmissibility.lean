-- Prove2me | Definitions.Def_BS2_b3ba934b_NumericAdmissibility
-- name    : BS2_b3ba934b_NumericAdmissibility
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:33:00.369948+00:00
-- url     : https://prove2.me/theorems/4331358d-dbc3-48cf-9c9f-b4f5a0731b4a
-- title:
--   Sensitivity separation: NumericAdmissibility (complete source module)
-- statement:
--   Complete Lean source module `NumericAdmissibility` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/NumericAdmissibility.lean; original SHA-256 fb7cfe1530d840838947bedc1f68aa1424bd9575e727b86a5f3a9213103420a9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Q2RawExpressions
import Definitions.Def_BS2_b3ba934b_ClosureHomogeneity
import Definitions.Def_BS2_b3ba934b_FlatProfiles

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

theorem ordered_scale {n : ℕ} (v : Profile n) (c : ℕ) (h : Ordered v) :
    Ordered (scale c v) := by
  intro i j hij
  obtain ⟨ha,hb,hc,hd⟩ := h i j hij
  exact ⟨Nat.mul_le_mul_left c ha,Nat.mul_le_mul_left c hb,
    Nat.mul_le_mul_left c hc,Nat.mul_le_mul_left c hd⟩

theorem guardOrdered_scale {n : ℕ} (r : Fin n → Entry) (v : Profile n) (c : ℕ)
    (h : GuardOrdered r v) : GuardOrdered r (scale c v) := by
  intro i j hij k hk
  have hleft := Expr.eval_homogeneous
    (bExpr n (r j).guard ((r j).threshold k.val)) v c
  have hright := Expr.eval_homogeneous (bExpr n (r j).guard (r i).guard) v c
  change (bExpr n (r j).guard ((r j).threshold k.val)).eval (fun z=>c*v z) ≤
    (bExpr n (r j).guard (r i).guard).eval (fun z=>c*v z)
  rw [hleft,hright]
  exact Nat.mul_le_mul_left c (h i j hij k hk)

theorem admissible_scale {n : ℕ} (r : Fin n → Entry) (v : Profile n) (c : ℕ)
    (h : Admissible r v) : Admissible r (scale c v) :=
  ⟨ordered_scale v c h.1,guardOrdered_scale r v c h.2⟩

def BasePositive {n : ℕ} (v : Profile n) : Prop :=
  ∀ i j : Fin n, i≤j → 1≤v (.a i j) ∧ 1≤v (.b i j)

instance {n : ℕ} (v : Profile n) : Decidable (BasePositive v) := by
  unfold BasePositive; infer_instance

theorem oneBit_upper {n : ℕ} (v : Profile n) (h : BasePositive v) :
    Upper (fun (_ : Fin n) (x : Unit → Bool)=>x ()) v := by
  intro coord
  cases coord with
  | a i j =>
      intro hij x hx
      exact (show (flipsTo (fun x : Unit → Bool=>x ()) true x).card≤1 by
        simpa using Finset.card_le_univ (flipsTo (fun x : Unit → Bool=>x ()) true x)).trans
        (h i j hij).1
  | b i j =>
      intro hij x hx
      exact (show (flipsTo (fun x : Unit → Bool=>x ()) false x).card≤1 by
        simpa using Finset.card_le_univ (flipsTo (fun x : Unit → Bool=>x ()) false x)).trans
        (h i j hij).2
  | m i j =>
      intro hij hn x hx hy
      change x ()=true at hx
      change x ()=false at hy
      rw [hy] at hx
      contradiction
  | p j l =>
      intro hjl x hx hy
      change x ()=true at hx
      change x ()=false at hy
      rw [hy] at hx
      contradiction
  | d i j l =>
      intro hij hjl x hx hy
      change x ()=true at hx
      change x ()=false at hy
      rw [hy] at hx
      contradiction

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.oneBit_upper
#print axioms ThreeBoundNumeric.admissible_scale


