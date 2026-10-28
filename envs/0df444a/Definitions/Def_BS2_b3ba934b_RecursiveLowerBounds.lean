-- Prove2me | Definitions.Def_BS2_b3ba934b_RecursiveLowerBounds
-- name    : BS2_b3ba934b_RecursiveLowerBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:36:38.429327+00:00
-- url     : https://prove2.me/theorems/d4e95328-818a-4475-8193-e991af834d0f
-- title:
--   Sensitivity separation: RecursiveLowerBounds (complete source module)
-- statement:
--   Complete Lean source module `RecursiveLowerBounds` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RecursiveLowerBounds.lean; original SHA-256 f371f969d5206a484b6d13b39a0779fc99604812ea088faf0ab3a434b7e251c2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Concrete arbitrary-depth graded/min-max constructions and their lower bounds.
Every recipe sequence below defines total Boolean functions.  No sensitivity
upper bound is claimed; the finite sensitivity-profile soundness remains a
separate obligation for the requested separation exponents.
-/
import Definitions.Def_BS2_b3ba934b_WitnessLifting
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundWitness
open OAI.Paper320

def IterProd (A : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => A × IterProd A n

instance iterProdFintype (A : Type) [Fintype A] : ∀ n : ℕ, Fintype (IterProd A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
      letI := iterProdFintype A n
      exact inferInstanceAs (Fintype (A × IterProd A n))

theorem card_iterProd (A : Type) [Fintype A] (n : ℕ) :
    Fintype.card (IterProd A n) = (Fintype.card A)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card (A × IterProd A n) = _
      rw [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

structure MinMaxRecipe (L V : Type) where
  Adj : V → V → Prop
  loopless : ∀ v, ¬ Adj v v
  label : V → V → Bool
  guard : L → L
  tolerance : L → ℕ
  lower : L → ℕ → L
  upper : L → ℕ → L

def minmaxTarget {L I : Type} (F : L → (I → Bool) → Bool)
    (t u : L → ℕ → L) (l : L) (d : ℕ) (x y : I → Bool) : Bool :=
  F (t l d) x && F (t l d) y && (F (u l d) x || F (u l d) y)

def MinMaxRecipe.stage {L I V : Type} (r : MinMaxRecipe L V)
    (F : L → (I → Bool) → Bool) : Stage L I V where
  Adj := r.Adj
  loopless := r.loopless
  label := r.label
  guard := r.guard
  tolerance := r.tolerance
  target := minmaxTarget F r.lower r.upper

theorem minmax_accepts {L I V : Type} (r : MinMaxRecipe L V)
    (F : L → (I → Bool) → Bool) (l : L) (x y : I → Bool)
    (hx : ∀ a, F a x = true) (hy : ∀ a, F a y = true) :
    (r.stage F).target l 0 x y = true := by
  simp [MinMaxRecipe.stage, minmaxTarget, hx, hy]

theorem minmax_rejects {L I V : Type} (r : MinMaxRecipe L V)
    (F : L → (I → Bool) → Bool) (l : L) (d : ℕ) (x y : I → Bool)
    (h : (∀ a, F a x = false) ∨ (∀ a, F a y = false)) :
    (r.stage F).target l d x y = false := by
  rcases h with hx | hy
  · simp [MinMaxRecipe.stage, minmaxTarget, hx]
  · simp [MinMaxRecipe.stage, minmaxTarget, hy]

/-- Equal lower and upper targets specialize the min/max condition to a graded AND target. -/
theorem minmax_equal_targets {L I : Type} (F : L → (I → Bool) → Bool)
    (t : L → ℕ → L) (l : L) (d : ℕ) (x y : I → Bool) :
    minmaxTarget F t t l d x y = (F (t l d) x && F (t l d) y) := by
  unfold minmaxTarget
  cases F (t l d) x <;> cases F (t l d) y <;> rfl

noncomputable def towerFamily {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) : ∀ n : ℕ,
      L → (IterProd (V × Bool) n → Bool) → Bool
  | 0 => fun _ x => x ()
  | n+1 => parent ((r n).stage (towerFamily r n)) (towerFamily r n)

structure CommonWitnesses {L I : Type} (F : L → (I → Bool) → Bool) (A B : Type) where
  zero : I → Bool
  positive : I → Bool
  positiveBits : A ↪ I
  blocks : B → Finset I
  zero_rejects : ∀ l, F l zero = false
  positive_accepts : ∀ l, F l positive = true
  positive_off : ∀ a l, F l (flip positive {positiveBits a}) = false
  blocks_nonempty : ∀ b, (blocks b).Nonempty
  blocks_disjoint : ∀ a b, a ≠ b → Disjoint (blocks a) (blocks b)
  blocks_on : ∀ b l, F l (flip zero (blocks b)) = true

noncomputable def CommonWitnesses.reindex {L I J A B : Type}
    {F : L → (I → Bool) → Bool} (w : CommonWitnesses F A B) (e : I ≃ J) :
    CommonWitnesses (fun l => ThreeBoundWitness.reindex e (F l)) A B where
  zero := fun j => w.zero (e.symm j)
  positive := fun j => w.positive (e.symm j)
  positiveBits := w.positiveBits.trans e.toEmbedding
  blocks := fun b => (w.blocks b).map e.toEmbedding
  zero_rejects l := by
    simpa only [ThreeBoundWitness.reindex, Equiv.symm_apply_apply] using w.zero_rejects l
  positive_accepts l := by
    simpa only [ThreeBoundWitness.reindex, Equiv.symm_apply_apply] using w.positive_accepts l
  positive_off a l := by
    change F l (fun i => OAI.Paper320.flip (fun j => w.positive (e.symm j))
      {e (w.positiveBits a)} (e i)) = false
    rw [flip_reindex_singleton]
    simpa only [Equiv.symm_apply_apply] using w.positive_off a l
  blocks_nonempty b := (w.blocks_nonempty b).map (f := e.toEmbedding)
  blocks_disjoint a b hab := (Finset.disjoint_map e.toEmbedding).mpr (w.blocks_disjoint a b hab)
  blocks_on b l := by
    change F l (fun i => OAI.Paper320.flip (fun j => w.zero (e.symm j))
      ((w.blocks b).map e.toEmbedding) (e i)) = true
    rw [flip_reindex]
    simpa only [Equiv.symm_apply_apply] using w.blocks_on b l

theorem common_witnesses_lift {L I V A B : Type} [Fintype V]
    (r : MinMaxRecipe L V) (F : L → (I → Bool) → Bool)
    (w : CommonWitnesses F A B) (v : V) :
    Nonempty (CommonWitnesses (parent (r.stage F) F) (Bool × A) (V × B)) := by
  obtain ⟨p', e', hp', he'⟩ := common_positive_lift (r.stage F) F
    w.zero w.positive w.zero_rejects w.positive_accepts w.positiveBits w.positive_off
    (minmax_accepts r F) (minmax_rejects r F) v
  obtain ⟨z', B', hz', hne', hdis', hflip'⟩ := common_blocks_lift (r.stage F) F
    w.zero w.zero_rejects w.blocks w.blocks_nonempty w.blocks_disjoint w.blocks_on
    (minmax_accepts r F) (minmax_rejects r F)
  exact ⟨⟨z', p', e', B', hz', hp', he', hne', hdis', hflip'⟩⟩

theorem tower_common_witnesses {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) (v : V) (n : ℕ) :
    Nonempty (CommonWitnesses (towerFamily r n) (IterProd Bool n) (IterProd V n)) := by
  classical
  induction n with
  | zero =>
      refine ⟨{
        zero := fun _ => false
        positive := fun _ => true
        positiveBits := Function.Embedding.refl Unit
        blocks := fun _ => {()}
        zero_rejects := fun _ => rfl
        positive_accepts := fun _ => rfl
        positive_off := ?_
        blocks_nonempty := ?_
        blocks_disjoint := ?_
        blocks_on := ?_ }⟩
      · intro a l
        cases a
        change (OAI.Paper320.flip (fun _ : Unit => true) {()}) () = false
        simp [OAI.Paper320.flip]
      · intro a
        exact Finset.singleton_nonempty ()
      · intro a b h
        cases a
        cases b
        exact False.elim (h rfl)
      · intro a l
        change (OAI.Paper320.flip (fun _ : Unit => false) {()}) () = true
        simp [OAI.Paper320.flip]
  | succ n ih =>
      obtain ⟨w⟩ := ih
      exact common_witnesses_lift (r n) (towerFamily r n) w v

theorem tower_lower_bounds {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) (v : V) (n : ℕ) (l : L) :
    2^n ≤ sensitivity (towerFamily r n l) ∧
      (Fintype.card V)^n ≤ blockSensitivity (towerFamily r n l) := by
  obtain ⟨w⟩ := tower_common_witnesses r v n
  constructor
  · have h := sensitivity_lower_of_indexed_bits (towerFamily r n l) w.positive
      w.positiveBits (fun a => by rw [w.positive_off a l, w.positive_accepts l]; decide)
    simpa only [card_iterProd, Fintype.card_bool] using h
  · have h := blockSensitivity_lower_of_indexed_blocks (towerFamily r n l) w.zero
      w.blocks w.blocks_nonempty w.blocks_disjoint
      (fun a => by rw [w.blocks_on a l, w.zero_rejects l]; decide)
    simpa only [card_iterProd] using h

theorem four_stage_lower_bounds {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) (v : V) (m : ℕ) (l : L) :
    16^m ≤ sensitivity (towerFamily r (4*m) l) ∧
      ((Fintype.card V)^4)^m ≤ blockSensitivity (towerFamily r (4*m) l) := by
  have h := tower_lower_bounds r v (4*m) l
  simpa only [pow_mul, show (2 : ℕ)^4 = 16 from rfl] using h

theorem tower_input_dimension {V : Type} [Fintype V] (n : ℕ) :
    Fintype.card (IterProd (V × Bool) n) = (2 * Fintype.card V)^n := by
  simp only [card_iterProd, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

/-- The constructed functions use the campaign's literal `Fin n` input type. -/
theorem tower_finite_lower_bounds {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) (v : V) (n : ℕ) (l : L) :
    ∃ f : (Fin ((2 * Fintype.card V)^n) → Bool) → Bool,
      2^n ≤ sensitivity f ∧ (Fintype.card V)^n ≤ blockSensitivity f := by
  classical
  obtain ⟨w⟩ := tower_common_witnesses r v n
  let e : IterProd (V × Bool) n ≃ Fin ((2 * Fintype.card V)^n) :=
    (Fintype.equivFin _).trans (finCongr (tower_input_dimension n))
  let w' := w.reindex e
  refine ⟨reindex e (towerFamily r n l), ?_, ?_⟩
  · have h := sensitivity_lower_of_indexed_bits (reindex e (towerFamily r n l))
      w'.positive w'.positiveBits (fun a => by
        rw [w'.positive_off a l, w'.positive_accepts l]
        decide)
    simpa only [card_iterProd, Fintype.card_bool] using h
  · have h := blockSensitivity_lower_of_indexed_blocks (reindex e (towerFamily r n l))
      w'.zero w'.blocks w'.blocks_nonempty w'.blocks_disjoint (fun a => by
        rw [w'.blocks_on a l, w'.zero_rejects l]
        decide)
    simpa only [card_iterProd] using h

theorem four_stage_finite_lower_bounds {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) (v : V) (m : ℕ) (l : L) :
    ∃ f : (Fin ((2 * Fintype.card V)^(4*m)) → Bool) → Bool,
      16^m ≤ sensitivity f ∧ ((Fintype.card V)^4)^m ≤ blockSensitivity f := by
  have h := tower_finite_lower_bounds r v (4*m) l
  simpa only [pow_mul, show (2 : ℕ)^4 = 16 from rfl] using h

end ThreeBoundWitness

#print axioms ThreeBoundWitness.tower_common_witnesses
#print axioms ThreeBoundWitness.tower_lower_bounds
#print axioms ThreeBoundWitness.four_stage_lower_bounds
#print axioms ThreeBoundWitness.tower_input_dimension
#print axioms ThreeBoundWitness.tower_finite_lower_bounds
#print axioms ThreeBoundWitness.four_stage_finite_lower_bounds


