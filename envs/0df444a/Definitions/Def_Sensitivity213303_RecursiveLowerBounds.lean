-- Prove2me | Definitions.Def_Sensitivity213303_RecursiveLowerBounds
-- name    : Sensitivity213303_RecursiveLowerBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:39:40.799968+00:00
-- url     : https://prove2.me/theorems/f6b28fad-0a4e-4cf9-b017-db186936786e
-- title:
--   Recursive min/max Boolean families and common sensitive-block witnesses
-- statement:
--   A min/max recipe assigns lower and upper target levels to each row-failure count. A target accepts when both children accept at the lower level and at least one accepts at the upper level. Iterating these recipes from the one-bit function defines total Boolean families on (2|V|)^d input coordinates at depth d. CommonWitnesses records a common rejecting input, a common accepting input with many sensitive single bits, and pairwise disjoint nonempty blocks whose flips make every family level accept. The data supports simultaneous recursive lower bounds on sensitivity and block sensitivity.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module RecursiveLowerBounds; source SHA256 f371f969d5206a484b6d13b39a0779fc99604812ea088faf0ab3a434b7e251c2.

/-
Concrete arbitrary-depth graded/min-max constructions and their lower bounds.
Every recipe sequence below defines total Boolean functions.  No sensitivity
upper bound is claimed; the finite sensitivity-profile soundness remains a
separate obligation for the requested separation exponents.
-/
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
namespace OAI.Paper320
end OAI.Paper320


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









theorem tower_input_dimension {V : Type} [Fintype V] (n : ℕ) :
    Fintype.card (IterProd (V × Bool) n) = (2 * Fintype.card V)^n := by
  simp only [card_iterProd, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]





end ThreeBoundWitness


