-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
-- name    : LeanPool_DeciSigma1_Constraints_GroundBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:52:32.393801+00:00
-- url     : https://prove2.me/theorems/e9c5d866-d180-4403-af67-698ceaf9da94
-- title:
--   Ground Bounds
-- statement:
--   Definitions and structural lemmas for Ground Bounds, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Constraints.GroundCompiler
open DeciSigma1.Semantics
variable {n k : ℕ} {V : Type*}
abbrev Occurrence : FTree n → Type
  | .bot | .top => Empty
  | .node a => Σ i : Fin n, Option (Occurrence (a i))
noncomputable instance occFintype (g : FTree n) : Fintype (Occurrence g) := by
  induction g with
  | bot => exact inferInstanceAs (Fintype Empty)
  | top => exact inferInstanceAs (Fintype Empty)
  | node a ih =>
    letI (i : Fin n) : Fintype (Occurrence (a i)) := ih i
    exact inferInstanceAs (Fintype (Σ i : Fin n, Option (Occurrence (a i))))
def depth : (g : FTree n) → Occurrence g → ℕ
  | .bot, o | .top, o => o.elim
  | .node _, ⟨_, none⟩ => 1
  | .node a, ⟨i, some o⟩ => depth (a i) o + 1
def value : (g : FTree n) → Occurrence g → FTree n
  | .bot, o | .top, o => o.elim
  | .node a, ⟨i, none⟩ => a i
  | .node a, ⟨i, some o⟩ => value (a i) o
def compile (lower : Bool) (x : V) : (g : FTree n) → (Occurrence g → V) → List (LitT n (V))
  | .bot, _ => if lower then [] else [.eqBot x]
  | .top, _ => if lower then [.eqTop x] else []
  | .node a, e =>
      (if lower then .fLe (fun i => e ⟨i, none⟩) x else .leF x (fun i => e ⟨i, none⟩)) ::
        (List.finRange n).flatMap fun i =>
          compile lower (e ⟨i, none⟩) (a i) (fun o => e ⟨i, some o⟩)
def IsRankedLiteral (lower : Bool) (Fresh : V → Prop) (rank : V → ℕ) : LitT n (V) → Prop
  | .fLe a x => lower = true ∧ (∀ i, Fresh (a i) ∧ rank x < rank (a i))
  | .leF x a => lower = false ∧ (∀ i, Fresh (a i) ∧ rank x < rank (a i))
  | .le _ _ => False
  | .eqBot _ | .eqTop _ => True
noncomputable def occurrenceVar (g : FTree n) :
    Occurrence g → Fin (k + Fintype.card (Occurrence g)) :=
  fun o => Fin.natAdd k (Fintype.equivFin (Occurrence g) o)
noncomputable def extend (g : FTree n) (ρ : Fin k → Tree n) :
    Fin (k + Fintype.card (Occurrence g)) → Tree n :=
  Fin.addCases ρ (fun i => (value g ((Fintype.equivFin (Occurrence g)).symm i)).toTree)
noncomputable def rank (g : FTree n) : Fin (k + Fintype.card (Occurrence g)) → ℕ :=
  Fin.addCases (fun _ => 0) (fun i => depth g ((Fintype.equivFin (Occurrence g)).symm i))
end DeciSigma1.Constraints.GroundCompiler


