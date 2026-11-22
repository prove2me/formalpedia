-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Decide
-- name    : LeanPool_DeciSigma1_Full_Decide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:14:23.526038+00:00
-- url     : https://prove2.me/theorems/3203ded6-3ed2-41a1-8ee7-4c94b75856eb
-- title:
--   Decide
-- statement:
--   Definitions and structural lemmas for Decide, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Decide.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Bound
public import Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_finite_iff
public import Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_iff_no_hole
public import Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_regular_iff
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Full
open DeciSigma1.Full.Reduction DeciSigma1.Holes
open DeciSigma1.Full.Models DeciSigma1.Constraints DeciSigma1.Readers.Table
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V)) (q : Fin k → V × V)
def decideExistsModeHole : Decidable (∃ m : Fin k → Bool, ∃ W, (compile c Γ q m).IsHole W) :=
  letI (m : Fin k → Bool) := decideHole (compile c Γ q m)
  inferInstance
def decideDisjEntails : Decidable (DisjEntailsIn (fun _ => True) c Γ q) :=
  match Closure.decideSat c Γ with
  | isFalse hs => isTrue (fun ρ _ hρ => False.elim (hs ⟨ρ, hρ⟩))
  | isTrue hs =>
    letI := decideExistsModeHole c Γ q
    decidable_of_iff _ (disjEntails_iff_no_hole hs).symm
def decideDisjEntailsReg : Decidable (DisjEntailsIn RegularTop c Γ q) :=
  @decidable_of_iff _ _ (disjEntails_regular_iff (c := c) (Γ := Γ) (q := q)).symm
    (decideDisjEntails c Γ q)
def decideDisjEntailsFin : Decidable (DisjEntailsIn FiniteTop c Γ q) :=
  match Signed.decideSatFin c Γ with
  | isFalse hf => isTrue ((disjEntails_finite_iff (c := c) (Γ := Γ) (q := q)).mpr
      (Or.inl hf))
  | isTrue hf =>
    match decideDisjEntails c Γ q with
    | isTrue h => isTrue ((disjEntails_finite_iff).mpr (Or.inr h))
    | isFalse h => isFalse (fun he => (disjEntails_finite_iff.mp he).elim
        (fun hn => hn hf) h)
end DeciSigma1.Full


