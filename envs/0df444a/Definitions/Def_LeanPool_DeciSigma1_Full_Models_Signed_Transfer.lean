-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
-- name    : LeanPool_DeciSigma1_Full_Models_Signed_Transfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:17:23.62018+00:00
-- url     : https://prove2.me/theorems/78b3cd53-d1a4-4a8c-821a-f8bf9f4c8b0d
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Theorems.Thm_DeciSigma1_Full_Models_satFin_iff_finite_assignment
public import Theorems.Thm_DeciSigma1_Satisfiability_Covariant_satFinB_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_satFinB_iff

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Full.Models.Signed.FinitePinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
def symmetrize (c : Fin n → Bool) (A : V × Bool → FTree n)
    (D : V → FTree n) (z : V × Bool) : FTree n :=
  FiniteMedian.median (A z) ((A (z.1, !z.2)).dual)
      ((D z.1).normalize c z.2)
end DeciSigma1.Full.Models.Signed.FinitePinning
namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
def GroundBound.HoldsWithVariance {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (b : GroundBound n V) : Prop :=
  if b.lower then Tree.Le c b.tree.toTree (ρ b.var)
  else Tree.Le c (ρ b.var) b.tree.toTree
end DeciSigma1.Full.Models
namespace DeciSigma1.Full.Models.Signed
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
namespace FinitePinning
variable {V : Type*}
def pin (c : Fin n → Bool) (b : GroundBound n V) (s : Bool) : GroundBound n (V × Bool) :=
  ⟨(b.var, s), Bool.xor b.lower s, b.tree.normalize c s⟩
def pins (c : Fin n → Bool) (B : List (GroundBound n V)) : List (GroundBound n (V × Bool)) :=
  B.flatMap fun b => [pin c b false, pin c b true]
end FinitePinning
end DeciSigma1.Full.Models.Signed
namespace DeciSigma1.Full.Models.Signed
open DeciSigma1.Full.Closure DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
abbrev Observation (n : ℕ) (V : Type*) := Closure.Config n V × Bool
def Observation.Holds {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (o : Observation n V) : Prop :=
  if o.2 then o.1 ∈ configSet c ρ else o.1 ∉ configSet c ρ
def Observation.normalized {V : Type*} (o : Observation n V) : Models.Observation n V :=
  ⟨!o.1.2.1, o.1.1, o.1.2.2, !o.2⟩
def Observation.bound {V : Type*} (c : Fin n → Bool) (o : Observation n V) :
    GroundBound n V :=
  let b := o.normalized.bound
  ⟨b.var, b.lower, b.tree.normalize c false⟩
def BoundRealization {V : Type*} (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) : Prop :=
  ∀ B : List (GroundBound n V),
    (∃ ρ, SatT c ρ Γ ∧ ∀ b ∈ B, b.HoldsWithVariance c ρ) →
    ∃ τ, (∀ v, C (τ v)) ∧ SatT c τ Γ ∧ ∀ b ∈ B, b.HoldsWithVariance c τ
end DeciSigma1.Full.Models.Signed
namespace DeciSigma1.Full.Models.Signed
open DeciSigma1.Satisfiability DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
def decideSatFin {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin n → Bool) (Γ : List (LitT n V)) : Decidable (SatFin c Γ) :=
  decidable_of_iff (satFinB c Γ = true)
    ((satFinB_iff c Γ).trans (satFin_iff_finite_assignment c Γ).symm)
end DeciSigma1.Full.Models.Signed


