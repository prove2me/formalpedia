-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
-- name    : LeanPool_DeciSigma1_Constraints_RankedExtensions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:51:58.352732+00:00
-- url     : https://prove2.me/theorems/f3231a41-8b98-4e6a-b76d-ed272e49af16
-- title:
--   Ranked Extensions
-- statement:
--   Definitions and structural lemmas for Ranked Extensions, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n k m : ℕ}
def lift (Γ : List (LitT n (Fin k))) (m : ℕ) : List (LitT n (Fin (k + m))) :=
  Γ.map (LitT.map (Fin.castAdd m))
variable {V : Type*}
end DeciSigma1.Constraints
namespace DeciSigma1.Constraints
namespace Ranked
variable {n k m : ℕ}
structure Extension (Γ : List (LitT n (Fin k))) (ψ : List (LitT n (Fin (k + m))))
    (Source Sink : Fin (k + m) → Prop) (rank : Fin (k + m) → ℕ) : Prop where
  source_not_original : ∀ {z}, Source z → ¬ z.val < k
  sink_not_original : ∀ {z}, Sink z → ¬ z.val < k
  source_not_sink : ∀ {z}, Source z → ¬ Sink z
  variable_cases : ∀ z, (∃ u : Fin k, z = Fin.castAdd m u) ∨ Source z ∨ Sink z
  original_mem : ∀ l ∈ Γ, l.map (Fin.castAdd m) ∈ ψ
  copy : ∀ a b, LitT.le a b ∈ ψ →
    ∃ a' b', LitT.le a' b' ∈ Γ ∧ a = Fin.castAdd m a' ∧ b = Fin.castAdd m b'
  lower : ∀ a c, LitT.fLe a c ∈ ψ →
    (∃ a' c', LitT.fLe a' c' ∈ Γ ∧ a = Fin.castAdd m ∘ a' ∧ c = Fin.castAdd m c') ∨
    ((∀ i, Source (a i) ∧ rank c < rank (a i)) ∧ ¬ Sink c)
  upper : ∀ c b, LitT.leF c b ∈ ψ →
    (∃ c' b', LitT.leF c' b' ∈ Γ ∧ c = Fin.castAdd m c' ∧ b = Fin.castAdd m ∘ b') ∨
    ((∀ i, Sink (b i) ∧ rank c < rank (b i)) ∧ ¬ Source c)
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}
end Ranked
end DeciSigma1.Constraints
namespace DeciSigma1.Constraints.Ranked
open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics
variable {n k m : ℕ}
section Extension
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}
end Extension
end DeciSigma1.Constraints.Ranked


