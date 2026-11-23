-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:49.800097+00:00
-- url     : https://prove2.me/theorems/19d2f93a-6d18-46c7-80d1-006ee9678a01
-- title:
--   Transfer Statement
-- statement:
--   Definitions and structural lemmas for Transfer Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/TransferStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
section Words
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def rWord (ε : Fin n → Bool) (D : List (Matrix (Fin n) (Fin n) ℂ)) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  D.foldr (fun Z F => EcV ε Z F) f
def hWord (D : List (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  D.foldr (fun Z G => Rhol Z G) F
def lWord (D : List (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  D.foldr (fun Z G => Lhol Z G) F
end Words
def adW (ε : Fin n → Bool) (k : KG ε) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    List (Matrix (Fin n) (Fin n) ℂ) :=
  D.map fun Z => toMK k⁻¹ * Z * toMK k
def PhiP (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ := PhiM μ z⁻¹
def OmegaP (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {z | z⁻¹ ∈ OmegaSet n}
def PsMWordInterface (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (μ : Fin n → ℤ),
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧
      (∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n) ∧
      ∀ D : List (Matrix (Fin n) (Fin n) ℂ),
        DifferentiableOn ℂ (lWord D (psM T μ)) U ∧
        (∀ z ∈ U, Continuous fun k : KG ε => lWord (adW ε k D) (PhiM μ) (toMK k⁻¹ * z * toMK k)) ∧
        ∀ z ∈ U, lWord D (psM T μ) z =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, lWord (adW ε k D) (PhiM μ) (toMK k⁻¹ * z * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)
def TransferStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    IsHCParam lam → IsMu lam μ →
    ∀ (N : ℕ) (D : Fin N → List (Matrix (Fin n) (Fin n) ℂ)) (v : Fin N → T.V),
      (∀ (k : KG ε) (z : Matrix (Fin n) (Fin n) ℂ), z ∈ OmegaP n →
          ∑ i, ⟪T.op k T.w, v i⟫_ℂ * hWord (adW ε k (D i)) (PhiP μ) z = 0) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∑ i, rWord ε (D i) (PsiM T μ) g (v i) = 0
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK


