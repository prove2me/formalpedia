-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_InducedCharRealised
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_InducedCharRealised
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:11.21126+00:00
-- url     : https://prove2.me/theorems/da4c2bcb-6e43-41a8-a76d-10c5b80561fb
-- title:
--   Induced Char Realised
-- statement:
--   Definitions and structural lemmas for Induced Char Realised, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealInducedCharacters/InducedCharRealised.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CharRealisedOverRootsOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace BrauerSchur
open scoped BigOperators
section IndFun
variable {G : Type*} [Group G] [Fintype G]
open scoped Classical in

noncomputable def indFun {R : Type*} [Field R] (H : Subgroup G) (f : H → R) (g : G) : R :=
  (Nat.card H : R)⁻¹ * ∑ x : G, if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0
end IndFun
def BrauerInduction : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (n : ℕ)
    (ρ : Representation L G (Fin n → L)),
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (ψ : (i : Fin r) → (H i →* Lˣ)) (a : Fin r → ℤ),
      ∀ g : G, ρ.character g = ∑ i, (a i : L) * indFun (H i) (fun h => ((ψ i h : Lˣ) : L)) g
def InducedCharRealised : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (K : Type) [Field K] [CharZero K] (H : Subgroup G)
    (ψ : H →* Kˣ),
    ∃ (m : ℕ) (σ : Representation K G (Fin m → K)),
      ∀ g : G, LinearMap.trace K (Fin m → K) (σ g) = indFun H (fun h => ((ψ h : Kˣ) : K)) g
def SchurIndexOne : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (K : Type) [Field K] [CharZero K] (χ : G → K),
    (∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) G (Fin n → AlgebraicClosure K)),
        ρ.IsIrreducible ∧ ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)) →
    (∃ (r : ℕ) (m : Fin r → ℕ) (σ : (i : Fin r) → Representation K G (Fin (m i) → K)) (a : Fin r → ℤ),
        ∀ g, χ g = ∑ i, (a i : K) * LinearMap.trace K (Fin (m i) → K) (σ i g)) →
    ∃ (m : ℕ) (τ : Representation K G (Fin m → K)),
      (Nontrivial (Fin m → K) ∧ Function.Surjective τ.asAlgebraHom) ∧
        ∀ g, LinearMap.trace K (Fin m → K) (τ g) = χ g
def CharRealExp : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] [CharZero K] (z : K),
    IsPrimitiveRoot z (Monoid.exponent Γ) →
    ∀ χ : Γ → K,
      (∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) Γ (Fin n → AlgebraicClosure K)),
        ρ.IsIrreducible ∧ ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)) →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K)),
        (Nontrivial (Fin m → K) ∧ Function.Surjective τ.asAlgebraHom) ∧
          ∀ g, LinearMap.trace K (Fin m → K) (τ g) = χ g
end BrauerSchur


