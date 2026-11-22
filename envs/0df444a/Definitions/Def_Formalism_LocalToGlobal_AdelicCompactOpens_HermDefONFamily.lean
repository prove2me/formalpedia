-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_HermDefONFamily
-- name    : Formalism_LocalToGlobal_AdelicCompactOpens_HermDefONFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:03.769832+00:00
-- url     : https://prove2.me/theorems/38b99c6e-6a7b-494b-a044-61c00cc601a6
-- title:
--   Herm Def ONFamily
-- statement:
--   Definitions and structural lemmas for Herm Def ONFamily, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AdelicCompactOpens/HermDefONFamily.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Props
open Matrix
open scoped ComplexOrder
def PolyDenseZero : Prop :=
  ∀ (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) (S : Set (σ → ℂ)), Dense S →
    (∀ x ∈ S, MvPolynomial.eval x p = 0) → p = 0
def HermDefON : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef → ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1
def HermConjExists : Prop :=
  ∀ (E : Type) [Field E] [CharZero E] (σ : E →+* E), (∀ x, σ (σ x) = x) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (J.map σ)ᵀ = J →
      ∃ P : Matrix (Fin n) (Fin n) E, (P.map σ)ᵀ * J * P = J.map σ
def DiagConj : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
    (∃ (P : GL (Fin n) ℂ) (d : Fin n → ℂ), (P : Matrix (Fin n) (Fin n) ℂ) * A * (P⁻¹ : GL (Fin n) ℂ) = diagonal d) →
    (∃ (P : GL (Fin n) ℂ) (d : Fin n → ℂ), (P : Matrix (Fin n) (Fin n) ℂ) * B * (P⁻¹ : GL (Fin n) ℂ) = diagonal d) →
    A.charpoly = B.charpoly →
    ∃ Q : GL (Fin n) ℂ, (Q : Matrix (Fin n) (Fin n) ℂ) * A * (Q⁻¹ : GL (Fin n) ℂ) = B
end Formalism.L2.Props


