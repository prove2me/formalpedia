-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
-- name    : Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:13:59.83395+00:00
-- url     : https://prove2.me/theorems/214d3d82-5c82-40fa-894f-200d8ea00fa9
-- title:
--   Det Index Product Places Inequality Sq
-- statement:
--   Definitions and structural lemmas for Det Index Product Places Inequality Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/DetIndexProductPlacesInequalitySq.lean

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors
noncomputable section
namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure
abbrev FreeQuotCard : Prop := Formalism.SLP.FreeQuotCard
abbrev GInj : Prop := Formalism.SLP.GInj
def EmbedGB : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] [Finite B] (g : ℕ) (φ : A →+ B),
    Function.Injective φ → (∀ x, φ x ∈ (nsmulAddMonoidHom g : B →+ B).range) →
    Nat.card A ≤ Nat.card (nsmulAddMonoidHom g : B →+ B).range
def GramDetGen : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t t' : R),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -t else 0) W Z
        (Matrix.diagonal fun i => if i = Fin.last r then -t' else 0)).det =
      (-1) ^ (r + 1) *
        (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
          (W.submatrix Fin.castSucc Fin.castSucc).det)
def GramDet : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T T' : ℝ),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then (-(T : ℂ)) else 0)
        Z.conjTranspose Z
        (Matrix.diagonal fun i => if i = Fin.last r then (-(T' : ℂ)) else 0)).det =
      (-1) ^ (r + 1) *
        ((‖Z.det‖ ^ 2 - T * T' * ‖(Z.submatrix Fin.castSucc Fin.castSucc).det‖ ^ 2 : ℝ) : ℂ)
def GramNondeg : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) (B : V →ₗ[K] V →ₛₗ[σ] K) (v : ι → V),
    (Matrix.of fun i j => B (v i) (v j)).det ≠ 0 →
    LinearIndependent K v ∧
      finrank K (Submodule.span K (Set.range v)) = Fintype.card ι ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B y x = 0) → x = 0) ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B x y = 0) → x = 0)
def QuadToJ : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ),
    (∀ u v : ℂ, ‖M 0 0 * u + M 0 1 * v‖ ^ 2 - ‖M 1 0 * u + M 1 1 * v‖ ^ 2 = ‖u‖ ^ 2 - ‖v‖ ^ 2) →
    M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J
def IsoBij : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J →
    ‖M.det‖ = 1 ∧ Function.Bijective M.mulVec
def DenomNormFrac : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (α : E) (J : FractionalIdeal (𝓞 E)⁰ E),
    α ≠ 0 → J ≠ 0 → (∀ x ∈ J, IsInt (α * x)) →
    1 ≤ |Algebra.norm ℚ α| * FractionalIdeal.absNorm J
def DetIndexProductInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g : ℝ) (e f : ℕ),
    0 < dPs₁ → 0 < dPs₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) →
    dLa₁ * i₁ ^ 2 ≤ G0₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dPs₁ * dPs₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂)
def DetIndexProductPlacesInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ : ℝ) (e f : ℕ),
    0 < P₁ → 0 < P₂ → 0 < dQ₁ → 0 < dQ₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    0 < NT → 0 < K₁ → 0 < K₂ → 0 < Nr₁ → 0 < Nr₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) → dPs₁ = P₁ * dQ₁ → dPs₂ = P₂ * dQ₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ / Nr₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ / Nr₂ →
    NT / (Nr₂ * K₂ ^ 2) ≤ P₁ → NT / (Nr₁ * K₁ ^ 2) ≤ P₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dQ₁ * dQ₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT
def FormCoeffEq : Prop :=
  ∀ (a b c d : ℂ) (T T' : ℝ), 0 < T → 0 < T' →
    (∀ u v : ℂ, T * ‖a * u + b * v‖ ^ 2 - T' * ‖c * u + d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) →
    T' * ‖c‖ ^ 2 / T = T * ‖b‖ ^ 2 / T' ∧ ‖a‖ = ‖d‖
def DivGlob : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (e : E) (N : ℕ), 0 < N → IsInt e →
    (∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P e N) →
    ∃ β : 𝓞 E, e = (N : E) * (β : E)
end Formalism.HermitianLatticeCounting.LocalIntegralStructure


