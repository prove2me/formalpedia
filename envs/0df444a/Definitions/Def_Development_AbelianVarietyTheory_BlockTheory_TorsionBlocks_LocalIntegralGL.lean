-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:48.362596+00:00
-- url     : https://prove2.me/theorems/c1a5118a-aaea-4901-ae7d-b9b64953f3a2
-- title:
--   Local Integral GL
-- statement:
--   Definitions and structural lemmas for Local Integral GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/LocalIntegralGL.lean

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
section Algebraic
variable {F : Type} [Field F] {r t : ℕ}
def weilPair (μ η : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (g : GL (Fin r) F)
    (h : GL (Fin r ⊕ Fin t) F) (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ) :
    Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ :=
  fun x =>
    ((μ (GeneralLinearGroup.det g) * (μ (GeneralLinearGroup.det h))⁻¹ *
        η (GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((nrm ((GeneralLinearGroup.det g : Fˣ) : F) ^ (((r + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
      ((nrm ((GeneralLinearGroup.det h : Fˣ) : F) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
      Φ (((h⁻¹ : GL (Fin r ⊕ Fin t) F) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F) * x *
        (g : Matrix (Fin r) (Fin r) F))
def blockChar (μ : Fˣ →* ℂˣ) (P : Subgroup (GL (Fin r) F)) (lam : P →* ℂˣ) : P →* ℂˣ :=
  lam * (μ.comp (GeneralLinearGroup.det.comp P.subtype))⁻¹
def datum (t : ℕ) (O : Subring F) (ϖ : F) (μ : Fˣ →* ℂˣ) (P : Subgroup (GL (Fin r) F))
    (lam : P →* ℂˣ) : Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ :=
  phiU O ϖ P (blockChar μ P lam)
def glInt (O : Subring F) (n : Type) [Fintype n] [DecidableEq n] : Subgroup (GL n F) :=
  (GeneralLinearGroup.map (n := n) O.subtype).range
def targetSet (t : ℕ) (O : Subring F) (ϖ : F) (P : Subgroup (GL (Fin r) F)) :
    Set (GL (Fin r ⊕ Fin t) F) :=
  {h | h ∈ glInt O (Fin r ⊕ Fin t) ∧
    (∃ p ∈ P, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ -
      (p : Matrix (Fin r) (Fin r) F) ∈ IIset O ϖ) ∧
    (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₂₁ ∈ IIset O ϖ}
def targetLevel (t : ℕ) (O : Subring F) (ϖ : F) (P : Subgroup (GL (Fin r) F)) :
    Subgroup (GL (Fin r ⊕ Fin t) F) :=
  Subgroup.closure (targetSet t O ϖ P)
def intMatrices (O : Subring F) (n a : Type) : Set (Matrix n a F) := {x | ∀ i j, x i j ∈ O}
def localZeta (q i : ℕ) : ℝ := (1 - ((q : ℝ) ^ i)⁻¹)⁻¹
def dFactor (q r t : ℕ) : ℝ := ∏ i ∈ Finset.Ioc t (r + t), localZeta q i
end Algebraic
section Local
variable {F : Type} [Field F] [ValuativeRel F]
def residueImage {r : ℕ} (P : Subgroup (GL (Fin r) F)) : Subgroup (GL (Fin r) 𝓀[F]) :=
  (P.comap (GeneralLinearGroup.map (n := Fin r) (𝒪[F]).subtype)).map
    (GeneralLinearGroup.map (n := Fin r) (IsLocalRing.residue 𝒪[F]))
def IsNormalisedAbs (nrm : AbsoluteValue F ℝ) : Prop :=
  (∀ x : F, nrm x ≤ 1 ↔ x ∈ 𝒪[F]) ∧
    ∀ ϖ : 𝒪[F], Irreducible ϖ → nrm (ϖ : F) = ((Nat.card 𝓀[F] : ℕ) : ℝ)⁻¹
def IsTame (μ : Fˣ →* ℂˣ) : Prop :=
  ∀ (u : Fˣ) (m : 𝒪[F]), m ∈ 𝓂[F] → (u : F) = 1 + (m : F) → μ u = 1
def IsUnramified (η : Fˣ →* ℂˣ) : Prop :=
  ∀ u : Fˣ, (u : F) ∈ 𝒪[F] → ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] → η u = 1
end Local
def LocalIntegralSingleBlock : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (r t : ℕ)
    (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (nrm : AbsoluteValue F ℝ), IsNormalisedAbs nrm →
  ∀ (μ η : Fˣ →* ℂˣ), IsTame μ → IsUnramified η → (∀ u, ‖((η u : ℂˣ) : ℂ)‖ = 1) →
  ∀ (P : Subgroup (GL (Fin r) F)) (hKP : congSub 𝒪[F] (ϖ : F) r ≤ P), P ≤ GLint 𝒪[F] r →
  ∀ (lam : P →* ℂˣ),
    (∀ (k : GL (Fin r) F) (hk : k ∈ congSub 𝒪[F] (ϖ : F) r), lam ⟨k, hKP hk⟩ = 1) →
  ∀ (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddHaarMeasure],
    ν (intMatrices 𝒪[F] (Fin r ⊕ Fin t) (Fin r)) = 1 →
    let q : ℕ := Nat.card 𝓀[F]
    let Φ : Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ := datum t 𝒪[F] (ϖ : F) μ P lam
    let J : Subgroup (GL (Fin r ⊕ Fin t) F) := targetLevel t 𝒪[F] (ϖ : F) P
    let normSq : ℂ := weilIP ν Φ Φ

    (IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
      (J : Set (GL (Fin r ⊕ Fin t) F)) = targetSet t 𝒪[F] (ϖ : F) P) ∧

    ((∀ g : GL (Fin r) F, g ∉ P → weilIP ν (weilPair μ η nrm g 1 Φ) Φ = 0) ∧
      ∀ g : P, weilIP ν (weilPair μ η nrm (g : GL (Fin r) F) 1 Φ) Φ =
        ((lam g : ℂˣ) : ℂ) * normSq) ∧

    ((∀ (ν₁ : Measure (Matrix (Fin r) (Fin r) F)) [ν₁.IsAddHaarMeasure]
        (ν₂ : Measure (Matrix (Fin t) (Fin r) F)) [ν₂.IsAddHaarMeasure],
        ν₁ (intMat 𝒪[F] r r) = 1 → ν₂ (intMat 𝒪[F] t r) = 1 →
        normSq = (((ν₁ (Jset P)).toReal * (ν₂ (IIset 𝒪[F] (ϖ : F))).toReal : ℝ) : ℂ)) ∧
      normSq = (((Nat.card (residueImage P) : ℝ) * ((q : ℝ) ^ (r ^ 2))⁻¹ *
        ((q : ℝ) ^ (r * t))⁻¹ : ℝ) : ℂ)) ∧

    (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (σ : Representation ℂ (GL (Fin r) F) V),
        (∀ g a b, inner ℂ (σ g a) (σ g b) = inner ℂ a b) →
      ∀ (x₁ x₂ : V), (∀ k : P, σ (k : GL (Fin r) F) x₁ = ((lam k : ℂˣ) : ℂ) • x₁) →
      ∀ (dg : Measure (GL (Fin r) F)) [dg.IsHaarMeasure],
        Integrable (fun g : GL (Fin r) F =>
          weilIP ν (weilPair μ η nrm g 1 Φ) Φ * conj (inner ℂ x₂ (σ g x₁))) dg ∧
        localZ dg ν (μ * η) nrm Φ Φ (fun g => inner ℂ x₂ (σ g x₁)) =
          (((dg (P : Set (GL (Fin r) F))).toReal : ℝ) : ℂ) * normSq * conj (inner ℂ x₂ x₁) ∧
        (dg (P : Set (GL (Fin r) F)) = 1 →
          localZ dg ν (μ * η) nrm Φ Φ (fun g => inner ℂ x₂ (σ g x₁)) =
            normSq * conj (inner ℂ x₂ x₁))) ∧

    (∀ h ∈ J, ∃ k : P,
      ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F).toBlocks₁₁ ∧
      weilPair μ η nrm 1 h Φ =
        (((blockChar μ P lam k * μ (GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) • Φ) ∧

    ((J.relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) : ℂ) * normSq =
        ((∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℝ) ^ i)⁻¹) : ℝ) : ℂ) ∧
      (J.relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) : ℂ) * normSq = ((1 / dFactor q r t : ℝ) : ℂ))
end GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL


