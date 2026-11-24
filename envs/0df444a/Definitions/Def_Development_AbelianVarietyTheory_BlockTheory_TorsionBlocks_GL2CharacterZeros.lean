-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:51.793852+00:00
-- url     : https://prove2.me/theorems/1bc78917-8b7f-4cf4-b25a-0c28090bd8a1
-- title:
--   GL2 Character Zeros
-- statement:
--   Definitions and structural lemmas for GL2 Character Zeros, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/GL2CharacterZeros.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
section Defs
variable {k : Type} [Field k]
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
def uMat (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) :
    Matrix (ρ ⊕ v ⊕ ρ) (ρ ⊕ v ⊕ ρ) k :=
  fromBlocks 1 (fromCols ν' b) 0 (fromBlocks 1 ν 0 1)
theorem det_uMat (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) :
    (uMat ν ν' b).det = 1 := by
  simp [uMat, det_fromBlocks_zero₂₁]
def uGL (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) : GL (ρ ⊕ v ⊕ ρ) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (uMat ν ν' b) (by rw [det_uMat]; exact one_ne_zero)
def nGL (ν : Matrix v ρ k) (ν' : Matrix ρ v k) : GL (ρ ⊕ v ⊕ ρ) k := uGL ν ν' 0
def zGL (v : Type) [Fintype v] [DecidableEq v] (b : Matrix ρ ρ k) : GL (ρ ⊕ v ⊕ ρ) k :=
  uGL (0 : Matrix v ρ k) 0 b
def glueCols (ξ : Matrix W ρ k) (x₀ : Matrix W v k) (c : Matrix W ρ k) : Matrix W (ρ ⊕ v ⊕ ρ) k :=
  fromCols ξ (fromCols x₀ c)
def glueRows {u : Type} (r : Matrix τ u k) (m : Matrix w u k) (s : Matrix τ u k) :
    Matrix (τ ⊕ w ⊕ τ) u k :=
  fromRows r (fromRows m s)
def glueFun {u : Type} (a : Matrix u τ k) (m : Matrix u w k) (c : Matrix u τ k) :
    Matrix u (τ ⊕ w ⊕ τ) k :=
  fromCols a (fromCols m c)
abbrev Mix₁ (k ρ v W : Type) := Matrix W ρ k × Matrix ρ W k × Matrix W v k
abbrev Mix₂ (k ρ v τ w : Type) :=
  Matrix (τ ⊕ w ⊕ τ) ρ k × Matrix ρ (τ ⊕ w ⊕ τ) k × Matrix τ v k × Matrix v τ k × Matrix w v k
def chr (ψ : AddChar k Circle) (s : ℤˣ) (t : k) : ℂ := (ψ (((s : ℤ) : k) * t) : ℂ)
variable [MeasurableSpace k]
def four₁ [Fintype W] (ψ : AddChar k Circle) (m : Measure k) (s : ℤˣ)
    (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) : Mix₁ k ρ v W → ℂ := fun z =>
  ∫ c, Φ (glueCols z.1 z.2.2 c) * chr ψ (-s) (trace (z.2.1 * c)) ∂(volM m W ρ)
def four₂ [Fintype τ] (ψ : AddChar k Circle) (m : Measure k) (s : ℤˣ)
    (F : Mix₁ k ρ v (τ ⊕ w ⊕ τ) → ℂ) : Mix₂ k ρ v τ w → ℂ := fun z =>
  ∫ r, F (z.1, z.2.1, glueRows r z.2.2.2.2 z.2.2.1) * chr ψ (-s) (trace (r * z.2.2.2.1)) ∂(volM m τ v)
def mixed [Fintype τ] [Fintype w] (ψ : AddChar k Circle) (m : Measure k) (s₁ s₂ : ℤˣ)
    (Φ : Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k → ℂ) : Mix₂ k ρ v τ w → ℂ :=
  four₂ ψ m s₂ (four₁ ψ m s₁ Φ)
end Defs
section Clauses
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable (ρ v τ w : Type) [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w]
def ModelsIso : Prop :=
  Set.BijOn (four₁ ψ m s₁) {Φ | Φ ∈ SB (Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k)}
      {F | F ∈ SB (Mix₁ k ρ v (τ ⊕ w ⊕ τ))} ∧
    Set.BijOn (four₂ ψ m s₂) {F | F ∈ SB (Mix₁ k ρ v (τ ⊕ w ⊕ τ))} {F | F ∈ SB (Mix₂ k ρ v τ w)}
def FirstStepN : Prop :=
  ∀ Φ ∈ SB (Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k), ∀ (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (ξ : Matrix (τ ⊕ w ⊕ τ) ρ k) (η : Matrix ρ (τ ⊕ w ⊕ τ) k) (x₀ : Matrix (τ ⊕ w ⊕ τ) v k),
    four₁ ψ m s₁ (om μ (nGL ν ν') 1 Φ) (ξ, η, x₀) =
      chr ψ s₁ (trace (η * (x₀ * ν))) * four₁ ψ m s₁ Φ (ξ, η, x₀ + ξ * ν')
def AtBasePointN : Prop :=
  ∀ Φ ∈ SB (Matrix (ρ ⊕ w ⊕ ρ) (ρ ⊕ v ⊕ ρ) k), ∀ (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (ys : Matrix ρ v k) (x₀₀ : Matrix w v k),
    (∀ r : Matrix ρ v k,
      four₁ ψ m s₁ (om μ (nGL ν ν') 1 Φ) (glueRows 1 0 0, glueFun 0 0 1, glueRows r x₀₀ ys) =
        chr ψ s₁ (trace (ys * ν)) *
          four₁ ψ m s₁ Φ (glueRows 1 0 0, glueFun 0 0 1, glueRows (r + ν') x₀₀ ys)) ∧
    ∀ y : Matrix v ρ k,
      mixed ψ m s₁ s₂ (om μ (nGL ν ν') 1 Φ) (glueRows 1 0 0, glueFun 0 0 1, ys, y, x₀₀) =
        chr ψ s₁ (trace (ys * ν)) * chr ψ s₂ (trace (ν' * y)) *
          mixed ψ m s₁ s₂ Φ (glueRows 1 0 0, glueFun 0 0 1, ys, y, x₀₀)
def SecondStepN : Prop :=
  ∀ Φ ∈ SB (Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k), ∀ (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (ξ' : Matrix τ ρ k) (ξ₀ : Matrix w ρ k) (η₀ : Matrix ρ w k) (ηd : Matrix ρ τ k)
    (ys : Matrix τ v k) (y : Matrix v τ k) (x₀₀ : Matrix w v k),
    mixed ψ m s₁ s₂ (om μ (nGL ν ν') 1 Φ) (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, ys, y, x₀₀) =
      chr ψ s₁ (trace ((η₀ * x₀₀ + ηd * ys) * ν)) * chr ψ s₂ (trace (ξ' * ν' * y)) *
        mixed ψ m s₁ s₂ Φ (glueRows ξ' ξ₀ 0, glueFun 0 η₀ ηd, ys, y, x₀₀ + ξ₀ * ν')
def PicksBasePoint : Prop :=
  ∀ (p₀ : ρ) (z : v) (ys : Matrix ρ v k) (y : Matrix v ρ k),
    (∀ (ν : Matrix v ρ k) (ν' : Matrix ρ v k),
        chr ψ s₁ (trace (ys * ν)) * chr ψ s₂ (trace (ν' * y)) =
          chr ψ s₁ (ν z p₀) * chr ψ s₂ (ν' p₀ z)) ↔
      ys = Matrix.single p₀ z 1 ∧ y = Matrix.single z p₀ 1
def CentreAction : Prop :=
  ∀ Φ ∈ SB (Matrix (τ ⊕ w ⊕ τ) (ρ ⊕ v ⊕ ρ) k), ∀ (b : Matrix ρ ρ k)
    (ξ : Matrix (τ ⊕ w ⊕ τ) ρ k) (η : Matrix ρ (τ ⊕ w ⊕ τ) k),
    (∀ x₀ : Matrix (τ ⊕ w ⊕ τ) v k,
      four₁ ψ m s₁ (om μ (zGL v b) 1 Φ) (ξ, η, x₀) =
        chr ψ s₁ (∑ p, ∑ q, (η * ξ) p q * b q p) * four₁ ψ m s₁ Φ (ξ, η, x₀)) ∧
    ∀ (ys : Matrix τ v k) (y : Matrix v τ k) (x₀₀ : Matrix w v k),
      mixed ψ m s₁ s₂ (om μ (zGL v b) 1 Φ) (ξ, η, ys, y, x₀₀) =
        chr ψ s₁ (∑ p, ∑ q, (η * ξ) p q * b q p) * mixed ψ m s₁ s₂ Φ (ξ, η, ys, y, x₀₀)
end Clauses
def SplitDictionary : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (m : Measure k), m.IsAddHaarMeasure →
    ∀ (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
      (ρ v τ w : Type) [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
      [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w],
      ModelsIso ψ m s₁ s₂ ρ v τ w ∧ FirstStepN ψ m μ s₁ ρ v τ w ∧ AtBasePointN ψ m μ s₁ s₂ ρ v w ∧
        SecondStepN ψ m μ s₁ s₂ ρ v τ w ∧ PicksBasePoint ψ s₁ s₂ ρ v ∧ CentreAction ψ m μ s₁ s₂ ρ v τ w
section Basic₂
variable {k : Type} [Field k]
variable {ρ v W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining


