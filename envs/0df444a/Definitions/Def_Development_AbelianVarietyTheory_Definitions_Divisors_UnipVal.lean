-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:27.069544+00:00
-- url     : https://prove2.me/theorems/347ea7a5-d37a-44a0-8e6d-040a33a7bd1f
-- title:
--   Unip Val
-- statement:
--   Definitions and structural lemmas for Unip Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/UnipVal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped Topology Classical
namespace GlobalTheory.KSp
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitUnitary
section Abstract
structure Good (X : Type) [AddCommGroup X] [TopologicalSpace X] : Prop where
  grp : IsTopologicalAddGroup X
  t2 : T2Space X
  lc : LocallyCompactSpace X
  sc : SecondCountableTopology X
  large : ∀ K : Set X, IsCompact K → ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ K ⊆ L
  small : ∀ U ∈ 𝓝 (0 : X), ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ (L : Set X) ⊆ U
variable {X : Type} [AddCommGroup X] [TopologicalSpace X]
structure IsPair (e : X → X → ℂ) : Prop where
  add : ∀ x x' y, e (x + x') y = e x y * e x' y
  symm : ∀ x y, e x y = e y x
  norm : ∀ x y, ‖e x y‖ = 1
  lc : IsLocallyConstant fun p : X × X => e p.1 p.2
  small : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ K, e x y = 1) → y ∈ U
  big : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ U, e x y = 1) → y ∈ K
variable [MeasurableSpace X]
def four (μ : Measure X) (e : X → X → ℂ) (φ : X → ℂ) : X → ℂ := fun x => ∫ y, e x y * φ y ∂μ
def HasGauss (μ : Measure X) (f : X → ℂ) (γ : ℂ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ K ⊆ L ∧
    ∫ x in (L : Set X), f x ∂μ = γ
end Abstract
section Group
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
def sgn (E : Type) [Field E] [Algebra F E] (t : Fˣ) : ℂ :=
  if t ∈ (Units.map (Algebra.norm F : E →* F)).range then 1 else -1
def pr (Q : Matrix α α E) (x y : Matrix α ν E) : F := form c Q (fromCols x 0) (fromCols 0 y)
def weyl (ν : Type) [Fintype ν] [DecidableEq ν] : UG c (stdJ ν E) :=
  ⟨⟨stdJ ν E, -stdJ ν E, by rw [Matrix.mul_neg, stdJ_mul_stdJ, neg_neg], by rw [Matrix.neg_mul, stdJ_mul_stdJ, neg_neg]⟩, by
    rw [mem_UG_iff]
    have h : ((stdJ ν E).map c)ᵀ = -stdJ ν E := by
      ext (i | i) (j | j) <;> simp [stdJ, one_apply, eq_comm]
    change stdJ ν E * stdJ ν E * ((stdJ ν E).map c)ᵀ = stdJ ν E
    rw [h, stdJ_mul_stdJ]
    simp⟩
def unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : UG c (stdJ ν E) :=
  ⟨⟨fromBlocks 1 b 0 1, fromBlocks 1 (-b) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
    rw [mem_UG_iff]
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
    simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, hb]⟩
abbrev mat (g : UG c (stdJ ν E)) : Matrix (ν ⊕ ν) (ν ⊕ ν) E := ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)
theorem mat_inv (g : UG c (stdJ ν E)) : mat c g⁻¹ = -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) := by
  have hg : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c (g : GL (ν ⊕ ν) E)).1 g.2
  have hr : mat c g * -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) = 1 := by
    rw [Matrix.mul_neg, ← mul_assoc, ← mul_assoc, hg, stdJ_mul_stdJ, neg_neg]
  have hl : mat c g⁻¹ * mat c g = 1 := by
    simp [mat]
  calc mat c g⁻¹ = mat c g⁻¹ * (mat c g * -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E)) := by
        rw [hr, mul_one]
    _ = -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) := by
        rw [← mul_assoc, hl, one_mul]
def sieg (ν : Type) [Fintype ν] [DecidableEq ν] : Subgroup (UG c (stdJ ν E)) where
  carrier := {g | (mat c g).toBlocks₂₁ = 0}
  one_mem' := by
    ext i j
    simp [mat, toBlocks₂₁]
  mul_mem' := by
    intro g h hg hh
    change (mat c g * mat c h).toBlocks₂₁ = 0
    rw [← fromBlocks_toBlocks (mat c g), ← fromBlocks_toBlocks (mat c h), fromBlocks_multiply, toBlocks_fromBlocks₂₁,
      show (mat c g).toBlocks₂₁ = 0 from hg, show (mat c h).toBlocks₂₁ = 0 from hh]
    simp
  inv_mem' := by
    intro g hg
    change (mat c g⁻¹).toBlocks₂₁ = 0
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    rw [mat_inv, ← fromBlocks_toBlocks (mat c g), show (mat c g).toBlocks₂₁ = 0 from hg]
    simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, h0]
def InCell (g : UG c (stdJ ν E)) : Prop := ∃ p ∈ sieg c ν, ∃ q ∈ sieg c ν, g = p * weyl c ν * q
end Group
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
def sc (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : E) : ℂ :=
  if h : z = 0 then 0 else (χ (Units.mk0 z h) : ℂ) *
    ((nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z h)) ^ ((m : ℝ) / 2) : ℝ) : ℂ)
def parFun (ψ : AddChar F ℂ) (χ : Eˣ →* Circle) (Q : Matrix α α E) (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  fun x => sc F χ (Fintype.card α) g.toBlocks₁₁.det *
    (ψ (2⁻¹ * pr c Q (x * g.toBlocks₁₁) (x * g.toBlocks₁₂)) * φ (x * g.toBlocks₁₁))
def fou [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ) (Q : Matrix α α E)
    (μ : Measure (Matrix α ν E)) (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  four μ (fun x y => ψ (pr c Q x y)) φ
structure IsKW [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ) (χ : Eˣ →* Circle)
    (Q : Matrix α α E) (μ : Measure (Matrix α ν E)) (κ : ℂ)
    (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))) : Prop where
  par : ∀ p ∈ sieg c ν, ∀ φ : SB (Matrix α ν E), (ω p φ : Matrix α ν E → ℂ) = parFun c ψ χ Q (mat c p) φ
  wey : ∀ φ : SB (Matrix α ν E), (ω (weyl c ν) φ : Matrix α ν E → ℂ) = κ • fou c ψ Q μ φ
end Local
end GlobalTheory.KSp
end


