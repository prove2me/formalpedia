-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:20.724999+00:00
-- url     : https://prove2.me/theorems/738ed451-5dbb-4dbd-b9ba-1c30c180fadc
-- title:
--   Kernel L2 Rows Columns
-- statement:
--   Definitions and structural lemmas for Kernel L2 Rows Columns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/ThetaCellCovers/KernelL2RowsColumns.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace PositivityTheory.Rg.BcB.E1
section Basic
variable {G : Type} [Group G]
def ker (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℂ := ∑ᶠ γ : Γ, φ (x⁻¹ * (γ : G) * y)
def cnt (Γ : Subgroup G) (Ω : Set G) (x : G) : ℝ≥0∞ := ∑' γ : Γ, Ω.indicator 1 (x⁻¹ * (γ : G) * x)
def adj (φ : G → ℂ) : G → ℂ := fun y => starRingEnd ℂ (φ y⁻¹)
def cv [MeasurableSpace G] (μ : Measure G) (φ₁ φ₂ : G → ℂ) : G → ℂ := fun y => ∫ z, φ₁ z * φ₂ (z⁻¹ * y) ∂μ
def Tst [TopologicalSpace G] (φ : G → ℂ) : Prop := Continuous φ ∧ HasCompactSupport φ
end Basic
structure Ctx : Type 1 where
  G : Type
  [grp : Group G]
  [top : TopologicalSpace G]
  [tg : IsTopologicalGroup G]
  [lc : LocallyCompactSpace G]
  [sc : SecondCountableTopology G]
  [t2 : T2Space G]
  [ms : MeasurableSpace G]
  [bs : BorelSpace G]
  μ : Measure G
  [haar : μ.IsHaarMeasure]
  Γ : Subgroup G
  [cn : Countable Γ]
  proper : ∀ C : Set G, IsCompact C → {γ : Γ | (γ : G) ∈ C}.Finite
  F : Set G
  fd : IsFundamentalDomain Γ F μ
attribute [instance] Ctx.grp Ctx.top Ctx.tg Ctx.lc Ctx.sc Ctx.t2 Ctx.ms Ctx.bs Ctx.haar Ctx.cn
def Ctx.line : Ctx :=
  letI : MeasurableSpace (Multiplicative ℝ) := borel _
  haveI : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩
  haveI : SecondCountableTopology (Multiplicative ℝ) := inferInstanceAs (SecondCountableTopology ℝ)
  { G := Multiplicative ℝ
    μ := Measure.haar
    Γ := ⊥
    proper := fun _ _ => Set.toFinite _
    F := Set.univ
    fd := .mk' MeasurableSet.univ.nullMeasurableSet fun _ => ⟨1, trivial, fun _ _ => Subsingleton.elim _ _⟩ }
def Ctx.ν (X : Ctx) : Measure X.G := X.μ.restrict X.F
abbrev Ctx.Hs (X : Ctx) (ι : Type) : Type := PiLp 2 fun _ : ι => Lp ℂ 2 X.ν
def Ctx.IsOp (X : Ctx) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (T : X.Hs ι →L[ℂ] X.Hs ι) : Prop :=
  ∀ f i, (T f i : X.G → ℂ) =ᵐ[X.ν] fun x => ∑ j, ∫ y, ker X.Γ (Φ i j) x y * (f j : X.G → ℂ) y ∂X.ν
def KerBasic : Prop := ∀ (X : Ctx) (φ : X.G → ℂ), Tst φ →
  (∀ x y, (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)).Finite) ∧
  Continuous (Function.uncurry (ker X.Γ φ)) ∧
  (∀ γ ∈ X.Γ, ∀ x y, ker X.Γ φ (γ * x) y = ker X.Γ φ x y ∧ ker X.Γ φ x (γ * y) = ker X.Γ φ x y) ∧
  Tst (adj φ) ∧ (∀ x y, ker X.Γ (adj φ) x y = starRingEnd ℂ (ker X.Γ φ y x)) ∧
  ∀ x y, ‖ker X.Γ φ x y‖ₑ ≤ ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ
def KerLin : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (φ : ι → X.G → ℂ) (c : ι → ℂ), (∀ i, Tst (φ i)) →
  Tst (fun y => ∑ i, φ i y * c i) ∧ ∀ x y, ker X.Γ (fun z => ∑ i, φ i z * c i) x y = ∑ i, ker X.Γ (φ i) x y * c i
def CntBasic : Prop := ∀ X : Ctx,
  (∀ Ω : Set X.G, IsCompact Ω → ∀ x, cnt X.Γ Ω x ≠ ⊤) ∧
  (∀ (Ω : Set X.G), ∀ γ ∈ X.Γ, ∀ x, cnt X.Γ Ω (γ * x) = cnt X.Γ Ω x) ∧
  (∀ Ω Ω' : Set X.G, Ω ⊆ Ω' → ∀ x, cnt X.Γ Ω x ≤ cnt X.Γ Ω' x) ∧
  ∀ (φ : X.G → ℂ) (B : ℝ), Tst φ → (∀ z, ‖φ z‖ ≤ B) → ∀ x, ‖ker X.Γ φ x x‖ₑ ≤ ENNReal.ofReal B * cnt X.Γ (tsupport φ) x
def RowInt : Prop := ∀ (X : Ctx) (φ : X.G → ℂ), Tst φ → ∃ A : ℝ≥0∞, A ≠ ⊤ ∧
  (∀ x, ∫⁻ y, ‖ker X.Γ φ x y‖ₑ ∂X.ν ≤ A) ∧ ∀ y, ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ∂X.ν ≤ A
def ColSq : Prop := ∀ (X : Ctx) (φ : X.G → ℂ) (B : ℝ) (Ω : Set X.G), Tst φ → (∀ z, ‖φ z‖ ≤ B) → IsCompact Ω →
  Function.support φ ⊆ Ω → ∀ y,
    ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ^ 2 ∂X.ν ≤ ENNReal.ofReal B ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y
def KernelL2RowsColumns : Prop := ∀ (X : Ctx) (φ : X.G → ℂ), Tst φ →
  (∀ y, MemLp (fun x => ker X.Γ φ x y) 2 X.ν) ∧ ∀ x, MemLp (fun y => ker X.Γ φ x y) 2 X.ν
def SchurL : Prop := ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) [SFinite ν] (k : α → α → ℝ≥0∞) (A : ℝ≥0∞)
  (f : α → ℝ≥0∞), Measurable (Function.uncurry k) → AEMeasurable f ν → (∀ x, ∫⁻ y, k x y ∂ν ≤ A) →
  (∀ y, ∫⁻ x, k x y ∂ν ≤ A) → ∫⁻ x, (∫⁻ y, k x y * f y ∂ν) ^ 2 ∂ν ≤ A ^ 2 * ∫⁻ y, f y ^ 2 ∂ν
def SchurInt : Prop := ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) [SFinite ν] (k : α → α → ℂ) (A : ℝ≥0∞),
  Measurable (Function.uncurry k) → A ≠ ⊤ → (∀ x, ∫⁻ y, ‖k x y‖ₑ ∂ν ≤ A) → (∀ y, ∫⁻ x, ‖k x y‖ₑ ∂ν ≤ A) →
  ∀ g f : α → ℂ, MemLp g 2 ν → MemLp f 2 ν → Integrable (fun p : α × α => g p.1 * k p.1 p.2 * f p.2) (ν.prod ν)
def SchurOp : Prop := ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) [SFinite ν] (k : α → α → ℂ) (A : ℝ≥0∞),
  Measurable (Function.uncurry k) → A ≠ ⊤ → (∀ x, ∫⁻ y, ‖k x y‖ₑ ∂ν ≤ A) → (∀ y, ∫⁻ x, ‖k x y‖ₑ ∂ν ≤ A) →
  ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ∀ f, (T f : α → ℂ) =ᵐ[ν] fun x => ∫ y, k x y * (f : α → ℂ) y ∂ν
def CvTest : Prop := ∀ (X : Ctx) (φ ψ : X.G → ℂ), Tst φ → Tst ψ →
  Tst (cv X.μ φ ψ) ∧ Function.support (cv X.μ φ ψ) ⊆ tsupport φ * tsupport ψ ∧
  ∀ B : ℝ, (∀ z, ‖φ z‖ ≤ B) → ∀ y, ‖cv X.μ φ ψ y‖ ≤ B * ∫ z, ‖ψ z⁻¹‖ ∂X.μ
def KerMul : Prop := ∀ (X : Ctx) (φ ψ : X.G → ℂ), Tst φ → Tst ψ → ∀ x y,
  ∫ z, ker X.Γ φ x z * ker X.Γ ψ z y ∂X.ν = ker X.Γ (cv X.μ φ ψ) x y
def ApproxF : Prop := ∀ (X : Ctx) (φ : X.G → ℂ) (V : Set X.G) (ε : ℝ), Tst φ → V ∈ nhds (1 : X.G) → 0 < ε →
  ∃ ψ : X.G → ℂ, Tst ψ ∧ tsupport ψ ⊆ V ∧ ∫ z, ‖ψ z⁻¹‖ ∂X.μ = 1 ∧
    ∀ y, ‖cv X.μ (adj ψ) (cv X.μ φ ψ) y - φ y‖ ≤ ε
def Approx : Prop := ∀ (X : Ctx) (φ : X.G → ℂ) (V : Set X.G) (ε : ℝ) (x y : X.G), Tst φ → V ∈ nhds (1 : X.G) → 0 < ε →
  ∃ ψ : X.G → ℂ, Tst ψ ∧ tsupport ψ ⊆ V ∧ ∫ z, ‖ψ z⁻¹‖ ∂X.μ = 1 ∧
    ‖ker X.Γ (cv X.μ (adj ψ) (cv X.μ φ ψ)) x y - ker X.Γ φ x y‖ ≤ ε
def OpExA : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
  ∃! T, X.IsOp Φ T
def OpAdj : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (T : X.Hs ι →L[ℂ] X.Hs ι),
  (∀ i j, Tst (Φ i j)) → X.IsOp Φ T → X.IsOp (fun i j => adj (Φ j i)) (ContinuousLinearMap.adjoint T)
def OpMul : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ : X.Hs ι →L[ℂ] X.Hs ι),
  (∀ i j, Tst (Φ₁ i j)) → (∀ i j, Tst (Φ₂ i j)) → X.IsOp Φ₁ T₁ → X.IsOp Φ₂ T₂ →
  (∀ i j, Tst fun y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) ∧ X.IsOp (fun i j y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) (T₁ * T₂)
def Ctx.IsCol (X : Ctx) {ι : Type} (ψ : X.G → ℂ) (y : X.G) (j : ι) (u : X.Hs ι) : Prop :=
  ((u j : X.G → ℂ) =ᵐ[X.ν] fun x => ker X.Γ ψ x y) ∧ ∀ l, l ≠ j → u l = 0
def ColOp : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (ψ : X.G → ℂ), Tst ψ → (∀ y (j : ι), ∃ u, X.IsCol ψ y j u) ∧
  ∀ (Φ : Matrix ι ι (X.G → ℂ)) (T : X.Hs ι →L[ℂ] X.Hs ι), (∀ i j, Tst (Φ i j)) → X.IsOp Φ T → ∀ y j u, X.IsCol ψ y j u →
    (∀ i, (T u i : X.G → ℂ) =ᵐ[X.ν] fun x => ker X.Γ (cv X.μ (Φ i j) ψ) x y) ∧
    ∀ x i v, X.IsCol ψ x i v → inner ℂ v (T u) = ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y
def ColNorm : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (T : X.Hs ι →L[ℂ] X.Hs ι)
  (V : Set X.G), (∀ i j, Tst (Φ i j)) → X.IsOp Φ T → IsCompact V → ∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧
    ∀ ψ : X.G → ℂ, Tst ψ → tsupport ψ ⊆ V → ∫ z, ‖ψ z⁻¹‖ ∂X.μ = 1 → ∀ y j u, X.IsCol ψ y j u →
      ‖T u‖ₑ ^ 2 ≤ C * cnt X.Γ Ω y
def CellSum : Prop := ∀ (X : Ctx) (ι : Type) [Countable ι] (a : ι → X.G) (Ω₀ Ω : Set X.G) (w : X.G → ℝ≥0∞) (c : ι → ℝ≥0∞),
  IsCompact Ω₀ → IsCompact Ω → (∀ x, ∃ γ ∈ X.Γ, ∃ i, ∃ o ∈ Ω₀, γ * x = a i * o) → (∀ γ ∈ X.Γ, ∀ x, w (γ * x) = w x) →
  (∀ i, ∀ o ∈ Ω₀, w (a i * o) ≤ c i) → ∫⁻ x, w x * cnt X.Γ Ω x ∂X.ν ≤ X.μ (Ω₀ * Ω) * ∑' i, c i
def PtBound : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ : X.Hs ι →L[ℂ] X.Hs ι),
  (∀ i j, Tst (Φ₁ i j)) → (∀ i j, Tst (Φ₂ i j)) → X.IsOp Φ₁ T₁ → X.IsOp Φ₂ T₂ →
  ∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ (U : X.Hs ι →L[ℂ] X.Hs ι) (Φ : Matrix ι ι (X.G → ℂ)),
    (∀ i j, Tst (Φ i j)) → X.IsOp Φ (T₁ * U * T₂) → ∀ i j x y,
      ‖ker X.Γ (Φ i j) x y‖ₑ ≤ C * ‖U‖ₑ * (cnt X.Γ Ω x + cnt X.Γ Ω y)
end PositivityTheory.Rg.BcB.E1
end


