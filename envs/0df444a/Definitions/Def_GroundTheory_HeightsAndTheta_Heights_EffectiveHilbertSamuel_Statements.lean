-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:58.248565+00:00
-- url     : https://prove2.me/theorems/ba00a9bb-3417-47b2-94fe-199310200872
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.EffectiveHS
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal
noncomputable section
def dbarC {D : ℕ} (f : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ) (l : Fin D) : ℂ :=
  (fderiv ℝ f y (Pi.single l 1) + Complex.I * fderiv ℝ f y (Pi.single l Complex.I)) / 2
structure EmbDatum (D : ℕ) where

  U : Type
  [top : TopologicalSpace U]
  [t2 : T2Space U]

  A : FinHolAtlas D U
  cover : IsAlgCover A

  L : HolLineBundle A

  L₂ : HolLineBundle A

  N : ℕ

  N₂ : ℕ

  e : Fin N → Fin A.n → U → ℂ

  e₂ : Fin N₂ → Fin A.n → U → ℂ
  e_mem : ∀ i, e i ∈ L.sections 1
  e₂_mem : ∀ i, e₂ i ∈ L₂.sections 1
  gen : NoCommonZero A e
  gen₂ : NoCommonZero A e₂
attribute [instance] EmbDatum.top EmbDatum.t2
namespace EmbDatum
variable {D : ℕ} (X : EmbDatum D)
def wt (m : ℕ) (k : Fin X.A.n) (x : X.U) : ℝ :=
  fsWeight X.e₂ k x + (m : ℝ) * fsWeight X.e k x
end EmbDatum
structure ZeroDatum {D : ℕ} (X : EmbDatum D) where

  c : Fin D → Fin X.N → ℂ
  finite : (zeroSet X.A fun i => lin X.e (c i)).Finite
  nondeg : IsNondeg X.A fun i => lin X.e (c i)
  fl : FLBound X.A X.e fun i => lin X.e (c i)
namespace ZeroDatum
variable {D : ℕ} {X : EmbDatum D} (Z : ZeroDatum X)
def s : Fin D → Fin X.A.n → X.U → ℂ := fun i => lin X.e (Z.c i)
def S : Set X.U := zeroSet X.A Z.s
end ZeroDatum
structure SpaceDatum {D : ℕ} (X : EmbDatum D) (T : ℕ) where

  β : ℝ
  one_le_β : 1 ≤ β

  φA : TwistWeight X.A X.L₂ X.L D
  φA_le : ∀ j, ∀ x ∈ (X.A.chart j).source,
    Real.exp (-φA.φ j x) ≤ β ^ (D + 1) * Real.exp (-X.wt D j x)

  V : ℕ → Submodule ℂ (Fin X.A.n → X.U → ℂ)
  V_le : ∀ j, V j ≤ topSections X.A X.L₂ X.L (D + j)

  normT : (Fin X.A.n → X.U → ℂ) → ℝ
  sections_zero_mem_natural : ∀ F ∈ V 0, F ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) 0
  sections_top_mem_natural : ∀ F ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) D, F ∈ V D
  H1 : ∀ j < T, ∀ i, ∀ F ∈ V j, X.e i * F ∈ V (j + 1)
  H2 : ∀ F ∈ V T, ENNReal.ofReal (normT F ^ 2) ≤
    ENNReal.ofReal (β ^ (D + T + 1)) * topNormSq X.A (X.wt (D + T)) F
def ResOnto {D T : ℕ} {X : EmbDatum D} (Z : ZeroDatum X) (Y : SpaceDatum X T) : Prop :=
  ∀ g : X.U → ℂ, ∃ m ∈ Y.V 0, ∀ x ∈ Z.S, res X.A Z.s m x = g x
def HormanderOnU.Statement : Prop :=
  ∀ (D : ℕ) (U : Type) [TopologicalSpace U] [T2Space U] (A : FinHolAtlas D U), IsAlgCover A →
  ∀ (M : HolLineBundle A),
    (∃ (N : ℕ) (fr : Fin N → Fin A.n → U → ℂ), (∀ i, fr i ∈ M.sections 1) ∧ NoCommonZero A fr) →
  ∀ (ψ : Fin A.n → U → ℝ) (F₀ : Fin A.n → U → ℂ) (h : Fin A.n → U → ℝ),
    (∀ j, A.SmoothOn (A.chart j).source (ψ j)) →
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
      ψ j x = ψ k x + Real.log (‖M.g j k x‖ ^ 2)) →
    (∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (ψ j ∘ (A.chart j).symm) y w) →
    (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F₀ j ∘ (A.chart j).symm) (A.chart j).target) →
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
      F₀ j x = jac A j k x * M.g j k x * F₀ k x) →
    (∀ j, ∀ x ∉ (A.chart j).source, F₀ j x = 0) →
    (∀ j, ∀ y ∈ (A.chart j).target, ∀ ξ : Fin D → ℂ,
      ‖∑ l, dbarC (F₀ j ∘ (A.chart j).symm) y l * starRingEnd ℂ (ξ l)‖ ^ 2 ≤
        h j ((A.chart j).symm y) * levi (ψ j ∘ (A.chart j).symm) y ξ) →
    ∃ F ∈ topSections A M M 0, topNormSq A ψ (F₀ - F) ≤
      chartIntegral A fun j x => ENNReal.ofReal (2 ^ D * h j x * Real.exp (-ψ j x))
def ZHolo {M : Type} [TopologicalSpace M] {n : ℕ} (z : M → Fin n → ℂ) (f : M → ℂ) : Prop :=
  ∀ φ : OpenPartialHomeomorph M (Fin n → ℂ), Set.EqOn φ z φ.source →
    AnalyticOnNhd ℂ (f ∘ φ.symm) φ.target
def ZSmoothPsh {M : Type} [TopologicalSpace M] {n : ℕ} (z : M → Fin n → ℂ) (ψ : M → ℝ) : Prop :=
  ∀ φ : OpenPartialHomeomorph M (Fin n → ℂ), Set.EqOn φ z φ.source →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ ∘ φ.symm) φ.target ∧
      ∀ y ∈ φ.target, ∀ w : Fin n → ℂ, 0 ≤ levi (ψ ∘ φ.symm) y w
def zIntegral {M : Type} {n : ℕ} (z : M → Fin n → ℂ) (f : M → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y, ∑' x : z ⁻¹' {y}, f x
def SkodaL2Estimate.Statement : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    (z : M → Fin n → ℂ), IsLocalHomeomorph z →
    (∃ e₀ : M → ℝ, ZSmoothPsh z e₀ ∧ ∀ a : ℝ, IsCompact {x | e₀ x ≤ a}) →
    ∀ (p : ℕ) (g : Fin p → M → ℂ) (φ₀ : M → ℝ) (t : ℝ) (f : M → ℂ),
      2 ≤ p → (∀ i, ZHolo z (g i)) → (∀ x, ∃ i, g i x ≠ 0) → ZSmoothPsh z φ₀ → (p : ℝ) - 1 < t →
      ZHolo z f →
      zIntegral z (fun x => ENNReal.ofReal
        (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) * Real.exp (-φ₀ x))) < ⊤ →
      ∃ h : Fin p → M → ℂ, (∀ i, ZHolo z (h i)) ∧ f = ∑ i, g i * h i ∧
        zIntegral z (fun x => ENNReal.ofReal
          ((∑ i, ‖h i x‖ ^ 2) * (∑ i, ‖g i x‖ ^ 2) ^ (-t) * Real.exp (-φ₀ x))) ≤
        ENNReal.ofReal (t / (t - p + 1)) * zIntegral z (fun x => ENNReal.ofReal
          (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) * Real.exp (-φ₀ x)))
def ExtensionLemma.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (j : ℕ), 1 ≤ D → 2 ≤ j →
    ∀ g : X.U → ℂ, ∃ F ∈ topSections X.A X.L₂ X.L (D + j),
      (∀ x ∈ Z.S, res X.A Z.s F x = g x) ∧
      topNormSq X.A (X.wt (D + j)) F ≤
        ENNReal.ofReal (140 * cD D * rSq Z.c ^ D * sNormSq X.A Z.S (X.wt j) g)
def DivisionB.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D), 1 ≤ D → D ≤ T →
    ∀ F ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) T, IsFil X.A Z.s F (T - D) →
      ∃ h : (Fin D → ℕ) → Fin X.A.n → X.U → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple D (T - D), h α ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) D) ∧
        F = ∑ α ∈ Finset.Nat.antidiagonalTuple D (T - D), sPow Z.s α * h α
def VppNat.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (Y : SpaceDatum X T), 1 ≤ D → D + 1 ≤ T →
    ∀ F ∈ Vpp X.e Z.s (Y.V 0) (Y.V D) T, ∃ G ∈ Vnat X.A X.L₂ X.L Y.φA.φ (fsWeight X.e) T,
      ∃ p ∈ Pspace Z.s (Y.V D) T, F = G + p
def VppFil.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (Y : SpaceDatum X T), 1 ≤ D → D + 1 ≤ T →
    ∀ F ∈ Vpp X.e Z.s (Y.V 0) (Y.V D) T, IsFil X.A Z.s F (T - D) ↔ F ∈ Pspace Z.s (Y.V D) T
def VppLe.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (Y : SpaceDatum X T), 1 ≤ D → D + 1 ≤ T →
    Vpp X.e Z.s (Y.V 0) (Y.V D) T ≤ Y.V T
def SymKer.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (Y : SpaceDatum X T), 1 ≤ D → D + 1 ≤ T →
    ∀ (a : ℕ), ∀ F ∈ Vpp X.e Z.s (Y.V 0) (Y.V D) T, IsFil X.A Z.s F a →
      (SymEq X.A Z.s F a 0 ↔ IsFil X.A Z.s F (a + 1))
def SymOnto.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (Y : SpaceDatum X T), 1 ≤ D → D + 1 ≤ T →
    ResOnto Z Y → ∀ a ≤ T - D - 1, ∀ g : (Fin D → ℕ) → X.U → ℂ,
      ∃ F ∈ Vpp X.e Z.s (Y.V 0) (Y.V D) T, IsFil X.A Z.s F a ∧ SymEq X.A Z.s F a g
def SymbolExtensionProperty.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (Y : SpaceDatum X T), 1 ≤ D → D + 1 ≤ T →
    ResOnto Z Y → ∀ a ≤ T - D - 1, ∀ g : (Fin D → ℕ) → X.U → ℂ,
      ∃ F ∈ Vpp X.e Z.s (Y.V 0) (Y.V D) T, F ∈ Y.V T ∧ IsFil X.A Z.s F a ∧ SymEq X.A Z.s F a g ∧
        Y.normT F ≤ Real.sqrt (Y.β ^ (T + D + 1) * 140 * cD D * ((a + D - 1).choose (D - 1) : ℕ) *
            rSq Z.c ^ D) * Real.sqrt (wtNormSq X.A Z.c Z.S (X.wt (T - a)) a g)
def ConstantAbsorbed.Statement : Prop :=
  ∀ (D : ℕ) (ρ : ℝ), 1 ≤ D → 2 ^ 26 ≤ ρ →
    (1 / 2) * (Real.log 280 + D * Real.log (2 * Real.pi)) ≤ 3.8 * D ∧
      3.8 * (D : ℝ) ≤ (D / 2) * Real.log ρ
end
end GroundTheory.Heights₂.Heights.EffectiveHS


