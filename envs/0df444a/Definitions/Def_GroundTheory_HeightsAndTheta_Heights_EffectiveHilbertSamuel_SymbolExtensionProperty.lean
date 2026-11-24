-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:41.170677+00:00
-- url     : https://prove2.me/theorems/b0228f64-2ee9-418c-9b0a-35ccecd52fdb
-- title:
--   Symbol Extension Property
-- statement:
--   Definitions and structural lemmas for Symbol Extension Property, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/SymbolExtensionProperty.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ProjTopology
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_SectionL2NormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS
open MeasureTheory Set
open scoped ENNReal ContDiff LinearAlgebra.Projectivization
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas ChartPartition chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.Bergman (HolLineBundle sectionSpace IsWeight IsSemipositive)
noncomputable section
def l2n {m : ℕ} (c : Fin m → ℂ) : ℝ := Real.sqrt (∑ i, ‖c i‖ ^ 2)
def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / ((D - 1).factorial : ℝ)
def Ra (D a : ℕ) : ℕ := Nat.choose (a + D - 1) (D - 1)
def tuples (D a : ℕ) : Finset (Fin D → ℕ) := Finset.Nat.antidiagonalTuple D a
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
def lbTensor (L₁ L₂ : HolLineBundle A) : HolLineBundle A where
  g j k x := L₁.g j k x * L₂.g j k x
  holo j k := fun i => (L₁.holo j k i).mul (L₂.holo j k i)
  ne_zero j k x hx := mul_ne_zero (L₁.ne_zero j k x hx) (L₂.ne_zero j k x hx)
  cocycle j k l x hx := by
    rw [← L₁.cocycle j k l x hx, ← L₂.cocycle j k l x hx]; ring
def lbPow (L : HolLineBundle A) (m : ℕ) : HolLineBundle A where
  g j k x := L.g j k x ^ m
  holo j k := fun i => (L.holo j k i).pow m
  ne_zero j k x hx := pow_ne_zero m (L.ne_zero j k x hx)
  cocycle j k l x hx := by rw [← mul_pow, L.cocycle j k l x hx]
def twist (L₂ L : HolLineBundle A) (m : ℕ) : HolLineBundle A := lbTensor L₂ (lbPow L m)
def wAdd (ψ φ : Fin A.n → X → ℝ) (m : ℕ) : Fin A.n → X → ℝ := fun j x => ψ j x + m * φ j x
def jacDet (A : FinHolAtlas D X) (j k : Fin A.n) (x : X) : ℂ :=
  LinearMap.det ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) (A.chart j x) :
    (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
def IsTopForm (B : HolLineBundle A) (f : Fin A.n → X → ℂ) : Prop :=
  (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
  (∀ j, ∀ x ∉ (A.chart j).source, f j x = 0) ∧
  ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = jacDet A j k x * B.g j k x * f k x
def IsSmoothTopForm (B : HolLineBundle A) (f : Fin A.n → X → ℂ) : Prop :=
  (∀ j i, ContDiffOn ℝ ∞ (f j ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source)) ∧
  (∀ j, ∀ x ∉ (A.chart j).source, f j x = 0) ∧
  ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = jacDet A j k x * B.g j k x * f k x
def topForms (B : HolLineBundle A) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | IsTopForm B f}
  add_mem' := by
    rintro f h ⟨hf1, hf2, hf3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun j i => (hf1 j i).add (hh1 j i), fun j x hx => ?_, fun j k x hx => ?_⟩
    · simp [hf2 j x hx, hh2 j x hx]
    · simp only [Pi.add_apply, hf3 j k x hx, hh3 j k x hx]; ring
  zero_mem' := ⟨fun _ _ => analyticOnNhd_const, fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨fun j i => (analyticOnNhd_const (v := c)).mul (hf1 j i), fun j x hx => ?_,
      fun j k x hx => ?_⟩
    · simp [hf2 j x hx]
    · simp only [Pi.smul_apply, smul_eq_mul, hf3 j k x hx]; ring
def secMul (f g : Fin A.n → X → ℂ) : Fin A.n → X → ℂ := fun j x => f j x * g j x
open scoped Classical in

def chartLIntegral (A : FinHolAtlas D X) (ρ : Fin A.n → X → ℝ) : ℝ≥0∞ :=
  if h : Nonempty (ChartPartition A) then
    ∑ j, ∫⁻ y in (A.chart j).target,
      ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * ρ j ((A.chart j).symm y))
  else ⊤
def topFormWeightedL2 (ψ : Fin A.n → X → ℝ) (f : Fin A.n → X → ℂ) : ℝ≥0∞ :=
  chartLIntegral A (fun j x => 2 ^ D * ‖f j x‖ ^ 2 * Real.exp (-ψ j x))
structure HermSpace (B : Submodule ℂ (Fin A.n → X → ℂ)) where

  n : ℕ

  e : Fin n → Fin A.n → X → ℂ
  mem : ∀ i, e i ∈ B
  indep : LinearIndependent ℂ e
namespace HermSpace
variable {B : Submodule ℂ (Fin A.n → X → ℂ)} (H : HermSpace B)
def sec (c : Fin H.n → ℂ) : Fin A.n → X → ℂ := ∑ i, c i • H.e i
def space : Submodule ℂ (Fin A.n → X → ℂ) := Submodule.span ℂ (Set.range H.e)
def hnorm (f : Fin A.n → X → ℂ) : ℝ := sInf (l2n '' {c | H.sec c = f})
end HermSpace
def fsPhi {B : Submodule ℂ (Fin A.n → X → ℂ)} (H : HermSpace B) (j : Fin A.n) (x : X) : ℝ :=
  Real.log (∑ i, ‖H.e i j x‖ ^ 2)
structure FSData (A : FinHolAtlas D X) (Y : Type) [TopologicalSpace Y] where

  L : HolLineBundle A

  L₂ : HolLineBundle A

  W : HermSpace (sectionSpace L 1)

  W₂ : HermSpace (sectionSpace L₂ 1)
  gen : ∀ j, ∀ x ∈ (A.chart j).source, ∃ i, W.e i j x ≠ 0
  gen₂ : ∀ j, ∀ x ∈ (A.chart j).source, ∃ i, W₂.e i j x ≠ 0
  isWeight : IsWeight L (fsPhi W)
  isWeight₂ : IsWeight L₂ (fsPhi W₂)

  ι : X → Y
  isOpenEmbedding : Topology.IsOpenEmbedding ι
  denseRange : DenseRange ι

  Φ : Y → ℙ ℂ (Fin W.n → ℂ)
  continuous_Φ : Continuous Φ
  Φ_ι : ∀ x, (fun i => W.e i (chartIdx A x) x) ∈ (Φ (ι x)).submodule
namespace FSData
variable {Y : Type} [TopologicalSpace Y] (d : FSData A Y)
def zeroY (s : Fin D → Fin d.W.n → ℂ) : Set Y := {y | ∀ i, ∑ k, s i k * (d.Φ y).rep k = 0}
def zeroU (s : Fin D → Fin d.W.n → ℂ) : Set X := {x | ∀ i, d.W.sec (s i) (chartIdx A x) x = 0}
def sLoc (s : Fin D → Fin d.W.n → ℂ) (j : Fin A.n) (z : Fin D → ℂ) : Fin D → ℂ :=
  fun i => d.W.sec (s i) j ((A.chart j).symm z)
def sJac (s : Fin D → Fin d.W.n → ℂ) (j : Fin A.n) (x : X) : ℂ :=
  LinearMap.det ((fderiv ℂ (d.sLoc s j) (A.chart j x) : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
structure IsGoodS (s : Fin D → Fin d.W.n → ℂ) : Prop where
  sub : d.zeroY s ⊆ Set.range d.ι
  finite : (d.zeroU s).Finite
  etale : ∀ x ∈ d.zeroU s, d.sJac s (chartIdx A x) x ≠ 0
def rr (s : Fin D → Fin d.W.n → ℂ) : ℝ := Real.sqrt (∑ i, l2n (s i) ^ 2)
def rPow (s : Fin D → Fin d.W.n → ℂ) (α : Fin D → ℕ) : ℝ := ∏ i, l2n (s i) ^ (2 * α i)
def res (s : Fin D → Fin d.W.n → ℂ) (F : Fin A.n → X → ℂ) (x : X) : ℂ :=
  F (chartIdx A x) x / d.sJac s (chartIdx A x) x
def gNormSq (s : Fin D → Fin d.W.n → ℂ) (j : ℕ) (g : X → ℂ) : ℝ :=
  ∑ᶠ x ∈ d.zeroU s, ‖g x‖ ^ 2 *
    Real.exp (-(fsPhi d.W₂ (chartIdx A x) x + j * fsPhi d.W (chartIdx A x) x))
def symNormSq (s : Fin D → Fin d.W.n → ℂ) (a j : ℕ) (g : (Fin D → ℕ) → X → ℂ) : ℝ :=
  ∑ α ∈ tuples D a, d.rPow s α * d.gNormSq s j (g α)
def monoSec (s : Fin D → Fin d.W.n → ℂ) (α : Fin D → ℕ) : Fin A.n → X → ℂ :=
  fun j x => ∏ i, d.W.sec (s i) j x ^ α i
def wProd {k : ℕ} (ws : Fin k → Fin d.W.n → ℂ) : Fin A.n → X → ℂ :=
  fun j x => ∏ l, d.W.sec (ws l) j x
def InFil (s : Fin D → Fin d.W.n → ℂ) (a : ℕ) (F : Fin A.n → X → ℂ) : Prop :=
  ∀ x ∈ d.zeroU s, ∀ m < a, iteratedFDeriv ℂ m (F (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm)
    (A.chart (chartIdx A x) x) = 0
def HasSymbol (s : Fin D → Fin d.W.n → ℂ) (a : ℕ) (F : Fin A.n → X → ℂ)
    (g : (Fin D → ℕ) → X → ℂ) : Prop :=
  d.InFil s a F ∧ ∀ x ∈ d.zeroU s,
    iteratedFDeriv ℂ a (F (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) =
      ∑ α ∈ tuples D a, (g α x * d.sJac s (chartIdx A x) x) •
        iteratedFDeriv ℂ a (fun z => ∏ i, d.sLoc s (chartIdx A x) z i ^ α i)
          (A.chart (chartIdx A x) x)
end FSData
def dbar (u : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (k : Fin D) : ℂ :=
  (fderiv ℝ u z (Pi.single k 1) + Complex.I * fderiv ℝ u z (Pi.single k Complex.I)) / 2
def Hormander (B : HolLineBundle A) : Prop :=
  ∀ (ψE : Fin A.n → X → ℝ) (ψ : X → ℝ) (F₀ : Fin A.n → X → ℂ) (h : Fin A.n → X → ℝ),
    IsWeight B ψE →
    (∀ i, ContDiffOn ℝ ∞ (ψ ∘ (A.chart i).symm) (A.chart i).target) →
    (∀ j l, ∀ y ∈ (A.chart l).target ∩ (A.chart l).symm ⁻¹' (A.chart j).source, ∀ w : Fin D → ℂ,
      0 ≤ levi ((fun x => ψE j x + ψ x) ∘ (A.chart l).symm) y w) →
    IsSmoothTopForm B F₀ →
    (∀ j x, 0 ≤ h j x) →
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, h j x = ‖jacDet A j k x‖ ^ 2 * h k x) →
    (∀ j, ∀ x ∈ (A.chart j).source, ∀ ξ : Fin D → ℂ,
      2 ^ D * ‖∑ k, dbar (F₀ j ∘ (A.chart j).symm) (A.chart j x) k * starRingEnd ℂ (ξ k)‖ ^ 2 *
          Real.exp (-ψE j x) ≤
        h j x * levi ((fun x => ψE j x + ψ x) ∘ (A.chart j).symm) (A.chart j x) ξ) →
    ∃ F ∈ topForms B, topFormWeightedL2 (fun j x => ψE j x + ψ x) (F₀ - F) ≤
      chartLIntegral A (fun j x => h j x * Real.exp (-ψ x))
structure HSData (A : FinHolAtlas D X) (Y : Type) [TopologicalSpace Y] extends FSData A Y where

  β : ℝ
  one_le_β : 1 ≤ β

  T : ℕ
  le_T : D + 1 ≤ T

  φA : Fin A.n → X → ℝ
  isWeightA : IsWeight (twist L₂ L D) φA
  pshA : IsSemipositive A φA
  boundA : ∀ j, ∀ x ∈ (A.chart j).source,
    Real.exp (-φA j x) ≤ β ^ (D + 1) * Real.exp (-(fsPhi W₂ j x + D * fsPhi W j x))

  V : (j : ℕ) → HermSpace (topForms (twist L₂ L (D + j)))
namespace HSData
variable {Y : Type} [TopologicalSpace Y] (d : HSData A Y)
def natSpace (j : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) :=
  Submodule.span ℂ {f | f ∈ topForms (twist d.L₂ d.L (D + j)) ∧
    topFormWeightedL2 (wAdd d.φA (fsPhi d.W) j) f < ⊤}
def H0' : Prop := (d.V 0).space ≤ d.natSpace 0 ∧ d.natSpace D ≤ (d.V D).space
def H1 : Prop :=
  ∀ j < d.T, ∀ c : Fin d.W.n → ℂ, ∀ f ∈ (d.V j).space,
    secMul (d.W.sec c) f ∈ (d.V (j + 1)).space ∧
      (d.V (j + 1)).hnorm (secMul (d.W.sec c) f) ≤ Real.sqrt d.β * l2n c * (d.V j).hnorm f
def H2' : Prop :=
  ∀ f ∈ (d.V d.T).space, ENNReal.ofReal ((d.V d.T).hnorm f ^ 2) ≤
    ENNReal.ofReal (d.β ^ (D + d.T + 1)) * topFormWeightedL2 (wAdd (fsPhi d.W₂) (fsPhi d.W) (D + d.T)) f
def Pσ (s : Fin D → Fin d.W.n → ℂ) : Submodule ℂ (Fin A.n → X → ℂ) :=
  Submodule.span ℂ {f | ∃ α ∈ tuples D (d.T - D), ∃ m ∈ (d.V D).space,
    f = secMul (d.monoSec s α) m}
def Vpp (s : Fin D → Fin d.W.n → ℂ) : Submodule ℂ (Fin A.n → X → ℂ) :=
  Submodule.span ℂ {f | ∃ (j : ℕ) (α : Fin D → ℕ) (ws : Fin j → Fin d.W.n → ℂ)
      (m : Fin A.n → X → ℂ), m ∈ (d.V 0).space ∧ (∑ i, α i) + j = d.T ∧
      (∑ i, α i) ≤ d.T - D - 1 ∧ f = secMul (d.monoSec s α) (secMul (d.wProd ws) m)} ⊔
    d.Pσ s
def ResOnto (s : Fin D → Fin d.W.n → ℂ) : Prop :=
  ∀ g : X → ℂ, ∃ m ∈ (d.V 0).space, ∀ x ∈ d.zeroU s, d.res s m x = g x
def HasUnitW (s : Fin D → Fin d.W.n → ℂ) : Prop :=
  ∃ c : Fin d.W.n → ℂ, ∀ x ∈ d.zeroU s, d.W.sec c (chartIdx A x) x ≠ 0
def Division (s : Fin D → Fin d.W.n → ℂ) : Prop :=
  ∀ f ∈ d.natSpace d.T, d.InFil s (d.T - D) f →
    f ∈ Submodule.span ℂ {g | ∃ α ∈ tuples D (d.T - D), ∃ h ∈ d.natSpace D,
      g = secMul (d.monoSec s α) h}
def SymbolExtensionProperty (s : Fin D → Fin d.W.n → ℂ) : Prop :=
  ∀ a ≤ d.T - D - 1, ∀ g : (Fin D → ℕ) → X → ℂ, ∃ F ∈ d.Vpp s,
    F ∈ (d.V d.T).space ∧ d.HasSymbol s a F g ∧
    (d.V d.T).hnorm F ≤
      Real.sqrt (d.β ^ (d.T + D + 1) * 140 * cD D * (Ra D a : ℝ) * d.rr s ^ (2 * D)) *
        Real.sqrt (d.symNormSq s a (d.T - a) g)
end HSData
def EffectiveHilbertSamuelAppendixFive.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas D X) (d : FSData A Y)
    (s : Fin D → Fin d.W.n → ℂ) (j : ℕ), d.IsGoodS s → 2 ≤ j →
    Hormander (twist d.L₂ d.L (D + j)) →
    ∀ g : X → ℂ, ∃ F ∈ topForms (twist d.L₂ d.L (D + j)),
      (∀ x ∈ d.zeroU s, d.res s F x = g x) ∧
      topFormWeightedL2 (wAdd (fsPhi d.W₂) (fsPhi d.W) (D + j)) F ≤
        ENNReal.ofReal (140 * cD D * d.rr s ^ (2 * D) * d.gNormSq s j g)
def EffectiveHilbertSamuelJetFirst.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas D X) (d : HSData A Y)
    (s : Fin D → Fin d.W.n → ℂ), d.H0' → d.Vpp s ≤ d.natSpace d.T ⊔ d.Pσ s
def EffectiveHilbertSamuelTheoremB.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas D X) (d : HSData A Y)
    (s : Fin D → Fin d.W.n → ℂ), d.H0' → d.Division s →
    ∀ f, (f ∈ d.Vpp s ∧ d.InFil s (d.T - D) f) ↔ f ∈ d.Pσ s
def EffectiveHilbertSamuelJetSecond.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas D X) (d : HSData A Y)
    (s : Fin D → Fin d.W.n → ℂ), d.IsGoodS s → d.ResOnto s → d.HasUnitW s →
    ∀ a ≤ d.T - D - 1, ∀ g : (Fin D → ℕ) → X → ℂ, ∃ F ∈ d.Vpp s, d.HasSymbol s a F g
def EffectiveHilbertSamuelJetThird.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas D X) (d : HSData A Y)
    (s : Fin D → Fin d.W.n → ℂ), d.IsGoodS s → d.H0' → d.H1 → d.H2' → d.ResOnto s →
    d.HasUnitW s → (∀ j, D + 1 ≤ j → j ≤ d.T → Hormander (twist d.L₂ d.L (D + j))) →
    d.Division s → d.SymbolExtensionProperty s
def EffectiveHilbertSamuelTheorem.Statement : Prop :=
  EffectiveHilbertSamuelJetFirst.Statement ∧ EffectiveHilbertSamuelTheoremB.Statement ∧ EffectiveHilbertSamuelJetSecond.Statement ∧ EffectiveHilbertSamuelJetThird.Statement
def EffectiveHilbertSamuelAppendixSixFirst.Statement : Prop := EffectiveHilbertSamuelTheoremB.Statement
def EffectiveHilbertSamuelAppendixSixSecond.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas D X) (d : HSData A Y)
    (s : Fin D → Fin d.W.n → ℂ), d.H1 → d.Vpp s ≤ (d.V d.T).space
def EffectiveHilbertSamuelAppendixSixThird.Statement : Prop := EffectiveHilbertSamuelJetThird.Statement
def EffectiveHilbertSamuelAppendixSixFourth.Statement : Prop :=
  ∀ (D : ℕ) (ρ : ℝ), 1 ≤ D → 2 ^ 26 ≤ ρ →
    (1 / 2 : ℝ) * (Real.log 280 + D * Real.log (2 * Real.pi)) ≤ 3.8 * D ∧
      3.8 * (D : ℝ) ≤ (D / 2 : ℝ) * Real.log ρ
def EffectiveHilbertSamuel₂.Statement : Prop :=
  EffectiveHilbertSamuelAppendixSixFirst.Statement ∧ EffectiveHilbertSamuelAppendixSixSecond.Statement ∧ EffectiveHilbertSamuelAppendixSixThird.Statement ∧ EffectiveHilbertSamuelAppendixSixFourth.Statement
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS


