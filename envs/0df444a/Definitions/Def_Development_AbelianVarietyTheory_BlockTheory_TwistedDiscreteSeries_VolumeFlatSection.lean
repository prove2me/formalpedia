-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_VolumeFlatSection
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_VolumeFlatSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:33.189602+00:00
-- url     : https://prove2.me/theorems/e360c3ef-fb4f-4496-97ae-9ba4c3df3d07
-- title:
--   Volume Flat Section
-- statement:
--   Definitions and structural lemmas for Volume Flat Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/VolumeFlatSection.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_GLDoubling_one_int
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
open scoped NNReal
namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section Blocks
variable (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
def parahoric : Subgroup (GL (A ⊕ D) k) :=
  ((parab 𝓀[k] (two (Equiv.refl (A ⊕ D)))).comap
      (GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]))).map
    (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k))
variable {k A D D'}
def typeSpace {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) :
    Submodule ℂ V where
  carrier := {f | ∀ g ∈ parahoric k A D, ∀ d : kˣ, (d : k) = g.1.toBlocks₂₂.det → π g f = (ξ d : ℂ) • f}
  add_mem' hf hf' g hg d hd := by rw [map_add, hf g hg d hd, hf' g hg d hd, smul_add]
  zero_mem' g _ d _ := by simp
  smul_mem' c f hf g hg d hd := by rw [map_smul, hf g hg d hd, smul_comm]
def InSupp (x : Matrix (A ⊕ D) (A ⊕ D') k) : Prop :=
  (∀ i j, x i j ∈ 𝒪[k]) ∧ valuation k x.toBlocks₁₁.det = 1 ∧ ∀ i j, valuation k (x (.inr i) (.inl j)) < 1
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype D] [DecidableEq D] [Fintype D']
  [DecidableEq D'] in
theorem InSupp.det_ne {x : Matrix (A ⊕ D) (A ⊕ D') k} (h : InSupp x) : x.toBlocks₁₁.det ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1
open Classical in

def datum (ξ : kˣ →* ℂˣ) (x : Matrix (A ⊕ D) (A ⊕ D') k) : ℂ :=
  if h : InSupp x then (((ξ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0
end Blocks
section Section
variable {k} {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [MeasurableSpace k]
def dblDatum (Φ₁ Φ₂ : Matrix b a k → ℂ) (y : Matrix b (a ⊕ a) k) : ℂ :=
  Φ₁ y.toCols₁ * starRingEnd ℂ (Φ₂ (-y.toCols₂))
def swSection (ν : Measure k) (μ : kˣ →* ℂˣ) (Φ₁ Φ₂ : Matrix b a k → ℂ) (h : GL (a ⊕ a) k) : ℂ :=
  ∫ x : Matrix b a k, om μ h (1 : GL b k) (dblDatum Φ₁ Φ₂) (fromCols x (-x)) ∂(volM ν b a)
def flatSection (ν : Measure k) (μ : kˣ →* ℂˣ) (Φ₁ Φ₂ : Matrix b a k → ℂ) (s : ℂ) (h : GL (a ⊕ a) k) : ℂ :=
  swSection ν μ Φ₁ Φ₂ h *
    npow (iwAbs (absRatio k a) (KO k (a ⊕ a)) h) (s - ((Fintype.card b : ℂ) - (Fintype.card a : ℂ)) / 2)
end Section
abbrev Blocks (l t : ℕ) : Type := Σ _ : Fin l, Fin t
variable {k}
abbrev blockRep {l : ℕ} (t : ℕ) (μ : Fin l → kˣ →* ℂˣ) :=
  multiProd (m := fun _ : Fin l => Fin t) (X := fun _ => ℂ) (Equiv.refl (Blocks l t)) fun i => detRep (Fin t) (μ i)
abbrev chainRep {r l : ℕ} (t : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin r) k) V) (μ : Fin l → kˣ →* ℂˣ) :=
  ind₂ (Equiv.refl (Fin r ⊕ Blocks l t)) (extTensor σ (blockRep t μ))
def IsInvForm {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ (∀ v, v ≠ 0 → 0 < (B v v).re) ∧ ∀ g v w, B (ρ g v) (ρ g w) = B v w
def blockParam {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ) (μ' : kˣ →* ℂˣ) (x : Blocks l t) : ℂˣ :=
  μ x.1 ϖ / μ' ϖ * absPow k (((x.2 : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ
def blockL {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ) (μ' : kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  lFactor (resCard k) (blockParam t ϖ μ μ') s * lFactor (resCard k) (blockParam t ϖ μ μ')⁻¹ s
def zetaAt (q i : ℕ) : ℝ := (1 - ((q : ℝ) ^ i)⁻¹)⁻¹
def volAdd [MeasurableSpace k] (ν : Measure k) (r : ℕ) : ℝ :=
  (volM ν (Fin r) (Fin r)).real (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)))
def stepValue [MeasurableSpace k] (ν : Measure k) (r : ℕ) {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ)
    (μ' : kˣ →* ℂˣ) : ℂ :=
  ((volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ : ℝ) : ℂ) * blockL t ϖ μ μ' ((1 + (t : ℂ)) / 2) /
    ((∏ i ∈ Finset.Ioc t ((l + 1) * t), zetaAt (resCard k) i : ℝ) : ℂ)
def ChainStep : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r t l : ℕ), 1 ≤ r → 1 ≤ t → 1 ≤ l →
  ∀ (ξ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ →
  ∀ (μ₀ : Fin l → kˣ →* ℂˣ) (μ₀' : kˣ →* ℂˣ), (∀ i, IsUnram (μ₀ i) ∧ IsUnitaryChar (μ₀ i)) →
    IsUnram μ₀' → IsUnitaryChar μ₀' →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V),
    IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSpherical σ →
  let q : ℕ := resCard k
  let μ : Fin l → kˣ →* ℂˣ := fun i => μ₀ i * ξ
  let μ' : kˣ →* ℂˣ := μ₀' * ξ
  let π := chainRep t σ μ
  let J := parahoric k (Fin r) (Blocks l t)
  let Φ : Matrix (Fin r ⊕ Blocks (l + 1) t) (Fin r ⊕ Blocks l t) k → ℂ := datum ξ
  let s₀ : ℝ := (t : ℝ) / 2
  let Zj : ℂ := stepValue ν r t ϖ μ μ'
  let idx : ℕ := (parahoric k (Fin r) (Blocks (l + 1) t)).relIndex (KO k (Fin r ⊕ Blocks (l + 1) t))
  let b : ℕ := r + (l + 1) * t

  Module.finrank ℂ (typeSpace π ξ) = 1 ∧

  volAdd ν r = ∏ i ∈ Finset.Icc 1 r, (zetaAt q i)⁻¹ ∧
  (idx : ℝ) = (q : ℝ) ^ (r * ((l + 1) * t)) * (∏ i ∈ Finset.Icc 1 b, (zetaAt q i)⁻¹) /
    ((∏ i ∈ Finset.Icc 1 r, (zetaAt q i)⁻¹) * ∏ i ∈ Finset.Icc 1 ((l + 1) * t), (zetaAt q i)⁻¹) ∧
  (idx : ℂ) * ((∏ i ∈ Finset.Ioc t b, zetaAt q i : ℝ) : ℂ) * Zj = blockL t ϖ μ μ' ((1 + (t : ℂ)) / 2) ∧
  blockL t ϖ μ μ' ((1 + (t : ℂ)) / 2) = ((∏ i : Fin l, ∏ n ∈ Finset.Icc 1 t,
    (‖1 - ((μ i ϖ / μ' ϖ : ℂˣ) : ℂ) * ((q : ℂ) ^ n)⁻¹‖ ^ 2)⁻¹ : ℝ) : ℂ) ∧
  ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m J = 1 →
  ∀ B, IsInvForm π B → ∀ f ∈ typeSpace π ξ,
  let F : ℂ → GL (Fin r ⊕ Blocks l t) k → ℂ := fun s g =>
    flatSection ν μ' Φ Φ s (io k _ (g, 1)) * starRingEnd ℂ (B (π g f) f)
  let Z : ℂ → ℂ := fun s => ∫ g, F s g ∂m

  (∀ s : ℂ, s₀ - 1 < s.re → Integrable (F s) m) ∧
  (∀ C : Set ℝ, IsCompact C → C ⊆ Set.Ioi (s₀ - 1) →
    ∃ M : GL (Fin r ⊕ Blocks l t) k → ℝ, Integrable M m ∧ ∀ s : ℂ, s.re ∈ C → ∀ g, ‖F s g‖ ≤ M g) ∧
  Integrable (fun g => ‖flatSection ν μ' Φ Φ (((t : ℂ) - 1) / 2) (io k _ (g, 1))‖ * ‖B (π g f) f‖) m ∧

  DifferentiableOn ℂ Z {s | s₀ - 1 < s.re} ∧
  Z s₀ = Zj * B f f ∧
  HasSum (fun c : DoubleCoset.Quotient (J : Set (GL (Fin r ⊕ Blocks l t) k)) (J : Set _) =>
    (m.real (DoubleCoset.doubleCoset c.out (J : Set _) (J : Set _)) : ℂ) * F s₀ c.out) (Zj * B f f)
example {A D D' : Type} [Fintype A] [DecidableEq A] (ξ : kˣ →* ℂˣ) :
    datum ξ (fromBlocks 1 0 0 0 : Matrix (A ⊕ D) (A ⊕ D') k) = 1 := by
  have h : InSupp (fromBlocks 1 0 0 0 : Matrix (A ⊕ D) (A ⊕ D') k) := by
    refine ⟨?_, by simp, fun i j => by simp⟩
    rintro (i | i) (j | j)
    · exact one_int i j
    all_goals exact zero_mem _
  rw [datum, dif_pos h]
  have : Units.mk0 _ h.det_ne = 1 := by ext; simp
  simp [this]
example {D : Type} [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ) :
    (1 : ℂ) ∈ typeSpace (A := Fin 0) (detRep (Fin 0 ⊕ D) ξ) ξ := fun g _ d hd => by
  have : GeneralLinearGroup.det g = d := by
    ext
    rw [hd, GeneralLinearGroup.val_det_apply, ← det_submatrix_equiv_self (Equiv.emptySum (Fin 0) D).symm]
    rfl
  simp [detRep, this]
end GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection


