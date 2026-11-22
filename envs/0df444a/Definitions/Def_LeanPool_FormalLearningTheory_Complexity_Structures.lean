-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
-- name    : LeanPool_FormalLearningTheory_Complexity_Structures
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:17.302112+00:00
-- url     : https://prove2.me/theorems/de0b5b1e-0d96-44e3-9af9-879aa80faefc
-- title:
--   Structures
-- statement:
--   Definitions and structural lemmas for Structures, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Structures.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
structure CompressionScheme (X : Type u) (Y : Type v) (C : ConceptClass X Y) where
  /-- Compression: extract ≤ size labeled examples from the sample -/
  compress : {m : ℕ} → (Fin m → X × Y) → Finset (X × Y)
  /-- Reconstruction: produce hypothesis from compressed subset alone -/
  reconstruct : Finset (X × Y) → (X → Y)
  /-- Size of the compressed representation -/
  size : ℕ
  /-- Compressed set is small -/
  compress_small : ∀ {m : ℕ} (S : Fin m → X × Y), (compress S).card ≤ size
  /-- Compressed set is a subset of the sample -/
  compress_sub : ∀ {m : ℕ} (S : Fin m → X × Y),
    ↑(compress S) ⊆ Set.range S
  /-- Correctness: reconstructed hypothesis agrees with every sample point,
      when the sample is C-realizable (∃ c ∈ C agreeing with all labels) -/
  correct : ∀ {m : ℕ} (S : Fin m → X × Y),
    (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) →
    ∀ i : Fin m, reconstruct (compress S) (S i).1 = (S i).2
structure UnlabeledCompression (X : Type u) (Y : Type v) where
  /-- Size of the compressed representation. -/
  size : ℕ
  /-- Selected sample indices. -/
  compress : {m : ℕ} → (Fin m → X × Y) → Finset (Fin m)
  /-- Reconstruct a concept from unlabeled sample points and selected indices. -/
  reconstruct : {m : ℕ} → (Fin m → X) → Finset (Fin m) → Concept X Y
  small : ∀ {m : ℕ} (S : Fin m → X × Y), (compress S).card ≤ size
structure AlgorithmicStability (X : Type u) (Y : Type v) where
  /-- The learner whose stability we measure -/
  learner : BatchLearner X Y
  /-- Stability parameter -/
  beta : ℝ
  beta_nonneg : 0 ≤ beta
  /-- Loss function used to measure prediction changes. -/
  loss : LossFunction Y
  /-- Stability: for any sample S and any index i, the loss of L(S) vs L(S\i)
      on any fresh point z differs by at most β.
      S\i denotes the sample with the i-th element removed. -/
  stable : ∀ {m : ℕ} (S : Fin (m + 1) → X × Y) (i : Fin (m + 1)) (z : X × Y),
    |loss (learner.learn S z.1) z.2 -
     loss (learner.learn (fun j => S (Fin.succAbove i j)) z.1) z.2| ≤ beta
noncomputable def NatarajanDim (X : Type u) (Y : Type v)
    (C : ConceptClass X Y) : WithTop ℕ :=
  ⨆ (S : Finset X)
    (_ : ∃ (f₀ f₁ : X → Y), (∀ x ∈ S, f₀ x ≠ f₁ x) ∧
      ∀ (h : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
        c x = if h x then f₀ x else f₁ x),
    (S.card : WithTop ℕ)
noncomputable def DSDim (X : Type u) (Y : Type v)
    (C : ConceptClass X Y) : WithTop ℕ :=
  ⨆ (S : Finset X)
    (_ : ∀ (f : X → Y), ∃ c ∈ C, ∀ x ∈ S, c x = f x),
    (S.card : WithTop ℕ)
noncomputable def Pseudodimension (X : Type u) (C : ConceptClass X ℝ) : WithTop ℕ :=
  ⨆ (S : Finset X) (t : X → ℝ)
    (_ : ∀ (b : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
      (b x = true → c x ≥ t x) ∧ (b x = false → c x < t x)),
    (S.card : WithTop ℕ)
noncomputable def FatShatteringDim (X : Type u) (C : ConceptClass X ℝ)
    (γ : ℝ) (hγ : 0 < γ) : WithTop ℕ :=
  if h : 0 < γ then
    ⨆ (S : Finset X) (t : X → ℝ)
      (_ : ∀ (b : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
        (b x = true → c x ≥ t x + γ) ∧ (b x = false → c x ≤ t x - γ)),
      (S.card : WithTop ℕ)
  else False.elim (h hγ)
noncomputable def SQDimension (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (τ : ℝ) : WithTop ℕ :=
  ⨆ (S : Finset (Concept X Bool))
    (_ : ↑S ⊆ C ∧ ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ →
      |∫ x, (if c₁ x = c₂ x then (1 : ℝ) else -1) ∂D| ≤ τ),
    (S.card : WithTop ℕ)
noncomputable def FormalLearningCoveringNumber (X : Type u) (C : ConceptClass X Bool)
    (d : Concept X Bool → Concept X Bool → ℝ) (ε : ℝ) : ℕ :=
  sInf { k : ℕ | ∃ (S : Finset (Concept X Bool)), S.card ≤ k ∧
    ∀ c, c ∈ C → ∃ s ∈ S, d c s ≤ ε }
noncomputable def TeachingDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (c : Concept X Bool) (_ : c ∈ C),
    ⨅ (T : Finset (X × Bool))
      (_ : (∀ p ∈ T, c p.1 = p.2) ∧
           ∀ c' ∈ C, c' ≠ c → ∃ p ∈ T, c' p.1 ≠ p.2),
      (T.card : WithTop ℕ)
noncomputable def EluderDim (X : Type u) (C : ConceptClass X Bool) : WithTop ℕ :=
  ⨆ (seq : List X)
    (_ : ∀ (i : Fin seq.length),
      ∃ (c₁ c₂ : Concept X Bool), c₁ ∈ C ∧ c₂ ∈ C ∧
        (∀ (j : Fin seq.length), j.val < i.val →
          c₁ (seq[j]) = c₂ (seq[j])) ∧
        c₁ (seq[i]) ≠ c₂ (seq[i])),
    (seq.length : WithTop ℕ)
noncomputable def KLComplexity (α : Type*) (prior posterior : α → ℝ) : ℝ :=
  ∑' x, if prior x > 0 ∧ posterior x > 0
    then posterior x * Real.log (posterior x / prior x)
    else 0
structure MarginTheory (X : Type u) where
  /-- Positive margin parameter. -/
  margin : ℝ
  margin_pos : 0 < margin
  /-- Real-valued concept class controlled by the margin bound. -/
  conceptClass : ConceptClass X ℝ
  /-- Generalization bound as a function of sample size. -/
  bound : ℕ → ℝ
structure CompressionSchemeWithInfo
    (X : Type u) (Y : Type v) (C : ConceptClass X Y) where
  /-- The side information type -/
  Info : Type*
  /-- Side information is finite -/
  infoFinite : Fintype Info
  /-- Compression: extract ≤ kernelSize labeled examples + side information -/
  compress : {m : ℕ} → (Fin m → X × Y) → Finset (X × Y) × Info
  /-- Reconstruction: produce hypothesis from compressed subset AND side information -/
  reconstruct : Finset (X × Y) → Info → (X → Y)
  /-- Kernel size bound -/
  kernelSize : ℕ
  /-- Compressed set is small -/
  compress_small : ∀ {m : ℕ} (S : Fin m → X × Y),
    (compress S).1.card ≤ kernelSize
  /-- Compressed set is a subset of the sample -/
  compress_sub : ∀ {m : ℕ} (S : Fin m → X × Y),
    ↑(compress S).1 ⊆ Set.range S
  /-- Correctness: reconstructed hypothesis agrees with every sample point,
      when the sample is C-realizable -/
  correct : ∀ {m : ℕ} (S : Fin m → X × Y),
    (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) →
    ∀ i : Fin m,
      reconstruct (compress S).1 (compress S).2 (S i).1 = (S i).2
attribute [instance] CompressionSchemeWithInfo.infoFinite
noncomputable def CompressionSchemeWithInfo.size
    {X : Type u} {Y : Type v} {C : ConceptClass X Y}
    (cs : CompressionSchemeWithInfo X Y C) : ℕ :=
  cs.kernelSize + Fintype.card cs.Info
def CompressionScheme.toWithInfo
    {X : Type u} {Y : Type v} {C : ConceptClass X Y}
    (cs : CompressionScheme X Y C) : CompressionSchemeWithInfo X Y C where
  Info := PUnit
  infoFinite := inferInstance
  compress := fun S => (cs.compress S, PUnit.unit)
  reconstruct := fun Z _ => cs.reconstruct Z
  kernelSize := cs.size
  compress_small := fun S => cs.compress_small S
  compress_sub := fun S => cs.compress_sub S
  correct := fun S hreal i => cs.correct S hreal i
def OpenNoInfoCompressionStrengthening : Prop :=
  ∀ (X : Type*) (C : ConceptClass X Bool),
    VCDim X C < ⊤ →
    ∃ (k : ℕ) (cs : CompressionScheme X Bool C), cs.size = k


