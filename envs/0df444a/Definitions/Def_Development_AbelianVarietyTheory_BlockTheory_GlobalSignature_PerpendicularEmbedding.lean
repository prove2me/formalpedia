-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:10.362848+00:00
-- url     : https://prove2.me/theorems/599eaa53-76de-4ceb-86b5-6841328dca48
-- title:
--   Perpendicular Embedding
-- statement:
--   Definitions and structural lemmas for Perpendicular Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/PerpendicularEmbedding.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
abbrev Sp (P Q : ℕ) : Type := Fin P ⊕ Fin Q → ℂ
def herm {P Q : ℕ} (x y : Sp P Q) : ℂ :=
  ∑ i : Fin P, x (Sum.inl i) * star (y (Sum.inl i)) -
    ∑ j : Fin Q, x (Sum.inr j) * star (y (Sum.inr j))
def qf {P Q : ℕ} (x : Sp P Q) : ℝ :=
  ∑ i : Fin P, Complex.normSq (x (Sum.inl i)) - ∑ j : Fin Q, Complex.normSq (x (Sum.inr j))
def dx (P Q : ℕ) : Measure (Sp P Q) := ((2 : ℝ≥0∞) ^ (P + Q)) • (volume : Measure (Sp P Q))
def cM (M : ℕ) : ℝ := (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)
def IsDxDq {P Q : ℕ} (fib : ℝ → Measure (Sp P Q)) : Prop :=
  IsFibreFamily (dx P Q) (qf : Sp P Q → ℝ) id {x | x ≠ 0} (volume : Measure ℝ) Set.univ fib
def act {P Q : ℕ} (g : UpqT P Q) (x : Sp P Q) : Sp P Q := UpqT.mat g *ᵥ x
def IsPerpEmb {P Q P' Q' : ℕ} (x₀ : Sp P Q)
    (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  (∀ u v : Sp P' Q', herm (A *ᵥ u) (A *ᵥ v) = herm u v) ∧
  (∀ y : Sp P Q, herm y x₀ = 0 ↔ ∃ u : Sp P' Q', A *ᵥ u = y) ∧
  (∀ g : UpqT P' Q', act (j g) x₀ = x₀ ∧ ∀ u : Sp P' Q', act (j g) (A *ᵥ u) = A *ᵥ act g u)
def IsSection {P Q : ℕ} (β : ℝ) (x₀ : Sp P Q) (s : Sp P Q → UpqT P Q) : Prop :=
  Measurable s ∧ ∀ y : Sp P Q, qf y = β → act (s y) x₀ = y
def QuotFormula (c : CDHaar) (P Q P' Q' : ℕ) (β : ℝ) : Prop :=
  ∀ x₀ : Sp P Q, qf x₀ = β →
    AllSome
      (fun Aj : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ × (UpqT P' Q' → UpqT P Q) =>
        IsPerpEmb x₀ Aj.1 Aj.2)
      (fun Aj =>
        Set.range Aj.2 = {g | act g x₀ = x₀} ∧
        AllSome (fun fib : ℝ → Measure (Sp P Q) => IsDxDq fib) (fun fib =>
          AllSome (fun s : Sp P Q → UpqT P Q => IsSection β x₀ s) (fun s =>
            ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
              ∫⁻ g, f g ∂(c.cd P Q) =
                (ENNReal.ofReal (cM (P + Q)))⁻¹ *
                  ∫⁻ y, (∫⁻ g', f (s y * Aj.2 g') ∂(c.cd P' Q')) ∂(fib β))))
def CompactDualQuotient : Prop :=
  ∀ (c : CDHaar) (P Q : ℕ),
    QuotFormula c (P + 1) Q P Q 1 ∧ QuotFormula c P (Q + 1) P Q (-1)
def SelfDualReal : Prop :=
  ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    (∀ P Q : ℕ, SelfDual (dx P Q) (fun x y : Sp P Q =>
      Complex.exp (2 * Real.pi * Complex.I * ((ε * (2 * (herm x y).re) : ℝ) : ℂ)))) ∧
    SelfDual (volume : Measure ℝ)
      (fun t s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (t * s) : ℝ) : ℂ)))
def SphereMass : Prop :=
  ∀ M : ℕ, 1 ≤ M → AllSome (fun fib : ℝ → Measure (Sp M 0) => IsDxDq fib)
    (fun fib => fib 1 Set.univ = ENNReal.ofReal (cM M))
example : cM 1 = 2 * Real.pi := by simp [cM]
example (P Q : ℕ) : qf (Pi.single (Sum.inl 0) 1 : Sp (P + 1) Q) = 1 ∧
    qf (Pi.single (Sum.inr 0) 1 : Sp P (Q + 1)) = -1 := by
  constructor <;> simp [qf, Fin.sum_univ_succ, Pi.single_apply]
end GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding


