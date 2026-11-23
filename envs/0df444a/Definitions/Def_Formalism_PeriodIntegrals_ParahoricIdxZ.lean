-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ParahoricIdxZ
-- name    : Formalism_PeriodIntegrals_ParahoricIdxZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:02.535139+00:00
-- url     : https://prove2.me/theorems/49672797-e98c-49bb-83b4-456efc7c3df3
-- title:
--   Parahoric Idx Z
-- statement:
--   Definitions and structural lemmas for Parahoric Idx Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ParahoricIdxZ.lean

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
open MeasureTheory Matrix ComplexConjugate Finset
namespace PI.ParahoricIdxZ
def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))
def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹
def blockCond {F : Type} [Field F] (O : Subring F) (ϖ : F) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (A : GL (Fin (a + t)) F) : Prop :=
  let M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A : Matrix (Fin (a + t)) (Fin (a + t)) F)
  (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = M.toBlocks₁₁) ∧
  (∀ i j, M.toBlocks₁₂ i j ∈ O) ∧
  M.toBlocks₂₁ ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ∧
  (∃ D ∈ Formalism.DoubleCosetMeasures.GLint O t, (D : Matrix (Fin t) (Fin t) F) = M.toBlocks₂₂)
end PI.ParahoricIdxZ
namespace PI
open PI.ParahoricIdxZ in

def ParahoricIdxZ : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (O : Subring F),
    IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a → IsCompact (J' : Set (GL (Fin a) F)) →
    ∀ (ρ : J' →* ℂˣ), (∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) →
    ∀ (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (lam : J' →* ℂˣ),
    (∀ k : J', ((χ (Matrix.GeneralLinearGroup.det (k : GL (Fin a) F)) : ℂˣ) : ℂ) *
        (((nrm ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) F) : Fˣ) : F)) ^
          (((a + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((ρ k : ℂˣ) : ℂ) * conj ((lam k : ℂˣ) : ℂ) = 1) →
    ∀ (c : GL (Fin a) F → ℂ), (∀ g : GL (Fin a) F, ∀ k : J', c (g * k) = ((lam k : ℂˣ) : ℂ) * c g) →
    c 1 = 1 →
    ∀ (μ : Measure (GL (Fin a) F)) [μ.IsMulLeftInvariant], μ (J' : Set (GL (Fin a) F)) = 1 →
    ∀ (ν₁ : Measure (Matrix (Fin a) (Fin a) F)) [ν₁.IsAddLeftInvariant] [SFinite ν₁],
    ν₁ (Formalism.DoubleCosetMeasures.intMat O a a) = 1 →
    ∀ (ν₂ : Measure (Matrix (Fin t) (Fin a) F)) [ν₂.IsAddLeftInvariant] [SFinite ν₂],
    ν₂ (Formalism.DoubleCosetMeasures.intMat O t a) = 1 →
    ∀ (J : Subgroup (GL (Fin (a + t)) F)), (∀ A, A ∈ J ↔ blockCond O ϖ J' A) →
    let q : ℝ := Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)
    ((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index : ℂ) * ((zetaProd q (a + t) : ℝ) : ℂ) *
        Formalism.DoubleCosetMeasures.localZ μ ((ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2)) χ nrm
          (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) c =
      ((zetaProd q t : ℝ) : ℂ)
end PI


