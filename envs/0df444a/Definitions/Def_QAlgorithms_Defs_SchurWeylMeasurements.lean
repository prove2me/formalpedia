-- Prove2me | Definitions.Def_QAlgorithms_Defs_SchurWeylMeasurements
-- name    : QAlgorithms_Defs_SchurWeylMeasurements
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T08:26:08.52472+00:00
-- url     : https://prove2.me/theorems/31aa913a-8aed-4291-bd3e-236589879908
-- title:
--   prove2quantum library: Defs.SchurWeylMeasurements
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.SchurWeylMeasurements`), reused by its paper formalizations.
--
--   - `weakSampling`: Weak Schur sampling's complete isotypic projector family on the n-copy register, fixed before rho. Positivity, orthogonality and completeness are derived representation properties, not input certificates (1508.01907 pp.6-7).
--   - `weakSamplingLaw`: Born measure of weak sampling on a sorted probability spectrum alpha: counting on partitions weighted by Re Tr(Pi_lambda diag(alpha) tensor-power n). No renormalization or uniform prior over shapes (1508.01907 pp.2-3,5-6, Eqs.(8)-(9)).
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.SchurWeylMeasurements

import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_Learning

noncomputable section

open MeasureTheory
open scoped Matrix

namespace QAlgorithms.Schur

/-- Weak Schur sampling's complete isotypic projector family on the n-copy
register, fixed before rho. Positivity, orthogonality and completeness are
derived representation properties, not input certificates
(1508.01907 pp.6-7). -/
def weakSampling (d n : ℕ) :
    Partition d n → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  isotypicProjector

/-- Born measure of weak sampling on a sorted probability spectrum alpha:
counting on partitions weighted by Re Tr(Pi_lambda diag(alpha) tensor-power n).
No renormalization or uniform prior over shapes (1508.01907 pp.2-3,5-6,
Eqs.(8)-(9)). -/
def weakSamplingLaw {d n : ℕ} (_hd : 0 < d) (_hn : 0 < n)
    (alpha : Fin d → ℝ) (_probability : Learning.IsDistribution alpha)
    (_sorted : Antitone alpha) : Measure (Partition d n) :=
  Measure.count.withDensity (fun lambda => ENNReal.ofReal
    (effectProb (weakSampling d n lambda)
      (piKron n (Matrix.diagonal fun i => (alpha i : ℂ)))))


/-- One-factor weak sampling has the identity as its sole isotypic
projector (1508.01907 p.6). -/
theorem weakSampling_one {d : ℕ} (lambda : Partition d 1) :
    weakSampling d 1 lambda = 1 := by
  have hs : spechtSpace lambda = ⊤ := by
    rw [spechtSpace,youngRightOperator_one]
    simp
  have hp : spechtProjection lambda = 1 := by
    ext g h
    simp [spechtProjection,hs,Submodule.starProjection_top,ket,Matrix.one_apply,
      EuclideanSpace.inner_single_left]
  have hr : leftRegular (1 : Equiv.Perm (Fin 1)) = 1 := by
    ext g h
    simp [leftRegular,Matrix.one_apply]
  have hc : ∀ pi : Equiv.Perm (Fin 1), spechtCharacter lambda pi = 1 := by
    intro pi
    have he : pi = 1 := Subsingleton.elim _ _
    rw [he,spechtCharacter,hr,hp,mul_one,Matrix.trace_one]
    simp [Fintype.card_perm]
  have ht : ∀ pi : Equiv.Perm (Fin 1), tensorPermutation d 1 pi = 1 := by
    intro pi
    have he : pi = 1 := Subsingleton.elim _ _
    subst pi
    ext x y
    rfl
  have hdim : Module.finrank ℂ (spechtSpace lambda) = 1 := by
    rw [hs]
    simp [finrank_top,Fintype.card_perm]
  simp [weakSampling,isotypicProjector,hdim,hc,ht,Fintype.card_perm]

/-- One-factor weak sampling ignores the choice of spectral eigenbasis:
the shared effect is identity (1508.01907 p.6). -/
example {d : ℕ} (lambda : Partition d 1) : weakSampling d 1 lambda = 1 :=
  weakSampling_one lambda

end QAlgorithms.Schur


