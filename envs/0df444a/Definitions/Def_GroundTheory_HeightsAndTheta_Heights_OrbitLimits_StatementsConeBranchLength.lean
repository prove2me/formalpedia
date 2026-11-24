-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:10.809007+00:00
-- url     : https://prove2.me/theorems/eb8df68e-2a0c-4ee3-965c-274e7c4b66b3
-- title:
--   Statements Cone Branch Length
-- statement:
--   Definitions and structural lemmas for Statements Cone Branch Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeBranchLength.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
section Objects
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
structure ConeBranch (P : Ideal (MRing ι)) (d : ℕ) (p : (Σ k, ι k) → ℂ) where

  radius : ℝ
  radius_pos : 0 < radius

  toFun : (Fin d → ℂ) → (Σ k, ι k) → ℂ
  differentiableOn : DifferentiableOn ℂ toFun (Metric.ball 0 radius)
  continuousOn : ContinuousOn toFun (Metric.closedBall 0 radius)
  injOn : Set.InjOn toFun (Metric.closedBall 0 radius)
  map_zero : toFun 0 = p
  mapsTo : Set.MapsTo toFun (Metric.closedBall 0 radius) (mcPts P)
def ConeBranch.image {P : Ideal (MRing ι)} {d : ℕ} {p : (Σ k, ι k) → ℂ} (γ : ConeBranch P d p) :
    Set ((Σ k, ι k) → ℂ) :=
  γ.toFun '' Metric.ball 0 γ.radius
def ConeBranch.slice {P : Ideal (MRing ι)} {d : ℕ} {p : (Σ k, ι k) → ℂ} (γ : ConeBranch P (d + 1) p) :
    Set ((Σ k, ι k) → ℂ) :=
  γ.toFun '' (Metric.ball 0 γ.radius ∩ {t | t 0 = 0})
def ConeBranchesAt (P : Ideal (MRing ι)) (s : MRing ι) (Wa : Ideal (MRingOver ℂ ι)) {d : ℕ}
    (p : (Σ k, ι k) → ℂ) {b : ℕ} (γ : Fin b → ConeBranch P (d + 1) p) (ord : Fin b → ℕ) : Prop :=
  (∀ k, ∃ i, p ⟨k, i⟩ ≠ 0) ∧ (∀ f ∈ Wa, eval p f = 0) ∧
    (∃ N ∈ 𝓝 p, mcPts P ∩ N ⊆ ⋃ j, (γ j).image) ∧
    (∀ j j', j ≠ j' → (γ j).image ∩ (γ j').image ⊆ {v | eval v (map (Int.castRingHom ℂ) s) = 0}) ∧
    (∃ N ∈ 𝓝 p, ∀ j, {v | ∀ f ∈ Wa, eval v f = 0} ∩ N ⊆ (γ j).slice) ∧
    ∀ j, ∃ H : (Fin (d + 1) → ℂ) → ℂ, DifferentiableOn ℂ H (Metric.ball 0 (γ j).radius) ∧
      (∀ t ∈ Metric.ball 0 (γ j).radius, H t ≠ 0) ∧
      ∀ t ∈ Metric.ball 0 (γ j).radius, eval ((γ j).toFun t) (map (Int.castRingHom ℂ) s) = t 0 ^ ord j * H t
end Objects
def ConeBranchLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (s : MRing ι) (a : K → ℕ) (W' : Ideal (MRing ι)) (Wa : Ideal (MRingOver ℂ ι))
    (p : (Σ k, ι k) → ℂ) (b : ℕ) (γ : Fin b → ConeBranch P (n + Fintype.card K + 1) p)
    (ord : Fin b → ℕ),
    IsArithVar P (n + 2) → IsMultiHomog s a → s ∉ P → W' ∈ divSupp P s → IsHorizontal W' →
    Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    ConeBranchesAt P s Wa p γ ord →
      multAt ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) Wa = ∑ j, ord j
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
def ptZeroOne : (Σ k : Unit, PBlk 2 k) → ℂ := fun q => if q.2 = 0 then 0 else 1
def lineFun (t : Fin 2 → ℂ) : (Σ k : Unit, PBlk 2 k) → ℂ := fun q => if q.2 = 0 then t 0 else 1 + t 1
theorem differentiable_lineFun : Differentiable ℂ lineFun := by
  refine differentiable_pi.2 fun q => ?_
  by_cases h : q.2 = 0
  · simp only [lineFun, h, if_true]
    exact differentiable_apply 0
  · simp only [lineFun, h, if_false]
    exact (differentiable_const 1).add (differentiable_apply 1)
def lineBranch : ConeBranch (⊥ : Ideal (MRing (PBlk 2))) 2 ptZeroOne where
  radius := 1 / 2
  radius_pos := by norm_num
  toFun := lineFun
  differentiableOn := differentiable_lineFun.differentiableOn
  continuousOn := differentiable_lineFun.continuous.continuousOn
  injOn := by
    intro t _ t' _ h
    funext i
    fin_cases i
    · have := congrFun h ⟨(), 0⟩
      simpa [lineFun] using this
    · have := congrFun h ⟨(), 1⟩
      simpa [lineFun] using this
  map_zero := by
    funext q
    simp only [lineFun, ptZeroOne]
    split_ifs <;> simp
  mapsTo := by
    intro t ht
    refine ⟨fun _ => ⟨1, ?_⟩, fun f hf => ?_⟩
    · show (if (1 : Fin 2) = 0 then t 0 else 1 + t 1) ≠ 0
      rw [if_neg (by decide)]
      have h1 : ‖t 1‖ ≤ 1 / 2 := (norm_le_pi_norm t 1).trans (mem_closedBall_zero_iff.mp ht)
      intro h
      have h2 : t 1 = -1 := by linear_combination h
      rw [h2, norm_neg, norm_one] at h1
      norm_num at h1
    · rw [Submodule.mem_bot] at hf
      simp [hf]
end Inhabitants
end GroundTheory.Heights₂.Heights.Targets


