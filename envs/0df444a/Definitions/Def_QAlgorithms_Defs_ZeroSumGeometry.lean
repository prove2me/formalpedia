-- Prove2me | Definitions.Def_QAlgorithms_Defs_ZeroSumGeometry
-- name    : QAlgorithms_Defs_ZeroSumGeometry
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:13:49.205125+00:00
-- url     : https://prove2.me/theorems/d70decde-2efe-4979-9de3-6c746d96cb79
-- title:
--   ZeroSumGeometry
-- statement:
--   ZeroSumGeometry
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ZeroSumGeometry.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped ENNReal

namespace QAlgorithms.ZeroSum

variable {n m d k b w M K N c out : ℕ}

/-- Source matrix-game domain: nonempty move sets and entries in [-1,1],
1904.03180 pp.1–2. -/
structure Game (n m : ℕ) where
  n_pos : 0 < n
  m_pos : 0 < m
  payoff : Matrix (Fin n) (Fin m) ℝ
  bounded : ∀ i j, |payoff i j| ≤ 1

/-- Value of the constrained minimax problem (1904.03180 pp.1–2, Eq.(1)).
The finite maximum is nonempty and the infimum ranges only over strategies. -/
def gameValue {n m : ℕ} (A : Game n m) : ℝ :=
  sInf {v | ∃ y : Fin m → ℝ, Learning.IsDistribution y ∧
    v = Finset.univ.sup' (by exact Finset.univ_nonempty_iff.mpr ⟨⟨0, A.n_pos⟩⟩)
      (A.payoff.mulVec y)}

/-- Separate value-relative epsilon optimality conditions for the two
normalized strategies, 1904.03180 p.2 (not merely payoff error). -/
def IsEpsOptimalPair {n m : ℕ} (A : Game n m) (eps : ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  Learning.IsDistribution x ∧ Learning.IsDistribution y ∧
    (∀ i, A.payoff.mulVec y i ≤ gameValue A + eps) ∧
    ∀ j, gameValue A - eps ≤ A.payoff.transpose.mulVec x j

/-- Classical finite Gibbs PMF, 1904.03180 p.3 and Definition 5 p.7.
Positive exponential weights and a nonempty type exclude zero mass. -/
def classicalGibbs {I : Type*} [Fintype I] [Nonempty I] (v : I → ℝ) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (Real.exp (v i) / ∑ j, Real.exp (v j))) (by
    have hs : 0 < ∑ j, Real.exp (v j) :=
      Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (Real.exp_pos _).le hs.le)]
    rw [← Finset.sum_div, div_self hs.ne']
    simp)

/-- Sanity check for the modeled source objects (arxiv-1904.03180v1, PDF pp.1,2,3,6,7). -/
example (v : Unit → ℝ) : classicalGibbs v () = 1 := by
  simp [classicalGibbs, PMF.ofFintype_apply, (Real.exp_pos (v ())).ne']

/-- Sanity check for the modeled source objects (arxiv-1904.03180v1, PDF pp.1,2,3,6,7). -/
example : gameValue (⟨by decide, by decide, 0, by simp⟩ : Game 1 1) = 0 := by
  have hs : {v : ℝ | ∃ y : Fin 1 → ℝ, Learning.IsDistribution y ∧
      v = Finset.univ.sup' (by exact Finset.univ_nonempty_iff.mpr ⟨(0 : Fin 1)⟩)
        ((0 : Matrix (Fin 1) (Fin 1) ℝ).mulVec y)} = {0} := by
    ext v
    simp only [Matrix.zero_mulVec, Finset.sup'_const, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, _, h⟩; exact h
    · intro h; exact ⟨fun _ => 1, ⟨by simp, by simp⟩, h⟩
  change sInf _ = 0
  rw [hs, csInf_singleton]

end QAlgorithms.ZeroSum


