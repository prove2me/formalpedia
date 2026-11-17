-- Prove2me | Definitions.Def_IntervalToDynamic_Supplement_Algorithms34
-- name    : IntervalToDynamic_Supplement_Algorithms34
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:38:17.328723+00:00
-- url     : https://prove2.me/theorems/ef441851-280d-4b2e-9957-4d027db5d9f3
-- title:
--   Algorithms 3–4 for polynomial interval regret
-- statement:
--   The **Algorithms 3–4 contract** records the complete theorem-visible implementation used by Theorem 9. It includes the dyadic geometric cover $\mathcal G_T$ and active intervals; an interval-normalized orthonormal basis of degree-at-most-$(k-1)$ polynomial restrictions; the coefficient domain $\mathcal K_J$ that forces every base prediction to remain in $\mathcal Y$; the convex OGD, exp-concave ONS and strongly convex specialized ONS coefficient updates with their printed projection metrics and regularizers; and Algorithm 4's active-learner aggregation with uniform priors, ML-Prod rates in the convex branch, and exponential-weight updates in the curved branches.
--
--   The aggregate decision agrees with a history-map online algorithm, so it is nonanticipating. A domain-relative gradient oracle realizes the gradients observed by the pseudocode without imposing ambient differentiability at the boundary, and the ONS state matrices are updated on every active round, including the interval's last round. The contract contains only the recurrences and feasibility conditions; polynomial interval-regret rates are conclusions of Theorem 9, not fields of the algorithm object.
--
--   **Formalization Note** Coefficient matrices are flattened only for the exp-concave Hessian. The strongly convex branch uses one $r_J\times r_J$ matrix on every row, exactly as Algorithm 3. Computational-cost claims from Appendix C.5 are excluded.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithms 3–4 and Eqs. (45)–(55), pp.43–50 (PDF pp.45–52)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_Geometry
import Definitions.Def_IntervalToDynamic_Supplement_HigherVariation
import Definitions.Def_IntervalToDynamic_OnlineAlgorithm
import Definitions.Def_IntervalToDynamic_decisions
import Definitions.Def_IntervalToDynamic_LossMode

namespace IntervalToDynamic.Supplement

abbrev Coeff (d r : ℕ) := Fin d × Fin r → ℝ

def rank (k : ℕ) {T : ℕ} (J : RoundInterval T) : ℕ := min k J.rounds.card

def evalCoeff {d r : ℕ} (W : Coeff d r) (phi : Fin r → ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ∑ j, W (i, j) * phi j)

def outerCoeff {d r : ℕ} (g : EuclideanSpace ℝ (Fin d)) (phi : Fin r → ℝ) :
    Coeff d r := fun ij => g ij.1 * phi ij.2

def coeffFeasible {d r : ℕ} {T : ℕ} (J : RoundInterval T) (DY : ℝ)
    (phi : ℕ → Fin r → ℝ) : Set (Coeff d r) :=
  {W | ∀ t ∈ J.rounds, ‖evalCoeff W (phi t)‖ ≤ DY / 2}

def sqDist {d r : ℕ} (U V : Coeff d r) : ℝ := ∑ ij, (U ij - V ij) ^ 2

def matrixDist {d r : ℕ} (H : Matrix (Fin d × Fin r) (Fin d × Fin r) ℝ)
    (U V : Coeff d r) : ℝ :=
  dotProduct (U - V) (H.mulVec (U - V))

def rowMatrixDist {d r : ℕ} (V : Matrix (Fin r) (Fin r) ℝ)
    (U W : Coeff d r) : ℝ :=
  ∑ i, dotProduct (fun j => U (i, j) - W (i, j))
    (V.mulVec (fun j => U (i, j) - W (i, j)))

def IsProjectionBy {C : Type*} (K : Set C) (dist : C → C → ℝ)
    (target next : C) : Prop :=
  next ∈ K ∧ ∀ U ∈ K, dist next target ≤ dist U target

/-- The theorem-visible contract of Algorithms 3 and 4 (Appendix C, pp.43--50): the dyadic
geometric cover, interval-normalized polynomial bases, coefficient-domain projections, the three
OGD/ONS base updates, and the ML-Prod/exponential-weights aggregation updates.

An inhabitant is an actual horizon-aware online algorithm, because its aggregate decision agrees
with `decisions A h t`, which depends only on losses before `t`. -/
structure Algorithms34 (mode : IntervalToDynamic.LossMode) (T d k : ℕ) (DY Gh : ℝ) where
  cover : Finset (RoundInterval T)
  cover_exact : ∀ J, J ∈ cover ↔ ∃ j s : ℕ,
    J.start = j * 2 ^ s + 1 ∧ J.stop = (j + 1) * 2 ^ s ∧ J.stop ≤ T
  phi : (J : RoundInterval T) → ℕ → Fin (rank k J) → ℝ
  basis_polynomial : ∀ J i, ∀ t ∈ Finset.Icc (J.start + k) J.stop,
    kthDifference k (fun s => phi J s i) t = 0
  basis_orthonormal : ∀ J i j,
    (1 / J.rounds.card : ℝ) * ∑ t ∈ J.rounds, phi J t i * phi J t j =
      if i = j then 1 else 0
  W : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) →
    (J : RoundInterval T) → ℕ → Coeff d (rank k J)
  H : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → (J : RoundInterval T) → ℕ →
    Matrix (Fin d × Fin (rank k J)) (Fin d × Fin (rank k J)) ℝ
  V : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → (J : RoundInterval T) → ℕ →
    Matrix (Fin (rank k J)) (Fin (rank k J)) ℝ
  weight : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → RoundInterval T → ℕ → ℝ
  probability : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → RoundInterval T → ℕ → ℝ
  A : IntervalToDynamic.OnlineAlgorithm (EuclideanSpace ℝ (Fin d))
  grad : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → ℕ →
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  grad_spec : ∀ h t,
    DifferentiableOn ℝ (h t)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2)) →
    ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2),
      HasGradientWithinAt (h t) (grad h t y)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2)) y
  initial_coeff : ∀ h J, W h J J.start = 0
  exp_initial : ∀ alpha, mode = .expConcave alpha → ∀ h J,
    H h J (J.start - 1) = (d * rank k J : ℝ) • 1
  strong_initial : ∀ lam, mode = .stronglyConvex lam → ∀ h J,
    V h J (J.start - 1) = (rank k J : ℝ) • 1
  base_feasible : ∀ h J t, t ∈ J.rounds →
    W h J t ∈ coeffFeasible J DY (phi J)
  convex_update : mode = .convex → ∀ h J t, t ∈ J.rounds → t < J.stop →
    let y := evalCoeff (W h J t) (phi J t)
    let G := outerCoeff (grad h t y) (phi J t)
    let eta := DY / (2 * Gh * max (6 * (k - 1) : ℝ) (Real.sqrt k) * Real.sqrt J.rounds.card)
    IsProjectionBy (coeffFeasible J DY (phi J)) sqDist (W h J t - eta • G) (W h J (t + 1))
  exp_state_update : ∀ alpha, mode = .expConcave alpha → ∀ h J t, t ∈ J.rounds →
    let y := evalCoeff (W h J t) (phi J t)
    let G := outerCoeff (grad h t y) (phi J t)
    H h J t = H h J (t - 1) + Matrix.vecMulVec G G
  exp_coeff_update : ∀ alpha, mode = .expConcave alpha →
      ∀ h J t, t ∈ J.rounds → t < J.stop →
    let y := evalCoeff (W h J t) (phi J t)
    let G := outerCoeff (grad h t y) (phi J t)
    let gamma := (1 / 2) * min alpha (1 / (DY * Gh))
    IsProjectionBy (coeffFeasible J DY (phi J)) (matrixDist (H h J t))
      (W h J t - (gamma⁻¹) • ((H h J t)⁻¹).mulVec G) (W h J (t + 1))
  strong_state_update : ∀ lam, mode = .stronglyConvex lam → ∀ h J t, t ∈ J.rounds →
    V h J t = V h J (t - 1) + lam • Matrix.vecMulVec (phi J t) (phi J t)
  strong_coeff_update : ∀ lam, mode = .stronglyConvex lam →
      ∀ h J t, t ∈ J.rounds → t < J.stop →
    let y := evalCoeff (W h J t) (phi J t)
    let G := outerCoeff (grad h t y) (phi J t)
    IsProjectionBy (coeffFeasible J DY (phi J)) (rowMatrixDist (V h J t))
      (fun ij => W h J t ij - ∑ l, G (ij.1, l) * ((V h J t)⁻¹) l ij.2) (W h J (t + 1))
  prior : ∀ h J, weight h J 1 = 1 / cover.card
  probabilities : ∀ h J t, J ∈ cover → t ∈ J.rounds →
    probability h J t =
      match mode with
      | .convex =>
          let eps := min (1 / 2 : ℝ) (Real.sqrt (Real.log cover.card / J.rounds.card))
          eps * weight h J t /
            ∑ K ∈ cover.filter (fun K => t ∈ K.rounds),
              min (1 / 2 : ℝ) (Real.sqrt (Real.log cover.card / K.rounds.card)) * weight h K t
      | _ => weight h J t /
          ∑ K ∈ cover.filter (fun K => t ∈ K.rounds), weight h K t
  aggregate : ∀ h t, t ∈ Finset.Icc 1 T →
    IntervalToDynamic.decisions A h t =
      ∑ J ∈ cover.filter (fun J => t ∈ J.rounds),
        probability h J t • evalCoeff (W h J t) (phi J t)
  weights_update : ∀ h J t, J ∈ cover → t ∈ Finset.Icc 1 T →
    weight h J (t + 1) = if t ∈ J.rounds then
      match mode with
      | .convex =>
          let eps := min (1 / 2 : ℝ) (Real.sqrt (Real.log cover.card / J.rounds.card))
          weight h J t * (1 + eps *
            (h t (IntervalToDynamic.decisions A h t) - h t (evalCoeff (W h J t) (phi J t))) / (DY * Gh))
      | .expConcave alpha => weight h J t * Real.exp
          (alpha * (h t (IntervalToDynamic.decisions A h t) - h t (evalCoeff (W h J t) (phi J t))))
      | .stronglyConvex lam => weight h J t * Real.exp
          ((lam / Gh ^ 2) * (h t (IntervalToDynamic.decisions A h t) -
            h t (evalCoeff (W h J t) (phi J t))))
      else weight h J t

end IntervalToDynamic.Supplement


