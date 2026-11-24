-- Prove2me | Definitions.Def_ReserveLP_ProLPR_Supplement_WeightedModel
-- name    : ReserveLP_ProLPR_Supplement_WeightedModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:07:27.928097+00:00
-- url     : https://prove2.me/theorems/6254f734-ed2e-4015-b955-cf0ecbbc5b13
-- title:
--   §6, p. 18 — weighted revenue, weighted Profile-LP optimality, independent rounding and auction copies
-- statement:
--   Let $D$ be the published finite nonnegative bid data-set, with its two distinct auxiliary zero-bid buyers, and let $w_a$ be an auction weight. Define
--
--   $$W_D(w,r)=\sum_a w_a\mathrm{Rev}_a(r),\qquad L_D(w,s)=\sum_a w_a\sum_{p\in\mathcal P_a}s_{a,p}\mathrm{Rev}_a(p).$$
--
--   Weighted optimality means the original Profile-LP constraints and maximality of $L_D(w,s)$ over every feasible pair. Define $R_D(w,q)=\sum_{\rho\in\mathsf R^{\mathsf B}}(\prod_bq_{b,\rho_b})W_D(w,\rho)$ and $Z_D(w)=W_D(w,0)$. The comparison in Theorem 3 is $\max(R_D(w,q),Z_D(w))$, with the maximum outside the expectation.
--
--   For the replication convention, the copy indices are $(a,j)$ with $0\le j<\lfloor Nw_a\rfloor$; the copied bid is $\beta_{a,b}$. This defines the finite replication object, without asserting a convergence theorem in the definition file. At $N=1$ and integer positive weights it is exactly the source's integer replication.
--
--   These definitions extend the published auction model without changing LP feasibility or the product rounding law. Strict positivity of weights is imposed by the theorem; the sum formulas themselves are defined for all real weights. All expectations are finite sums. The sentinel reserve, distinct profile buyers and zero-on-empty revenue convention are inherited from the published model.
--
--   Differences from the source:
--   - generalization: the weighted model is introduced for strictly positive real auction weights and sufficiently large replication scale → the sum formulas accept all real weights and the copy operation accepts every natural scale N, using natural floor; reason: restriction to positive weights and large N gives exactly the source operation; nonpositive floor arguments and N=0 give no copies; the tightness theorem still requires strictly positive weights
--   - encoding: weighted revenue, independent reserve sampling and auction replication → finite sums with the published product law, a sigma type of copy indices, and copied DataSet fields; reason: these spell out the source operations without changing feasibility or placing the maximum inside expectation; no convergence theorem is asserted in this definition bundle
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 18, §6 weighted instance; pp. 18–19, Theorem 3

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR.Supplement

noncomputable section

open Finset

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]

/-- Weighted eager revenue, §6, p. 18. Positivity of weights is imposed in the theorem. -/
def weightedRev (D : DataSet A B) (w : A → ℝ) (r : B → ℝ) : ℝ :=
  ∑ a, w a * revA D a r

/-- Profile-LP with the weighted objective and the original constraints, p. 18. -/
def weightedLPObj (D : DataSet A B) (w : A → ℝ) (s : A → Profile B → ℝ) : ℝ :=
  ∑ a, w a * ∑ p ∈ validProfiles D a, s a p * revProfile D a p

/-- Maximality for the weighted objective; this is not unweighted LP optimality. -/
def weightedLPOptimal (D : DataSet A B) (w : A → ℝ)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) : Prop :=
  LPFeasible D s q ∧ ∀ s' q', LPFeasible D s' q' →
    weightedLPObj D w s' ≤ weightedLPObj D w s

/-- Expected weighted revenue of independent rounding, with no maximum inside the expectation. -/
def weightedRound (D : DataSet A B) (w : A → ℝ) (q : B → ℝ → ℝ) : ℝ :=
  ∑ ρ ∈ roundings D, roundProb q ρ * weightedRev D w ρ

/-- The deterministic all-zero reserve revenue. -/
def zeroRev (D : DataSet A B) (w : A → ℝ) : ℝ :=
  weightedRev D w (fun _ => 0)

/-- The auction indices for the floor(N w_a) copies in §6, p. 18. -/
def replicaAuctions (w : A → ℝ) (N : ℕ) : Type :=
  (a : A) × Fin ⌊(N : ℝ) * w a⌋₊

/-- Each replicated auction retains the original bid row and auxiliary buyers. -/
def replicaDataSet (D : DataSet A B) (w : A → ℝ) (N : ℕ) :
    DataSet (replicaAuctions w N) B where
  bid a b := D.bid a.1 b
  bid_nonneg a b := D.bid_nonneg a.1 b
  b0 := D.b0
  b00 := D.b00
  b0_ne_b00 := D.b0_ne_b00
  bid_b0 a := D.bid_b0 a.1
  bid_b00 a := D.bid_b00 a.1

end

end ReserveLP.ProLPR.Supplement


