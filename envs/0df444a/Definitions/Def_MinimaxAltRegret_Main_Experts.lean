-- Prove2me | Definitions.Def_MinimaxAltRegret_Main_Experts
-- name    : MinimaxAltRegret_Main_Experts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:49.584123+00:00
-- url     : https://prove2.me/theorems/bb2289f9-41fb-41f8-80cc-a6ebafaf5b21
-- title:
--   Expert losses, corrected AltHedge, and the corrected potential
-- statement:
--   For d positive, the action set is the probability simplex Delta_d, and the loss of p under ell is its dot product with ell. Loss coordinates belong to [-1,1]. Given a score R and eta, let q_i=exp(eta R_i)/sum_j exp(eta R_j), m=sum_i q_i ell_i, a_i=ell_i-m, and H=sum_i q_i a_i^2. The corrected action is
--
--   $$p_i=q_i\left[1-4\eta a_i-2\eta^2(a_i^2-H)\right].$$
--
--   The scores start at zero and satisfy R_t=R_(t-1)-(ell_(t-1)+ell_t). The maps implement Algorithm 1 at eta=1/10, including the terminal corrected action and analysis score. They also define F(R)=eta^(-1) log(d^(-1) sum_i exp(eta R_i)), U_alpha=F-alpha eta Var_q(ell), and the full real interpolation G_alpha(theta)=U_alpha(R-theta z,ell-theta z).
--
--   These are the finite objects shared by the feasibility, differential, and regret statements. The simplex itself is Mathlib's `stdSimplex`; its feasibility is a theorem, not an assumed property of the formula.
--
--   **Formalization Note** The expert regret uses a real supremum. The nonempty finite simplex is compact and the comparator objective is continuous, so this equals the source's attained maximum.
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 5 / PDF p. 6, Eq. (4), Algorithm 1 (printed p. 6 / PDF p. 7), Eqs. (5), (9), (10), (12); SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Protocol

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

abbrev ExpertVector (d : ℕ) := Fin d → ℝ
abbrev ExpertAction (d : ℕ) := ↥(stdSimplex ℝ (Fin d))

def expertLosses (d T : ℕ) (ℓ : ℕ → ExpertVector d) : Prop :=
  ∀ t < T, ∀ i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1

def expertDot {d : ℕ} (p ℓ : ExpertVector d) : ℝ := ∑ i, p i * ℓ i

def expertRegret {d : ℕ} (T : ℕ) (ℓ p : ℕ → ExpertVector d) : ℝ :=
  alternatingRegret (stdSimplex ℝ (Fin d)) T (fun t u => expertDot u (ℓ t)) p

def expertEW {d : ℕ} (η : ℝ) (R : ExpertVector d) (i : Fin d) : ℝ :=
  Real.exp (η * R i) / ∑ j, Real.exp (η * R j)

def expertMean {d : ℕ} (q v : ExpertVector d) : ℝ := ∑ i, q i * v i

def expertCentered {d : ℕ} (q v : ExpertVector d) (i : Fin d) : ℝ :=
  v i - expertMean q v

def expertVariance {d : ℕ} (q v : ExpertVector d) : ℝ :=
  expertMean q (fun i => (expertCentered q v i)^2)

def expertF {d : ℕ} (η : ℝ) (R : ExpertVector d) : ℝ :=
  Real.log ((∑ i, Real.exp (η*R i)) / (d : ℝ)) / η

def expertU {d : ℕ} (α η : ℝ) (R ℓ : ExpertVector d) : ℝ :=
  expertF η R - α*η*expertVariance (expertEW η R) ℓ

def expertG {d : ℕ} (α η : ℝ) (R ℓ z : ExpertVector d) (θ : ℝ) : ℝ :=
  expertU α η (fun i => R i - θ*z i) (fun i => ℓ i - θ*z i)

/-- Eq. (4), from a known pre-update score and previous loss; eta occurs once in EW. -/
def expertCorrection {d : ℕ} (η : ℝ) (R ℓ : ExpertVector d) (i : Fin d) : ℝ :=
  let q := expertEW η R
  let a := expertCentered q ℓ
  let H := expertVariance q ℓ
  q i * (1 - 4*η*a i - 2*η^2*(a i^2-H))

/-- Source loss ell_(t+1), padded by zero at and after the horizon. -/
def expertPadded {d : ℕ} (T : ℕ) (ℓ : ℕ → ExpertVector d) (t : ℕ) : ExpertVector d :=
  if t < T then ℓ t else 0

/-- Source loss ell_t, including ell_0=0. -/
def expertPrevious {d : ℕ} (T : ℕ) (ℓ : ℕ → ExpertVector d) : ℕ → ExpertVector d
  | 0 => 0
  | t+1 => expertPadded T ℓ t

/-- Score R_t; at t=T+1 it is the analysis score -2 sum ell_t. -/
def expertScore {d : ℕ} (T : ℕ) (ℓ : ℕ → ExpertVector d) (t : ℕ) (i : Fin d) : ℝ :=
  - ∑ s ∈ Finset.range t, (expertPrevious T ℓ s i + expertPadded T ℓ s i)

/-- Algorithm 1's actual action p_(t+1), including its terminal action at t=T. -/
def expertAlgorithm {d : ℕ} (T : ℕ) (ℓ : ℕ → ExpertVector d) (t : ℕ) : ExpertVector d :=
  expertCorrection (1/10) (expertScore T ℓ t) (expertPrevious T ℓ t)

end MinimaxAltRegret.Main


