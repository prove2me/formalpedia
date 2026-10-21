-- Prove2me | Definitions.Def_SeqRankAgg_Optimality_Model
-- name    : SeqRankAgg_Optimality_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:50.527001+00:00
-- url     : https://prove2.me/theorems/ccfc0dfa-89c2-4615-936b-8d7ec093ca71
-- title:
--   §2–§3.2 — sequential rank aggregation model, risk, stopping rules, and assumptions
-- statement:
--   Fix $K=m+1\ge2$ items and a parameter $\theta=(\theta_2,\ldots,\theta_K)$ with $\theta_1=0$. A pair $a=(i,j)$, $i<j$, produces a binary outcome with mass function $f^a_\theta(x)$, where $x=1$ means that item $i$ is preferred. A randomized comparison policy chooses the next pair from the observed history. The trajectory law is the published canonical bandit interaction law, with the pairs as arms and outcomes $0,1$ as rewards.
--
--   A terminal ranking is a permutation encoded by its pair decisions $R_{ij}$. Its Kendall loss, the Bayes risk of a comparison policy $\pi=(A,T,R)$, and the unrestricted optimal risk are
--
--   $$
--   L_K(\theta,R)=\sum_{i<j}\left[\mathbf1\{\theta_i>\theta_j\}(1-R_{ij})+\mathbf1\{\theta_i<\theta_j\}R_{ij}\right],\qquad
--   V_c(\rho,\pi)=\mathbb E_{\rho,\pi}[L_K+cT],\qquad
--   V_c^*(\rho)=\inf_{\pi}V_c(\rho,\pi).
--   $$
--
--   The infimum ranges over all randomized adaptive pair selectors, stopping times, and rankings measurable at the stopping time. The file also defines the prior support $W$, the comparison KL divergences $D^{i,j}(\theta\|\tilde\theta)$, the max–min information $D(\theta)$, $t_c(\theta)=|\log c|/D(\theta)$, both generalized likelihood ratio stopping rules $T_1,T_2$, the MLE and max–min selector predicates, the ε-greedy pair rule, and assumptions A1–A8. These definitions are shared by every result in the mission.
--
--   **Formalization Note** Parameters use $m$ coordinates and item indices are zero based. Rankings break score ties by item index. Risks and sample counts take values in $[0,\infty]$ so nontermination has infinite cost. The prior is a measurable probability density. The comparison mass function is positive, making its logarithm well defined. A2 uses sup-norm balls with centers in $W$; A4 is a uniform positive separation of differently ranked parameters in $W$ together with the page's own gloss of A4 (p. 11, "Assumption A4 requires that there is no tie in the support of the prior distribution"): no $\theta\in W$ has two equal scores $\theta_i=\theta_j$ (including $\theta_1=0$). A6 has an existential exponent and A8 is uniform over finite histories after the initial random comparison. The max–min value $D(\theta)$ is a supremum over the simplex and an infimum over the rank alternatives $\{\tilde\theta\in W:r(\tilde\theta)\ne r(\theta)\}$, each taken over exactly that set (as a subtype); the paper's max and min are these sup and inf whenever they are attained.
-- source:
--   Chen, Chen & Li, Asymptotically optimal sequential design for rank aggregation, arXiv:1710.06056v1, pp. 5–13, §2–§3.2, (2.1)–(2.5), (3.1)–(3.6), Assumptions A1–A8

import Mathlib
import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace SeqRankAgg.Optimality

abbrev Pair (m : ℕ) := {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2}
def numPairs (m : ℕ) : ℕ := Fintype.card (Pair m)
noncomputable def pairOf (m : ℕ) : Fin (numPairs m) ≃ Pair m :=
  (Fintype.equivFin (Pair m)).symm

def score {m : ℕ} (θ : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.cons 0 θ

/-- The paper's binary comparison mass function, with its induced arm laws. -/
structure CompModel (m : ℕ) where
  f : Pair m → (Fin m → ℝ) → Bool → ℝ
  pos : ∀ a θ x, 0 < f a θ x
  sum_one : ∀ a θ, f a θ true + f a θ false = 1
  measurable : ∀ a x, Measurable (fun θ => f a θ x)
  armLaw : (Fin m → ℝ) → Fin (numPairs m) → Measure ℝ
  armProb : ∀ θ a, IsProbabilityMeasure (armLaw θ a)
  armLaw_zero : ∀ θ a, armLaw θ a {0} = ENNReal.ofReal (f (pairOf m a) θ false)
  armLaw_one : ∀ θ a, armLaw θ a {1} = ENNReal.ofReal (f (pairOf m a) θ true)
  armLaw_support : ∀ θ a, armLaw θ a ({0, 1} : Set ℝ) = 1

noncomputable def bandit {m : ℕ} (M : CompModel m) (θ : Fin m → ℝ) :
    BanditAlgorithm.StochasticBandit (numPairs m) where
  P := M.armLaw θ
  prob := M.armProb θ

def W {m : ℕ} (ρ : (Fin m → ℝ) → ℝ≥0∞) : Set (Fin m → ℝ) :=
  closure {θ | 0 < ρ θ}

def Wij {m : ℕ} (ρ : (Fin m → ℝ) → ℝ≥0∞) (i j : Fin (m + 1)) :
    Set (Fin m → ℝ) :=
  {θ | score θ j ≤ score θ i} ∩ W ρ

noncomputable def rankDecision {m : ℕ} (θ : Fin m → ℝ) (i j : Fin (m + 1)) : Bool :=
  decide (score θ j < score θ i ∨ (score θ j = score θ i ∧ i < j))

/-- Equality of the paper's rankings, using the same deterministic tie convention as `rankDecision`. -/
def SameRank {m : ℕ} (θ θ' : Fin m → ℝ) : Prop :=
  ∀ i j : Fin (m + 1), rankDecision θ i j = rankDecision θ' i j

def simplex (N : ℕ) : Set (Fin N → ℝ) :=
  {wgt | (∀ a, 0 ≤ wgt a) ∧ ∑ a, wgt a = 1}

noncomputable def Dij {m : ℕ} (M : CompModel m) (a : Pair m)
    (θ θ' : Fin m → ℝ) : ℝ :=
  ∑ x : Bool, M.f a θ x * Real.log (M.f a θ x / M.f a θ' x)

/-- The rank alternatives of `θ` in the support: `{θ' ∈ W : r(θ') ≠ r(θ)}`, as a subtype. -/
abbrev Alt {m : ℕ} (ρ : (Fin m → ℝ) → ℝ≥0∞) (θ : Fin m → ℝ) : Type :=
  {θ' : Fin m → ℝ // θ' ∈ W ρ ∧ ¬ SameRank θ' θ}

/-- The inner minimum of (3.4)–(3.5): `inf_{θ' ∈ W, r(θ') ≠ r(θ)} Σ λ^{ij} D^{ij}(θ‖θ')`.
The infimum ranges over the subtype `Alt ρ θ`, so it is the infimum over exactly that set. -/
noncomputable def innerMin {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (θ : Fin m → ℝ) (wgt : Fin (numPairs m) → ℝ) : ℝ :=
  ⨅ θ' : Alt ρ θ, ∑ a : Fin (numPairs m), wgt a * Dij M (pairOf m a) θ θ'.1

/-- `D(θ)` of (3.4): the supremum over the simplex (a subtype) of the inner minimum. -/
noncomputable def Dfun {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (θ : Fin m → ℝ) : ℝ :=
  ⨆ wgt : simplex (numPairs m), innerMin M ρ θ wgt.1

noncomputable def tc {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (c : ℝ) (θ : Fin m → ℝ) : ℝ :=
  |Real.log c| / Dfun M ρ θ

noncomputable def Etc {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in W ρ, ρ θ * ENNReal.ofReal (tc M ρ c θ)

noncomputable def loglik {m n : ℕ} (M : CompModel m)
    (h : BanditAlgorithm.BanditHistory (numPairs m) n) (θ : Fin m → ℝ) : ℝ :=
  ∑ t : Fin n, Real.log (M.f (pairOf m (h t).1) θ ((h t).2 = 1))

noncomputable def loglikTraj {m : ℕ} (M : CompModel m) (n : ℕ)
    (ω : ℕ → Fin (numPairs m) × ℝ) (θ : Fin m → ℝ) : ℝ :=
  loglik M (BanditAlgorithm.banditTrajPrefix (numPairs m) n ω) θ

noncomputable def glr {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (n : ℕ)
    (ω : ℕ → Fin (numPairs m) × ℝ) (a : Pair m) : ℝ :=
  |sSup (loglikTraj M n ω '' Wij ρ a.1.1 a.1.2) -
   sSup (loglikTraj M n ω '' Wij ρ a.1.2 a.1.1)|

noncomputable def hc (αh c : ℝ) : ℝ :=
  |Real.log c| * (1 + |Real.log c| ^ (-αh))

noncomputable def T1 {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (αh c : ℝ)
    (ω : ℕ → Fin (numPairs m) × ℝ) : ℕ∞ :=
  ⨅ n : ℕ, ⨅ _ : 2 ≤ n ∧
      (∑ a : Pair m, Real.exp (-(glr M ρ n ω a))) ≤ Real.exp (-(hc αh c)),
    (n : ℕ∞)

noncomputable def T2 {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (αh c : ℝ)
    (ω : ℕ → Fin (numPairs m) × ℝ) : ℕ∞ :=
  ⨅ n : ℕ, ⨅ _ : 2 ≤ n ∧ (∀ a : Pair m, hc αh c ≤ glr M ρ n ω a),
    (n : ℕ∞)

abbrev Trajectory (m : ℕ) := ℕ → Fin (numPairs m) × ℝ
abbrev Ranking (m : ℕ) := Fin (m + 1) → Fin (m + 1) → Bool

/-- A selection rule, a stopping time, and a terminal ranking. -/
structure Policy (m : ℕ) where
  A : BanditAlgorithm.BanditPolicy (numPairs m)
  T : Trajectory m → ℕ∞
  R : Trajectory m → Ranking m

def IsAdmissible {m : ℕ} (π : Policy m) : Prop :=
  BanditAlgorithm.IsBanditStoppingTime π.T ∧
  (∀ ω, ∃ σ : Equiv.Perm (Fin (m + 1)),
    ∀ i j, π.R ω i j = decide (σ i < σ j)) ∧
  ∃ hT : BanditAlgorithm.IsBanditStoppingTime π.T,
    Measurable[hT.measurableSpace] π.R

noncomputable def kendall {m : ℕ} (θ : Fin m → ℝ) (R : Ranking m) : ℕ :=
  ∑ a : Pair m,
    ((if score θ a.1.2 < score θ a.1.1 ∧ R a.1.1 a.1.2 = false then 1 else 0) +
     (if score θ a.1.1 < score θ a.1.2 ∧ R a.1.1 a.1.2 = true then 1 else 0))

noncomputable def bayesRisk {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (c : ℝ) (π : Policy m) : ℝ≥0∞ :=
  ∫⁻ θ, ρ θ * ∫⁻ ω, ((kendall θ (π.R ω) : ℝ≥0∞) +
      ENNReal.ofReal c * (π.T ω : ℝ≥0∞))
    ∂BanditAlgorithm.banditTrajMeasure (bandit M θ) π.A

noncomputable def optRisk {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (c : ℝ) : ℝ≥0∞ :=
  ⨅ π : Policy m, ⨅ _ : IsAdmissible π, bayesRisk M ρ c π

noncomputable def expectedKendall {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (π : Policy m) : ℝ≥0∞ :=
  ∫⁻ θ, ρ θ * ∫⁻ ω, (kendall θ (π.R ω) : ℝ≥0∞)
    ∂BanditAlgorithm.banditTrajMeasure (bandit M θ) π.A

noncomputable def expectedT {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) (π : Policy m) : ℝ≥0∞ :=
  ∫⁻ θ, ρ θ * ∫⁻ ω, (π.T ω : ℝ≥0∞)
    ∂BanditAlgorithm.banditTrajMeasure (bandit M θ) π.A

def IsMLESelector {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ)) : Prop :=
  (∀ n, Measurable (θhat n)) ∧
  ∀ n h, θhat n h ∈ W ρ ∧ ∀ θ ∈ W ρ, loglik M h θ ≤ loglik M h (θhat n h)

def IsMaxMinSelector {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ) : Prop :=
  Measurable lamStar ∧ ∀ θ ∈ W ρ,
    lamStar θ ∈ simplex (numPairs m) ∧
    ∀ wgt ∈ simplex (numPairs m), innerMin M ρ θ wgt ≤ innerMin M ρ θ (lamStar θ)

def A1 {m : ℕ} (ρ : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  IsCompact (W ρ) ∧
  ∀ σ : Equiv.Perm (Fin (m + 1)),
    (interior {θ ∈ W ρ | ∀ i j,
      rankDecision θ i j = decide (σ i < σ j)}).Nonempty

def A2 {m : ℕ} (ρ : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  ∃ δb : ℝ, 0 < δb ∧ ∀ θ ∈ W ρ, ∀ s : ℝ, 0 < s →
    min (δb * s ^ m) 1 ≤ (volume (Metric.ball θ s ∩ W ρ)).toReal

def A3 {m : ℕ} (M : CompModel m) (ρ : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  (∀ a x, ContDiff ℝ 1 (fun θ => Real.log (M.f a θ x))) ∧
  ∃ κ : ℝ, ∀ θ ∈ W ρ, ∀ a x,
    ‖fderiv ℝ (fun θ' => Real.log (M.f a θ' x)) θ‖ ≤ κ

/-- A4, p. 11: the rank alternatives in the support are separated in KL divergence, and (the page's
gloss of A4, p. 11: "Assumption A4 requires that there is no tie in the support of the prior
distribution") no parameter in the support has two items with equal scores. -/
def A4 {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  (∀ θ ∈ W ρ, Function.Injective (score θ)) ∧
  ∃ η : ℝ, 0 < η ∧ ∀ θ ∈ W ρ, ∀ θ' ∈ W ρ,
    ¬ SameRank θ' θ → ∃ a : Pair m, η ≤ Dij M a θ θ'

def A5 {m : ℕ} (ρ : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ (∫⁻ θ, ρ θ) = 1 ∧
  (∃ lo : ℝ≥0∞, 0 < lo ∧ ∀ θ ∈ interior (W ρ), lo ≤ ρ θ) ∧
  (∃ hi : ℝ≥0∞, hi < ⊤ ∧ ∀ θ ∈ W ρ, ρ θ ≤ hi)

def A7 {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  ∀ θ ∈ W ρ, ∀ θ' ∈ W ρ, θ ≠ θ' →
    ∃ a : Pair m, ∃ x : Bool, M.f a θ x ≠ M.f a θ' x

def A6 {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m)) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ᶠ c in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    ∀ θ ∈ W ρ, ∀ᵐ ω ∂BanditAlgorithm.banditTrajMeasure (bandit M θ) (Afam c),
      ∀ n a, ENNReal.ofReal (|Real.log c| ^ (-(1 / 2 : ℝ) + δ0)) ≤
        (Afam c).select n (BanditAlgorithm.banditTrajPrefix (numPairs m) n ω) {a}

def A8 {m : ℕ}
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ)
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m)) : Prop :=
  Tendsto (fun c => ⨆ n : ℕ, ⨆ h : BanditAlgorithm.BanditHistory (numPairs m) (n + 1),
    ∑ a : Fin (numPairs m),
      |lamStar (θhat (n + 1) h) a - ((Afam c).select (n + 1) h {a}).toReal|)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)

/-- The exploration probability, clipped to the probability interval away from the limit. -/
noncomputable def pExp (δ0 C c : ℝ) : ℝ :=
  min 1 (C * |Real.log c| ^ (-(1 / 2 : ℝ) + δ0))

/-- The categorical pair law of Algorithm 1, with a uniform first round. -/
def IsEpsGreedyFamily {m : ℕ}
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ)
    (p : ℝ → ℝ)
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m)) : Prop :=
  ∀ c ∈ Set.Ioo (0 : ℝ) 1,
    (∀ h : BanditAlgorithm.BanditHistory (numPairs m) 0,
      ∀ a : Fin (numPairs m),
        (Afam c).select 0 h {a} = ENNReal.ofReal (1 / (numPairs m : ℝ))) ∧
    (∀ n : ℕ, ∀ h : BanditAlgorithm.BanditHistory (numPairs m) (n + 1),
      ∀ a : Fin (numPairs m),
        (Afam c).select (n + 1) h {a} =
          ENNReal.ofReal (p c / (numPairs m : ℝ) +
            (1 - p c) * lamStar (θhat (n + 1) h) a))

noncomputable def mleRank {m : ℕ}
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (T : Trajectory m → ℕ∞) (ω : Trajectory m) : Ranking m :=
  let n := (T ω).untopD 0
  rankDecision (θhat n (BanditAlgorithm.banditTrajPrefix (numPairs m) n ω))

def IsProposedFamily {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (lamStar : (Fin m → ℝ) → Fin (numPairs m) → ℝ)
    (αh δ0 C : ℝ) (i : Fin 2) (πfam : ℝ → Policy m) : Prop :=
  IsEpsGreedyFamily θhat lamStar (pExp δ0 C) (fun c => (πfam c).A) ∧
  ∀ c ∈ Set.Ioo (0 : ℝ) 1,
    IsAdmissible (πfam c) ∧
    (πfam c).T = (if i = 0 then T1 M ρ αh c else T2 M ρ αh c) ∧
    (πfam c).R = mleRank θhat (πfam c).T

def IsGeneralFamily {m : ℕ} (M : CompModel m)
    (ρ : (Fin m → ℝ) → ℝ≥0∞)
    (θhat : (n : ℕ) → BanditAlgorithm.BanditHistory (numPairs m) n → (Fin m → ℝ))
    (αh : ℝ) (i : Fin 2)
    (Afam : ℝ → BanditAlgorithm.BanditPolicy (numPairs m))
    (πfam : ℝ → Policy m) : Prop :=
  ∀ c ∈ Set.Ioo (0 : ℝ) 1,
    IsAdmissible (πfam c) ∧ (πfam c).A = Afam c ∧
    (πfam c).T = (if i = 0 then T1 M ρ αh c else T2 M ρ αh c) ∧
    (πfam c).R = mleRank θhat (πfam c).T

end SeqRankAgg.Optimality


