-- Prove2me | Definitions.Def_ConsistentSubmodular_MainStatements
-- name    : ConsistentSubmodular_MainStatements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:06:29.77821+00:00
-- url     : https://prove2.me/theorems/a31a1432-02e3-4d81-bacd-67766aefe553
-- title:
--   Model, window instances, certificates and the paper's numbered results (Theorems 1-7, Lemmas 1-6, B.1-B.7, Proposition 1, Main Results 1-2)
-- statement:
--   **Conventions.** Elements of the stream are indexed by `Fin n`; all sets are `Finset`s. Throughout, `k` is the cardinality budget, `C` or `R` a consistency (recourse) bound, and `ξ⋆` the threshold defined below.
--
--   ## Model
--
--   - `Objective n`: a set function `f : 2^{[n]} → ℝ` (`value`) that is nonnegative, monotone, and submodular in the form $f(A\cup B)+f(A\cap B)\le f(A)+f(B)$. The value at $\emptyset$ may be nonzero.
--   - `arrivedPrefix n t`: the prefix $X_t=\{e : e<t\}$ of elements arrived after $t$ steps.
--   - `recourse A B`: $|A\triangle B|=|A\setminus B|+|B\setminus A|$.
--   - `FeasibleTrajectory k C S`: a sequence $S_0,\dots,S_n$ with $S_0=\emptyset$, $S_t\subseteq X_t$, $|S_t|\le k$ for all $t$, and $|S_{t+1}\triangle S_t|\le C$ for every update.
--   - `RandomTrajectory n`: a finitely supported probability law `prob` on trajectories $(S_t)_{t\le n}$ (nonnegative weights summing to $1$). `Feasible k C` means every trajectory of nonzero weight is feasible; `expectation g t` is $\sum_S \mathrm{prob}(S)\,g(S_t)$.
--   - `ConsistentGuarantee α ε R`: for all `n, k` and every objective $f$ there is a feasible trajectory with recourse $\le R$ such that $f(S_t)\ge(\alpha-\varepsilon)f(A)$ for all $t$ and all $A\subseteq X_t$, $|A|\le k$ (deterministic clairvoyant algorithm).
--   - `RandomizedGuarantee α ε C`: the same with a random trajectory, every realization $C$-consistent and $\mathbb E f(S_t)\ge(\alpha-\varepsilon)f(A)$.
--   - `coverageValue cover A` $=|\bigcup_{e\in A}\mathrm{cover}(e)|$ (unweighted coverage). `independentExpectation U z g` $=\sum_{S\subseteq U}\prod_{e\in S}z_e\prod_{e\in U\setminus S}(1-z_e)\,g(S)$.
--   - `psi` $\Psi(\xi)=89\xi^4-44\xi^3-19\xi^2-3\xi+1$; `xiStar` $=\xi^\star=\sup\{\xi\in(1/2,1):\Psi(\xi)=0\}\approx0.7942$; `phi` $\Phi(x)=x^4+x^3-2x^2-3x+2$.
--
--   ## Window instances and addition robustness
--
--   - `Point m` $=\{0,\dots,m\}\to\mathbb R$; `IsSimplex p`: $p\ge0$, $\sum_i p_i=1$; `vertex i` is the unit vector $\delta_i$; `mix p q x` $=(1-x)p+xq$.
--   - `WindowInstance n`: an objective $f$, a set `present` $=V_{now}$, a budget $\kappa=$`coreBudget`, a last stage $m=$`lastStage`, nested arrival prefixes $\emptyset=R_0\subseteq\dots\subseteq R_m$ disjoint from `present`, and candidates $O_j\subseteq V_{now}$, $|O_j|\le\kappa$, with $O_j$ maximizing $f(O\cup R_j)$ among such sets. `SingleArrivals`: $R_{j+1}=R_j\cup\{v_{j+1}\}$ with $v_{j+1}\notin R_j$. `benchmark j` $=P_j=f(O_j\cup R_j)$.
--   - `IsAdditionRobust α w` (Definition 2.1): $w$ is a probability law on sets $S\subseteq V_{now}$, $|S|\le\kappa$, with $\sum_S w_S f(S\cup R_j)\ge\alpha P_j$ for all $j$. `AdmitsAdditionRobust α`: every `SingleArrivals` window instance has such a $w$.
--   - `lpValue` $=\rho^\star$, the largest $\rho\in[0,1]$ for which some $a\in\Delta$ has $\sum_i a_i f(O_i\cup R_j)\ge\rho P_j$ for all $j$ (LP (1)); `payoff i j` $=f(O_i\cup R_j)/P_j$.
--
--   ## Interval selection
--
--   - `IntervalInstance N`: intervals $[\ell_i,r_i]$, $0\le\ell_i\le r_i$, $i\in\{0..N\}$, with a probability vector $p$. `value i j` $=v(i,j)=\ell_j+\max(0,r_i-\max(\ell_i,\ell_j))$; `fixedValue` $=\max_i\sum_j p_jv(i,j)$; `adaptiveValue` $=\sum_jp_j\max_iv(i,j)$; `adaptivityGap` $=\Gamma$ is their ratio (Definition 2.2), set to $1$ if the denominator is $0$.
--   - `IsNonincreasingConsecutive`: $\ell_0=0$, $\ell_{i+1}=r_i$, lengths $r_i-\ell_i$ nonincreasing and the last one positive; `IsEqualizing`: $\sum_jp_jv(i,j)$ is the same for all $i$ (Definition 2.3).
--
--   ## Certificates (Section 3 / Appendix B)
--
--   - `PolygonalPath m`: nodes $\gamma_0,\dots,\gamma_{\text{pieces}}$ in `Point m`; `Along γ Φ`: $\Phi$ holds at every node and every point of every segment.
--   - `mixtureValue j p` $=H_j(p)=\sum_{I}\prod_{i\in I}p_i\prod_{i\notin I}(1-p_i)\,f(R_j\cup\bigcup_{i\in I}O_i)$ (equation (3)); `bufferMixtureValue Q p` $=H_Q(p)$ is the same with a fixed buffer $Q$ in place of $R_j$.
--   - `Certificate α L` (Definition 3.1): an anchor $p\in\Delta$, an entry path from $\delta_0$ to $p$ and an exit path from $p$ to $\delta_m$, both inside $\Delta$, with $H_j(p)\ge\alpha P_j$ for all $j$, the entry path safe ($H_0\ge\alpha P_0$ along it), the exit path safe at stage $m$, and total number of segments $\le L$. `AdmitsCertificates α L` / `AdmitsArrivalCertificates α L` ask for an $(\alpha,L(m))$-certificate for every window instance / every `SingleArrivals` one.
--
--   ## Grid stream and auxiliary quantities
--
--   - `gridStreamCover k m`: the coverage sets of the stream $\Sigma=A\circ B_1\circ\dots\circ B_m$: first $k$ row sets of the $k\times k$ grid, then for stage $j$ the $k$ column sets $b_{i,j}$ covering column $i$ plus auxiliary elements $u_{i,1..j}$. `rowsHeld k S` $=n_t$, number of row sets in $S$.
--   - `arrivalValue` $\lambda_j=f(R_j)$; `gain` $g_j=P_j-\lambda_j$; `physicalVector p` $=z(p)=\sum_ip_i\mathbf 1_{O_i}$; `multilinearExtension Q z` $=F_Q(z)=\mathbb E f(Q\cup S(z))$, $S(z)\subseteq V_{now}$ independent with marginals $z$; `twoTypeValue f Q A B s` $=H_Q(A,B;s)=s(1-s)f(Q)+(1-s)^2f(Q\cup A)+s^2f(Q\cup B)+s(1-s)f(Q\cup A\cup B)$; `residual i j` $=f(R_j\cup O_i)-\lambda_j$; `credit j` $=K_j=2g_j-r_j$ with $r_j=$ `residual 0 j`.
--
--   ## Goal statements (one `Prop` per numbered result)
--
--   - `RandomizedUpperGoal`: Theorem 1, randomized impossibility $\xi^\star+O(\varepsilon)$ for $\varepsilon k$-consistent algorithms on coverage.
--   - `RandomizedUpperLimitGoal`: Remark 1, constant recourse $C$, ratio $>\xi^\star+\delta$ impossible for large $k$.
--   - `RandomizedLowerGoal`: Theorem 2, $O(\varepsilon^{-2})$-consistent randomized $(\xi^\star-\varepsilon)$-approximation.
--   - `AdditionRobustReductionGoal`: Lemma 1, addition robustness at $\alpha$ implies a randomized $(\alpha-3\gamma)$ algorithm with $O(\gamma^{-2})$ recourse.
--   - `IntervalSelectionReductionGoal`: Lemma 2, $\Gamma\ge\alpha$ on intervals implies $\alpha$-addition-robust distributions.
--   - `ConsecutiveIntervalReductionGoal`: Lemma 3, reduction to nonincreasing consecutive equalized intervals.
--   - `ConsecutiveIntervalGapGoal`: Lemma 4, $\Gamma\ge\xi^\star$ there, tight at three explicit intervals.
--   - `PsiRootGoal`: Proposition 1, unique root of $\Psi$ in $(1/2,1)$ with decimal bounds.
--   - `MinimaxGoal`: Lemma 5, minimax duality for $\rho^\star$.
--   - `DeterministicUpperGoal`: Theorem 3, $3/4+O(\varepsilon)$ impossibility; `DeterministicUpperLimitGoal`: its constant-recourse form.
--   - `DeterministicLowerGoal`: Theorem 4, $O(\varepsilon^{-3}\log\frac1\varepsilon)$-consistent $(3/4-\varepsilon)$ algorithm.
--   - `CertificateReductionGoal`: Theorem 5, certificates with $L\le C(m+1)$ give consistent algorithms.
--   - `SqrtTwoCertificatesGoal`: Theorem 6, $(1/\sqrt2,3)$-certificates exist; `ThreeQuarterCertificatesGoal`: Theorem 7, $(3/4,m+3)$-certificates exist.
--   - `GridStreamCrossingGoal`: Lemma 6, behavior of $3/4$-approximate trajectories on $\Sigma$.
--   - `WindowBoundsGoal`: Lemma B.1; `MixtureComparisonsGoal`: Lemma B.2; `TwoTypeInterpolationGoal`: Lemma B.3; `PrefixSuffixTradeoffGoal`: Theorem B.4; `PrefixBoundGoal`: Lemma B.5; `SuffixBoundGoal`: Lemma B.6; `ConcentrationGoal`: Lemma B.7.
--   - `RandomizedTightGoal`: Main Result 1 (Theorems 1-2); `DeterministicTightGoal`: Main Result 2 (Theorems 3-4).
--
--   These definitions and statements form the specification of the whole development: every proof module targets one of the goals above.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainStatements.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

/-- A nonnegative monotone submodular objective. Its value at the empty set
may be nonzero. Computation and value queries are unrestricted. -/
structure Objective (n : ℕ) where
  value : Finset (Fin n) → ℝ
  nonnegative : ∀ A, 0 ≤ value A
  monotone : ∀ A B, A ⊆ B → value A ≤ value B
  submodular : ∀ A B,
    value (A ∪ B) + value (A ∩ B) ≤ value A + value B

/-- The arrived prefix `X_t = {x_1, ..., x_t}`: the elements available after
`t` arrivals. -/
def arrivedPrefix (n t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun e => e.val < t)

/-- The symmetric difference `|A △ B|`: deletions plus insertions. -/
def recourse {n : ℕ} (A B : Finset (Fin n)) : ℕ :=
  ((A \ B) ∪ (B \ A)).card

/-- A trajectory `ALG_0, ..., ALG_n` that starts empty, keeps
`ALG_t ⊆ X_t` and `|ALG_t| ≤ k` at every time, and is `C`-consistent:
`|ALG_t △ ALG_{t-1}| ≤ C` at every update. It may depend on the entire stream,
so it describes a deterministic clairvoyant algorithm run on that stream. -/
def FeasibleTrajectory {n : ℕ} (cardBudget changeBudget : ℕ)
    (S : Fin (n + 1) → Finset (Fin n)) : Prop :=
  S 0 = ∅ ∧
  (∀ t : Fin (n + 1),
    S t ⊆ arrivedPrefix n t.val ∧ (S t).card ≤ cardBudget) ∧
  (∀ t : Fin n,
    recourse (S t.succ) (S t.castSucc) ≤ changeBudget)

/-- The law of the trajectory of a randomized clairvoyant algorithm run on a
fully disclosed stream: a probability distribution on the finitely many
trajectories. -/
structure RandomTrajectory (n : ℕ) where
  prob : (Fin (n + 1) → Finset (Fin n)) → ℝ
  prob_nonneg : ∀ S, 0 ≤ prob S
  prob_sum : ∑ S, prob S = 1

namespace RandomTrajectory

variable {n : ℕ} (μ : RandomTrajectory n)

/-- Every realization of the randomness is feasible and `C`-consistent. -/
def Feasible (cardBudget changeBudget : ℕ) : Prop :=
  ∀ S, μ.prob S ≠ 0 → FeasibleTrajectory cardBudget changeBudget S

/-- The expectation `E[g(ALG_t)]`. -/
def expectation (g : Finset (Fin n) → ℝ) (t : Fin (n + 1)) : ℝ :=
  ∑ S, μ.prob S * g (S t)

end RandomTrajectory

/-- A deterministic clairvoyant algorithm with recourse at most `R` at every
update that is an `(α - ε)`-approximation at every time. The quantifiers over
the stream length, the budget, and the objective follow `R`. -/
def ConsistentGuarantee (α ε : ℝ) (R : ℕ) : Prop :=
  ∀ (n k : ℕ) (f : Objective n), ∃ S : Fin (n + 1) → Finset (Fin n),
    FeasibleTrajectory k R S ∧
    ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
      A ⊆ arrivedPrefix n t.val → A.card ≤ k →
      (α - ε) * f.value A ≤ f.value (S t)

/-- A randomized clairvoyant algorithm that is `C`-consistent for every
realization of its randomness and an `(α - ε)`-approximation in expectation at
every time. The quantifiers over the stream length, the budget, and the
objective follow `C`. -/
def RandomizedGuarantee (α ε : ℝ) (C : ℕ) : Prop :=
  ∀ (n k : ℕ) (f : Objective n), ∃ μ : RandomTrajectory n,
    μ.Feasible k C ∧
    ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
      A ⊆ arrivedPrefix n t.val → A.card ≤ k →
      (α - ε) * f.value A ≤ μ.expectation f.value t

/-- Unweighted coverage: the number of universe elements covered by `A`. -/
def coverageValue {n u : ℕ} (cover : Fin n → Finset (Fin u))
    (A : Finset (Fin n)) : ℝ :=
  ((A.biUnion cover).card : ℝ)

/-- The expectation `E[g(S)]` for the random set `S ⊆ U` that contains each
`e ∈ U` independently with probability `z e`. -/
def independentExpectation {α : Type*} [DecidableEq α] (U : Finset α) (z : α → ℝ)
    (g : Finset α → ℝ) : ℝ :=
  ∑ S ∈ U.powerset, ((∏ e ∈ S, z e) * ∏ e ∈ U \ S, (1 - z e)) * g S

/-- The polynomial `Ψ(ξ) = 89 ξ⁴ - 44 ξ³ - 19 ξ² - 3 ξ + 1`. -/
def psi (ξ : ℝ) : ℝ := 89 * ξ ^ 4 - 44 * ξ ^ 3 - 19 * ξ ^ 2 - 3 * ξ + 1

/-- The threshold `ξ⋆ ≈ 0.7942`, the root of `Ψ` in `(1/2, 1)`. Proposition 1
(`PsiRootGoal`) shows that this root exists and is unique. -/
def xiStar : ℝ := sSup {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0}

/-- The polynomial `Φ(x) = x⁴ + x³ - 2 x² - 3 x + 2` of Section 2.1, whose
root in `(0, 1)` is the weight `u₁` of the hard instance. -/
def phi (x : ℝ) : ℝ := x ^ 4 + x ^ 3 - 2 * x ^ 2 - 3 * x + 2

/-- **Theorem 1** (impossibility for randomized algorithms). For every
`ε ∈ [1/k, 1]`, no randomized `εk`-consistent clairvoyant algorithm achieves
an approximation ratio better than `ξ⋆ + O(ε)` for maximum coverage subject
to a cardinality constraint `k`: on one unweighted coverage stream, every such
algorithm has a time `t` and a feasible competitor `A` with
`E[f(ALG_t)] ≤ (ξ⋆ + K ε) f(A)`. The constant `K` is absolute. -/
def RandomizedUpperGoal : Prop :=
  ∃ K : ℝ, ∀ (k : ℕ) (ε : ℝ), 0 < k → 1 / (k : ℝ) ≤ ε → ε ≤ 1 →
    ∃ (n u : ℕ) (cover : Fin n → Finset (Fin u)),
      ∀ μ : RandomTrajectory n, μ.Feasible k ⌊ε * k⌋₊ →
        ∃ (t : Fin (n + 1)) (A : Finset (Fin n)),
          A ⊆ arrivedPrefix n t.val ∧ A.card ≤ k ∧ 0 < coverageValue cover A ∧
          μ.expectation (coverageValue cover) t ≤ (xiStar + K * ε) * coverageValue cover A

/-- **Remark 1** (constant recourse). For any fixed consistency bound `C` and
any `δ > 0`, choosing `k` sufficiently large yields an unweighted coverage
instance on which no randomized `C`-consistent clairvoyant algorithm can
maintain an approximation ratio better than `ξ⋆ + δ`. -/
def RandomizedUpperLimitGoal : Prop :=
  ∀ (C : ℕ) (δ : ℝ), 0 < δ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (n u : ℕ) (cover : Fin n → Finset (Fin u)),
      ∀ μ : RandomTrajectory n, μ.Feasible k C →
        ∃ (t : Fin (n + 1)) (A : Finset (Fin n)),
          A ⊆ arrivedPrefix n t.val ∧ A.card ≤ k ∧
          μ.expectation (coverageValue cover) t <
            (xiStar + δ) * coverageValue cover A

/-- **Theorem 2** (randomized algorithm). For every `ε ∈ (0, 1)` there is a
randomized clairvoyant algorithm that is `O(ε⁻²)`-consistent and a
`(ξ⋆ - ε)`-approximation in expectation at every time. -/
def RandomizedLowerGoal : Prop :=
  ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ C : ℕ, (C : ℝ) ≤ K * (1 / ε) ^ 2 ∧ RandomizedGuarantee xiStar ε C

/-- Weights on the candidates `0, ..., m`. -/
abbrev Point (m : ℕ) := Fin (m + 1) → ℝ

/-- Membership in the simplex `Δ` of probability distributions on
`{0, ..., m}`. -/
def IsSimplex {m : ℕ} (p : Point m) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

/-- An instance of the clairvoyant addition-robust problem with stages
`0, ..., m`, together with a choice of the sets `O_0, ..., O_m`. The set
`present` is `V_now`, the set `arrivals j` is the prefix `R_j` of the known
future, so `∅ = R_0 ⊆ R_1 ⊆ ... ⊆ R_m`, and `candidate j` is a set `O_j` of at
most `κ` present elements maximizing `f(O ∪ R_j)`. Section 3.2 calls the same
data a window instance, the sets `O_j` its candidates, and `f(O_j ∪ R_j)` the
benchmark (2) at stage `j`.

Section 2.3 adds one future element per stage, the case `SingleArrivals`. As
in Appendix B.2.1, prefixes are recorded as nested sets, so a stage may also
add several elements or none. -/
structure WindowInstance (n : ℕ) where
  objective : Objective n
  present : Finset (Fin n)
  coreBudget : ℕ
  lastStage : ℕ
  arrivals : Fin (lastStage + 1) → Finset (Fin n)
  candidate : Fin (lastStage + 1) → Finset (Fin n)
  arrivals_zero : arrivals 0 = ∅
  arrivals_mono : Monotone arrivals
  arrivals_disjoint : ∀ j, Disjoint (arrivals j) present
  candidate_subset : ∀ j, candidate j ⊆ present
  candidate_card : ∀ j, (candidate j).card ≤ coreBudget
  candidate_optimal : ∀ j (O : Finset (Fin n)), O ⊆ present → O.card ≤ coreBudget →
    objective.value (O ∪ arrivals j) ≤ objective.value (candidate j ∪ arrivals j)

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- One future element per stage, as for `V_future = (v_1, ..., v_m)` in
Section 2.3: `R_{j+1} = R_j ∪ {v_{j+1}}` with `v_{j+1} ∉ R_j`. -/
def SingleArrivals : Prop :=
  ∀ j : Fin W.lastStage, ∃ v, v ∉ W.arrivals j.castSucc ∧
    W.arrivals j.succ = insert v (W.arrivals j.castSucc)

/-- The benchmark `f(O_j ∪ R_j)` at stage `j` (equation (2)). -/
def benchmark (j : Fin (W.lastStage + 1)) : ℝ :=
  W.objective.value (W.candidate j ∪ W.arrivals j)

/-- **Definition 2.1** (clairvoyant addition robustness). The weights `w`
describe a possibly randomized set `S ⊆ V_now` with `|S| ≤ κ`; it is
`α`-addition robust if `E[f(S ∪ R_j)] ≥ α f(O_j ∪ R_j)` at every stage `j`. -/
def IsAdditionRobust (α : ℝ) (w : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ w S) ∧ (∑ S, w S) = 1 ∧
  (∀ S, w S ≠ 0 → S ⊆ W.present ∧ S.card ≤ W.coreBudget) ∧
  ∀ j, α * W.benchmark j ≤ ∑ S, w S * W.objective.value (S ∪ W.arrivals j)

end WindowInstance

/-- Every instance of the clairvoyant addition-robust problem, with one future
element per stage as in Section 2.3, admits an `α`-addition-robust
distribution. -/
def AdmitsAdditionRobust (α : ℝ) : Prop :=
  ∀ (n : ℕ) (W : WindowInstance n), W.SingleArrivals → ∃ w, W.IsAdditionRobust α w

/-- **Lemma 1** (from clairvoyant addition robustness to consistency). If every
instance of the clairvoyant addition-robust problem admits an `α`-addition-robust
distribution, where `0 ≤ α ≤ 1`, then for every `γ ∈ (0, 1/8)` there is a
randomized clairvoyant `O(γ⁻²)`-consistent algorithm that is an
`(α - 3γ)`-approximation. The consistency bound is chosen before `α`. -/
def AdditionRobustReductionGoal : Prop :=
  ∃ K : ℝ, ∀ γ : ℝ, 0 < γ → γ < 1 / 8 →
    ∃ C : ℕ, (C : ℝ) ≤ K * (1 / γ) ^ 2 ∧
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 → AdmitsAdditionRobust α →
        RandomizedGuarantee α (3 * γ) C

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The value `ρ⋆` of the addition-robustness linear program (1): the largest
`ρ ∈ [0, 1]` such that some distribution `α ∈ Δ` over the candidates has
`Σ_i α_i f(O_i ∪ R_j) ≥ ρ f(O_j ∪ R_j)` at every stage `j`. -/
def lpValue : ℝ :=
  sSup {ρ : ℝ | 0 ≤ ρ ∧ ρ ≤ 1 ∧ ∃ a : Point W.lastStage, IsSimplex a ∧
    ∀ j, ρ * W.benchmark j ≤ ∑ i, a i * W.objective.value (W.candidate i ∪ W.arrivals j)}

/-- The normalized payoff `w_{i,j} = f(O_i ∪ R_j) / f(O_j ∪ R_j)` of
Section 2.3 and Appendix A.4. -/
def payoff (i j : Fin (W.lastStage + 1)) : ℝ :=
  W.objective.value (W.candidate i ∪ W.arrivals j) / W.benchmark j

end WindowInstance

/-- An interval-selection instance (Definition 2.2): intervals `[ℓ_i, r_i]`
with `0 ≤ ℓ_i ≤ r_i`, indexed by the finite set `{0, ..., N}`, and a
probability distribution `p` on the indices. -/
structure IntervalInstance (N : ℕ) where
  left : Fin (N + 1) → ℝ
  right : Fin (N + 1) → ℝ
  prob : Fin (N + 1) → ℝ
  left_nonneg : ∀ i, 0 ≤ left i
  left_le_right : ∀ i, left i ≤ right i
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum : ∑ i, prob i = 1

namespace IntervalInstance

variable {N : ℕ} (I : IntervalInstance N)

/-- The value `v(i, j) = ℓ_j + |[ℓ_i, r_i] ∩ [ℓ_j, ∞)|` of interval `i` at
realization `j`. -/
def value (i j : Fin (N + 1)) : ℝ :=
  I.left j + max 0 (I.right i - max (I.left i) (I.left j))

/-- The best fixed expected value `max_i E_{j∼p}[v(i, j)]`. -/
def fixedValue : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, I.prob j * I.value i j

/-- The expected value in hindsight `E_{j∼p}[max_i v(i, j)]`. -/
def adaptiveValue : ℝ :=
  ∑ j, I.prob j * Finset.univ.sup' Finset.univ_nonempty fun i => I.value i j

/-- **Definition 2.2**: the adaptivity gap `Γ(ℓ, r, p)`, the ratio of the
best fixed expected value to the expected value in hindsight, and `1` if the
denominator is zero. -/
def adaptivityGap : ℝ :=
  if I.adaptiveValue = 0 then 1 else I.fixedValue / I.adaptiveValue

/-- **Definition 2.3** (nonincreasing consecutive intervals): `ℓ_0 = 0`,
`ℓ_{i+1} = r_i` for `i < N`, and `r_0 - ℓ_0 ≥ ... ≥ r_N - ℓ_N > 0`. -/
def IsNonincreasingConsecutive : Prop :=
  I.left 0 = 0 ∧
  (∀ i : Fin N, I.left i.succ = I.right i.castSucc) ∧
  (∀ i : Fin N, I.right i.succ - I.left i.succ ≤ I.right i.castSucc - I.left i.castSucc) ∧
  0 < I.right (Fin.last N) - I.left (Fin.last N)

/-- **Definition 2.3** (equalizing distribution): every fixed interval `i` has
the same expected value `E_{j∼p}[v(i, j)]`. -/
def IsEqualizing : Prop :=
  ∀ i i' : Fin (N + 1), ∑ j, I.prob j * I.value i j = ∑ j, I.prob j * I.value i' j

end IntervalInstance

/-- **Lemma 2** (from interval selection to addition robustness). Let
`α ∈ [0, 1]`. If `Γ(ℓ, r, p) ≥ α` for every interval-selection instance, then
every instance of clairvoyant addition-robust monotone submodular maximization
admits an `α`-addition-robust distribution. -/
def IntervalSelectionReductionGoal : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    (∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap) →
    ∀ (n : ℕ) (W : WindowInstance n), ∃ w, W.IsAdditionRobust α w

/-- **Lemma 3** (reduction to consecutive intervals). Let `α ∈ [0, 1]`. If
`Γ(ℓ, r, p) ≥ α` for every instance of nonincreasing consecutive intervals with
the equalizing distribution, then `Γ(ℓ, r, p) ≥ α` for every
interval-selection instance. -/
def ConsecutiveIntervalReductionGoal : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    (∀ (N : ℕ) (I : IntervalInstance N), I.IsNonincreasingConsecutive → I.IsEqualizing →
      α ≤ I.adaptivityGap) →
    ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap

/-- **Lemma 4** (consecutive intervals). Every instance of nonincreasing
consecutive intervals with the equalizing distribution has `Γ(ℓ, r, p) ≥ ξ⋆`.
Equality holds for the three intervals `[0, 1]`, `[1, 1 + u₁]`, and
`[1 + u₁, 1 + u₁ + u₂]` with the equalizing distribution, whose probabilities
are `(u₂, u₂/u₁ - u₂, 1 - u₂/u₁)`, where `u₁` is the unique root of `Φ` in
`(0, 1)` and `u₂ = u₁² (1 + u₁)`. -/
def ConsecutiveIntervalGapGoal : Prop :=
  (∀ (N : ℕ) (I : IntervalInstance N), I.IsNonincreasingConsecutive → I.IsEqualizing →
    xiStar ≤ I.adaptivityGap) ∧
  ∃ u₁ u₂ : ℝ, 0 < u₁ ∧ u₁ < 1 ∧ phi u₁ = 0 ∧
    (∀ x : ℝ, 0 < x → x < 1 → phi x = 0 → x = u₁) ∧ u₂ = u₁ ^ 2 * (1 + u₁) ∧
    ∃ I : IntervalInstance 2, I.IsNonincreasingConsecutive ∧ I.IsEqualizing ∧
      I.adaptivityGap = xiStar ∧
      I.left = ![0, 1, 1 + u₁] ∧ I.right = ![1, 1 + u₁, 1 + u₁ + u₂] ∧
      I.prob = ![u₂, u₂ / u₁ - u₂, 1 - u₂ / u₁]

/-- **Proposition 1** (Appendix A.1). The polynomial `Ψ` has a unique root
`ξ⋆ ≈ 0.7941970147` in `(1/2, 1)`; precisely,
`0.7941970146 < ξ⋆ < 0.7941970148`. -/
def PsiRootGoal : Prop :=
  1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 ∧
    (∀ ξ : ℝ, 1 / 2 < ξ → ξ < 1 → psi ξ = 0 → ξ = xiStar) ∧
    (0.7941970146 : ℝ) < xiStar ∧ xiStar < 0.7941970148

/-- **Lemma 5** (finite minimax duality, Appendix A.4). Under the standing
assumptions `κ ≥ 1` and `f(O_0) > 0`, the value `ρ⋆` of the linear program (1)
satisfies `ρ⋆ = max_{α ∈ Δ} min_j Σ_i α_i w_{i,j} = min_{β ∈ Δ} max_i Σ_j β_j w_{i,j}`,
where `w_{i,j} = f(O_i ∪ R_j) / f(O_j ∪ R_j)`; both extrema are attained. -/
def MinimaxGoal : Prop :=
  ∀ (n : ℕ) (W : WindowInstance n), 1 ≤ W.coreBudget → 0 < W.objective.value (W.candidate 0) →
    IsGreatest {v | ∃ a : Point W.lastStage, IsSimplex a ∧
        v = Finset.univ.inf' Finset.univ_nonempty fun j => ∑ i, a i * W.payoff i j}
      W.lpValue ∧
    IsLeast {v | ∃ b : Point W.lastStage, IsSimplex b ∧
        v = Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, b j * W.payoff i j}
      W.lpValue

/-- **Theorem 3** (impossibility for deterministic algorithms; Section 3.1 and
Appendix B.1). For `1/k ≤ ε ≤ 1`, no deterministic `εk`-consistent clairvoyant
algorithm achieves an approximation ratio better than `3/4 + O(ε)` for maximum
coverage subject to a uniform cardinality constraint `k`: on one unweighted
coverage stream, every such trajectory has a time `t` and a feasible
competitor `A` with `f(ALG_t) ≤ (3/4 + K ε) f(A)`. The constant `K` is
absolute. -/
def DeterministicUpperGoal : Prop :=
  ∃ K : ℝ, ∀ (k : ℕ) (ε : ℝ), 0 < k → 1 / (k : ℝ) ≤ ε → ε ≤ 1 →
    ∃ (n u : ℕ) (cover : Fin n → Finset (Fin u)),
      ∀ S : Fin (n + 1) → Finset (Fin n), FeasibleTrajectory k ⌊ε * k⌋₊ S →
        ∃ (t : Fin (n + 1)) (A : Finset (Fin n)),
          A ⊆ arrivedPrefix n t.val ∧ A.card ≤ k ∧ 0 < coverageValue cover A ∧
          coverageValue cover (S t) ≤ (3 / 4 + K * ε) * coverageValue cover A

/-- The impossibility of Main Result 2 for constant recourse: for every fixed
consistency bound `C` and every ratio `α > 3/4`, a finite unweighted coverage
stream defeats every `C`-consistent trajectory, including clairvoyant ones. -/
def DeterministicUpperLimitGoal : Prop :=
  ∀ α : ℝ, (3 : ℝ) / 4 < α → ∀ C : ℕ,
    ∃ (n k u : ℕ) (cover : Fin n → Finset (Fin u)),
      ∀ S : Fin (n + 1) → Finset (Fin n),
        FeasibleTrajectory k C S →
        ∃ (t : Fin (n + 1)) (A : Finset (Fin n)),
          A ⊆ arrivedPrefix n t.val ∧ A.card ≤ k ∧
          coverageValue cover (S t) < α * coverageValue cover A

/-- **Theorem 4** (deterministic guarantee). For every `ε ∈ (0, 1)` there is a
deterministic clairvoyant `O(ε⁻³ log(1/ε))`-consistent algorithm with
`f(ALG_t) ≥ (3/4 - ε) f(OPT_t)` at every time `t`. The recourse bound is chosen
before the stream length, the budget, and the objective. -/
def DeterministicLowerGoal : Prop :=
  ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ C : ℕ, (C : ℝ) ≤ K * (1 / ε) ^ 3 * Real.log (1 / ε) ∧
      ConsistentGuarantee (3 / 4) ε C

/-- The vertex `δ_i`, which puts all weight on candidate `i`. -/
def vertex {m : ℕ} (i : Fin (m + 1)) : Point m :=
  fun j => if j = i then 1 else 0

/-- The point with parameter `x` on the segment from `p` to `q`. -/
def mix {m : ℕ} (p q : Point m) (x : ℝ) : Point m :=
  fun i => (1 - x) * p i + x * q i

/-- A continuous piecewise-affine path with `pieces` affine segments, each
joining two consecutive nodes. -/
structure PolygonalPath (m : ℕ) where
  pieces : ℕ
  node : Fin (pieces + 1) → Point m

namespace PolygonalPath

/-- A property holds at every point of the path: at every node and at every
point of every segment. Nodes are checked, so a zero-piece path is not vacuous. -/
def Along {m : ℕ} (γ : PolygonalPath m) (Φ : Point m → Prop) : Prop :=
  (∀ i, Φ (γ.node i)) ∧ ∀ (i : Fin γ.pieces) x, 0 ≤ x → x ≤ 1 →
    Φ (mix (γ.node i.castSucc) (γ.node i.succ) x)

end PolygonalPath

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The value `H_j(p)` of a mixture at stage `j` (equation (3)): the expected
value of `R_j` together with the candidates in a random set `I(p)` that
contains each index `i` independently with probability `p i`. -/
def mixtureValue (j : Fin (W.lastStage + 1)) (p : Point W.lastStage) : ℝ :=
  ∑ I : Finset (Fin (W.lastStage + 1)),
    ((∏ i ∈ I, p i) * ∏ i ∈ Iᶜ, (1 - p i)) *
      W.objective.value (W.arrivals j ∪ I.biUnion W.candidate)

/-- **Definition 3.1** (clairvoyant certificate). An `(α, L)`-certificate: the
anchor `p` is persistent at every stage, the entry path `γ⁻` from `δ_0` to `p`
is safe at stage `0`, the exit path `γ⁺` from `p` to `δ_m` is safe at stage
`m`, and the two paths have at most `L` segments in total. -/
structure Certificate (α : ℝ) (L : ℕ) where
  anchor : Point W.lastStage
  entry : PolygonalPath W.lastStage
  exit : PolygonalPath W.lastStage
  anchor_mem : IsSimplex anchor
  entry_mem : entry.Along IsSimplex
  exit_mem : exit.Along IsSimplex
  entry_start : entry.node 0 = vertex 0
  entry_finish : entry.node (Fin.last entry.pieces) = anchor
  exit_start : exit.node 0 = anchor
  exit_finish : exit.node (Fin.last exit.pieces) = vertex (Fin.last W.lastStage)
  persistence : ∀ j, α * W.benchmark j ≤ W.mixtureValue j anchor
  safe_entry : entry.Along (fun q => α * W.benchmark 0 ≤ W.mixtureValue 0 q)
  safe_exit : exit.Along (fun q =>
    α * W.benchmark (Fin.last W.lastStage) ≤ W.mixtureValue (Fin.last W.lastStage) q)
  segments : entry.pieces + exit.pieces ≤ L

end WindowInstance

/-- Every window instance with stages `0, ..., m` admits an
`(α, L m)`-certificate. -/
def AdmitsCertificates (α : ℝ) (L : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (W : WindowInstance n), Nonempty (W.Certificate α (L W.lastStage))

/-- Every window instance of Section 3.2, with one arrival per stage and
stages `0, ..., m`, admits an `(α, L m)`-certificate. -/
def AdmitsArrivalCertificates (α : ℝ) (L : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (W : WindowInstance n), W.SingleArrivals →
    Nonempty (W.Certificate α (L W.lastStage))

/-- **Theorem 5** (reduction from consistency to clairvoyant certificates).
Let `0 < α ≤ 3/4` and suppose that every window instance with stages
`0, ..., m` admits an `(α, L)`-certificate with `L ≤ C (m + 1)`. Then for every
`ε ∈ (0, 1)` there is a deterministic clairvoyant
`O(ε⁻³ log(1/ε))`-consistent algorithm with `f(ALG_t) ≥ (α - ε) f(OPT_t)` at
every time. The constant `K` depends only on `C`, and the recourse `R` is chosen
before `α`. Certificates are assumed only for windows with one arrival per
stage, as in Section 3.2. -/
def CertificateReductionGoal : Prop :=
  ∀ C : ℕ, ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ R : ℕ, (R : ℝ) ≤ K * (1 / ε) ^ 3 * Real.log (1 / ε) ∧
      ∀ α : ℝ, 0 < α → α ≤ 3 / 4 →
        AdmitsArrivalCertificates α (fun m => C * (m + 1)) → ConsistentGuarantee α ε R

/-- **Theorem 6** (certificates at `1/√2`). Every window instance admits a
`(1/√2, 3)`-certificate. -/
def SqrtTwoCertificatesGoal : Prop :=
  AdmitsCertificates (1 / Real.sqrt 2) (fun _ => 3)

/-- **Theorem 7** (certificates at `3/4`). Every window instance with stages
`0, ..., m` admits a `(3/4, m + 3)`-certificate. -/
def ThreeQuarterCertificatesGoal : Prop :=
  AdmitsCertificates (3 / 4) (fun m => m + 3)

/-- The coverage stream `Σ = A ∘ B_1 ∘ ... ∘ B_m` of Appendix B.1.1, for the
budget `k`. The universe consists of the `k × k` grid `U_core`, whose cell in
row `r` and column `c` (counted from `0`) is `r k + c`, and of the `k m`
auxiliary elements of `U_aux`, where `k² + (i - 1) m + (l - 1)` stands for
`u_{i,l}`. The first `k` sets are the rows `a_1, ..., a_k`. Stage
`j = 1, ..., m` then presents the columns `b_{1,j}, ..., b_{k,j}`; the set
`b_{i,j}` covers column `i` of the grid and the `j` auxiliary elements
`u_{i,1}, ..., u_{i,j}`, so `|b_{i,j}| = k + j`. -/
def gridStreamCover (k m : ℕ) (e : Fin (k + m * k)) : Finset (Fin (k * k + k * m)) :=
  Finset.univ.filter fun x =>
    if e.val < k then x.val < k * k ∧ x.val / k = e.val
    else (x.val < k * k ∧ x.val % k = (e.val - k) % k) ∨
      (k * k ≤ x.val ∧ (x.val - k * k) / m = (e.val - k) % k ∧
        (x.val - k * k) % m ≤ (e.val - k) / k)

/-- The number `n_t` of row sets `a_1, ..., a_k` in `S`. -/
def rowsHeld (k : ℕ) {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  (S.filter fun e => e.val < k).card

/-- **Lemma 6** (behavior on the stream `Σ`). If a trajectory on `Σ` with
cardinality budget `k` maintains a `3/4`-approximation to the dynamic optimum,
then it holds `n_k ≥ 3k/4` rows once the rows have arrived, and, provided that
`m ≥ k`, at most `k/3` rows at some time `t > k`. -/
def GridStreamCrossingGoal : Prop :=
  ∀ k m : ℕ, 0 < k →
    ∀ (C : ℕ) (S : Fin (k + m * k + 1) → Finset (Fin (k + m * k))),
      FeasibleTrajectory k C S →
      (∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
        A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
        3 / 4 * coverageValue (gridStreamCover k m) A ≤
          coverageValue (gridStreamCover k m) (S t)) →
      3 * k ≤ 4 * rowsHeld k (S ⟨k, by omega⟩) ∧
      (k ≤ m → ∃ t : Fin (k + m * k + 1), k < t.val ∧ 3 * rowsHeld k (S t) ≤ k)

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The value `λ_j = f(R_j)` of the arrivals alone (equation (18)). -/
def arrivalValue (j : Fin (W.lastStage + 1)) : ℝ := W.objective.value (W.arrivals j)

/-- The residual `g_j = P_j - λ_j` of the benchmark `P_j = f(O_j ∪ R_j)`
(equation (18)): the remaining optimum at stage `j`. -/
def gain (j : Fin (W.lastStage + 1)) : ℝ := W.benchmark j - W.arrivalValue j

/-- The value `H_Q(p)` of a type vector `p` with a fixed buffer `Q` in place of
`R_j`: the expected value of `Q` together with the candidates in the random
set `I(p)` that contains each index `i` independently with probability `p i`.
It is defined on the whole type cube `[0, 1]^{m+1}`, and `H_{R_j} = H_j`. -/
def bufferMixtureValue (Q : Finset (Fin n)) (p : Point W.lastStage) : ℝ :=
  ∑ I : Finset (Fin (W.lastStage + 1)),
    ((∏ i ∈ I, p i) * ∏ i ∈ Iᶜ, (1 - p i)) * W.objective.value (Q ∪ I.biUnion W.candidate)

/-- The physical fractional vector `z(p) = Σ_i p_i 1_{O_i}` of a type vector `p`
(equation (20)). -/
def physicalVector (p : Point W.lastStage) (e : Fin n) : ℝ :=
  ∑ i, if e ∈ W.candidate i then p i else 0

/-- The multilinear extension `F_Q(z) = E[f(Q ∪ S(z))]`, where `S(z) ⊆ V_now`
contains each present element `e` independently with probability `z e`. -/
def multilinearExtension (Q : Finset (Fin n)) (z : Fin n → ℝ) : ℝ :=
  independentExpectation W.present z fun S => W.objective.value (Q ∪ S)

end WindowInstance

/-- **Lemma B.1** (window bounds). The values `λ_j` and `P_j` are nondecreasing
in `j`, the residual `g_j` is nonincreasing in `j`, and for all stages `s ≤ j`,
`0 ≤ g_j ≤ V ≤ P_j` and `0 ≤ P_j - P_s ≤ λ_j - λ_s`, where `V = P_0`. The
appendix normalizes `f(∅) = 0`; these bounds hold without it. -/
def WindowBoundsGoal : Prop :=
  ∀ (n : ℕ) (W : WindowInstance n),
    Monotone W.arrivalValue ∧ Monotone W.benchmark ∧ Antitone W.gain ∧
    ∀ s j : Fin (W.lastStage + 1), s ≤ j →
      0 ≤ W.gain j ∧ W.gain j ≤ W.benchmark 0 ∧ W.benchmark 0 ≤ W.benchmark j ∧
      0 ≤ W.benchmark j - W.benchmark s ∧
      W.benchmark j - W.benchmark s ≤ W.arrivalValue j - W.arrivalValue s

/-- **Lemma B.2** (mixture comparisons). Fix a buffer `Q`. For every `p` in the
type cube `[0, 1]^{m+1}` with `Σ_i p_i ≤ 1`, `F_Q(z(p)) ≥ H_Q(p)` (21), and for
every mixture `p ∈ Δ`, `H_Q(p) ≤ Σ_i p_i f(Q ∪ O_i)` (22). -/
def MixtureComparisonsGoal : Prop :=
  ∀ (n : ℕ) (W : WindowInstance n) (Q : Finset (Fin n)),
    (∀ p : Point W.lastStage, (∀ i, 0 ≤ p i) → ∑ i, p i ≤ 1 →
      W.bufferMixtureValue Q p ≤ W.multilinearExtension Q (W.physicalVector p)) ∧
    ∀ p : Point W.lastStage, IsSimplex p →
      W.bufferMixtureValue Q p ≤ ∑ i, p i * W.objective.value (Q ∪ W.candidate i)

/-- The two-type objective `H_Q(A, B; s)` of Appendix B.2.1: the expected value
of `Q` together with `A` and `B`, selected independently with probabilities
`1 - s` and `s`, summed over the four outcomes. -/
def twoTypeValue {n : ℕ} (f : Objective n) (Q A B : Finset (Fin n)) (s : ℝ) : ℝ :=
  s * (1 - s) * f.value Q + (1 - s) ^ 2 * f.value (Q ∪ A) + s ^ 2 * f.value (Q ∪ B) +
    s * (1 - s) * f.value (Q ∪ (A ∪ B))

/-- **Lemma B.3** (two-type interpolation). Write `λ = f(Q)`,
`a = f(Q ∪ A) - λ`, `b = f(Q ∪ B) - λ`, and the residual overlap
`o = f(Q ∪ A) + f(Q ∪ B) - f(Q ∪ A ∪ B) - λ`. For every `s ∈ [0, 1]`,
`H_Q(A, B; s) = λ + (1 - s) a + s b - s (1 - s) o` (23); at the midpoint,
`H_Q(A, B; 1/2) ≥ λ + (a + b)/2 - min(a, b)/4` (24); and if
`f(Q ∪ A) ≥ W` and `f(Q ∪ B) ≥ W`, then every point of the edge has value at
least `3W/4`. -/
def TwoTypeInterpolationGoal : Prop :=
  ∀ (n : ℕ) (f : Objective n) (Q A B : Finset (Fin n)),
    let lam := f.value Q
    let a := f.value (Q ∪ A) - lam
    let b := f.value (Q ∪ B) - lam
    let o := f.value (Q ∪ A) + f.value (Q ∪ B) - f.value (Q ∪ (A ∪ B)) - lam
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      twoTypeValue f Q A B s = lam + (1 - s) * a + s * b - s * (1 - s) * o) ∧
    lam + (a + b) / 2 - min a b / 4 ≤ twoTypeValue f Q A B (1 / 2) ∧
    ∀ w : ℝ, w ≤ f.value (Q ∪ A) → w ≤ f.value (Q ∪ B) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 3 / 4 * w ≤ twoTypeValue f Q A B s

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The residual `f(R_j ∪ O_i) - λ_j` of candidate `i` at stage `j`; for
`i = 0` it is `r_j` of equation (25). -/
def residual (i j : Fin (W.lastStage + 1)) : ℝ :=
  W.objective.value (W.arrivals j ∪ W.candidate i) - W.arrivalValue j

/-- The quantity `K_j = 2 g_j - r_j` of equation (25). -/
def credit (j : Fin (W.lastStage + 1)) : ℝ := 2 * W.gain j - W.residual 0 j

end WindowInstance

/-- **Theorem B.4** (prefix–suffix tradeoff). For `1/2 < β ≤ 3/4`, let
`D = max_j (2 K_j - 4 (1 - β) P_j)` as in (27). Some index `j` has `K_j ≥ D`,
so the last such index `c` exists. With `A = O_0` and `B = O_c`, the half
mixture has value at least `β P_j` for `j ≤ c` and at least `P_j / (2β)` for
`j > c`, and it is the anchor of a certificate at the common level
`α(β) = min{β, 1/(2β)}` of (28) whose entry path has one segment and whose
exit path has at most two. -/
def PrefixSuffixTradeoffGoal : Prop :=
  ∀ β : ℝ, 1 / 2 < β → β ≤ 3 / 4 → ∀ (n : ℕ) (W : WindowInstance n),
    (∃ j, Finset.univ.sup' Finset.univ_nonempty
        (fun i => 2 * W.credit i - 4 * (1 - β) * W.benchmark i) ≤ W.credit j) ∧
    ∀ c : Fin (W.lastStage + 1),
      Finset.univ.sup' Finset.univ_nonempty
          (fun i => 2 * W.credit i - 4 * (1 - β) * W.benchmark i) ≤ W.credit c →
      (∀ j, c < j → W.credit j < Finset.univ.sup' Finset.univ_nonempty
          (fun i => 2 * W.credit i - 4 * (1 - β) * W.benchmark i)) →
      (∀ j, j ≤ c → β * W.benchmark j ≤
        twoTypeValue W.objective (W.arrivals j) (W.candidate 0) (W.candidate c) (1 / 2)) ∧
      (∀ j, c < j → W.benchmark j / (2 * β) ≤
        twoTypeValue W.objective (W.arrivals j) (W.candidate 0) (W.candidate c) (1 / 2)) ∧
      ∃ Z : W.Certificate (min β (1 / (2 * β))) 3,
        Z.anchor = mix (vertex 0) (vertex c) (1 / 2) ∧ Z.entry.pieces = 1 ∧ Z.exit.pieces ≤ 2

/-- **Lemma B.5** (prefix bound). Fix `A = O_0`. If `B = O_c` is the candidate
at stage `c`, then `H_{R_j}(A, B; 1/2) ≥ λ_j + r_j / 2 + K_c / 4` at every
stage `j ≤ c`. -/
def PrefixBoundGoal : Prop :=
  ∀ (n : ℕ) (W : WindowInstance n) (j c : Fin (W.lastStage + 1)), j ≤ c →
    W.arrivalValue j + W.residual 0 j / 2 + W.credit c / 4 ≤
      twoTypeValue W.objective (W.arrivals j) (W.candidate 0) (W.candidate c) (1 / 2)

/-- **Lemma B.6** (suffix bound). Let `λ, g, u, z ≥ 0` and `0 ≤ γ ≤ 2`. If
`2 g - u ≤ γ (λ + z)`, then
`λ + (u + z)/2 - min(u, z)/4 ≥ 2/(2 + γ) (λ + g)` (30). -/
def SuffixBoundGoal : Prop :=
  ∀ lam g u z γ : ℝ, 0 ≤ lam → 0 ≤ g → 0 ≤ u → 0 ≤ z → 0 ≤ γ → γ ≤ 2 →
    2 * g - u ≤ γ * (lam + z) →
    2 / (2 + γ) * (lam + g) ≤ lam + (u + z) / 2 - min u z / 4

/-- **Lemma B.7** (concentration). Let `G` be a nonnegative monotone submodular
set function whose marginal values are at most `c > 0`, let `S` be a random set
containing each element `i` independently with probability `q i`, and put
`μ = E G(S)`. Then `P{G(S) ≤ μ - a} ≤ exp(-a² / (2 c μ))` for `0 < a < μ` (37).
If `X` is a sum of independent Bernoulli variables with mean at most `κ`, here
`X = |S|`, then `P{X > (1 + η) κ} ≤ exp(-η² κ / 3)` for `0 < η ≤ 1` (38). -/
def ConcentrationGoal : Prop :=
  (∀ (d : ℕ) (q : Fin d → ℝ) (G : Finset (Fin d) → ℝ) (c a : ℝ),
    (∀ i, 0 ≤ q i ∧ q i ≤ 1) → (∀ A, 0 ≤ G A) → (∀ A B, A ⊆ B → G A ≤ G B) →
    (∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B) → 0 < c →
    (∀ A e, G (insert e A) - G A ≤ c) →
    let μ := independentExpectation Finset.univ q G
    0 < a → a < μ →
    independentExpectation Finset.univ q (fun S => if G S ≤ μ - a then 1 else 0) ≤
      Real.exp (-(a ^ 2) / (2 * c * μ))) ∧
  ∀ (d : ℕ) (q : Fin d → ℝ) (κ η : ℝ), (∀ i, 0 ≤ q i ∧ q i ≤ 1) → ∑ i, q i ≤ κ →
    0 < η → η ≤ 1 →
    independentExpectation Finset.univ q
        (fun S => if (1 + η) * κ < (S.card : ℝ) then 1 else 0) ≤
      Real.exp (-(η ^ 2) * κ / 3)

/-- **Main Result 1** (tight randomized bound; Theorems 1 and 2). For every
`ε ∈ (0, 1)`, a randomized clairvoyant algorithm is `O(ε⁻²)`-consistent and a
`(ξ⋆ - ε)`-approximation, and no consistent randomized clairvoyant algorithm
achieves a ratio greater than `ξ⋆`, even for coverage functions. -/
def RandomizedTightGoal : Prop :=
  RandomizedLowerGoal ∧ RandomizedUpperLimitGoal

/-- **Main Result 2** (tight deterministic bound; Theorems 3 and 4). For every
`ε ∈ (0, 1)`, a deterministic clairvoyant algorithm is
`O(ε⁻³ log(1/ε))`-consistent and a `(3/4 - ε)`-approximation, and no consistent
deterministic clairvoyant algorithm achieves a ratio greater than `3/4`, even
for coverage functions. -/
def DeterministicTightGoal : Prop :=
  DeterministicLowerGoal ∧ DeterministicUpperLimitGoal

end ConsistentSubmodular

end


