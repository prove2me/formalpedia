-- Prove2me | Definitions.Def_OnDemandCoord_Model
-- name    : OnDemandCoord_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:42.975588+00:00
-- url     : https://prove2.me/theorems/def0e756-8f2a-4e40-885d-e9052e1e4783
-- title:
--   The on-demand staffing model: demands, wages, worker supply, cost $C(Q,\eta)$, LP (8), allocation policies
-- statement:
--   **The staffing system** (§3, pp. 6–11). There are $n\ge 1$ firms $I=\{1,\dots,n\}$. Firm $i$ faces a random labor demand $X_i\ge 0$ on a probability space; each $X_i$ is continuous (its law has no atoms, so $F_i(0)=0$) and has finite mean, and the joint law of $X=(X_1,\dots,X_n)$ is arbitrary (not necessarily independent or identical). Write $\bar F_i(x)=\mathbb P(X_i>x)$. Permanent workers cost $c$ each, unmet demand costs $p$ per unit, and
--   $$0<c<p,\qquad 0<\underline\tau<p,\qquad \underline\tau<\bar\tau,\qquad N>0 .$$
--   On-demand workers have availability thresholds with cdf $G$ and density $g>0$ on the support $[\underline\tau,\bar\tau]$, with $G$ log-concave. At compensation rate $\eta$ the platform has $S(\eta)=N\,G(\eta)$ workers.
--
--   Given staffing levels $Q$, firm $i$ posts the vacancy $\hat X_i=(X_i-Q_i)^+$. The module defines:
--   1. the **system cost** (5), $$C(Q,\eta)=p\,\mathbb E\Big[\Big(\sum_{i\in I}(X_i-Q_i)^+-S(\eta)\Big)^+\Big]+\eta\,N G(\eta)+c\sum_{i\in I}Q_i,$$ and a **system optimum**: $Q\ge 0$ with $C(Q,\eta)\le C(Q',\eta')$ for all $Q'\ge 0$, $\eta'\in\mathbb R$;
--   2. the cost before the no-waste simplification (p. 11), $p\sum_i\mathbb E[(X_i-Q_i)^+-A_i]+\eta NG(\eta)+c\sum_iQ_i$;
--   3. the cost $\hat C(Q,S)=p\,\mathbb E[(\sum_i(X_i-Q_i)^+-S)^+]+G^{-1}(S/N)\,S+c\sum_iQ_i$ of p. A1, $\varphi(x)=x+G(x)/g(x)$, and the tail $\mathbb P(\sum_iX_i>x)$;
--   4. the **permanent-only benchmark** (p. 12): any $Q^p$ with $p\bar F_i(Q^p_i)=c$ for all $i$, the threshold $\varphi^p=p\,\mathbb P(X_i>Q^p_i\text{ for some }i)$, and the stand-alone cost $h^p_i=p\,\mathbb E[(X_i-Q^p_i)^+]+cQ^p_i$ (p. 21);
--   5. the set function $g(U)=\mathbb E[\min\{S,\sum_{i\in U}\hat X_i\}]$ and feasibility and optimality for the **linear program (8)**: maximize $\sum_i\beta_i\mathbb E[\hat X_i]$ subject to $\beta\ge0$ and $\sum_{i\in U}\beta_i\mathbb E[\hat X_i]\le g(U)$ for all $U\subseteq I$;
--   6. **allocation policies** (1): a policy is a Markov kernel from $(\hat x,S)$ to allocations $a\in\mathbb R^n$; it belongs to $\mathcal A$ if for all $\hat x\ge0$, $S\ge0$, almost surely $0\le a_i\le\hat x_i$ and $\sum_ia_i\le S$. It is **no-waste** (4) if almost surely $\sum_ia_i=\min\{S,\sum_i\hat x_i\}$. The expected allocation $\mathbb E[A_i(\hat X,S)]$ averages over $X$ and the policy's randomization.
--   7. the greedy vector $x^*$ of Claim 3 (p. A6) for a set function and an ordering.
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note** $\underline\tau,\bar\tau$ are `τl`, `τu`. "Continuous" is an atomless law; "density $g$ strictly positive on $[\underline\tau,\bar\tau]$" is read as: $G$ has derivative $g>0$ within $[\underline\tau,\bar\tau]$ (one-sided at the ends), $G=0$ left of $\underline\tau$ and $G=1$ right of $\bar\tau$; "log-concave" concerns the cdf: $\log G$ is concave on $(\underline\tau,\bar\tau]$. "$N$ sufficiently large" is not part of the model; it is pinned down where it is used (Theorem 1). Randomized policies are Markov kernels (the paper: "$A(\hat X,S)$ does not need to be a deterministic function"). Firms are indexed by `Fin n`. $G^{-1}$ is the inverse of $G$ on $[\underline\tau,\bar\tau]$.
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), §3 pp. 6–11, (1) p. 8, (4)–(5) p. 11, p. 12, (8) p. 15, p. 21, pp. A1, A6 (PDF 33, 38)

import Mathlib

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **The staffing system of §3.** Lu–Zheng–Zhong, *Maximizing the Benefits of an On-Demand
Workforce*, SSRN:2783617 (PDF of 2023-05-13), §3, pp. 6–9.

`n ≥ 1` firms indexed by `Fin n` face demands `X i` on a probability space `(Ω, P)`. The wage of
permanent workers is `c`, the understaffing rate is `p`, the on-demand population has size `N`,
and availability thresholds have cdf `G` with density `g` on the support `[τl, τu]`.

**Formalization Note.** `τl`, `τu` are the paper's `τ̲`, `τ̄`; `τu` is finite because the support is
the closed interval `[τ̲, τ̄]`. "Continuous and nonnegative with `F_i(0) = 0`" is `0 ≤ X i` a.s. and
an atomless law, `P(X_i = x) = 0` for every `x`. The joint law of the demands is arbitrary (p. 7, "not necessarily independent or
identical"). "`G` log-concave" concerns the cdf: `log ∘ G` is concave on `(τl, τu]`. "Density `g`
strictly positive on `[τ̲, τ̄]`" is: `G` has derivative `g > 0` within `[τl, τu]`, one-sided at the
ends. `G` is `0` left of `τl` and `1` right of `τu`. The assumption that `N` is "sufficiently large"
is not a field; it appears, pinned down, only where it is used (`theorem_1`). -/
structure Model (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) where
  /-- `P` is a probability measure. -/
  isProb : IsProbabilityMeasure P
  /-- There is at least one firm: `I = {1, …, n}`. -/
  n_pos : 0 < n
  /-- The demands `X_i`. -/
  X : Fin n → Ω → ℝ
  measurable_X : ∀ i, Measurable (X i)
  integrable_X : ∀ i, Integrable (X i) P
  nonneg_X : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω
  atomless_X : ∀ (i : Fin n) (x : ℝ), P {ω | X i ω = x} = 0
  /-- The wage rate `c` of permanent workers. -/
  c : ℝ
  /-- The understaffing cost rate `p`. -/
  p : ℝ
  /-- The lower end `τ̲` of the support of the availability threshold. -/
  τl : ℝ
  /-- The upper end `τ̄` of the support of the availability threshold. -/
  τu : ℝ
  /-- The size `N` of the population of on-demand workers. -/
  N : ℝ
  c_pos : 0 < c
  c_lt_p : c < p
  τl_pos : 0 < τl
  τl_lt_p : τl < p
  τl_lt_τu : τl < τu
  N_pos : 0 < N
  /-- The cdf `G` of the availability threshold. -/
  G : ℝ → ℝ
  /-- The density `g` of the availability threshold. -/
  g : ℝ → ℝ
  continuous_G : Continuous G
  monotone_G : Monotone G
  G_of_le : ∀ x, x ≤ τl → G x = 0
  G_of_ge : ∀ x, τu ≤ x → G x = 1
  g_pos : ∀ x ∈ Set.Icc τl τu, 0 < g x
  hasDerivWithinAt_G : ∀ x ∈ Set.Icc τl τu, HasDerivWithinAt G (g x) (Set.Icc τl τu) x
  logConcave_G : ConcaveOn ℝ (Set.Ioc τl τu) (Real.log ∘ G)

/-- `a` satisfies the restrictions (1), p. 8, for the vacancies `x` and the workforce `s`:
`0 ≤ a i ≤ x i` for every firm and `∑ i, a i ≤ s`. -/
def IsFeasibleAlloc {n : ℕ} (x : Fin n → ℝ) (s : ℝ) (a : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ a i ∧ a i ≤ x i) ∧ ∑ i, a i ≤ s

/-- **The set `𝒜` of allocation policies**, (1), p. 8–9. A randomized policy is a Markov kernel
from `(x̂, S)` to allocations, and `κ ∈ 𝒜` iff for all `x̂ ≥ 0`, `S ≥ 0` the restrictions (1) hold
`κ (x̂, S)`-almost surely.

**Formalization Note.** Policies as Markov kernels is the reading of "`A(X̂, S)` does not need to be
a deterministic function of `X̂` and `S`" (p. 8). A deterministic measurable policy is a
deterministic kernel. -/
def IsPolicy {n : ℕ} (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) : Prop :=
  IsMarkovKernel κ ∧ ∀ (x : Fin n → ℝ) (s : ℝ), 0 ≤ x → 0 ≤ s →
    ∀ᵐ a ∂κ (x, s), IsFeasibleAlloc x s a

/-- **The no-waste condition (4)**, p. 11, for a policy: for all `x̂ ≥ 0`, `S ≥ 0`,
`κ (x̂, S)`-almost surely `∑ i, a i = min {S, ∑ i, x̂ i}`. -/
def IsNoWaste {n : ℕ} (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) : Prop :=
  ∀ (x : Fin n → ℝ) (s : ℝ), 0 ≤ x → 0 ≤ s →
    ∀ᵐ a ∂κ (x, s), ∑ i, a i = min s (∑ i, x i)

/-- The first `l` elements `{j(1), …, j(l)}` of the permutation `j` (p. A6, Claim 3; PDF 38). In
Lean the elements are `j 0, …, j (l - 1)`. -/
def topSet {n : ℕ} (j : Equiv.Perm (Fin n)) (l : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ((j⁻¹ i : Fin n) : ℕ) < l

/-- **The greedy vector `x*` of Claim 3**, p. A6 (PDF 38): the marginal
`g({j(1), …, j(l + 1)}) − g({j(1), …, j(l)})` at the position `l + 1 ≤ k`, and `0` at later positions.

**Formalization Note.** The first line of the printed display, `x*_{j(1)} = g({j(1)})`, is the case
`l = 0` of the marginal, since a rank function has `g(∅) = 0`. -/
noncomputable def greedyVector {n : ℕ} (g : Finset (Fin n) → ℝ) (j : Equiv.Perm (Fin n)) (k : ℕ) :
    Fin n → ℝ :=
  fun i => if ((j⁻¹ i : Fin n) : ℕ) < k then
    g (topSet j (((j⁻¹ i : Fin n) : ℕ) + 1)) - g (topSet j ((j⁻¹ i : Fin n) : ℕ)) else 0

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)

/-- The tail `F̄_i(x) = P(X_i > x)`, p. 7. -/
noncomputable def Fbar (i : Fin n) (x : ℝ) : ℝ := P.real {ω | x < M.X i ω}

/-- The on-demand workforce `S(η) = N G(η)`, p. 8. -/
noncomputable def S (η : ℝ) : ℝ := M.N * M.G η

/-- The vacancy `X̂_i = (X_i − Q_i)⁺` of firm `i`, p. 7. -/
noncomputable def vac (Q : Fin n → ℝ) (i : Fin n) (ω : Ω) : ℝ := max (M.X i ω - Q i) 0

/-- The vector of vacancies `X̂ = (X̂_1, …, X̂_n)`. -/
noncomputable def vacVec (Q : Fin n → ℝ) (ω : Ω) : Fin n → ℝ := fun i => M.vac Q i ω

/-- The vacancy vector is measurable, so its law `P.map (M.vacVec Q)` (used by the TFRB policy) is
a probability measure, not the junk zero measure. -/
theorem measurable_vacVec (Q : Fin n → ℝ) : Measurable (M.vacVec Q) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact ((M.measurable_X i).sub_const (Q i)).max measurable_const

/-- The mean vacancy `E[(X_i − Q_i)⁺]`. The integrand is dominated by `|X_i| + |Q_i|`. -/
noncomputable def mean (Q : Fin n → ℝ) (i : Fin n) : ℝ := ∫ ω, M.vac Q i ω ∂P

/-- **The system cost (5)**, p. 11:
`C(Q, η) = p E[(∑_i (X_i − Q_i)⁺ − S)⁺] + η N G(η) + c ∑_i Q_i` with `S = N G(η)`. -/
noncomputable def C (Q : Fin n → ℝ) (η : ℝ) : ℝ :=
  M.p * ∫ ω, max (∑ i, M.vac Q i ω - M.S η) 0 ∂P + η * M.S η + M.c * ∑ i, Q i

/-- **A system-wide optimum**: `(Q, η)` minimizes (5) over `Q ≥ 0` and `η ∈ ℝ` (p. 10, "which
minimizes the total expected cost of the staffing system"; p. 11).

**Formalization Note.** This is the paper's own definition, not the formulas of Theorem 1: those
are a theorem about minimizers (`theorem_1`). -/
def IsSystemOptimum (Q : Fin n → ℝ) (η : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ (Q' : Fin n → ℝ) (η' : ℝ), 0 ≤ Q' → M.C Q η ≤ M.C Q' η'

/-- **The total cost before the no-waste simplification**, p. 11 (and p. A6, PDF 38):
`p ∑_i E[(X_i − Q_i)⁺ − A_i] + η N G(η) + c ∑_i Q_i`, for a policy `κ`. -/
noncomputable def origCost (Q : Fin n → ℝ) (η : ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) : ℝ :=
  M.p * ∑ i, ∫ ω, ∫ a, (M.vac Q i ω - a i) ∂κ (M.vacVec Q ω, M.S η) ∂P
    + η * M.S η + M.c * ∑ i, Q i

/-- The inverse `G⁻¹` of `G` on the support `[τl, τu]`, p. A1. `G` is strictly increasing there,
so for `u ∈ [0, 1]` this is the unique point of the support with `G = u`. -/
noncomputable def Ginv (u : ℝ) : ℝ := Function.invFunOn M.G (Set.Icc M.τl M.τu) u

/-- **The cost `Ĉ(Q, S)`** in the variable `S`, p. A1 (PDF 33):
`Ĉ(Q, S) = p E[(∑_i (X_i − Q_i)⁺ − S)⁺] + G⁻¹(S/N) S + c ∑_i Q_i`. -/
noncomputable def Chat (Q : Fin n → ℝ) (s : ℝ) : ℝ :=
  M.p * ∫ ω, max (∑ i, M.vac Q i ω - s) 0 ∂P + M.Ginv (s / M.N) * s + M.c * ∑ i, Q i

/-- The function `φ(x) = x + G(x)/g(x)` of p. 12 and p. A1. -/
noncomputable def phi (x : ℝ) : ℝ := x + M.G x / M.g x

/-- The tail `1 − F_{ΣX}(x) = P(∑_i X_i > x)` of total demand, p. 12. -/
noncomputable def tailSum (x : ℝ) : ℝ := P.real {ω | x < ∑ i, M.X i ω}

/-- **The permanent-only staffing level**, p. 12: `Q` solves `p F̄_i(Q_i) = c` for every `i`.

**Formalization Note.** Such a `Q` need not be unique when `F_i` is flat. `phiP` and `hp` do not
depend on the choice. Any solution is nonnegative, since `F̄_i = 1` on the negative half-line. -/
def IsPermanentBenchmark (Q : Fin n → ℝ) : Prop := ∀ i, M.p * M.Fbar i (Q i) = M.c

/-- The threshold `φ^p = p P(X_i > Q_i^p for some i)`, p. 12: a union event over the firms. -/
noncomputable def phiP (Q : Fin n → ℝ) : ℝ := M.p * P.real {ω | ∃ i, Q i < M.X i ω}

/-- The stand-alone cost `h_i^p = p E[(X_i − Q_i^p)⁺] + c Q_i^p` of firm `i`, p. 21. -/
noncomputable def hp (Q : Fin n → ℝ) (i : Fin n) : ℝ := M.p * M.mean Q i + M.c * Q i

/-- The set function `g(U) = E[min {S, ∑_{i ∈ U} (X_i − Q_i)⁺}]`, right side of (8), p. 15, and
p. A6 (PDF 38). -/
noncomputable def rankFn (Q : Fin n → ℝ) (s : ℝ) (U : Finset (Fin n)) : ℝ :=
  ∫ ω, min s (∑ i ∈ U, M.vac Q i ω) ∂P

/-- **Feasibility for the linear program (8)**, p. 15: `β ≥ 0` and
`∑_{i ∈ U} β_i E[X̂_i] ≤ E[min {S, ∑_{i ∈ U} X̂_i}]` for all `U ⊆ I`. -/
def IsFeasibleLP (Q : Fin n → ℝ) (s : ℝ) (β : Fin n → ℝ) : Prop :=
  0 ≤ β ∧ ∀ U : Finset (Fin n), ∑ i ∈ U, β i * M.mean Q i ≤ M.rankFn Q s U

/-- **Optimality for the linear program (8)**, p. 15: `β` is feasible and maximizes
`∑_i β_i E[X̂_i]` over the feasible set. -/
def IsOptimalLP (Q : Fin n → ℝ) (s : ℝ) (β : Fin n → ℝ) : Prop :=
  M.IsFeasibleLP Q s β ∧ ∀ β', M.IsFeasibleLP Q s β' →
    ∑ i, β' i * M.mean Q i ≤ ∑ i, β i * M.mean Q i

/-- The expected allocation `E[A_i(X̂, s)]` of firm `i` under the policy `κ`, with `X̂ = (X − Q)⁺`:
the expectation runs over `X` and over the policy's randomization (p. 9). -/
noncomputable def expAlloc (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (Q : Fin n → ℝ) (s : ℝ)
    (i : Fin n) : ℝ :=
  ∫ ω, ∫ a, a i ∂κ (M.vacVec Q ω, s) ∂P

end Model

end OnDemandCoord


