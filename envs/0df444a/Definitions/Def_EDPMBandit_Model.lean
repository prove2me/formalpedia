-- Prove2me | Definitions.Def_EDPMBandit_Model
-- name    : EDPMBandit_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:33.369997+00:00
-- url     : https://prove2.me/theorems/095b87e2-6a97-43eb-b450-c22534aa4a17
-- title:
--   The bandit model of §3: rewards, admissible policies, empirical and pseudo empirical distributions, $D^\Delta$, $\Delta_i$, $D$, $\rho$
-- statement:
--   There are $K$ arms. Arm $i$ has a reward distribution $F^{(i)}$, an arbitrary probability distribution on $\mathbb R$, and a sequence of rewards $X_{i,1},X_{i,2},\dots$ with law $F^{(i)}$. All rewards $X_{i,t}$ ($i\le K$, $t\ge1$) are mutually independent, and a randomization variable $V$ with values in an arbitrary measurable space is independent of all of them.
--
--   An **admissible policy** chooses the arm $\pi_t$ of round $t$ as a measurable function of $V$ and of the history $(\pi_1,X_{\pi,1},\dots,\pi_{t-1},X_{\pi,t-1})$; the pull count is $\tau_i(t)=\sum_{s\le t}\mathbb 1\{\pi_s=i\}$ and the observed reward is $X_{\pi,t}=X_{i,\tau_i(t)}$ on $\{\pi_t=i\}$ (eqs. (1)–(3)).
--
--   Distribution functions live in a real vector space $L$ of functions on $\mathbb R$ that contains every indicator $\mathbb I_{[a,\infty)}$ and every distribution function, equipped with a seminorm $\|\cdot\|$. The **empirical distribution** of $x_1,\dots,x_t$ is $\hat F_t=\frac1t\sum_{s=1}^t\mathbb I_{[x_s,\infty)}$ (4); $\hat F^\pi_T$ uses the observed rewards $X_{\pi,1},\dots,X_{\pi,T}$ (5) and $\hat F^{(i)}_t$ the first $t$ rewards of arm $i$ (6). The **pseudo empirical distribution** is
--
--   $$
--   F^\pi_T=\frac1T\sum_{i=1}^K\tau_i(T)\,F^{(i)} \qquad (12).
--   $$
--
--   Further, $D^\Delta=\{\sum_i p_iF^{(i)}:p\in\Delta\}$ is the set of mixtures of the arm distributions (9), $\Delta_i=U(F^{(i^*)})-U(F^{(i)})$ is the gap of arm $i$, $D=\max_{i,j}\|F^{(i)}-F^{(j)}\|$ and $\rho=\max_{i\ne i^*}\|F^{(i^*)}-F^{(i)}\|/\Delta_i$ (14), $L=b(1+D^{q-1})$ (Lemma 1), and the **pseudo regret** is $\bar R_\pi(T)=\mathbb E[U(F^{(i^*)})-U(F^\pi_T)]$ (13). The standing assumption of p.5 that the expectations exist is recorded as measurability of $U$ and of the seminorm along empirical distributions.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The bandit is the structure `BanditModel` (probability measure, arm laws, reward stack `X i k` = the paper's $X_{i,k+1}$, randomization `V`, measurability, `iIndepFun` of the stack, laws, independence of `V`); policies are `Policy` (measurable decision rules `rule n : 𝒱 → (Fin n → Fin K × ℝ) → Fin K`), and the history is built recursively. The pull count is the published `ImprovedLinBandits.UCBDelta.pullCount`. The space is `DistSpace` (a submodule of `ℝ → ℝ` with the two membership properties); the seminorm `N : Seminorm ℝ S.L` and $U:L\to\mathbb R$ are arguments of each statement. $D$ and $\rho$ are suprema over finite index types ($\rho=0$ for $K=1$, where it multiplies an empty sum). `MeasurableAlongEmp` is the measurability reading of the standing assumption.
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, pp.4–8: §3 model and admissible policies (1)–(3), (4)–(6), (9), standing assumption p.5, (12), (13), Δ_i, (14), L of Lemma 1

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Cassel–Mannor–Zeevi, *A General Framework for Bandit Problems Beyond Cumulative
Objectives*, arXiv:1806.01380v3, p.5: the indicator `𝕀_{[a,∞]}` of the interval `[a, ∞]`,
i.e. the distribution function of the point mass at `a`.

**Formalization Note.** The paper defines the indicator on the extended real line; here it is
restricted to `ℝ` (`y ↦ 1` if `a ≤ y`, else `0`). The values of a distribution function at
`±∞` are `0` and `1` for every distribution, so nothing is lost. -/
noncomputable def stepFn (a : ℝ) : ℝ → ℝ := fun y => if a ≤ y then 1 else 0

/-- The seminormed space `L_{‖·‖}` of distribution functions, arXiv:1806.01380v3, pp.5–6:
"D is a subset of an infinite dimensional vector space … our analysis is done with respect to a
general seminorm ‖·‖ and its matching seminormed space L_{‖·‖}".

**Formalization Note.** `L` is any real linear subspace of the functions `ℝ → ℝ` that contains
every indicator `𝕀_{[a,∞]}` and the distribution function `x ↦ μ((-∞, x])` of every
probability measure `μ` on `ℝ` (Mathlib's `ProbabilityTheory.cdf`). The span of these
functions is the smallest choice; any larger subspace is allowed. The seminorm is a separate
argument `N : Seminorm ℝ S.L` of every statement (a seminorm, not a norm: `N h = 0` with
`h ≠ 0` is allowed). -/
structure DistSpace where
  /-- The vector space `L` of p.6. -/
  L : Submodule ℝ (ℝ → ℝ)
  /-- Every indicator `𝕀_{[a,∞]}` (the empirical distribution of one sample) lies in `L`. -/
  stepFn_mem : ∀ a : ℝ, stepFn a ∈ L
  /-- Every distribution function lies in `L` (`D ⊆ L`). -/
  cdf_mem : ∀ μ : ProbabilityMeasure ℝ, (⇑(cdf (μ : Measure ℝ)) : ℝ → ℝ) ∈ L

namespace DistSpace

variable (S : DistSpace)

/-- `𝕀_{[a,∞]}` as an element of `L`. -/
noncomputable def step (a : ℝ) : S.L := ⟨stepFn a, S.stepFn_mem a⟩

/-- The distribution function of a probability measure `μ` on `ℝ`, as an element of `L`. -/
noncomputable def distFn (μ : ProbabilityMeasure ℝ) : S.L :=
  ⟨cdf (μ : Measure ℝ), S.cdf_mem μ⟩

/-- The empirical distribution (4), p.4: `F̂_t(x_1, …, x_t; ·) = (1/t) ∑_{s=1}^t 𝕀_{[x_s,∞]}`.
At `t = 0` the value is `0` (junk; every statement uses `t ≥ 1` or multiplies by `t = 0`). -/
noncomputable def emp {t : ℕ} (x : Fin t → ℝ) : S.L :=
  (t : ℝ)⁻¹ • ∑ s, S.step (x s)

end DistSpace

/-- The bandit of §3, arXiv:1806.01380v3, p.4: `K` arms; arm `i` carries an i.i.d. sequence of
rewards with law `F^{(i)}` (`ν i`), all rewards mutually independent, and a randomization
variable `V` independent of the rewards.

**Formalization Note.** Arms are `Fin K`. The reward stack is `X i k`, the reward received at
the `(k+1)`-st pull of arm `i` (the paper's `X_{i,k+1}`; zero-based sample index). Mutual
independence over all `(i, k)` is `iIndepFun`; the law of every `X i k` is `ν i`, an arbitrary
probability measure on `ℝ` (no moment or support assumption). `V` takes values in an arbitrary
measurable space `𝒱` and is independent of the whole stack. -/
structure BanditModel (K : ℕ) (Ω : Type*) [MeasurableSpace Ω] (𝒱 : Type*)
    [MeasurableSpace 𝒱] where
  /-- The underlying probability measure. -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  /-- The arm laws `F^{(i)}`. -/
  ν : Fin K → ProbabilityMeasure ℝ
  /-- The reward stack: `X i k` is the reward of the `(k+1)`-st pull of arm `i`. -/
  X : Fin K → ℕ → Ω → ℝ
  /-- The randomization variable `V`. -/
  V : Ω → 𝒱
  measurable_X : ∀ i k, Measurable (X i k)
  measurable_V : Measurable V
  iIndep_X : iIndepFun (fun p : Fin K × ℕ => X p.1 p.2) P
  law_X : ∀ i k, P.map (X i k) = (ν i : Measure ℝ)
  indep_V : IndepFun V (fun ω (p : Fin K × ℕ) => X p.1 p.2 ω) P

/-- An admissible policy, (1), arXiv:1806.01380v3, p.4: the arm of round `n + 1` is a measurable
function of the randomization `V` and of the history `(π_1, X_{π,1}, …, π_n, X_{π,n})` of the
first `n` rounds.

**Formalization Note.** `rule n v h` is the arm chosen at round `n + 1` when `V = v` and the
history of the first `n` rounds is `h`, given as `n` (arm, reward) pairs. Joint measurability of
`rule n` makes `π_{n+1}` measurable with respect to `H_n = σ(V, π_1, X_{π,1}, …, π_n, X_{π,n})`,
as on p.4; conversely every `H_n`-measurable choice is of this form. The class therefore
contains every non-anticipating policy, randomized through `V` or not. -/
structure Policy (K : ℕ) (𝒱 : Type*) [MeasurableSpace 𝒱] where
  /-- The decision rule of round `n + 1`. -/
  rule : (n : ℕ) → 𝒱 → (Fin n → Fin K × ℝ) → Fin K
  measurable_rule : ∀ n, Measurable (Function.uncurry (rule n))

variable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]

/-- The history `(π_1, X_{π,1}, …, π_n, X_{π,n})` of the first `n` rounds, built by the
recursion (1)–(3), p.4: round `n + 1` plays `a = rule n V h` and observes the next unused reward
of arm `a`, `X_{a, τ_a(n) + 1}` (zero-based `X a (τ_a(n))`, where `τ_a(n)` is the number of
earlier pulls of `a` in `h`). -/
noncomputable def history (M : BanditModel K Ω 𝒱) (π : Policy K 𝒱) :
    (n : ℕ) → Ω → (Fin n → Fin K × ℝ)
  | 0, _ => fun s => s.elim0
  | n + 1, ω =>
    let h := history M π n ω
    let a := π.rule n (M.V ω) h
    Fin.snoc (α := fun _ => Fin K × ℝ) h
      (a, M.X a ((Finset.univ.filter (fun s : Fin n => (h s).1 = a)).card) ω)

/-- The arm process `π_t`, (1), p.4, for rounds `t ≥ 1`: `π_t = rule (t-1) V (history of the
first t-1 rounds)`. The value at `t = 0` (no round 0) is the round-1 choice and is never used. -/
noncomputable def arm (M : BanditModel K Ω 𝒱) (π : Policy K 𝒱) (t : ℕ) (ω : Ω) : Fin K :=
  π.rule (t - 1) (M.V ω) (history M π (t - 1) ω)

/-- The pull count `τ_i(t) = ∑_{s=1}^t 1{π_s = i}`, (2), p.4: the published
`ImprovedLinBandits.UCBDelta.pullCount` of the arm process (rounds `1, …, t`; `τ_i(0) = 0`). -/
noncomputable def pulls (M : BanditModel K Ω 𝒱) (π : Policy K 𝒱) (i : Fin K) (t : ℕ)
    (ω : Ω) : ℕ :=
  ImprovedLinBandits.UCBDelta.pullCount (arm M π) i t ω

/-- The observed reward `X_{π,t} = X_{i, τ_i(t)}` on `{π_t = i}`, (3), p.4, for `t ≥ 1`: the
`τ_i(t)`-th reward of arm `i = π_t`, i.e. zero-based `X i (τ_i(t-1))`. -/
noncomputable def obsReward (M : BanditModel K Ω 𝒱) (π : Policy K 𝒱) (t : ℕ) (ω : Ω) : ℝ :=
  M.X (arm M π t ω) (pulls M π (arm M π t ω) (t - 1) ω) ω

/-- The distribution function `F^{(i)}` of arm `i`, as an element of `L`. -/
noncomputable def armDist (S : DistSpace) (M : BanditModel K Ω 𝒱) (i : Fin K) : S.L :=
  S.distFn (M.ν i)

/-- `F̂^{(i)}_t = F̂_t(X_{i,1}, …, X_{i,t})`, (6), p.5: the empirical distribution of the first `t`
rewards of arm `i`. -/
noncomputable def empArm (S : DistSpace) (M : BanditModel K Ω 𝒱) (i : Fin K) (t : ℕ)
    (ω : Ω) : S.L :=
  S.emp (fun s : Fin t => M.X i s ω)

/-- `F̂^π_T = F̂_T(X_{π,1}, …, X_{π,T})`, (5), p.5: the empirical distribution of the rewards
collected by policy `π` in rounds `1, …, T`. -/
noncomputable def empPolicy (S : DistSpace) (M : BanditModel K Ω 𝒱) (π : Policy K 𝒱) (T : ℕ)
    (ω : Ω) : S.L :=
  S.emp (fun s : Fin T => obsReward M π (s.val + 1) ω)

/-- The pseudo empirical distribution `F^π_T = (1/T) ∑_{i=1}^K τ_i(T) F^{(i)}`, (12), p.7. -/
noncomputable def pseudoEmp (S : DistSpace) (M : BanditModel K Ω 𝒱) (π : Policy K 𝒱) (T : ℕ)
    (ω : Ω) : S.L :=
  (T : ℝ)⁻¹ • ∑ i, (pulls M π i T ω : ℝ) • armDist S M i

/-- `D^Δ = {F_p = ∑_i p_i F^{(i)} : p ∈ Δ}`, (9), p.5: the convex combinations of the arm
distributions (`Δ` the probability simplex, Mathlib's `stdSimplex`). -/
noncomputable def mixtures (S : DistSpace) (M : BanditModel K Ω 𝒱) : Set S.L :=
  {F | ∃ p ∈ stdSimplex ℝ (Fin K), F = ∑ i, p i • armDist S M i}

/-- The sub-optimality gap `Δ_i = U(F^{(i*)}) − U(F^{(i)})`, p.8. -/
noncomputable def gap (S : DistSpace) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱) (istar i : Fin K) : ℝ :=
  U (armDist S M istar) - U (armDist S M i)

/-- The diameter `D = max_{i,j} ‖F^{(i)} − F^{(j)}‖` of `D^Δ`, (14), p.8.

**Formalization Note.** A supremum over the finite type `Fin K × Fin K`, so it is the maximum
when `K ≥ 1` (`0` for `K = 0`). -/
noncomputable def diam (S : DistSpace) (N : Seminorm ℝ S.L) (M : BanditModel K Ω 𝒱) : ℝ :=
  ⨆ p : Fin K × Fin K, N (armDist S M p.1 - armDist S M p.2)

/-- The maximum gap ratio `ρ = max_{i ≠ i*} ‖F^{(i*)} − F^{(i)}‖ / Δ_i`, (14), p.8.

**Formalization Note.** A supremum over the finite type `{i // i ≠ i*}`; every statement using
it assumes `Δ_i > 0` for `i ≠ i*`, so no division by zero occurs. For `K = 1` the index set is
empty and the value is `0`; it then multiplies an empty sum. -/
noncomputable def gapRatio (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ)
    (M : BanditModel K Ω 𝒱) (istar : Fin K) : ℝ :=
  ⨆ i : {i : Fin K // i ≠ istar}, N (armDist S M istar - armDist S M i) / gap S U M istar i

/-- The Lipschitz constant `L = b(1 + D^{q−1})` of Lemma 1, p.8 (`Real.rpow`; `0^0 = 1`). -/
noncomputable def lipConst (b q D : ℝ) : ℝ := b * (1 + D ^ (q - 1))

/-- The pseudo regret `R̄_π(T) = E[U(F^{(i*)}) − U(F^π_T)]`, (13), p.7. -/
noncomputable def pseudoRegret (S : DistSpace) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱)
    (istar : Fin K) (π : Policy K 𝒱) (T : ℕ) : ℝ :=
  ∫ ω, (U (armDist S M istar) - U (pseudoEmp S M π T ω)) ∂M.P

/-- The standing assumption of p.5, "Throughout it is assumed implicitly that the class of
distributions and performance functions is such that this expectation exists and is finite
valued".

**Formalization Note.** Encoded as Borel measurability of `U` and of the seminorm along
empirical distributions: for every sample size `t`, every `G ∈ L` and every `c ∈ ℝ`, the maps
`(x_1, …, x_t) ↦ U(G + c F̂_t(x))` and `(x_1, …, x_t) ↦ ‖G + c F̂_t(x)‖` are measurable. This
makes every expectation the paper writes a well-defined integral of a measurable function;
finiteness then follows from stability. -/
def MeasurableAlongEmp (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) : Prop :=
  ∀ (t : ℕ) (G : S.L) (c : ℝ),
    Measurable (fun x : Fin t → ℝ => U (G + c • S.emp x)) ∧
    Measurable (fun x : Fin t → ℝ => N (G + c • S.emp x))

end EDPMBandit


