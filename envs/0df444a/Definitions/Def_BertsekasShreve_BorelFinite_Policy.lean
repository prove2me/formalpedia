-- Prove2me | Definitions.Def_BertsekasShreve_BorelFinite_Policy
-- name    : BertsekasShreve_BorelFinite_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:39:56.201796+00:00
-- url     : https://prove2.me/theorems/4cad16d5-2fcb-42a7-9573-a2faf1dadd9a
-- title:
--   Policies, the K-stage cost J_{K,π}, the optimal cost J*_K, assumptions (F⁺)/(F⁻) and ε-optimality (Definitions 8.2–8.3)
-- statement:
--   Fix a model $(S,C,U,W,p,f,\alpha,g,N)$ as in Definition 8.1.
--
--   **Arithmetic and integrals in $R^*$.** Sums follow the convention $-\infty+\infty=+\infty-\infty=+\infty$, and the integral of an extended-real function is $\int f\,dp=\int f^+\,dp-\int f^-\,dp$ with the same convention.
--
--   **Policies.** A policy is $\pi=(\mu_0,\dots,\mu_{N-1})$ where each $\mu_k(du_k\mid x_0,u_0,\dots,u_{k-1},x_k)$ is a universally measurable stochastic kernel on $C$ given $SC\cdots CS$ with $\mu_k(U(x_k)\mid x_0,\dots,x_k)=1$ for every history. The policy is *semi-Markov* if each $\mu_k$ depends only on $(x_0,x_k)$, *Markov* if it depends only on $x_k$, and *nonrandomized* if each $\mu_k(\cdot\mid x_0,\dots,x_k)$ is a point mass. $\Pi'$ is the set of all policies, $\Pi$ that of Markov policies, and $U(C\mid S)$ the set of universally measurable stochastic kernels $\mu$ on $C$ given $S$ with $\mu(U(x)\mid x)=1$ for all $x$.
--
--   **Costs.** For $p\in P(S)$ and $\pi\in\Pi'$, $r_N(\pi,p)$ is the probability measure on $S_0C_0\cdots S_{N-1}C_{N-1}$ whose integral of a universally measurable $h\ge0$ is the iterated integral
--   $$\int h\,dr_N(\pi,p)=\int_{S_0}\int_{C_0}\cdots\int_{S_{N-1}}\int_{C_{N-1}}h\;\mu_{N-1}(du_{N-1}\mid\cdot)\,t(dx_{N-1}\mid x_{N-2},u_{N-2})\cdots\mu_0(du_0\mid x_0)\,p(dx_0).$$
--   For $K\le N$ the $K$-stage cost of $\pi$ at $x$ and the $K$-stage optimal cost are
--   $$J_{K,\pi}(x)=\int\Big[\sum_{k=0}^{K-1}\alpha^k g(x_k,u_k)\Big]dr_N(\pi,p_x),\qquad J^*_K(x)=\inf_{\pi\in\Pi'}J_{K,\pi}(x),$$
--   with $p_x$ the point mass at $x$; the infimum is over **all** policies.
--
--   **Assumptions.** With $q_k(\pi,p)$ the marginal of $r_N(\pi,p)$ on $S_kC_k$, assumption (F⁺) is $\int g^-\,dq_k(\pi,p_x)<\infty$ and (F⁻) is $\int g^+\,dq_k(\pi,p_x)<\infty$, for all $\pi\in\Pi'$, $x\in S$, $k=0,\dots,N-1$.
--
--   **$\varepsilon$-optimality.** For $\varepsilon>0$, $\pi$ is $K$-stage $\varepsilon$-optimal at $x$ if
--   $$J_{K,\pi}(x)\le\begin{cases}J^*_K(x)+\varepsilon&\text{if }J^*_K(x)>-\infty,\\-1/\varepsilon&\text{if }J^*_K(x)=-\infty,\end{cases}$$
--   and $\varepsilon$-optimal if this holds with $K=N$ at every $x\in S$.
--
--   **Formalization Note** `badd` is the book's addition (Mathlib's `EReal` has $\bot+\top=\bot$ instead). Histories are pairs (`Fin k → S × C`, current state). The integral against $r_N(\pi,p)$ of a function $h\ge0$ is taken to be the iterated integral of Eq. (4) (`pathInt`), which by Proposition 7.45 is $\int h\,dr_N(\pi,p)$ for every universally measurable $h\ge0$; $J_{K,\pi}$ applies it to the positive and negative parts of the stage sum. Markov policies are the policies whose kernels depend on the history only through $x_k$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 190–192, Definitions 8.2 and 8.3, Eqs. (4)–(6) and (F⁺)/(F⁻) of Chapter 8; p. 139, Eqs. (42)–(43) of Chapter 7

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.BorelFinite

open MeasureTheory

/-- A finite sum in `R*` computed with the convention (42) (`badd`); it is `+∞` as soon as one
term is `+∞`. -/
noncomputable def bsum (l : List EReal) : EReal :=
  l.foldr BertsekasShreve.FiniteHorizon.badd 0

/-- Positive part `f⁺ = max(f, 0)` of an extended-real function, as a `[0, ∞]`-valued function. -/
noncomputable def posPart {X : Type*} (f : X → EReal) : X → ENNReal :=
  fun x => (f x).toENNReal

/-- Negative part `f⁻ = max(-f, 0)` of an extended-real function, as a `[0, ∞]`-valued function. -/
noncomputable def negPart {X : Type*} (f : X → EReal) : X → ENNReal :=
  fun x => (-(f x)).toENNReal

/-- The extended integral (43) of Chapter 7 (p. 139), `∫ f = ∫ f⁺ - ∫ f⁻` with `∞ - ∞ = ∞`,
for an integration functional `I` on `[0, ∞]`-valued functions (a Lebesgue integral `∫⁻ · dp`,
or the iterated integral `pathInt` below). -/
noncomputable def extInt {X : Type*} (I : (X → ENNReal) → ENNReal) (f : X → EReal) : EReal :=
  if I (posPart f) = ⊤ then ⊤ else (I (posPart f) : EReal) - (I (negPart f) : EReal)

/-- The history `(x₀, u₀, …, x_{k-1}, u_{k-1}, x_k)` on which the `k`-th control may depend:
`k` state–control pairs followed by the current state (the space `S₀C₀⋯S_{k-1}C_{k-1}S_k`). -/
def Hist (S C : Type*) (k : ℕ) := (Fin k → S × C) × S

instance instMeasurableSpaceHist {S C : Type*} [MeasurableSpace S] [MeasurableSpace C] (k : ℕ) :
    MeasurableSpace (Hist S C k) :=
  inferInstanceAs (MeasurableSpace ((Fin k → S × C) × S))

/-- The initial state `x₀` of a history. -/
def Hist.init {S C : Type*} {k : ℕ} (h : Hist S C k) : S :=
  if hk : 0 < k then (h.1 ⟨0, hk⟩).1 else h.2

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

/-- **Definition 8.2** (p. 190). A policy `π = (μ₀, …, μ_{N-1})`: each `μ_k(du_k|x₀,u₀,…,x_k)` is a
universally measurable stochastic kernel on `C` given `SC⋯CS` with
`μ_k(U(x_k)|x₀,u₀,…,u_{k-1},x_k) = 1` for every history. The set of all policies is `Π′`. -/
structure Policy (M : Model S C W) where
  μ : (k : Fin M.N) → UMKernel (Hist S C k) C
  feasible : ∀ (k : Fin M.N) (h : Hist S C k), (μ k).toFun h (M.U h.2) = 1

/-- The set `U(C|S)` (p. 194): universally measurable stochastic kernels `μ` on `C` given `S` with
`μ(U(x)|x) = 1` for every `x ∈ S`. -/
def UCS (M : Model S C W) : Type _ := {ν : UMKernel S C // ∀ x, ν.toFun x (M.U x) = 1}

namespace Policy

variable {M : Model S C W}

/-- `π` is *Markov* (p. 190): each `μ_k` is parameterized only by the current state `x_k`. -/
def IsMarkov (π : Policy M) : Prop :=
  ∀ (k : Fin M.N) (h h' : Hist S C k), h.2 = h'.2 → (π.μ k).toFun h = (π.μ k).toFun h'

/-- `π` is *semi-Markov* (p. 190): each `μ_k` is parameterized only by `(x₀, x_k)`. -/
def IsSemiMarkov (π : Policy M) : Prop :=
  ∀ (k : Fin M.N) (h h' : Hist S C k), h.init = h'.init → h.2 = h'.2 →
    (π.μ k).toFun h = (π.μ k).toFun h'

/-- `π` is *nonrandomized* (p. 190): every `μ_k(·|x₀,…,x_k)` assigns mass one to a point of `C`. -/
def IsNonrandomized (π : Policy M) : Prop :=
  ∀ (k : Fin M.N) (h : Hist S C k), ∃ u : C, (π.μ k).toFun h = Measure.dirac u

/-- `π` is the Markov policy `(ν₀, …, ν_{N-1})` with `ν_k ∈ U(C|S)`: `μ_k(·|x₀,…,x_k) = ν_k(·|x_k)`. -/
def IsMarkovWith (π : Policy M) (ν : Fin M.N → UCS M) : Prop :=
  ∀ (k : Fin M.N) (h : Hist S C k), (π.μ k).toFun h = (ν k).1.toFun h.2

/-- The kernel `μ_k` as a function of the history, extended by the zero measure for `k ≥ N`
(never used: the path space has exactly `N` stages). -/
noncomputable def kernel (π : Policy M) (k : ℕ) (h : Hist S C k) : Measure C :=
  if hk : k < M.N then (π.μ ⟨k, hk⟩).toFun h else 0

end Policy

/-- Law of the state `x_n` given the earlier pairs `(x₀,u₀,…,x_{n-1},u_{n-1})`: the initial
distribution `p` for `n = 0`, and `t(·|x_{n-1},u_{n-1})` otherwise. -/
noncomputable def stateLaw (M : Model S C W) (p : Measure S) :
    (n : ℕ) → (Fin n → S × C) → Measure S
  | 0, _ => p
  | n + 1, ω => M.t (ω (Fin.last n))

/-- The iterated integral on the right-hand side of Eq. (4) of Chapter 8 (p. 191), for a
nonnegative function `h` of `(x₀,u₀,…,x_{n-1},u_{n-1})`:
`∫_{S₀}∫_{C₀}⋯∫_{S_{n-1}}∫_{C_{n-1}} h · μ_{n-1}(du_{n-1}|…) t(dx_{n-1}|x_{n-2},u_{n-2}) ⋯ μ₀(du₀|x₀) p(dx₀)`.
It is computed by integrating out the last pair `(x_{n-1}, u_{n-1})` and recursing. -/
noncomputable def pathInt (M : Model S C W) (π : Policy M) (p : Measure S) :
    (n : ℕ) → ((Fin n → S × C) → ENNReal) → ENNReal
  | 0, h => h Fin.elim0
  | n + 1, h => pathInt M π p n (fun ω =>
      ∫⁻ x, ∫⁻ u, h (Fin.snoc (α := fun _ => S × C) ω (x, u)) ∂(π.kernel n (ω, x))
        ∂(stateLaw M p n ω))

/-- `∫ h dr_N(π, p)` for `h ≥ 0` on `S₀C₀⋯S_{N-1}C_{N-1}`: by Proposition 7.45 and Eq. (4) of
Chapter 8, `r_N(π, p)` is the unique probability measure whose integral of every universally
measurable `h ≥ 0` is the iterated integral `pathInt`. -/
noncomputable def rInt (M : Model S C W) (π : Policy M) (p : Measure S) :
    ((Fin M.N → S × C) → ENNReal) → ENNReal :=
  pathInt M π p M.N

/-- The `K`-stage cost `∑_{k=0}^{K-1} α^k g(x_k, u_k)` of a path, summed with the convention (42). -/
noncomputable def stageSum (M : Model S C W) (K : ℕ) (ω : Fin M.N → S × C) : EReal :=
  bsum ((List.finRange M.N).map fun k : Fin M.N =>
    if (k : ℕ) < K then ((M.α ^ (k : ℕ) : ℝ) : EReal) * M.g (ω k) else 0)

/-- **Definition 8.3**, Eq. (5) (p. 191). The `K`-stage cost of `π` at `x`:
`J_{K,π}(x) = ∫ [∑_{k=0}^{K-1} α^k g(x_k,u_k)] dr_N(π, p_x)`, with `p_x` the point mass at `x`
and the integral taken in the extended sense (43) of Chapter 7. -/
noncomputable def J (M : Model S C W) (K : ℕ) (π : Policy M) (x : S) : EReal :=
  extInt (rInt M π (Measure.dirac x)) (stageSum M K)

/-- **Definition 8.3**, Eq. (6) (p. 191). The `K`-stage optimal cost
`J*_K(x) = inf_{π ∈ Π′} J_{K,π}(x)`, the infimum over **all** policies. -/
noncomputable def Jstar (M : Model S C W) (K : ℕ) (x : S) : EReal :=
  ⨅ π : Policy M, J M K π x

/-- Assumption (F⁺) (p. 192): `∫_{S_kC_k} g⁻ dq_k(π, p_x) < ∞` for all `π ∈ Π′`, `x ∈ S`,
`k = 0, …, N-1`, where `q_k(π, p_x)` is the marginal of `r_N(π, p_x)` on `S_kC_k`. -/
def FPlus (M : Model S C W) : Prop :=
  ∀ (π : Policy M) (x : S) (k : Fin M.N),
    rInt M π (Measure.dirac x) (fun ω => negPart M.g (ω k)) < ⊤

/-- Assumption (F⁻) (p. 192): `∫_{S_kC_k} g⁺ dq_k(π, p_x) < ∞` for all `π ∈ Π′`, `x ∈ S`,
`k = 0, …, N-1`. -/
def FMinus (M : Model S C W) : Prop :=
  ∀ (π : Policy M) (x : S) (k : Fin M.N),
    rInt M π (Measure.dirac x) (fun ω => posPart M.g (ω k)) < ⊤

/-- **Definition 8.3** (p. 191). `π` is `K`-stage `ε`-optimal at `x`:
`J_{K,π}(x) ≤ J*_K(x) + ε` if `J*_K(x) > -∞`, and `J_{K,π}(x) ≤ -1/ε` if `J*_K(x) = -∞`. -/
def IsEpsOptimalAt (M : Model S C W) (K : ℕ) (ε : ℝ) (π : Policy M) (x : S) : Prop :=
  (Jstar M K x ≠ ⊥ → J M K π x ≤ Jstar M K x + (ε : EReal)) ∧
  (Jstar M K x = ⊥ → J M K π x ≤ ((-1 / ε : ℝ) : EReal))

/-- **Definition 8.3** (p. 191). `π` is `ε`-optimal: `N`-stage `ε`-optimal at every `x ∈ S`. -/
def IsEpsOptimal (M : Model S C W) (ε : ℝ) (π : Policy M) : Prop :=
  ∀ x, IsEpsOptimalAt M M.N ε π x

end BertsekasShreve.BorelFinite


