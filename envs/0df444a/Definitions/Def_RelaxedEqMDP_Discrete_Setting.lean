-- Prove2me | Definitions.Def_RelaxedEqMDP_Discrete_Setting
-- name    : RelaxedEqMDP_Discrete_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:01.347309+00:00
-- url     : https://prove2.me/theorems/f98dbcd5-6100-435b-9eb0-407ff94ad06a
-- title:
--   §2, pp. 4–9 — time-inconsistent MDP with relaxed controls: values, entropy, Gibbs map, equilibria, Assumptions 2.1–2.3
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   **Model.** A *relaxed feedback control* is a map $\pi:\mathcal S\to\mathcal P(U)$; $\Pi$ is the set of them. Given $\pi\in\Pi$, at a time $t$ in state $X_t=i$ an action $u\sim\pi(i)$ is sampled and $X_{t+1}$ is drawn from $p^u_i$. Equivalently (Remark 2.1) the chain has transition matrix $p^\pi_{ij}=\int_U p^u_{ij}\,(\pi(i))(du)$. For $\mu\in\mathcal P(U)$ write $f^\mu(t,i)=\int_U f(t,i,u)\,\mu(du)$.
--
--   **Entropy and regular controls (Definition 2.1).** For a density $\rho$ on $U$, $\mathcal H(\rho)=-\int_U\ln(\rho(u))\rho(u)\,du$ (2.3). A control $\pi$ is *regular*, $\pi\in\Pi_r$, if each $\pi(i)$ has a density $\rho_i$ on $U$ with $\mathcal H(\rho_i)>-\infty$.
--
--   **Values.** With $\delta$ a discount function ($\delta:\mathbb N_0\to[0,1]$ nonincreasing, $\delta(0)=1$) and $\lambda>0$,
--   $$J^\pi(i)=\mathbb E_i\Big[\sum_{k\ge0}f^{\pi(X_k)}(k,X_k)\Big],\qquad J^\pi_\lambda(i)=\mathbb E_i\Big[\sum_{k\ge0}\big(f^{\pi(X_k)}(k,X_k)+\lambda\delta(k)\mathcal H(\pi(X_k))\big)\Big]$$
--   ((2.1), (2.4)), and $V^\pi$, $V^\pi_\lambda$ are the same sums with $f(1+k,\cdot)$ and $\delta(1+k)$ ((2.19), (2.9)). The concatenation $\pi'\otimes_1\pi$ uses $\pi'$ at time $0$ and $\pi$ from time $1$ on; its values are the same expected sums for this time-dependent control.
--
--   **Equilibria (Definition 2.2).** $\pi\in\Pi_r$ is a *regular relaxed equilibrium* (for (2.4)) if $J^{\pi'\otimes_1\pi}_\lambda(i)-J^\pi_\lambda(i)\le0$ for all $i\in\mathcal S$ and $\pi'\in\Pi_r$ (2.7); $\pi\in\Pi$ is a *relaxed equilibrium* (for (2.1)) if $J^{\pi'\otimes_1\pi}(i)-J^\pi(i)\le0$ for all $i$ and $\pi'\in\Pi$ (2.8).
--
--   **Gibbs map and operators.** $\Gamma_\lambda(y,i)(u)=e^{\frac1\lambda(f(0,i,u)+p^u_i\cdot y)}\big/\int_U e^{\frac1\lambda(f(0,i,v)+p^v_i\cdot y)}dv$ (2.12), $\Phi_\lambda(\pi)=\Gamma_\lambda(V^\pi_\lambda,\cdot)$ (2.14), $\Psi_\lambda(y)=V^{\Gamma_\lambda(y,\cdot)}_\lambda$. Without regularization: $E(y,i)=\arg\max_{u\in U}\{f(0,i,u)+p^u_i\cdot y\}$ (2.20), $\Gamma(y)=\{\pi\in\Pi:\operatorname{supp}\pi(i)\subseteq E(y,i)\ \forall i\}$ (2.21), $\Psi(y)=\{V^\pi:\pi\in\Gamma(y)\}$ (2.22), $\Phi(\pi)=\Gamma(V^\pi)$ (2.23).
--
--   **Assumptions.**
--   1. *Assumption 2.1:* $M=\sum_{t\ge0}\big(\sup_{i,u\in U}|f(t,i,u)|+\delta(t)\big)<\infty$.
--   2. *Assumption 2.2 (2.16):* $|f(t,i,u_1)-f(t,i,u_2)|+|p^{u_1}_i-p^{u_2}_i|\le\Theta|u_1-u_2|$ on $U$, uniformly in $(t,i)$.
--   3. *Assumption 2.3 (uniform cone condition):* there are $\vartheta>0$, $\iota\in(0,\pi/2]$ such that at every $u\in U$ some cone with vertex $u$ and half-angle $\iota$, cut by the ball $B_\vartheta(u)$, lies in $U$.
--
--   These are the objects of Section 2 of the paper; every statement of the mission is phrased through them.
--
--   **Formalization Note** Actions live in `EuclideanSpace ℝ (Fin ℓ)`; vectors $y\in\mathbb R^d$ are `Fin d → ℝ`, and every norm $|y|$ or $|p^{u_1}_i-p^{u_2}_i|$ is the Euclidean one (`enorm2`). A control is a family of measures on $\mathbb R^\ell$; `IsRelaxed` asks each $\pi(i)$ to be a probability measure with $\pi(i)(U^c)=0$; `IsRegular` adds $\pi(i)\ll\mathrm{Leb}|_U$ and integrability of $\rho\ln\rho$ on $U$ for the Radon–Nikodym density $\rho$ (this is $\mathcal H(\rho)>-\infty$, since $-\rho\ln\rho\le1/e$ and $\mathrm{Leb}(U)<\infty$). Expectations are computed through the averaged matrices of Remark 2.1: the time-$k$ law from $i$ is row $i$ of $p^{\sigma_0}\cdots p^{\sigma_{k-1}}$ (`seqValue`, an infinite sum); the concatenation is the control sequence $(\pi',\pi,\pi,\dots)$, not the formula on p. 6. $\delta$ is indexed by $t\in\mathbb N_0$ (only integer times occur). Added relative to the page: each $p^u$ ($u\in U$) is a stochastic matrix; $\Theta>0$ (any upper bound of the supremum in (2.16)); in Assumption 2.3 the cone is one nappe $\{v:\langle v-u,a\rangle\ge|v-u|\cos\iota\}$ with unit axis $a$ (the printed $\Delta_\iota$ is a double cone, which no polyhedron vertex admits, contradicting Remark 2.3) and the ball is open; for $\ell=1$ this is "$[u,u+\vartheta)$ or $(u-\vartheta,u]$ lies in $U$". `MeasMaps` (measurability of $u\mapsto f(t,i,u)$ and $u\mapsto p^u_{ij}$) is used where the page assumes only Assumption 2.1. The support condition in $\Gamma(y)$ is $\pi(i)(E(y,i)^c)=0$ (equivalent for closed $E(y,i)$).
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, pp. 4–9, (2.1)–(2.4), (2.9), (2.12), (2.14), (2.16), (2.19)–(2.23), Definitions 2.1–2.2, Assumptions 2.1–2.3, Remark 2.1

import Mathlib

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- The action carrier `ℝ^ℓ` (p. 4), with its Euclidean norm. -/
abbrev A (ℓ : ℕ) := EuclideanSpace ℝ (Fin ℓ)

/-- The Euclidean norm `|y| = (∑ⱼ yⱼ²)^{1/2}` of a vector `y ∈ ℝ^d`, written on `Fin d → ℝ` (whose
own norm is the sup norm). Used for `|y|` in (2.17), (2.18), Lemma 2.2, and for `|p^{u₁}_i − p^{u₂}_i|`
in (2.16). -/
noncomputable def enorm2 {d : ℕ} (y : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ j, y j ^ 2)

/-- Standing setup of §2 (p. 4): the action space `U ⊂ ℝ^ℓ` is compact with `Leb(U) > 0`, and for
every action `u ∈ U`, `p^u = (p^u_{ij})` is a transition (stochastic) matrix on `S = {1, …, d}`. -/
structure Standing {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) : Prop where
  compact : IsCompact U
  vol_pos : 0 < volume U
  nonneg : ∀ u ∈ U, ∀ i j, 0 ≤ p u i j
  row_sum : ∀ u ∈ U, ∀ i, ∑ j, p u i j = 1

/-- Measurability of `u ↦ f(t,i,u)` and `u ↦ p^u_{ij}`, implicit in `f^μ(t,i) = ∫_U f(t,i,u) μ(du)`
(p. 4) and in (2.12). -/
structure MeasMaps {d ℓ : ℕ} (f : ℕ → Fin d → A ℓ → ℝ) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) :
    Prop where
  f_meas : ∀ t i, Measurable (f t i)
  p_meas : ∀ i j, Measurable (fun u => p u i j)

/-- The discount function of (2.4) (p. 5): `δ : [0,∞) → [0,1]`, nonincreasing, `δ(0) = 1`
(only its values at integer times are used in §2). -/
structure IsDiscount (δ : ℕ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ δ t
  le_one : ∀ t, δ t ≤ 1
  anti : Antitone δ
  zero : δ 0 = 1

/-- Assumption 2.1 (p. 5): `M := ∑_{t=0}^∞ (sup_{i∈S,u∈U} |f(t,i,u)| + δ(t)) < ∞`, written as
summability of `δ` and of a majorant `b t ≥ sup_{i,u∈U} |f(t,i,u)|` (all terms are nonnegative).
It also records that `δ` is a discount function, as required where (2.4) is introduced. -/
structure Assumption21 {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) :
    Prop where
  discount : IsDiscount δ
  summable_delta : Summable δ
  bound : ∃ b : ℕ → ℝ, Summable b ∧ ∀ t i, ∀ u ∈ U, |f t i u| ≤ b t

/-- Assumption 2.2, (2.16) (p. 8): `u ↦ f(t,i,u)` and `u ↦ p^u_i` are Lipschitz on `U`, uniformly
in `(t,i)`, with `Θ > 0` a bound of the supremum in (2.16):
`|f(t,i,u₁) − f(t,i,u₂)| + |p^{u₁}_i − p^{u₂}_i| ≤ Θ |u₁ − u₂|` (Euclidean norms). -/
structure Assumption22 {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℕ → Fin d → A ℓ → ℝ)
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (Theta : ℝ) : Prop where
  pos : 0 < Theta
  lip : ∀ t i, ∀ u₁ ∈ U, ∀ u₂ ∈ U,
    |f t i u₁ - f t i u₂| + enorm2 (p u₁ i - p u₂ i) ≤ Theta * ‖u₁ - u₂‖

/-- Assumption 2.3 (p. 8), uniform cone condition: there are `ϑ > 0` and `ι ∈ (0, π/2]` such that
at every `u ∈ U` a cone with vertex `u`, unit axis `a` and half-angle `ι`, cut by the (open) ball
`B_ϑ(u)`, lies in `U`. The cone is `{v : ⟨v − u, a⟩ ≥ |v − u| cos ι}` (one nappe). For `ℓ = 1`
this says `[u, u + ϑ)` or `(u − ϑ, u]` lies in `U`. -/
structure Assumption23 {ℓ : ℕ} (U : Set (A ℓ)) (iota vartheta : ℝ) : Prop where
  vartheta_pos : 0 < vartheta
  iota_pos : 0 < iota
  iota_le : iota ≤ Real.pi / 2
  cone : ∀ u ∈ U, ∃ a : A ℓ, ‖a‖ = 1 ∧
    ∀ v : A ℓ, ‖v - u‖ < vartheta → ‖v - u‖ * Real.cos iota ≤ inner ℝ (v - u) a → v ∈ U

/-- A relaxed feedback control `π : S → 𝒫(U)` (p. 4), as a family of measures on `ℝ^ℓ`. -/
abbrev Control (d ℓ : ℕ) := Fin d → Measure (A ℓ)

/-- `π ∈ Π` (p. 4): every `π(i)` is a probability measure carried by `U`. -/
def IsRelaxed {d ℓ : ℕ} (U : Set (A ℓ)) (pol : Control d ℓ) : Prop :=
  ∀ i, IsProbabilityMeasure (pol i) ∧ pol i Uᶜ = 0

/-- The density `ρ = dμ/du` of a measure `μ` with respect to Lebesgue measure on `U`. -/
noncomputable def density {ℓ : ℕ} (U : Set (A ℓ)) (μ : Measure (A ℓ)) : A ℓ → ℝ :=
  fun u => (μ.rnDeriv (volume.restrict U) u).toReal

/-- Shannon differential entropy (2.3) (p. 5): `ℋ(ρ) = −∫_U ln(ρ(u)) ρ(u) du` (with `0 ln 0 = 0`). -/
noncomputable def entDensity {ℓ : ℕ} (U : Set (A ℓ)) (ρ : A ℓ → ℝ) : ℝ :=
  -∫ u in U, ρ u * Real.log (ρ u)

/-- `ℋ(μ) := ℋ(dμ/du)`, the entropy of a measure through its density on `U`. -/
noncomputable def ent {ℓ : ℕ} (U : Set (A ℓ)) (μ : Measure (A ℓ)) : ℝ :=
  entDensity U (density U μ)

/-- Definition 2.1 (p. 5), `π ∈ Π_r`: `π` is relaxed, each `π(i)` has a density `ρᵢ` on `U`, and
`ℋ(ρᵢ) > −∞`, i.e. `ρᵢ ln ρᵢ` is integrable on `U`. -/
def IsRegular {d ℓ : ℕ} (U : Set (A ℓ)) (pol : Control d ℓ) : Prop :=
  IsRelaxed U pol ∧ ∀ i, pol i ≪ volume.restrict U ∧
    IntegrableOn (fun u => density U (pol i) u * Real.log (density U (pol i) u)) U

/-- `f^μ(t,i) := ∫_U f(t,i,u) μ(du)` (p. 4). -/
noncomputable def fbar {d ℓ : ℕ} (f : ℕ → Fin d → A ℓ → ℝ) (μ : Measure (A ℓ)) (t : ℕ)
    (i : Fin d) : ℝ :=
  ∫ u, f t i u ∂μ

/-- Remark 2.1 (p. 4): the averaged transition matrix `p^π_{ij} := ∫_U p^u_{ij} (π(i))(du)`. -/
noncomputable def Pbar {d ℓ : ℕ} (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (pol : Control d ℓ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ u, p u i j ∂(pol i)

/-- Expected total reward of the chain started at `i` when the control `σ k` is used at time `k`
and `r k (σ k) j` is the time-`k` reward in state `j`:
`∑_{k≥0} ∑_j (p^{σ 0} ⋯ p^{σ (k−1)})_{ij} r_k(σ k)(j)` (the law of `X_k` is row `i` of the product
of the averaged matrices, Remark 2.1). -/
noncomputable def seqValue {d ℓ : ℕ} (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (σ : ℕ → Control d ℓ)
    (r : ℕ → Control d ℓ → Fin d → ℝ) (i : Fin d) : ℝ :=
  ∑' k : ℕ, ((List.ofFn (fun m : Fin k => Pbar p (σ m))).prod *ᵥ r k (σ k)) i

/-- The concatenation `π′ ⊗₁ π` (p. 5): `π′` at time `0`, `π` from time `1` onward. -/
def concat {d ℓ : ℕ} (pol' pol : Control d ℓ) : ℕ → Control d ℓ :=
  fun k => if k = 0 then pol' else pol

/-- (2.1) for a time-dependent control sequence `σ`: `E_i[∑_k f^{σ_k(X_k)}(k, X_k)]`. -/
noncomputable def Jseq {d ℓ : ℕ} (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (σ : ℕ → Control d ℓ) : Fin d → ℝ :=
  seqValue p σ (fun k c j => fbar f (c j) k j)

/-- (2.1) (p. 4): `J^π(i) = E_i[∑_k f^{π(X_k)}(k, X_k)]`. -/
noncomputable def J {d ℓ : ℕ} (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ)
    (pol : Control d ℓ) : Fin d → ℝ :=
  Jseq p f (fun _ => pol)

/-- (2.4) for a time-dependent control sequence `σ`:
`E_i[∑_k (f^{σ_k(X_k)}(k, X_k) + λ δ(k) ℋ(σ_k(X_k)))]`. -/
noncomputable def JlamSeq {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) (lam : ℝ) (σ : ℕ → Control d ℓ) : Fin d → ℝ :=
  seqValue p σ (fun k c j => fbar f (c j) k j + lam * δ k * ent U (c j))

/-- (2.4) (p. 5): `J^π_λ(i) = E_i[∑_k (f^{π(X_k)}(k, X_k) + λ δ(k) ℋ(π(X_k)))]`. -/
noncomputable def Jlam {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) (lam : ℝ) (pol : Control d ℓ) : Fin d → ℝ :=
  JlamSeq U p f δ lam (fun _ => pol)

/-- (2.19) (p. 9): `V^π(i) = E_i[∑_k f^{π(X_k)}(1 + k, X_k)]`. -/
noncomputable def V {d ℓ : ℕ} (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ)
    (pol : Control d ℓ) : Fin d → ℝ :=
  seqValue p (fun _ => pol) (fun k c j => fbar f (c j) (1 + k) j)

/-- (2.9) (p. 6): `V^π_λ(i) = E_i[∑_k (f^{π(X_k)}(1 + k, X_k) + λ δ(1 + k) ℋ(π(X_k)))]`. -/
noncomputable def Vlam {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) (lam : ℝ) (pol : Control d ℓ) : Fin d → ℝ :=
  seqValue p (fun _ => pol) (fun k c j => fbar f (c j) (1 + k) j + lam * δ (1 + k) * ent U (c j))

/-- Definition 2.2, (2.7) (p. 6): `π ∈ Π_r` is a regular relaxed equilibrium for (2.4) if
`J^{π′⊗₁π}_λ(i) − J^π_λ(i) ≤ 0` for all `i ∈ S` and all `π′ ∈ Π_r`. -/
def IsRegularRelaxedEq {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) (lam : ℝ) (pol : Control d ℓ) : Prop :=
  IsRegular U pol ∧ ∀ i, ∀ pol' : Control d ℓ, IsRegular U pol' →
    JlamSeq U p f δ lam (concat pol' pol) i - Jlam U p f δ lam pol i ≤ 0

/-- Definition 2.2, (2.8) (p. 6): `π ∈ Π` is a relaxed equilibrium for (2.1) if
`J^{π′⊗₁π}(i) − J^π(i) ≤ 0` for all `i ∈ S` and all `π′ ∈ Π`. -/
def IsRelaxedEq {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (pol : Control d ℓ) : Prop :=
  IsRelaxed U pol ∧ ∀ i, ∀ pol' : Control d ℓ, IsRelaxed U pol' →
    Jseq p f (concat pol' pol) i - J p f pol i ≤ 0

/-- The unnormalized Gibbs weight `exp((f(0,i,u) + p^u_i · y)/λ)` of (2.12). -/
noncomputable def gibbsWeight {d ℓ : ℕ} (f : ℕ → Fin d → A ℓ → ℝ)
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (y : Fin d → ℝ) (i : Fin d) (u : A ℓ) : ℝ :=
  Real.exp ((f 0 i u + p u i ⬝ᵥ y) / lam)

/-- (2.12) (p. 6): `Γ_λ(y,i)(u) = e^{(f(0,i,u)+p^u_i·y)/λ} / ∫_U e^{(f(0,i,v)+p^v_i·y)/λ} dv`. -/
noncomputable def gibbsDensity {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℕ → Fin d → A ℓ → ℝ)
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (y : Fin d → ℝ) (i : Fin d) (u : A ℓ) : ℝ :=
  gibbsWeight f p lam y i u / ∫ v in U, gibbsWeight f p lam y i v

/-- The control `Γ_λ(y, ·)`: `π(i)` has density `Γ_λ(y,i)` on `U`. -/
noncomputable def gibbsCtrl {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℕ → Fin d → A ℓ → ℝ)
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (y : Fin d → ℝ) : Control d ℓ :=
  fun i => (volume.restrict U).withDensity (fun u => ENNReal.ofReal (gibbsDensity U f p lam y i u))

/-- The objective of (2.11) (p. 6) at a density `ρ` on `U`:
`∫_U (f(0,i,u) − λ ln(ρ(u)) + p^u_i · y) ρ(u) du`. -/
noncomputable def gibbsObjective {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℕ → Fin d → A ℓ → ℝ)
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (y : Fin d → ℝ) (i : Fin d)
    (ρ : A ℓ → ℝ) : ℝ :=
  ∫ u in U, (f 0 i u - lam * Real.log (ρ u) + p u i ⬝ᵥ y) * ρ u

/-- p. 7: `Ψ_λ(y) := V_λ^{Γ_λ(y,·)}`. -/
noncomputable def PsiLam {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) (lam : ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  Vlam U p f δ lam (gibbsCtrl U f p lam y)

/-- (2.14) (p. 7): `Φ_λ(π) := Γ_λ(V^π_λ, ·)`. -/
noncomputable def PhiLam {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) (lam : ℝ) (pol : Control d ℓ) : Control d ℓ :=
  gibbsCtrl U f p lam (Vlam U p f δ lam pol)

/-- (2.20) (p. 9): `E(y,i) := argmax_{u∈U} {f(0,i,u) + p^u_i · y} ⊆ U`. -/
def argmaxSet {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℕ → Fin d → A ℓ → ℝ)
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (i : Fin d) : Set (A ℓ) :=
  {u | u ∈ U ∧ ∀ v ∈ U, f 0 i v + p v i ⬝ᵥ y ≤ f 0 i u + p u i ⬝ᵥ y}

/-- (2.21) (p. 9): `Γ(y) := {π ∈ Π : supp(π(i)) ⊆ E(y,i) ∀ i}`, with the support condition written as
`π(i)(E(y,i)ᶜ) = 0`. -/
def GammaSet {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℕ → Fin d → A ℓ → ℝ)
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) : Set (Control d ℓ) :=
  {pol | IsRelaxed U pol ∧ ∀ i, pol i (argmaxSet U f p y i)ᶜ = 0}

/-- (2.22) (p. 9): `Ψ(y) := {V^π : π ∈ Γ(y)} ⊆ ℝ^d`. -/
def PsiSet {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (y : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {z | ∃ pol ∈ GammaSet U f p y, V p f pol = z}

/-- (2.23) (p. 9): `Φ(π) := Γ(V^π) ⊆ Π`. -/
def PhiSet {d ℓ : ℕ} (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (pol : Control d ℓ) : Set (Control d ℓ) :=
  GammaSet U f p (V p f pol)

/-- A sequence `{λ_n}` in `(0, 1]` with `λ_n ↓ 0` (Lemma 2.2, p. 8; proof of Theorem 2.2, p. 22). -/
def IsLamSeq (lam : ℕ → ℝ) : Prop :=
  (∀ n, 0 < lam n ∧ lam n ≤ 1) ∧ Antitone lam ∧ Tendsto lam atTop (𝓝 0)

/-- Weak convergence `μ_n → μ` of measures on `ℝ^ℓ`, tested against bounded continuous functions. -/
def WeakTendsto {ℓ : ℕ} (μs : ℕ → Measure (A ℓ)) (μ : Measure (A ℓ)) : Prop :=
  ∀ h : BoundedContinuousFunction (A ℓ) ℝ, Tendsto (fun n => ∫ u, h u ∂(μs n)) atTop (𝓝 (∫ u, h u ∂μ))

end RelaxedEqMDP.Discrete


