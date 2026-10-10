-- Prove2me | Definitions.Def_NondomArb_OptDecomp_Model
-- name    : NondomArb_OptDecomp_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:15:06.615887+00:00
-- url     : https://prove2.me/theorems/86057b7f-4429-420a-86fc-a954904bb151
-- title:
--   §1.1–§1.2, §4.2: the nondominated market (𝒫_t, 𝒫, S, ℋ, H • S_T), q.s., NA(𝒫), the martingale measures 𝒬, the expectation (1.1), NA(𝒫_t(ω)), N_t, 𝒬_t(ω) and ℰ_t
-- statement:
--   This definition sets up the nondominated discrete-time market of Bouchard and Nutz (§1.1–§1.2) and the one-period objects of §4.2 that are used in the nondominated optional decomposition.
--
--   **Paths and information.** Let $\Omega_1$ be a Polish space with its Borel $\sigma$-field, let $T \in \mathbb N$ be the horizon, and let $\Omega_t := \Omega_1^t$ for $t = 0, 1, \dots, T$, so that $\Omega_0$ is a singleton and $\Omega := \Omega_T$. A point of $\Omega_t$ is identified with the first $t$ coordinates of a path $\omega = (\omega_1, \dots, \omega_T) \in \Omega$. The $\sigma$-field $\mathcal F_t$ is the universal completion of $\mathcal B(\Omega_t)$; a function is $\mathcal F_t$-measurable when it is universally measurable on $\Omega_t$.
--
--   **Extended expectation (1.1).** For a measure $P$ and a function $f$ with values in $[-\infty, \infty]$,
--   $$E_P[f] := E_P[f^+] - E_P[f^-], \qquad \infty - \infty := -\infty .$$
--
--   **Upper semianalytic functions.** $f : X \to [-\infty, \infty]$ on a topological space $X$ is upper semianalytic if $\{f > c\}$ is an analytic set for every $c \in \mathbb R$.
--
--   **The market.** For $t = 0, \dots, T-1$ and $\omega \in \Omega_t$ a set $\mathcal P_t(\omega)$ of Borel probability measures on $\Omega_1$ is given; the standing assumptions are that each $\mathcal P_t(\omega)$ is nonempty and convex and that $\operatorname{graph}(\mathcal P_t) = \{(\omega, P) : P \in \mathcal P_t(\omega)\} \subseteq \Omega_t \times \mathfrak P(\Omega_1)$ is analytic, where $\mathfrak P(\Omega_1)$ carries the topology of weak convergence. The stock prices $S_t : \Omega_t \to \mathbb R^d$, $t = 0, \dots, T$, are Borel, and so are the options $g : \Omega \to \mathbb R^e$ (in this mission $e = 0$). The set of possible models is
--   $$\mathcal P = \{P_0 \otimes P_1 \otimes \cdots \otimes P_{T-1} : P_t(\cdot) \in \mathcal P_t(\cdot) \text{ almost surely},\ t = 0, \dots, T-1\},$$
--   the laws on $\Omega$ obtained by composing Markov kernels $P_t : \Omega_t \to \mathfrak P(\Omega_1)$ that take values in $\mathcal P_t$ almost surely under the law of the first $t$ coordinates.
--
--   **Quasi-sure statements.** A set $A \subseteq \Omega$ is $\mathcal P$-polar if $P(A) = 0$ for all $P \in \mathcal P$, and a property holds $\mathcal P$-quasi surely ($\mathcal P$-q.s.) if it holds $P$-almost surely for every $P \in \mathcal P$.
--
--   **Strategies and NA($\mathcal P$).** A trading strategy $H \in \mathcal H$ is a predictable $\mathbb R^d$-valued process: $H_{u}$ is an $\mathcal F_{u-1}$-measurable function of the first $u - 1$ coordinates, $u = 1, \dots, T$. Its terminal wealth is $H \bullet S_T = \sum_{u=1}^T H_u \Delta S_u$ with $\Delta S_u = S_u - S_{u-1}$. Condition NA($\mathcal P$) (Definition 1.1) holds if for all $(H, h) \in \mathcal H \times \mathbb R^e$, $H \bullet S_T + hg \ge 0$ $\mathcal P$-q.s. implies $H \bullet S_T + hg = 0$ $\mathcal P$-q.s.
--
--   **Martingale measures (1.3).** A probability $Q$ on $\Omega$ is a martingale measure if $S$ is a $Q$-martingale in $(\mathcal F_t)$ (in particular every $S_t$ is $Q$-integrable). $Q \lll \mathcal P$ means $Q \ll P$ for some $P \in \mathcal P$, and
--   $$\mathcal Q = \{Q \lll \mathcal P : Q \text{ is a martingale measure and } E_Q[g^i] = 0,\ i = 1, \dots, e\}.$$
--
--   **One-period objects (§4.2).** For $\omega \in \Omega_t$ the increment $\Delta S_{t+1}(\omega, \cdot) = S_{t+1}(\omega, \cdot) - S_t(\omega)$ defines a one-period market on $(\Omega_1, \mathcal B(\Omega_1))$ under $\mathcal P_t(\omega)$. Its no-arbitrage condition NA($\mathcal P_t(\omega)$) says: for $y \in \mathbb R^d$, $y \Delta S_{t+1}(\omega, \cdot) \ge 0$ $\mathcal P_t(\omega)$-q.s. implies $y \Delta S_{t+1}(\omega, \cdot) = 0$ $\mathcal P_t(\omega)$-q.s. The set where it fails is
--   $$N_t = \{\omega \in \Omega_t : \mathrm{NA}(\mathcal P_t(\omega)) \text{ fails}\}.$$
--   The one-period martingale measures (Lemma 4.8) and the conditional sublinear expectation (Lemma 4.10) are
--   $$\mathcal Q_t(\omega) = \{Q \in \mathfrak P(\Omega_1) : Q \lll \mathcal P_t(\omega),\ E_Q[\Delta S_{t+1}(\omega, \cdot)] = 0\}, \qquad \mathcal E_t(f)(\omega) = \sup_{Q \in \mathcal Q_t(\omega)} E_Q[f(\omega, \cdot)]$$
--   for $f : \Omega_t \times \Omega_1 \to [-\infty, \infty]$, the supremum taken in $[-\infty, \infty]$.
--
--   These objects are the vocabulary of the multi-period fundamental theorem (Theorem 4.5) and of the nondominated optional decomposition (Theorem 6.1).
--
--   **Formalization Note.** $\Omega_t$ is `Fin t → Ω₁`. Measures are Borel measures and polar sets are measured with the outer measure; every exceptional set that occurs in the mission's statements is universally measurable, and for such sets this agrees with the paper's definition of polar sets. The set $\mathcal P$ uses Borel Markov kernels lying in $\mathcal P_t$ almost surely, which is the paper's equivalent description on p. 4. The Lean strategy `H u` is the paper's $H_{u+1}$. The expectation (1.1) is computed in `EReal`, where `⊤ - ⊤ = ⊥` is the convention $\infty - \infty = -\infty$. The martingale property is tested on Borel sets $B \subseteq \Omega_t$, which suffices because $\mathcal F_t$ is the universal completion of $\mathcal B(\Omega_t)$; $E_Q[\Delta S_{t+1}] = 0$ in the sense of (1.1) is written as integrability plus zero integral. The paper's p. 4 prints $\mathfrak P(\Omega_t)$ and $g : \Omega \to \mathbb R^d$; the formalization uses the intended $\mathfrak P(\Omega_1)$ and $\mathbb R^e$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, pp. 3–6, §1.1–§1.2, Definition 1.1, (1.1)–(1.3); p. 20 (NA(𝒫_t(ω))), p. 21 (N_t), p. 22 (𝒬_t, Lemma 4.8), p. 25 (ℰ_t, Lemma 4.10)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model

namespace NondomArb.OptDecomp

open MeasureTheory ProbabilityTheory BertsekasShreve.AnalyticSelection

/-! §1.1–§1.2 (pp. 3–6) and §4.2 (pp. 20–22) of Bouchard–Nutz: the nondominated multi-period
market, used in §6 with no options (`e = 0`).

* `Ω₁` is a Polish space with its Borel σ-field; `Ω_t = Ω₁ᵗ` is `Fin t → Ω₁` (so `Ω₀` is a
  singleton) and `Ω = Ω_T`. The prefix map `ω ↦ (ω_1, …, ω_t)` identifies `Ω_t` with the first
  `t` coordinates of `Ω`.
* Measures are Borel measures; `F_t`-measurability (the universal completion of `B(Ω_t)`) is
  universal measurability (`IsUniversallyMeasurable`, published definition).
* `𝒫_t(ω) ⊆ 𝔓(Ω₁)` are given for `t < T` (nonempty, convex, analytic graph), and `𝒫` is the set
  of all `P₀ ⊗ ⋯ ⊗ P_{T−1}` whose kernels take values in `𝒫_t(·)` almost surely (the paper's
  "equivalently" formulation on p. 4), with Borel Markov kernels.
* `S_t : Ω_t → ℝ^d` is Borel; `g : Ω → ℝ^e` is Borel (the options, priced `0`).
* Strategies: `H u : Ω_u → ℝ^d` (`u = 0, …, T−1`) is the paper's `H_{u+1}` — a universally
  measurable function of the first `u` coordinates (predictability). -/

section Model

variable {Ω₁ : Type*} [MeasurableSpace Ω₁]

/-- The data of the nondominated market of §1.2: horizon `T`, `d` stocks, `e` options. -/
structure Market (Ω₁ : Type*) [MeasurableSpace Ω₁] [TopologicalSpace Ω₁] (T d e : ℕ) where
  /-- the random sets of one-period models `𝒫_t : Ω_t ↠ 𝔓(Ω₁)` (used for `t < T`) -/
  Pt : (t : ℕ) → (Fin t → Ω₁) → Set (ProbabilityMeasure Ω₁)
  /-- the stock prices `S_t : Ω_t → ℝ^d` (used for `t ≤ T`) -/
  S : (t : ℕ) → (Fin t → Ω₁) → (Fin d → ℝ)
  /-- the options `g = (g¹, …, gᵉ) : Ω → ℝ^e`, each traded at price `0` -/
  g : (Fin T → Ω₁) → (Fin e → ℝ)

namespace Market

variable [TopologicalSpace Ω₁] {T d e : ℕ}

/-- The standing assumptions of §1.2 (pp. 3–5): `Ω₁` Polish with its Borel σ-field (carried by
the typeclass hypotheses of the statements), and for every `t < T` and `ω ∈ Ω_t` the set
`𝒫_t(ω)` is nonempty and convex, `graph(𝒫_t) ⊆ Ω_t × 𝔓(Ω₁)` is analytic; `S_t` is Borel for
`t ≤ T`; `g` is Borel. -/
def Standing [OpensMeasurableSpace Ω₁] (M : Market Ω₁ T d e) : Prop :=
  (∀ t < T, ∀ ω : Fin t → Ω₁, (M.Pt t ω).Nonempty) ∧
  (∀ t < T, ∀ ω : Fin t → Ω₁, ∀ P ∈ M.Pt t ω, ∀ P' ∈ M.Pt t ω, ∀ a : NNReal, a ≤ 1 →
    ∃ R ∈ M.Pt t ω, (R : Measure Ω₁) = a • (P : Measure Ω₁) + (1 - a) • (P' : Measure Ω₁)) ∧
  (∀ t < T, AnalyticSet {p : (Fin t → Ω₁) × ProbabilityMeasure Ω₁ | p.2 ∈ M.Pt t p.1}) ∧
  (∀ t ≤ T, Measurable (M.S t)) ∧
  Measurable M.g

/-- The set `𝒫 ⊆ 𝔓(Ω)` of possible models (p. 4): all laws `P₀ ⊗ ⋯ ⊗ P_{T−1}` of Borel Markov
kernels `P_t` with `P_t(ω) ∈ 𝒫_t(ω)` for `(P₀ ⊗ ⋯ ⊗ P_{t−1})`-almost every `ω`, `t < T`.
Only the kernels `κ t`, `t < T`, enter `law κ T`, so only they are required to be Markov
(for `T = 0`, `𝒫 = {δ}` is the Dirac mass on the point of `Ω₀`, even if `Ω₁ = ∅`). -/
def models (M : Market Ω₁ T d e) : Set (Measure (Fin T → Ω₁)) :=
  {P | ∃ κ : (t : ℕ) → Kernel (Fin t → Ω₁) Ω₁, (∀ t < T, IsMarkovKernel (κ t)) ∧
    (∀ t < T, ∀ᵐ ω ∂(NondomArb.Superhedge.law κ t), ∃ R ∈ M.Pt t ω, (R : Measure Ω₁) = κ t ω) ∧ P = NondomArb.Superhedge.law κ T}

/-- A property holds `𝒫`-quasi surely: it holds `P`-almost surely for every `P ∈ 𝒫` (with
Borel measures and outer measure, this is the paper's "outside a `𝒫`-polar set", §1.1). -/
def QS (M : Market Ω₁ T d e) (p : (Fin T → Ω₁) → Prop) : Prop :=
  ∀ P ∈ M.models, ∀ᵐ ω ∂P, p ω

/-- A set `A ⊆ Ω` is `𝒫`-polar: `P(A) = 0` (outer measure) for every `P ∈ 𝒫`. -/
def IsPolar (M : Market Ω₁ T d e) (A : Set (Fin T → Ω₁)) : Prop :=
  ∀ P ∈ M.models, P A = 0

/-- `ℋ`: the predictable strategies. `H u` (the paper's `H_{u+1}`) is a universally measurable
function of the first `u` coordinates, `u = 0, …, T − 1`. -/
def Admissible (_M : Market Ω₁ T d e) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ)) : Prop :=
  ∀ u < T, NondomArb.Superhedge.IsUMeasurable (H u)

/-- **(1.2)** The terminal wealth `H • S_T(ω) = Σ_{u=1}^T H_u(ω) ΔS_u(ω)` (Lean index
`u = 0, …, T − 1`, with `ΔS_{u+1} = S_{u+1} − S_u`). -/
def wealth (M : Market Ω₁ T d e) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ))
    (ω : Fin T → Ω₁) : ℝ :=
  ∑ u : Fin T, H (u : ℕ) (NondomArb.Superhedge.pre ω u u.isLt.le) ⬝ᵥ
    (M.S ((u : ℕ) + 1) (NondomArb.Superhedge.pre ω ((u : ℕ) + 1) u.isLt) - M.S (u : ℕ) (NondomArb.Superhedge.pre ω u u.isLt.le))

/-- **Definition 1.1** (p. 5). `NA(𝒫)`: for all `(H, h) ∈ ℋ × ℝ^e`,
`H • S_T + hg ≥ 0` `𝒫`-q.s. implies `H • S_T + hg = 0` `𝒫`-q.s. -/
def NA (M : Market Ω₁ T d e) : Prop :=
  ∀ H, M.Admissible H → ∀ h : Fin e → ℝ,
    M.QS (fun ω => 0 ≤ M.wealth H ω + h ⬝ᵥ M.g ω) →
    M.QS (fun ω => M.wealth H ω + h ⬝ᵥ M.g ω = 0)

/-- `Q` is a *martingale measure* (p. 6): `S` is a `Q`-martingale in the filtration `(F_t)`.
Every `S_t` is `Q`-integrable, and `E_Q[(S_{t+1} − S_t) 1_B] = 0` for every `B ∈ F_t`; since
`F_t` is the universal completion of `B(Ω_t)`, Borel test sets `B ⊆ Ω_t` suffice. -/
def IsMartingaleMeasure (M : Market Ω₁ T d e) (Q : Measure (Fin T → Ω₁)) : Prop :=
  (∀ t : Fin (T + 1), ∀ i : Fin d,
    Integrable (fun ω => M.S (t : ℕ) (NondomArb.Superhedge.pre ω t (Nat.lt_succ_iff.mp t.isLt)) i) Q) ∧
  ∀ t : Fin T, ∀ i : Fin d, ∀ B : Set (Fin t → Ω₁), MeasurableSet B →
    ∫ ω in (fun ω => NondomArb.Superhedge.pre ω t t.isLt.le) ⁻¹' B,
      (M.S ((t : ℕ) + 1) (NondomArb.Superhedge.pre ω ((t : ℕ) + 1) t.isLt) i - M.S (t : ℕ) (NondomArb.Superhedge.pre ω t t.isLt.le) i) ∂Q = 0

/-- **(1.3)** `𝒬 = {Q ⋘ 𝒫 : Q is a martingale measure and E_Q[gⁱ] = 0, i = 1, …, e}`, with
`E_Q` the extended expectation (1.1). In §6, `e = 0` and the last clause is empty. -/
def MartMeasures (M : Market Ω₁ T d e) : Set (Measure (Fin T → Ω₁)) :=
  {Q | IsProbabilityMeasure Q ∧ NondomArb.Superhedge.AbsContSet Q M.models ∧ M.IsMartingaleMeasure Q ∧
    ∀ i : Fin e, NondomArb.Superhedge.extExp Q (fun ω => ((M.g ω i : ℝ) : EReal)) = 0}

/-- The one-period increment `ΔS_{t+1}(ω, ·) = S_{t+1}(ω, ·) − S_t(ω)` on `Ω₁` (p. 20). -/
def incr (M : Market Ω₁ T d e) (t : ℕ) (ω : Fin t → Ω₁) (x : Ω₁) : Fin d → ℝ :=
  M.S (t + 1) (Fin.snoc (α := fun _ => Ω₁) ω x) - M.S t ω

/-- `NA(𝒫_t(ω))` (p. 20): the no-arbitrage condition of the one-period market of §3 on
`(Ω₁, B(Ω₁))` with increment `ΔS_{t+1}(ω, ·)` under `𝒫_t(ω)`: for `y ∈ ℝ^d`,
`yΔS_{t+1}(ω, ·) ≥ 0` `𝒫_t(ω)`-q.s. implies `yΔS_{t+1}(ω, ·) = 0` `𝒫_t(ω)`-q.s. -/
def LocalNA (M : Market Ω₁ T d e) (t : ℕ) (ω : Fin t → Ω₁) : Prop :=
  ∀ y : Fin d → ℝ, (∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁), 0 ≤ y ⬝ᵥ M.incr t ω x) →
    ∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁), y ⬝ᵥ M.incr t ω x = 0

/-- `N_t = {ω ∈ Ω_t : NA(𝒫_t(ω)) fails}` (Theorem 4.5, Lemma 4.6). -/
def badSet (M : Market Ω₁ T d e) (t : ℕ) : Set (Fin t → Ω₁) :=
  {ω | ¬ M.LocalNA t ω}

/-- `𝒬_t(ω) = {Q ∈ 𝔓(Ω₁) : Q ⋘ 𝒫_t(ω), E_Q[ΔS_{t+1}(ω, ·)] = 0}` (Lemma 4.8, p. 22); under
convention (1.1) the zero mean includes integrability. -/
def localMartMeasures (M : Market Ω₁ T d e) (t : ℕ) (ω : Fin t → Ω₁) : Set (Measure Ω₁) :=
  {Q | IsProbabilityMeasure Q ∧ (∃ P ∈ M.Pt t ω, Q ≪ (P : Measure Ω₁)) ∧
    Integrable (M.incr t ω) Q ∧ ∫ x, M.incr t ω x ∂ Q = 0}

/-- `ℰ_t(f)(ω) = sup_{Q ∈ 𝒬_t(ω)} E_Q[f(ω, ·)]` (Lemma 4.10, p. 25), in `[−∞, ∞]`
(`−∞` when `𝒬_t(ω) = ∅`). -/
noncomputable def condSup (M : Market Ω₁ T d e) (t : ℕ) (f : (Fin t → Ω₁) × Ω₁ → EReal)
    (ω : Fin t → Ω₁) : EReal :=
  ⨆ Q ∈ M.localMartMeasures t ω, NondomArb.Superhedge.extExp Q (fun x => f (ω, x))

end Market

end Model

end NondomArb.OptDecomp


