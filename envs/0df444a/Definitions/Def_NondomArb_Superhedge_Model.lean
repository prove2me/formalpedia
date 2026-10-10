-- Prove2me | Definitions.Def_NondomArb_Superhedge_Model
-- name    : NondomArb_Superhedge_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:22:24.184995+00:00
-- url     : https://prove2.me/theorems/208f7eb9-8d2c-414e-ae67-1e012d2a0637
-- title:
--   §1.2: the nondominated market (𝒫_t, 𝒫, S, ℋ, H • S, g), NA(𝒫), 𝒬, 𝒬_φ, π(f), N_t, 𝒬_t(ω) and ℰ_t
-- statement:
--   This is the multi-period market of §1.2 of Bouchard–Nutz, with the auxiliary objects of §4.
--
--   **Spaces.** Let $T\in\mathbb N$ and let $\Omega_1$ be a Polish space with its Borel $\sigma$-field. For $t=0,\dots,T$ let $\Omega_t=\Omega_1^t$ (with $\Omega_0$ a singleton) and $\Omega=\Omega_T$; $\Omega_t$ is identified with the first $t$ coordinates of $\Omega$. $\mathcal F_t$ is the universal completion of $\mathcal B(\Omega_t)$; "random variable" means a real universally measurable function on $\Omega$.
--
--   **Models.** For each $t<T$ and $\omega\in\Omega_t$ a nonempty convex set $\mathcal P_t(\omega)\subseteq\mathfrak P(\Omega_1)$ is given, with analytic graph $\{(\omega,P):P\in\mathcal P_t(\omega)\}\subseteq\Omega_t\times\mathfrak P(\Omega_1)$. The set of models is
--   $$\mathcal P=\{P_0\otimes P_1\otimes\cdots\otimes P_{T-1}:\ P_t(\cdot)\in\mathcal P_t(\cdot)\ \ (P_0\otimes\cdots\otimes P_{t-1})\text{-a.s.},\ t<T\}.$$
--
--   **Market.** Stock prices $S_t:\Omega_t\to\mathbb R^d$ are Borel; options $g=(g^1,\dots,g^e):\Omega\to\mathbb R^e$ are Borel and traded statically at price $0$. A strategy $(H,h)\in\mathcal H\times\mathbb R^e$ consists of a predictable $H$ ($H_{u}$ a universally measurable function of the first $u-1$ coordinates) and $h\in\mathbb R^e$; its terminal value is $H\bullet S_T+hg$ with $H\bullet S_T=\sum_{u=1}^T H_u\Delta S_u$.
--
--   1. **NA($\mathcal P$)** (Definition 1.1): $H\bullet S_T+hg\ge0$ $\mathcal P$-q.s. implies $H\bullet S_T+hg=0$ $\mathcal P$-q.s.
--   2. **Martingale measures** (1.3): $\mathcal Q=\{Q\lll\mathcal P:\ S \text{ is a } Q\text{-martingale},\ E_Q[g^i]=0,\ i=1,\dots,e\}$, and for a random variable $\varphi\ge1$, $\mathcal Q_\varphi=\{Q\in\mathcal Q: E_Q[\varphi]<\infty\}$.
--   3. **Superhedging price**:
--   $$\pi(f)=\inf\{x\in\mathbb R:\ \exists (H,h)\in\mathcal H\times\mathbb R^e,\ x+H\bullet S_T+hg\ge f\ \ \mathcal P\text{-q.s.}\},\qquad\inf\emptyset=+\infty;$$
--   $f$ is *replicable* if $x+H\bullet S_T+hg=f$ $\mathcal P$-q.s. for some $x$ and $(H,h)$.
--   4. **One-period pieces** (§4): $\Delta S_{t+1}(\omega,\cdot)=S_{t+1}(\omega,\cdot)-S_t(\omega)$ on $\Omega_1$; $\mathrm{NA}(\mathcal P_t(\omega))$ is the one-period no-arbitrage condition of §3 for this increment under $\mathcal P_t(\omega)$; $N_t=\{\omega\in\Omega_t:\mathrm{NA}(\mathcal P_t(\omega))\text{ fails}\}$; $\mathcal Q_t(\omega)=\{Q\in\mathfrak P(\Omega_1): Q\lll\mathcal P_t(\omega),\ E_Q[\Delta S_{t+1}(\omega,\cdot)]=0\}$ and $\mathcal E_t(f)(\omega)=\sup_{Q\in\mathcal Q_t(\omega)}E_Q[f(\omega,\cdot)]$.
--
--   This is the nondominated market in which the paper's fundamental theorems and superhedging duality are proved.
--
--   **Formalization Note** $\Omega_t$ is `Fin t → Ω₁`; measures are Borel measures and $\mathcal F_t$-measurability is universal measurability (the published `IsUniversallyMeasurable`). $\mathfrak P(\Omega_1)$ is Mathlib's `ProbabilityMeasure` with the weak topology. $\mathcal P$ is built from Borel Markov kernels $P_t$ with $P_t(\omega)\in\mathcal P_t(\omega)$ for almost every $\omega$: this is the paper's own equivalent description on p. 4 (a universally measurable selector agrees with a Borel kernel off a null set). $\mathcal P$-q.s. means $P$-a.s. for every $P\in\mathcal P$, and a set is $\mathcal P$-polar if it has outer measure $0$ under every $P\in\mathcal P$; for the universally measurable sets that occur here this is the paper's definition. Lean's `H u` is the paper's $H_{u+1}$, a function of the first $u$ coordinates. "$S$ is a $Q$-martingale" is stated as integrability of every $S_t$ plus $E_Q[(S_{t+1}-S_t)\mathbf 1_B]=0$ for Borel $B\subseteq\Omega_t$ (which suffices since $\mathcal F_t$ is the universal completion). $E_Q[g^i]$ is the extended expectation (1.1); $\pi(f)$ is an `EReal` infimum. Two typos of p. 4 are corrected: $\mathrm{graph}(\mathcal P_t)\subseteq\Omega_t\times\mathfrak P(\Omega_1)$ and $g:\Omega\to\mathbb R^e$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, pp. 3–6, §1.1–§1.2, Definition 1.1, (1.1)–(1.3); p. 7 (replicable); pp. 20–22, §4.2 (N_t, Lemma 4.8: 𝒬_t); p. 25, §4.3 (𝒬_φ, Lemma 4.10: ℰ_t)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic

namespace NondomArb.Superhedge

open MeasureTheory ProbabilityTheory BertsekasShreve.AnalyticSelection

/-! §1.2 (pp. 3–6): the nondominated multi-period market.

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

/-- A function between measurable spaces is *universally measurable* if the preimage of every
measurable set is universally measurable (`IsUniversallyMeasurableFun` on the whole domain). -/
def IsUMeasurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y) : Prop :=
  IsUniversallyMeasurableFun (Set.univ : Set X) (fun x : (Set.univ : Set X) => f x)

/-- The prefix map `Ω_T → Ω_t`, `ω ↦ (ω_1, …, ω_t)`, for `t ≤ T`. -/
def pre {T : ℕ} (ω : Fin T → Ω₁) (t : ℕ) (h : t ≤ T) : Fin t → Ω₁ :=
  fun i => ω (Fin.castLE h i)

/-- The law of the first `t` coordinates under `P₀ ⊗ P₁ ⊗ ⋯ ⊗ P_{t−1}` built from the kernels
`κ s : Ω_s → 𝔓(Ω₁)`: the Dirac mass on the point of `Ω₀` for `t = 0`, and
`(law κ t ⊗ κ t)` pushed forward by `(ω, x) ↦ (ω, x) ∈ Ω_{t+1}` for `t + 1`. -/
noncomputable def law (κ : (t : ℕ) → Kernel (Fin t → Ω₁) Ω₁) : (t : ℕ) → Measure (Fin t → Ω₁)
  | 0 => Measure.dirac (fun i => i.elim0)
  | t + 1 => ((law κ t) ⊗ₘ (κ t)).map (fun p => Fin.snoc (α := fun _ => Ω₁) p.1 p.2)

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
    (∀ t < T, ∀ᵐ ω ∂(law κ t), ∃ R ∈ M.Pt t ω, (R : Measure Ω₁) = κ t ω) ∧ P = law κ T}

/-- A property holds `𝒫`-quasi surely: it holds `P`-almost surely for every `P ∈ 𝒫` (with
Borel measures and outer measure; the exceptional sets arising here are universally
measurable, for which this is the paper's "outside a `𝒫`-polar set"). -/
def QS (M : Market Ω₁ T d e) (p : (Fin T → Ω₁) → Prop) : Prop :=
  ∀ P ∈ M.models, ∀ᵐ ω ∂P, p ω

/-- A set `A ⊆ Ω` is `𝒫`-polar: `P(A) = 0` (outer measure) for every `P ∈ 𝒫`. -/
def IsPolar (M : Market Ω₁ T d e) (A : Set (Fin T → Ω₁)) : Prop :=
  ∀ P ∈ M.models, P A = 0

/-- `ℋ`: the predictable strategies. `H u` (the paper's `H_{u+1}`) is a universally measurable
function of the first `u` coordinates, `u = 0, …, T − 1`. -/
def Admissible (_M : Market Ω₁ T d e) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ)) : Prop :=
  ∀ u < T, IsUMeasurable (H u)

/-- **(1.2)** The terminal wealth `H • S_T(ω) = Σ_{u=1}^T H_u(ω) ΔS_u(ω)` (Lean index
`u = 0, …, T − 1`, with `ΔS_{u+1} = S_{u+1} − S_u`). -/
def wealth (M : Market Ω₁ T d e) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ))
    (ω : Fin T → Ω₁) : ℝ :=
  ∑ u : Fin T, H (u : ℕ) (pre ω u u.isLt.le) ⬝ᵥ
    (M.S ((u : ℕ) + 1) (pre ω ((u : ℕ) + 1) u.isLt) - M.S (u : ℕ) (pre ω u u.isLt.le))

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
    Integrable (fun ω => M.S (t : ℕ) (pre ω t (Nat.lt_succ_iff.mp t.isLt)) i) Q) ∧
  ∀ t : Fin T, ∀ i : Fin d, ∀ B : Set (Fin t → Ω₁), MeasurableSet B →
    ∫ ω in (fun ω => pre ω t t.isLt.le) ⁻¹' B,
      (M.S ((t : ℕ) + 1) (pre ω ((t : ℕ) + 1) t.isLt) i - M.S (t : ℕ) (pre ω t t.isLt.le) i) ∂Q = 0

/-- **(1.3)** `𝒬 = {Q ⋘ 𝒫 : Q is a martingale measure and E_Q[gⁱ] = 0, i = 1, …, e}`, with
`E_Q` the extended expectation (1.1). -/
def MartMeasures (M : Market Ω₁ T d e) : Set (Measure (Fin T → Ω₁)) :=
  {Q | IsProbabilityMeasure Q ∧ AbsContSet Q M.models ∧ M.IsMartingaleMeasure Q ∧
    ∀ i : Fin e, extExp Q (fun ω => ((M.g ω i : ℝ) : EReal)) = 0}

/-- `𝒬_φ = {Q ∈ 𝒬 : E_Q[φ] < ∞}` (p. 25, p. 30), for a weight function `φ ≥ 1`. -/
def MartMeasuresWeighted (M : Market Ω₁ T d e) (φ : (Fin T → Ω₁) → ℝ) :
    Set (Measure (Fin T → Ω₁)) :=
  {Q | Q ∈ M.MartMeasures ∧ (∫⁻ ω, ENNReal.ofReal (φ ω) ∂ Q) < ⊤}

/-- The superhedging price (Superhedging Theorem, p. 6; Theorem 5.1(b), p. 30):
`π(f) = inf{x ∈ ℝ : ∃ (H, h) ∈ ℋ × ℝ^e, x + H • S_T + hg ≥ f 𝒫-q.s.}`, an infimum in
`[−∞, ∞]` with `inf ∅ = +∞`. -/
noncomputable def price (M : Market Ω₁ T d e) (f : (Fin T → Ω₁) → ℝ) : EReal :=
  sInf {x : EReal | ∃ x' : ℝ, x = (x' : EReal) ∧ ∃ H, M.Admissible H ∧ ∃ h : Fin e → ℝ,
    M.QS (fun ω => f ω ≤ x' + M.wealth H ω + h ⬝ᵥ M.g ω)}

/-- `f` is *replicable* (p. 7): `x + H • S_T + hg = f` `𝒫`-q.s. for some `x ∈ ℝ` and
`(H, h) ∈ ℋ × ℝ^e`. -/
def Replicable (M : Market Ω₁ T d e) (f : (Fin T → Ω₁) → ℝ) : Prop :=
  ∃ x : ℝ, ∃ H, M.Admissible H ∧ ∃ h : Fin e → ℝ,
    M.QS (fun ω => x + M.wealth H ω + h ⬝ᵥ M.g ω = f ω)

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

/-- `ℰ_t(f)(ω) = sup_{Q ∈ 𝒬_t(ω)} E_Q[f(ω, ·)]` (Lemma 4.10, p. 25), in `[−∞, ∞]`. -/
noncomputable def condSup (M : Market Ω₁ T d e) (t : ℕ) (f : (Fin t → Ω₁) × Ω₁ → EReal)
    (ω : Fin t → Ω₁) : EReal :=
  ⨆ Q ∈ M.localMartMeasures t ω, extExp Q (fun x => f (ω, x))

end Market

end Model

end NondomArb.Superhedge


