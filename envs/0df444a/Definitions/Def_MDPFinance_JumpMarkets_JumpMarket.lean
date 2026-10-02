-- Prove2me | Definitions.Def_MDPFinance_JumpMarkets_JumpMarket
-- name    : MDPFinance_JumpMarkets_JumpMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:23:15.111827+00:00
-- url     : https://prove2.me/theorems/4fe28398-72dd-4640-9396-481dcbe1fd91
-- title:
--   The pure jump market, the terminal wealth problem and its embedded discrete-time model
-- statement:
--   The data of §9.3. The market is the pure jump market of §3.2: the bond is
--   $S^0_t = e^{\rho t}$ with $\rho \ge 0$, and the risky assets follow
--   $dS^k_t = S^k_{t-}(\mu_k dt + dC^k_t)$ where $C_t = \sum_{n \le N_t} Y_n$ is a multivariate
--   compound Poisson process of intensity $\lambda$ whose jump law $Q_Y$ is supported in
--   $(-1,\infty)^d$ — which is what keeps the stock prices positive. Short-sellings are prohibited, so
--   the admissible fractions of wealth are
--
--   $$ \mathcal{U} := \{u \in \mathbb{R}^d \mid u \ge 0,\ u \cdot e \le 1\}, $$
--
--   a compact set, and the wealth follows
--   $dX_t = X_{t-}((\rho + \pi_t \cdot (\mu - \rho e))dt + \pi_t dC_t)$ **(9.10)**. The investor
--   maximises $V_\pi(t,x) := \mathbb{E}^\pi_{tx}[U(X_T)]$ over portfolio strategies, with
--   $V(t,x) := \sup_\pi V_\pi(t,x)$ **(9.11)**, where $U$ is strictly increasing and strictly concave;
--   $\mathbb{E}\|Y_n\| < \infty$ is assumed throughout.
--
--   This is a Piecewise Deterministic Markov Decision Problem with *finite* horizon, so the time
--   component enters the state space. The embedded discrete-time model (p. 282) has state space
--   $E = [0,T] \times \mathbb{R}_+$ — a state $(t,x)$ is a jump time point and the wealth directly
--   after that jump — and action space
--
--   $$ A := \{\alpha : [0,T] \to \mathcal{U} \text{ measurable}\} \tag{9.12} $$
--
--   whose elements are whole deterministic *control paths* to be followed until the next jump, not
--   single portfolio vectors. Between jumps the wealth moves by
--
--   $$ \phi^\alpha_t(x) = x \exp\Big(\int_0^t (\rho + \alpha_s \cdot (\mu - \rho e))ds\Big). \tag{9.13} $$
--
--   The transition kernel is
--   $Q(B|t,x,\alpha) = \lambda\int_0^{T-t} e^{-\lambda s}[\int \mathbf 1_B(t+s, \phi^\alpha_s(x)(1+\alpha_s \cdot y))Q_Y(dy)]ds$,
--   **substochastic**: the missing mass $e^{-\lambda(T-t)}$ is the probability of no further jump
--   before $T$, which the book writes as transition to a cemetery state $\Delta$ and which here is the
--   deficiency of the measure. The one-stage reward is
--   $r(t,x,\alpha) := e^{-\lambda(T-t)}U(\phi^\alpha_{T-t}(x))$, non-negative and **unbounded**.
--
--   Chapter 7's contracting theory then needs the bounding function $b(t,x) := e^{\gamma(T-t)}(1+x)$,
--   the constants $\barμ := \max\{\mu_1,\dots,\mu_d,\rho\}$ and
--   $\bar y := \max\{\mathbb{E}Y_1,\dots,\mathbb{E}Y_d,0\}$, the explicit modulus $\alpha_\gamma$ of
--   **(9.14)**, and the set
--
--   $$ IM_{cv} := \{v \in IB_b \mid v \text{ continuous},\ v(t,x) \text{ concave and increasing in } x
--   \text{ and decreasing in } t,\ v \ge U\}. $$
--
--   Two conventions govern the whole formalization.
--
--   **Suprema are never `sSup`.** The operator $\mathcal{T}$ of **(9.15)** is a supremum over $A$, and
--   Mathlib's `sSup` of a set of reals unbounded above is $0$, so `sSup` would make every statement
--   about $\mathcal{T}$ vacuous — a live risk here, since the reward is unbounded. $\mathcal{T}$ is
--   therefore carried as a *relation* ("$w$ is $\mathcal{T}v$") defined by `IsLUB` against the
--   explicit set of achievable values, and its iterates $\mathcal{T}^n g$ as a chain of such
--   relations. The weighted norm $\|\cdot\|_b$ is likewise never formed; statements using it are given
--   in their $\le$-form against $b$.
--
--   **The continuous-time side is built.** Theorem 9.3.1 *is* the identification of the
--   continuous-time value with the discrete-time one, so carrying either abstractly would make it
--   vacuous. The law of the embedded jump chain $(T_n, Z_n)$ is pinned by the one-step conditional law
--   displayed on p. 282, $X_T$ is read off the chain on $\{T_k \le T < T_{k+1}\}$, and the
--   discrete-time reward is the one-stage reward summed with the indicator $\mathbf 1_{[T_k \le T]}$
--   that encodes the cemetery state.
--
--   **Moderation note.** The draft carried no topology or σ-algebra on the action space `A`: `Ls` was quantified over an *arbitrary* `TopologicalSpace (Control d)` instance (with the indiscrete topology `Ls A^*_n` is everything, with the discrete one it is empty, so Theorem 9.3.4 e) and 9.3.7 b) were refutable), and "measurable decision rules" could not be stated. Now the relaxed controls `R` carry the Young topology of Remark 8.2.3 with its Borel σ-algebra and `A ⊂ R` the induced ones; `A^*` over `R` (`AstarRel`), the relaxed flow, reward and kernel are defined. `V_π` and `J_{∞(f_n)}` were real Bochner integrals (junk `0` when not integrable); they are `[0,∞]`-valued now, with `V := sup_π V_π` over history-dependent strategies (`HistPolicy`, Theorem 9.3.1 b)'s actual content) and `J_∞ := sup_{(f_n)} J_{∞(f_n)}` over measurable Markov policies; the bounding-function integral is a Lebesgue integral; `U` is continuous on `[0,∞)` and `𝔼‖Y‖ < ∞` a Lebesgue condition. `𝒯` on real `v ∈ IB_b` keeps the `IsLUB` rendering.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §9.3, pp. 280-286 (PDF 290-296)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MDPFinance.JumpMarkets

/-- `𝒰 := {u ∈ ℝ^d | u ≥ 0, u·e ≤ 1}`, the admissible fractions of wealth in the stocks (p. 281):
short-sellings are prohibited, which keeps the wealth positive in a market with jumps. Compact. -/
def Ucal (d : ℕ) : Set (Fin d → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}

/-- `A := {α : [0,T] → 𝒰 measurable}` **(9.12)**: a whole deterministic control path, followed
until the next jump. -/
structure Control (d : ℕ) where
  val : ℝ → (Fin d → ℝ)
  meas : Measurable val
  mem : ∀ s, val s ∈ Ucal d

/-- The relaxed controls `R := {α : [0,T] → ℙ(𝒰) measurable}` (p. 285, as in Chapter 8). -/
def RelaxedControl (d : ℕ) := {α : ℝ → ProbabilityMeasure (Ucal d) // Measurable α}

/-- Strong Carathéodory functions `Car(ℝ₊ × 𝒰)` (Remark 8.2.3). -/
def IsCaratheodory {d : ℕ} (w : ℝ × Ucal d → ℝ) : Prop :=
  (∀ t, Continuous fun u => w (t, u)) ∧ (∀ u, Measurable fun t => w (t, u)) ∧
    (∫⁻ t in Set.Ioi (0 : ℝ), ⨆ u, ENNReal.ofReal |w (t, u)|) < ⊤

set_option warn.classDefReducibility false in
/-- The **Young topology** (Remark 8.2.3): the coarsest topology making
`α ↦ ∫_0^∞ ∫_𝒰 w(t,u) α_t(du) dt` continuous for every `w ∈ Car`. `R` is compact metrizable in
it and `A ⊂ R` (via point masses) is a Borel space — the topology and σ-algebra the book uses for
`Ls` and for "measurable decision rules `E → A`". -/
noncomputable def youngTopology (d : ℕ) : TopologicalSpace (ℝ → ProbabilityMeasure (Ucal d)) :=
  ⨅ w ∈ {w : ℝ × Ucal d → ℝ | IsCaratheodory w},
    TopologicalSpace.induced
      (fun α : ℝ → ProbabilityMeasure (Ucal d) =>
        ∫ t in Set.Ioi (0 : ℝ), ∫ u, w (t, u) ∂(α t).toMeasure)
      inferInstance

noncomputable instance instTopologicalSpaceRelaxedControl (d : ℕ) :
    TopologicalSpace (RelaxedControl d) :=
  TopologicalSpace.induced Subtype.val (youngTopology d)

noncomputable instance instMeasurableSpaceRelaxedControl (d : ℕ) :
    MeasurableSpace (RelaxedControl d) :=
  borel (RelaxedControl d)

variable {d : ℕ}

/-- `A ⊂ R`: an ordinary control as the relaxed control `s ↦ δ_{α_s}`. -/
noncomputable def Control.toRelaxed (a : Control d) : RelaxedControl d :=
  ⟨fun s => ⟨Measure.dirac (⟨a.val s, a.mem s⟩ : Ucal d), Measure.dirac.isProbabilityMeasure⟩,
    (Measure.measurable_dirac.comp (a.meas.subtype_mk)).subtype_mk⟩

noncomputable instance instTopologicalSpaceControl (d : ℕ) : TopologicalSpace (Control d) :=
  TopologicalSpace.induced Control.toRelaxed inferInstance

noncomputable instance instMeasurableSpaceControl (d : ℕ) : MeasurableSpace (Control d) :=
  MeasurableSpace.comap Control.toRelaxed inferInstance

/-- The pure jump market of §3.2 as §9.3 uses it (p. 280) with the terminal-wealth utility: bond
`S^0_t = e^{ρt}`, `ρ ≥ 0`; stocks `dS^k_t = S^k_{t-}(μ_k dt + dC^k_t)` with `C` a compound Poisson
process of intensity `λ` and jump law `Q_Y` on `(-1,∞)^d`; `𝔼‖Y_n‖ < ∞`; `U : [0,∞) → ℝ_+`
strictly increasing, strictly concave, continuous; horizon `T`. -/
structure JumpMarket (d : ℕ) where
  rho : ℝ
  rho_nonneg : 0 ≤ rho
  mu : Fin d → ℝ
  lam : ℝ
  lam_pos : 0 < lam
  QY : Measure (Fin d → ℝ)
  QY_prob : IsProbabilityMeasure QY
  QY_supp : QY {y : Fin d → ℝ | ∃ i, y i ≤ -1} = 0
  QY_integrable : ∫⁻ y, ‖y‖ₑ ∂QY < ⊤
  T : ℝ
  T_pos : 0 < T
  U : ℝ → ℝ
  U_nonneg : ∀ x, 0 ≤ x → 0 ≤ U x
  U_mono : StrictMonoOn U (Set.Ici 0)
  U_concave : StrictConcaveOn ℝ (Set.Ici 0) U
  U_cont : ContinuousOn U (Set.Ici 0)

/-- The state space `E = [0,T] × ℝ_+` of the embedded model (p. 282). -/
def JumpMarket.E (M : JumpMarket d) : Set (ℝ × ℝ) := Set.Icc 0 M.T ×ˢ Set.Ici 0

/-- `\barμ := max{μ_1,…,μ_d, ρ}` (p. 284). -/
noncomputable def JumpMarket.mubar (M : JumpMarket d) : ℝ :=
  max M.rho (⨆ i : Fin d, M.mu i)

/-- `\bar y := max{𝔼Y_1,…,𝔼Y_d, 0}` (p. 284). -/
noncomputable def JumpMarket.ybar (M : JumpMarket d) : ℝ :=
  max 0 (⨆ i : Fin d, ∫ y, y i ∂M.QY)

/-- `φ^α_t(x) = x exp(∫_0^t (ρ + α_s·(μ - ρe)) ds)` **(9.13)**. -/
noncomputable def JumpMarket.phi (M : JumpMarket d) (a : Control d) (t x : ℝ) : ℝ :=
  x * Real.exp (∫ s in Set.Ioc (0 : ℝ) t, (M.rho + ∑ i, a.val s i * (M.mu i - M.rho)))

/-- The relaxed flow `φ^α_t(x) = x exp(∫_0^t ∫_𝒰 (ρ + u·(μ - ρe)) α_s(du) ds)` (p. 287). -/
noncomputable def JumpMarket.phiRel (M : JumpMarket d) (α : RelaxedControl d) (t x : ℝ) : ℝ :=
  x * Real.exp (∫ s in Set.Ioc (0 : ℝ) t,
    ∫ u, (M.rho + ∑ i, (u : Fin d → ℝ) i * (M.mu i - M.rho)) ∂(α.1 s).toMeasure)

/-- The substochastic transition law `Q(·|t,x,α)` of the embedded model (p. 282):
`Q(B|t,x,α) = λ ∫_0^{T-t} e^{-λs} ∫ 1_B(t+s, φ^α_s(x)(1+α_s·y)) Q_Y(dy) ds`; the missing mass
`e^{-λ(T-t)}` is the cemetery state `Δ` (no further jump before `T`). -/
noncomputable def JumpMarket.Q (M : JumpMarket d) (a : Control d) (p : ℝ × ℝ) :
    Measure (ℝ × ℝ) :=
  (((volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))).bind
    (fun s => M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))))

/-- The extension of `Q` to relaxed controls (p. 285):
`∫ v dQ(·|t,x,α) = λ ∫_0^{T-t} e^{-λs} ∫∫ v(t+s, φ^α_s(x)(1+u·y)) α_s(du) Q_Y(dy) ds`. -/
noncomputable def JumpMarket.QRel (M : JumpMarket d) (α : RelaxedControl d) (p : ℝ × ℝ) :
    Measure (ℝ × ℝ) :=
  (((volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))).bind
    (fun s => ((α.1 s).toMeasure.prod M.QY).map
      (fun uy : Ucal d × (Fin d → ℝ) =>
        (p.1 + s, M.phiRel α s p.2 * (1 + ∑ i, (uy.1 : Fin d → ℝ) i * uy.2 i)))))

/-- `r(t,x,α) := e^{-λ(T-t)} U(φ^α_{T-t}(x))` (p. 282), nonnegative and unbounded. -/
noncomputable def JumpMarket.r (M : JumpMarket d) (a : Control d) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-M.lam * (M.T - p.1)) * M.U (M.phi a (M.T - p.1) p.2)

/-- `r(t,x,α)` for relaxed `α` (p. 285). -/
noncomputable def JumpMarket.rRel (M : JumpMarket d) (α : RelaxedControl d) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-M.lam * (M.T - p.1)) * M.U (M.phiRel α (M.T - p.1) p.2)

/-- The one-step law of the embedded jump chain `(T_n, Z_n)` under the control path `α`
(p. 282): inter-jump time `Exp(λ)`, post-jump wealth `φ^α_s(x)(1+α_s·y)`. A probability, since
it does not truncate at the horizon. -/
noncomputable def JumpMarket.step (M : JumpMarket d) (a : Control d) (p : ℝ × ℝ) :
    Measure (ℝ × ℝ) :=
  (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))).bind
    (fun s => M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))))

/-- A (history-dependent) portfolio strategy `π_t = g_n(T_0,Z_0,…,T_n,Z_n)(t - T_n)` on
`(T_n, T_{n+1}]` (p. 283): measurable maps `g_n : E^{n+1} → A`. Markov strategies
`π = (f_n)` are the case `g_n(h) = f_n(h_n)` (`ofMarkov`). -/
def HistPolicy (d : ℕ) := (n : ℕ) → (Fin (n + 1) → ℝ × ℝ) → Control d

def IsHistPolicy (g : HistPolicy d) : Prop := ∀ n, Measurable (g n)

def ofMarkov (f : ℕ → ℝ × ℝ → Control d) : HistPolicy d := fun n h => f n (h (Fin.last n))

def IsMarkovStrategy (f : ℕ → ℝ × ℝ → Control d) : Prop := ∀ n, Measurable (f n)

/-- Cylinder probabilities of the embedded chain under `g`, by iterated integration against
`step` along the history. -/
noncomputable def JumpMarket.chainCyl (M : JumpMarket d) (g : HistPolicy d) :
    (n : ℕ) → (Fin (n + 1) → ℝ × ℝ) → ℕ → (ℕ → Set (ℝ × ℝ)) → ℝ≥0∞
  | _, _, 0, _ => 1
  | n, h, (m + 1), B =>
      ∫⁻ q in B 0, M.chainCyl g (n + 1) (Fin.snoc h q) m (fun i => B (i + 1))
        ∂(M.step (g n h) (h (Fin.last n)))

/-- `Pr` is the law `ℙ^π_{tx}` of the embedded jump chain `((T_n, Z_n))_n` under `g`, started at
`(t,x)`: a probability measure on paths whose finite-dimensional distributions are the ones the
displayed conditional law of p. 282 prescribes. -/
def JumpMarket.IsChainLaw (M : JumpMarket d) (g : HistPolicy d)
    (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) : Prop :=
  (∀ p, IsProbabilityMeasure (Pr p)) ∧
  ∀ (p : ℝ × ℝ) (m : ℕ) (B : ℕ → Set (ℝ × ℝ)), (∀ i, MeasurableSet (B i)) →
    Pr p {w : ℕ → ℝ × ℝ | ∀ i ≤ m, w i ∈ B i}
      = (B 0).indicator (fun q => M.chainCyl g 0 (fun _ => q) m (fun i => B (i + 1))) p

/-- `X_T` along a path: on `{T_k ≤ T < T_{k+1}}` it is `φ^{π}_{T-T_k}(Z_k)` (p. 283). -/
noncomputable def JumpMarket.terminalWealth (M : JumpMarket d) (g : HistPolicy d)
    (w : ℕ → ℝ × ℝ) : ℝ :=
  open Classical in
  if h : ∃ k : ℕ, (w k).1 ≤ M.T ∧ M.T < (w (k + 1)).1 then
    M.phi (g h.choose (fun i => w i)) (M.T - (w h.choose).1) (w h.choose).2
  else 0

/-- `V_π(t,x) := 𝔼^π_{tx}[U(X_T)]` in `[0,∞]` (p. 281). -/
noncomputable def JumpMarket.Vpi (M : JumpMarket d) (g : HistPolicy d)
    (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (M.U (M.terminalWealth g w)) ∂(Pr p)

/-- `V(t,x) := sup_π V_π(t,x)` **(9.11)** over all (history-dependent) strategies, given the
family `Pr` of their chain laws. -/
noncomputable def JumpMarket.V (M : JumpMarket d)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ⨆ g : HistPolicy d, ⨆ (_ : IsHistPolicy g), M.Vpi g (Pr g) p

/-- `J_{∞(f_n)}(t,x) := 𝔼^{(f_n)}_{tx}[Σ_k r(T'_k, Z'_k, f_k(T'_k, Z'_k))]` (p. 283), the
indicator `1_{[T_k ≤ T]}` encoding the cemetery state. -/
noncomputable def JumpMarket.Jinfpi (M : JumpMarket d) (f : ℕ → ℝ × ℝ → Control d)
    (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ∑' k : ℕ, (if (w k).1 ≤ M.T then ENNReal.ofReal (M.r (f k (w k)) (w k)) else 0) ∂(Pr p)

/-- `J_∞(t,x) := sup_{(f_n) ∈ F^∞} J_{∞(f_n)}(t,x)` (p. 283). -/
noncomputable def JumpMarket.Jinf (M : JumpMarket d)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ⨆ f : ℕ → ℝ × ℝ → Control d, ⨆ (_ : IsMarkovStrategy f), M.Jinfpi f (Pr (ofMarkov f)) p

/-- `J_f`, the value of the stationary policy `(f,f,…)`. -/
noncomputable def JumpMarket.Jstat (M : JumpMarket d)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ)) (f : ℝ × ℝ → Control d) (p : ℝ × ℝ) :
    ℝ≥0∞ :=
  M.Jinfpi (fun _ => f) (Pr (ofMarkov fun _ => f)) p

/-- The bounding function `b(t,x) := e^{γ(T-t)}(1+x)` of Proposition 9.3.2 (p. 284). -/
noncomputable def JumpMarket.bfun (M : JumpMarket d) (gamma : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (gamma * (M.T - p.1)) * (1 + p.2)

/-- `α_γ := (λ(1+\bar y)/(γ+λ-\barμ))(1 - e^{-T(γ+λ-\barμ)})` **(9.14)**. -/
noncomputable def JumpMarket.alphaGamma (M : JumpMarket d) (gamma : ℝ) : ℝ :=
  (M.lam * (1 + M.ybar) / (gamma + M.lam - M.mubar)) *
    (1 - Real.exp (-M.T * (gamma + M.lam - M.mubar)))

/-- `b` is a bounding function with module `α_b` (Definition 7.1.1): `r ≤ c_r b` on `E × A`
and `∫ b dQ(·|t,x,α) ≤ α_b b(t,x)` (Lebesgue integral of `b ≥ 0`). -/
def JumpMarket.IsBoundingFunction (M : JumpMarket d) (bf : ℝ × ℝ → ℝ) (alpha : ℝ) : Prop :=
  (∀ p ∈ M.E, 0 < bf p) ∧
  (∃ cr : ℝ, ∀ p ∈ M.E, ∀ a : Control d, |M.r a p| ≤ cr * bf p) ∧
  ∀ p ∈ M.E, ∀ a : Control d,
    ∫⁻ q, ENNReal.ofReal (bf q) ∂(M.Q a p) ≤ ENNReal.ofReal (alpha * bf p)

/-- `w = 𝒯v` **(9.15)**: `(𝒯v)(t,x) = sup_{α ∈ A} {r(t,x,α) + ∫ v dQ(·|t,x,α)}` on `E`, carried
as a relation via `IsLUB` (a real supremum over an unbounded set would be `0`). -/
def JumpMarket.IsTOf (M : JumpMarket d) (v w : ℝ × ℝ → ℝ) : Prop :=
  ∀ p ∈ M.E, IsLUB {y : ℝ | ∃ a : Control d, y = M.r a p + ∫ q, v q ∂(M.Q a p)} (w p)

/-- The chain of iterates `h_0 = g`, `h_{n+1} = 𝒯h_n` (the meaning of `𝒯^n g`). -/
def JumpMarket.IsTChain (M : JumpMarket d) (g : ℝ × ℝ → ℝ) (h : ℕ → ℝ × ℝ → ℝ) : Prop :=
  h 0 = g ∧ ∀ n : ℕ, M.IsTOf (h n) (h (n + 1))

/-- `IM_cv := {v ∈ IB_b | v continuous, v(t,x) concave and increasing in x and decreasing in t,
v ≥ U}` (p. 285). -/
def JumpMarket.IMcv (M : JumpMarket d) (bf : ℝ × ℝ → ℝ) (v : ℝ × ℝ → ℝ) : Prop :=
  (∃ C : ℝ, ∀ p ∈ M.E, |v p| ≤ C * bf p) ∧
  ContinuousOn v M.E ∧
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x => v (t, x))) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, MonotoneOn (fun x => v (t, x)) (Set.Ici (0 : ℝ))) ∧
  (∀ x : ℝ, 0 ≤ x → AntitoneOn (fun t => v (t, x)) (Set.Icc (0 : ℝ) M.T)) ∧
  ∀ p ∈ M.E, M.U p.2 ≤ v p

/-- `Lv(t,x,α) := r(t,x,α) + ∫ v dQ(·|t,x,α)` in `[0,∞]`, for ordinary and relaxed controls. -/
noncomputable def JumpMarket.L (M : JumpMarket d) (v : ℝ × ℝ → ℝ≥0∞) (a : Control d)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M.r a p) + ∫⁻ q, v q ∂(M.Q a p)

noncomputable def JumpMarket.LRel (M : JumpMarket d) (v : ℝ × ℝ → ℝ≥0∞) (α : RelaxedControl d)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M.rRel α p) + ∫⁻ q, v q ∂(M.QRel α p)

/-- `A^*_v(t,x)`, the maximum points of `α ↦ Lv(t,x,α)` over `A`. -/
def JumpMarket.Astar (M : JumpMarket d) (v : ℝ × ℝ → ℝ≥0∞) (p : ℝ × ℝ) : Set (Control d) :=
  {a | ∀ a' : Control d, M.L v a' p ≤ M.L v a p}

/-- `A^*_v(t,x)` over the relaxed controls `R` (p. 290, where `A^*_n(t,x) ⊂ R`). -/
def JumpMarket.AstarRel (M : JumpMarket d) (v : ℝ × ℝ → ℝ≥0∞) (p : ℝ × ℝ) :
    Set (RelaxedControl d) :=
  {α | ∀ α' : RelaxedControl d, M.LRel v α' p ≤ M.LRel v α p}

/-- `Ls D_n`, the upper limit of a sequence of sets (p. 201). -/
def LsSeq {X : Type*} [TopologicalSpace X] (Dn : ℕ → Set X) : Set X :=
  {a | ∃ an : ℕ → X, (∀ n, an n ∈ Dn n) ∧ MapClusterPt a atTop an}

end MDPFinance.JumpMarkets


