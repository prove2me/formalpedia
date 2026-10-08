-- Prove2me | Definitions.Def_UncertainPricing_Superrep_Setting
-- name    : UncertainPricing_Superrep_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:03.130892+00:00
-- url     : https://prove2.me/theorems/dfe40b54-1605-47ae-aeaa-05ffe27cc31e
-- title:
--   §2 and Appendix, pp. 3–10, 23 — canonical space, martingale measures, H(μ̲, μ̄), capacity, q.s., ℒ, stochastic integral, K, Λ
-- statement:
--   This file sets up the framework of §2 of Denis–Martini for superreplication under model uncertainty.
--
--   **Canonical space.** Fix $T>0$. $\Omega$ is the space of continuous paths $B=(B_t)_{t\in[0,T]}$ with $B_0=0$, with the uniform norm and its Borel $\sigma$-field $\mathcal B$. The coordinate process is $B_t(\omega)=\omega(t)$ and $\mathcal F_t=\sigma(B_s : s\le t)$ is the canonical filtration. A probability $P$ on $(\Omega,\mathcal B)$ is a **martingale measure** if $B$ is an $(\mathcal F_t)$-martingale under $P$; $\mathbf P_m$ is the set of these.
--
--   **Bracket bounds.** A nonzero measure $\bar\mu$ on $[0,T]$ with continuous distribution function is identified with that function, $\bar\mu_t=\bar\mu([0,t])$; it is **Hölder continuous** (display (1)) if $\bar\mu_t-\bar\mu_s\le C|t-s|^\alpha$ for $0\le s\le t\le T$ and some $C,\alpha>0$. For a set $\mathbf P\subseteq\mathbf P_m$, hypothesis $H(\bar\mu)$ says that for every $P\in\mathbf P$ the process $\bar\mu-\langle B\rangle^P$ is $P$-a.s. nondecreasing, written $d\langle B\rangle^P_t\le d\bar\mu_t$; hypothesis $H(\underline\mu,\bar\mu)$ says
--   $$d\underline\mu_t\le d\langle B\rangle^P_t\le d\bar\mu_t\qquad P\text{-a.s., for every }P\in\mathbf P.$$
--
--   **Capacity.** For bounded continuous $\varphi$, $c(\varphi)=\sup_{P\in\mathbf P}\|\varphi\|_{L^2(P)}$. It is extended (Appendix) first to lower semicontinuous $f\ge0$ by $c(f)=\sup\{c(\varphi):\varphi\in C_b(\Omega),\,0\le\varphi\le f\}$ and then to arbitrary $g$ by $c(g)=\inf\{c(f): f \text{ l.s.c.},\ f\ge|g|\}$. A set $A$ (measurable or not) is **polar** if $c(\mathbb 1_A)=0$, and a property holds **quasi-surely** (q.s.) if it holds outside a polar set. $\mathcal L$ is the completion of $C_b(\Omega)$ for the semi-norm $c$; its elements are the functions that are $c$-limits of bounded continuous functions.
--
--   **Stochastic integral.** An elementary integrand is $h_s=\sum_{i=0}^N k_{t_i}\mathbb 1_{]t_i,t_{i+1}]}(s)$ with a deterministic subdivision $0=t_0\le\dots\le t_{N+1}=T$ and bounded continuous $\mathcal F_{t_i}$-measurable $k_{t_i}$; its integral is $I_T(h)=\sum_i k_{t_i}(B_{t_{i+1}}-B_{t_i})$. The semi-norm of $\mathcal H$ is
--   $$\|h\|_{\mathcal H}=\sup_{P\in\mathbf P}\Big(E_P\int_0^T h_s^2\,d\bar\mu_s\Big)^{1/2}.$$
--   $K=\{I_T(h):h\in\mathcal H\}$: a function $g$ belongs to $K$ when it is the $c$-limit of the integrals $I_T(h^n)$ of an $\|\cdot\|_{\mathcal H}$-Cauchy sequence of elementary integrands; $K_{]a,b]}$ (the integrals $\int_a^b h_u\,dB_u$) is the same with integrands vanishing outside $]a,b]$.
--
--   **Superreplication price.** For a claim $f$,
--   $$\Lambda(f)=\inf\{a\in\mathbb R:\ \exists g\in K,\ a+g\ge f\ \text{q.s.}\},$$
--   valued in $[-\infty,+\infty]$. $\mathbf P'$ is the set of martingale measures that do not charge polar sets, and $\sup\{E_Pf:P\in S\}$ is taken in $[-\infty,+\infty]$ ($-\infty$ for empty $S$).
--
--   **Claim families** (Lemmas 5.4–5.6). A bounded continuous $f$ is *cylindrical* if $f=F(B_{t_1},\dots,B_{t_d})$ with $F$ bounded continuous; an *integral claim* if $f=G\big(\int_0^T F(B_s)\,ds\big)$ with $F$ continuous and $G$ bounded continuous; a *sup claim* if $f=G(\sup_{t\in[0,T]}B_t)$ with $G$ bounded continuous.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Points of $[0,T]$ are elements of `Set.Icc 0 T`; `evalR ω x` reads the path at a real time and is only used for $x\in[0,T]$. Distribution functions are `StieltjesFunction`s that are continuous, vanish at $0$ and are positive at $T$; $\bar\mu(]s,t])=\bar\mu([s,t])=\bar\mu_t-\bar\mu_s$. The quadratic variation is a predicate: $A$ is $(\mathcal F_t)$-adapted, $P$-a.s. its paths are continuous, nondecreasing and start at $0$, and $B^2-A$ is a $P$-martingale; when $\langle B\rangle^P_T\le\bar\mu_T$ the classical bracket satisfies this, and by Doob–Meyer uniqueness it is the only process that does. The capacity takes values in $[0,\infty]$; q.s. is capacity-based, not "a.s. for every $P$". The $\mathcal H$ semi-norm is read as $c\big((\int h^2d\bar\mu)^{1/2}\big)=\sup_P(E_P\int h^2d\bar\mu)^{1/2}$; the printed right-hand side on p. 5 puts the square root inside $E_P$, which is a slip (Lemma 2.4's proof uses the reading adopted here). $K$ is the image of the completion $\mathcal H$, not the $c$-closure of the elementary integrals. $\Lambda$ and all suprema are `EReal`. "Does not charge polar sets" uses the outer measure $P(A)$ of a possibly non-measurable $A$. In the cylindrical family $d=0$ (constants) is allowed and $F$ is taken bounded, as in the proof of Lemma 4.6.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, §2.1–§2.3 (pp. 3–10), display (1) p. 3, §5.2 Lemmas 5.4–5.6 (p. 22) and Appendix (p. 23)

import Mathlib

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

noncomputable section

/-- The canonical space `Ω = C([0,T], ℝ)` of continuous scalar paths `B` with `B₀ = 0` (§2.1, p. 3),
with the uniform (sup-norm) topology. -/
def Ω (T : ℝ) : Type :=
  {ω : C(Set.Icc (0 : ℝ) T, ℝ) // ∀ h : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T, ω ⟨0, h⟩ = 0}

instance (T : ℝ) : MetricSpace (Ω T) :=
  inferInstanceAs (MetricSpace {ω : C(Set.Icc (0 : ℝ) T, ℝ) //
    ∀ h : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T, ω ⟨0, h⟩ = 0})

/-- `𝓑`, the Borel σ-field of `Ω`. -/
instance (T : ℝ) : MeasurableSpace (Ω T) := borel (Ω T)

instance (T : ℝ) : BorelSpace (Ω T) := ⟨rfl⟩

/-- The coordinate process `B_t(ω) = ω(t)`, `t ∈ [0,T]`. -/
def B {T : ℝ} (t : Set.Icc (0 : ℝ) T) (ω : Ω T) : ℝ := ω.1 t

theorem continuous_B {T : ℝ} (t : Set.Icc (0 : ℝ) T) : Continuous (B t : Ω T → ℝ) :=
  (continuous_eval_const t).comp continuous_subtype_val

theorem measurable_B {T : ℝ} (t : Set.Icc (0 : ℝ) T) : Measurable (B t : Ω T → ℝ) :=
  (continuous_B t).measurable

/-- The path read at a real time: `B_x(ω)` for `x ∈ [0,T]`, and `0` outside `[0,T]`
(only times in `[0,T]` are ever used). -/
def evalR {T : ℝ} (ω : Ω T) (x : ℝ) : ℝ :=
  if h : x ∈ Set.Icc (0 : ℝ) T then ω.1 ⟨x, h⟩ else 0

/-- The canonical filtration `𝓕_t = σ(B_s : s ≤ t)`. -/
def canonFilt (T : ℝ) : Filtration (Set.Icc (0 : ℝ) T) (inferInstance : MeasurableSpace (Ω T)) where
  seq t := ⨆ (s : Set.Icc (0 : ℝ) T) (_ : s ≤ t),
    MeasurableSpace.comap (B s : Ω T → ℝ) inferInstance
  mono' _ _ hst := iSup₂_mono' fun s hs => ⟨s, le_trans hs hst, le_rfl⟩
  le' _ := iSup₂_le fun s _ => (measurable_B s).comap_le

/-- A martingale measure: a probability `P` on `(Ω, 𝓑)` under which the coordinate process is an
`𝓕_t`-martingale. `Ps_m` is the set of these. -/
def IsMartingaleMeasure {T : ℝ} (P : Measure (Ω T)) : Prop :=
  IsProbabilityMeasure P ∧ Martingale (fun t ω => B t ω) (canonFilt T) P

/-- A nonzero measure on `[0,T]` with continuous distribution function `μ_t = μ([0,t])`,
encoded by its distribution function. -/
def IsDistFn (T : ℝ) (μ : StieltjesFunction ℝ) : Prop :=
  Continuous μ ∧ μ 0 = 0 ∧ 0 < μ T

/-- Hölder continuity (1) of a distribution function on `[0,T]`. -/
def IsHolder (T : ℝ) (μ : ℝ → ℝ) : Prop :=
  ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → μ t - μ s ≤ C * |t - s| ^ α

/-- `A` is the quadratic variation `⟨B⟩^P` of `B` under `P`: `A` is adapted, `P`-a.s. its paths are
continuous, nondecreasing and start at `0`, and `B² − A` is a `P`-martingale. -/
def IsQuadVar {T : ℝ} (P : Measure (Ω T)) (A : Set.Icc (0 : ℝ) T → Ω T → ℝ) : Prop :=
  StronglyAdapted (canonFilt T) A ∧
  (∀ᵐ ω ∂P, Continuous (fun t => A t ω) ∧ Monotone (fun t => A t ω) ∧
    ∀ h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T, A ⟨0, h0⟩ ω = 0) ∧
  Martingale (fun t ω => B t ω ^ 2 - A t ω) (canonFilt T) P

/-- Hypothesis `H(μ̄)` for one `P`: `d⟨B⟩^P_t ≤ dμ̄_t`, i.e. `μ̄ − ⟨B⟩^P` is increasing `P`-a.s. -/
def HypU {T : ℝ} (μU : ℝ → ℝ) (P : Measure (Ω T)) : Prop :=
  ∃ A, IsQuadVar P A ∧ ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) T, s ≤ t →
    A t ω - A s ω ≤ μU t - μU s

/-- Hypothesis `H(μ̲, μ̄)` for one `P`: `dμ̲_t ≤ d⟨B⟩^P_t ≤ dμ̄_t`, `P`-a.s. -/
def HypLU {T : ℝ} (μL μU : ℝ → ℝ) (P : Measure (Ω T)) : Prop :=
  ∃ A, IsQuadVar P A ∧ ∀ᵐ ω ∂P, ∀ s t : Set.Icc (0 : ℝ) T, s ≤ t →
    μL t - μL s ≤ A t ω - A s ω ∧ A t ω - A s ω ≤ μU t - μU s

/-- The capacity on `C_b(Ω)`: `c(φ) = sup{‖φ‖_{L²(P)} : P ∈ Ps}` (§2.1.1). -/
def capCb {T : ℝ} (Ps : Set (Measure (Ω T))) (φ : Ω T →ᵇ ℝ) : ℝ≥0∞ :=
  ⨆ P ∈ Ps, eLpNorm (φ : Ω T → ℝ) 2 P

/-- Lebesgue extension, first step (Appendix, p. 23): for lower semicontinuous `f ≥ 0`,
`c(f) = sup{c(φ) : φ ∈ C_b(Ω), 0 ≤ φ ≤ f}`. -/
def capLsc {T : ℝ} (Ps : Set (Measure (Ω T))) (f : Ω T → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (φ : Ω T →ᵇ ℝ) (_ : ∀ ω, 0 ≤ φ ω ∧ ENNReal.ofReal (φ ω) ≤ f ω), capCb Ps φ

/-- Lebesgue extension, second step: for arbitrary `g`,
`c(g) = inf{c(f) : f lower semicontinuous, f ≥ |g|}`. -/
def cap {T : ℝ} (Ps : Set (Measure (Ω T))) (g : Ω T → ℝ) : ℝ≥0∞ :=
  ⨅ (f : Ω T → ℝ≥0∞) (_ : LowerSemicontinuous f) (_ : ∀ ω, ‖g ω‖ₑ ≤ f ω), capLsc Ps f

/-- A set `A ⊆ Ω` (not necessarily measurable) is polar if `c(A) = c(𝟙_A) = 0`. -/
def IsPolar {T : ℝ} (Ps : Set (Measure (Ω T))) (A : Set (Ω T)) : Prop :=
  cap Ps (A.indicator 1) = 0

/-- A property holds quasi-surely if it holds outside a polar set. -/
def QS {T : ℝ} (Ps : Set (Measure (Ω T))) (p : Ω T → Prop) : Prop :=
  ∃ A, IsPolar Ps A ∧ ∀ ω ∉ A, p ω

/-- Membership in `ℒ`, the completion of `C_b(Ω)` for the semi-norm `c`: `f` is a `c`-limit of a
sequence of bounded continuous functions. -/
def InL {T : ℝ} (Ps : Set (Measure (Ω T))) (f : Ω T → ℝ) : Prop :=
  ∃ φ : ℕ → (Ω T →ᵇ ℝ), Tendsto (fun n => cap Ps (fun ω => φ n ω - f ω)) atTop (𝓝 0)

/-- An elementary integrand `h_s = Σ_{i=0}^N k_{t_i} 𝟙_{]t_i,t_{i+1}]}(s)` of `ℋ_e` (§2.2.1): a
deterministic subdivision `0 = t_0 ≤ … ≤ t_{N+1} = T` and `𝓕_{t_i}`-measurable, bounded continuous
`k_{t_i}`. -/
structure ElemIntegrand (T : ℝ) where
  N : ℕ
  t : Fin (N + 2) → Set.Icc (0 : ℝ) T
  mono : Monotone t
  start : (t 0 : ℝ) = 0
  last : (t (Fin.last (N + 1)) : ℝ) = T
  k : Fin (N + 1) → Ω T →ᵇ ℝ
  meas : ∀ i : Fin (N + 1), Measurable[canonFilt T (t i.castSucc)] (k i : Ω T → ℝ)

namespace ElemIntegrand

variable {T : ℝ}

/-- The process `h_s(ω)`. -/
def proc (h : ElemIntegrand T) (s : ℝ) (ω : Ω T) : ℝ :=
  ∑ i : Fin (h.N + 1), h.k i ω *
    (Set.Ioc ((h.t i.castSucc : ℝ)) (h.t i.succ : ℝ)).indicator (fun _ => (1 : ℝ)) s

/-- The elementary stochastic integral `I_T(h) = Σ_i k_{t_i} (B_{t_{i+1}} − B_{t_i})`. -/
def integral (h : ElemIntegrand T) (ω : Ω T) : ℝ :=
  ∑ i : Fin (h.N + 1), h.k i ω * (B (h.t i.succ) ω - B (h.t i.castSucc) ω)

end ElemIntegrand

/-- The semi-norm of `ℋ`: `‖h‖_ℋ = sup_{P ∈ Ps} (E_P ∫_0^T h_s² dμ̄_s)^{1/2}`
(= `c((∫_0^T h_s² dμ̄_s)^{1/2})` on `ℋ_e`). -/
def normH {T : ℝ} (Ps : Set (Measure (Ω T))) (μU : StieltjesFunction ℝ) (h : ℝ → Ω T → ℝ) : ℝ≥0∞ :=
  ⨆ P ∈ Ps, (∫⁻ ω, ∫⁻ s in Set.Ioc 0 T, ‖h s ω‖ₑ ^ 2 ∂μU.measure ∂P) ^ (1 / 2 : ℝ)

/-- `g = ∫_a^b h_u dB_u` for some `h ∈ ℋ`, up to a `c`-null difference: `g` is the `c`-limit of the
elementary integrals of an `‖·‖_ℋ`-Cauchy sequence of elementary integrands supported in `]a,b]`. -/
def InKOn {T : ℝ} (Ps : Set (Measure (Ω T))) (μU : StieltjesFunction ℝ) (a b : ℝ) (g : Ω T → ℝ) :
    Prop :=
  ∃ hs : ℕ → ElemIntegrand T,
    (∀ n s ω, s ∉ Set.Ioc a b → (hs n).proc s ω = 0) ∧
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      normH Ps μU (fun s ω => (hs m).proc s ω - (hs n).proc s ω) < ε) ∧
    Tendsto (fun n => cap Ps (fun ω => (hs n).integral ω - g ω)) atTop (𝓝 0)

/-- `K = {I_T(h) : h ∈ ℋ}` (§2.2.2). -/
def InK {T : ℝ} (Ps : Set (Measure (Ω T))) (μU : StieltjesFunction ℝ) (g : Ω T → ℝ) : Prop :=
  InKOn Ps μU 0 T g

/-- The superreplication price `Λ(f) = inf{a : ∃ g ∈ K, a + g ≥ f q.s.}` (§2.3), in `EReal`
(`+∞` if no `a` works, `−∞` if every `a` works). -/
def Lam {T : ℝ} (Ps : Set (Measure (Ω T))) (μU : StieltjesFunction ℝ) (f : Ω T → ℝ) : EReal :=
  sInf {x : EReal | ∃ a : ℝ, x = (a : EReal) ∧ ∃ g, InK Ps μU g ∧ QS Ps (fun ω => f ω ≤ a + g ω)}

/-- `Ps′`: the martingale measures that do not charge polar sets (outer measure). -/
def Pprime {T : ℝ} (Ps : Set (Measure (Ω T))) : Set (Measure (Ω T)) :=
  {P | IsMartingaleMeasure P ∧ ∀ A, IsPolar Ps A → P A = 0}

/-- `sup{E_P f : P ∈ S}` in `EReal` (`−∞` for an empty `S`). -/
def supE {T : ℝ} (S : Set (Measure (Ω T))) (f : Ω T → ℝ) : EReal :=
  ⨆ P ∈ S, ((∫ ω, f ω ∂P : ℝ) : EReal)

/-- Cylindrical claims `f = F(B_{t_1}, …, B_{t_d})`, `F` bounded continuous (Lemma 5.4). -/
def IsCylindrical {T : ℝ} (f : Ω T →ᵇ ℝ) : Prop :=
  ∃ (d : ℕ) (ts : Fin d → Set.Icc (0 : ℝ) T) (F : (Fin d → ℝ) → ℝ),
    Continuous F ∧ BddAbove (Set.range fun x => |F x|) ∧ ∀ ω, f ω = F (fun i => B (ts i) ω)

/-- Claims `f = G(∫_0^T F(B_s) ds)`, `F` continuous, `G` bounded continuous (Lemma 5.5). -/
def IsIntegralClaim {T : ℝ} (f : Ω T →ᵇ ℝ) : Prop :=
  ∃ F G : ℝ → ℝ, Continuous F ∧ Continuous G ∧ BddAbove (Set.range fun x => |G x|) ∧
    ∀ ω, f ω = G (∫ s in (0 : ℝ)..T, F (evalR ω s))

/-- Claims `f = G(S)`, `S = sup_{t ∈ [0,T]} B_t`, `G` bounded continuous (Lemma 5.6). -/
def IsSupClaim {T : ℝ} (f : Ω T →ᵇ ℝ) : Prop :=
  ∃ G : ℝ → ℝ, Continuous G ∧ BddAbove (Set.range fun x => |G x|) ∧
    ∀ ω, f ω = G (⨆ t : Set.Icc (0 : ℝ) T, B t ω)

/-- The union of the three claim families of Lemmas 5.4–5.6. -/
def InClaimFamilies {T : ℝ} (f : Ω T →ᵇ ℝ) : Prop :=
  IsCylindrical f ∨ IsIntegralClaim f ∨ IsSupClaim f

end

end UncertainPricing.Superrep


