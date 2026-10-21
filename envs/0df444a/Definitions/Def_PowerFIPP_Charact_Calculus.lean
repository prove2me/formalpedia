-- Prove2me | Definitions.Def_PowerFIPP_Charact_Calculus
-- name    : PowerFIPP_Charact_Calculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:47.190764+00:00
-- url     : https://prove2.me/theorems/d45345e9-fd94-4977-96bb-4a571ecc31c3
-- title:
--   §2.1, (2.1)–(2.2) — jumps, differential characteristics, continuous martingale part, compensated jump integrals, stochastic integral, Doléans-Dade exponential, class (DL)
-- statement:
--   This file introduces the general semimartingale calculus used by Bo, Capponi and Zhou. Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathbb F=(\mathcal F_t)_{t\ge0}$, time runs over $[0,\infty)$, and a process is a map $[0,\infty)\times\Omega\to\mathbb R^n$. "Local martingale" means the published notion `EthierKurtz.IsSourceLocalMartingale` (a localizing sequence of stopping times whose stopped processes are martingales), componentwise for vector processes. Every object below is either an explicit formula or a relation that determines it up to indistinguishability.
--
--   1. **Jumps.** For a path $X$, $X_{t-}$ is the left limit (with $X_{0-}=X_0$) and $\Delta X_t=X_t-X_{t-}$; a path is *càdlàg* if it is right-continuous with left limits.
--   2. **Truncation.** $h(u)=u\,\mathbf 1_{\{|u|\le1\}}$ on $\mathbb R^n$ with the Euclidean norm, and $h^D(v)=v\,\mathbf 1_{\{|v|\le1\}}$ on $\mathbb R$.
--   3. **Differential characteristics** $(b,c,F)$ of $X$ under a measure $Q$, with $B=\int_0^\cdot b_t\,dt$, $C=\int_0^\cdot c_t\,dt$, $\nu(dt,du)=F_t(du)\,dt$: $X$ is adapted and càdlàg, $b,c$ are predictable, $c$ is symmetric positive semidefinite, $F$ is a predictable kernel with $F_t(\{0\})=0$ and $\int(|u|^2\wedge1)F_t(du)<\infty$, the rates are pathwise locally integrable, and, writing $X(h)=X-X_0-\sum_{s\le\cdot}(\Delta X_s-h(\Delta X_s))$ and $M(h)=X(h)-B$,
--   $$M(h),\qquad M(h)^iM(h)^j-\int_0^\cdot\Big(c^{ij}_s+\int h^ih^j\,dF_s\Big)ds,\qquad \sum_{s\le\cdot}g(\Delta X_s)-\int_0^\cdot\!\!\int g\,dF_s\,ds$$
--   are local martingales, the last one for every bounded continuous $g\ge0$ vanishing near $0$.
--   4. **Continuous and purely discontinuous local martingales.** A continuous local martingale has continuous paths and starts at $0$; a purely discontinuous one is càdlàg, starts at $0$, and is strongly orthogonal to every continuous local martingale.
--   5. **Continuous martingale part** $X^c$: each component is a continuous local martingale and $M(h)-X^c$ is purely discontinuous.
--   6. **Compensated jump integral** $N=W*(\mu^X-\nu)$: a purely discontinuous local martingale with $\Delta N_t=W_t(\Delta X_t)\mathbf 1_{\{\Delta X_t\ne0\}}$ a.s.
--   7. **Integral against a continuous local martingale** $L=\beta\cdot X^c$ when $\langle X^{c,i},X^{c,j}\rangle=\int c^{ij}ds$: $L$ is a continuous local martingale, $\int_0^t\beta^\top c\beta\,ds<\infty$, and $L^2-\int\beta^\top c\beta\,ds$ and $LX^{c,i}-\int(c\beta)^i\,ds$ are local martingales.
--   8. **Stochastic integral** $I=\pi\cdot X$ of a predictable $\pi$, through the canonical decomposition (2.1):
--   $$I=\int_0^\cdot\pi_s^\top b_s\,ds+\pi\cdot X^c+(\pi^\top h(u))*(\mu-\nu)+\sum_{s\le\cdot}\pi_s^\top\big(\Delta X_s-h(\Delta X_s)\big),$$
--   every term existing.
--   9. **Doléans-Dade exponential**, for a process $N$ and $A=\langle N^c\rangle$:
--   $$\mathcal E(N)_t=\exp\Big(N_t-N_0-\tfrac12A_t\Big)\prod_{0<s\le t}(1+\Delta N_s)e^{-\Delta N_s}.$$
--   10. **Class (DL)** for a $[0,\infty]$-valued process $\zeta$ under $Q$: for every $T$, $\lim_{K\to\infty}\sup_{\tau}E^Q[\zeta_\tau\mathbf 1_{\{\zeta_\tau>K\}}]=0$, the supremum over stopping times $\tau\le T$.
--
--   These are the objects in terms of which the paper's model, admissible strategies, forward performance processes and the conditions of Theorem 3.3 are stated.
--
--   **Formalization Note** Characteristics follow the martingale-problem characterization of Jacod–Shiryaev, Theorem II.2.21; uniqueness of $X^c$ is Jacod–Shiryaev I.4.18, of $W*(\mu-\nu)$ is I.4.19 (the compensator has no atoms in time, so $\hat W=0$), and the Doléans-Dade formula is I.4.64. The stochastic integral is restricted to the class of integrands for which the four canonical-decomposition integrals exist separately, a subclass of general $X$-integrability (Jacod–Shiryaev III.6.30) containing every bounded predictable process. Lebesgue measure on $[0,\infty)$ is the restriction of Lebesgue measure on $\mathbb R$. Lean's infinite product is $1$ when the product does not converge; for semimartingale paths it converges. Class (DL) is stated in its classical uniform-integrability form, not Mathlib's $\varepsilon$–$\delta$ form.
-- source:
--   Bo, Capponi & Zhou, Power forward performance in semimartingale markets with stochastic integrated factors, arXiv:1811.11899v4, pp. 4–7, §2.1, (2.1)–(2.2), and p. 27 (class (DL), Lemma A.1)

import Mathlib
import Definitions.Def_EthierKurtz_IsSourceLocalMartingale

namespace PowerFIPP.Charact

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

/-! # Semimartingale calculus layer (§2.1 of Bo–Capponi–Zhou, arXiv:1811.11899v4, pp. 4–7)

Time is `ℝ≥0`; processes are maps `ℝ≥0 → Ω → E`. Every object of the general semimartingale
calculus that the paper uses (jumps, differential characteristics, continuous martingale part,
integrals against a continuous local martingale and against a compensated jump measure, the
stochastic integral `π · R`, the Doléans-Dade exponential, class (DL)) is introduced here, either
by an explicit formula or by a relation that determines it up to indistinguishability. Local
martingales are the published `EthierKurtz.IsSourceLocalMartingale`. -/

/-- Lebesgue measure on the time axis `ℝ≥0` (the restriction of Lebesgue measure on `ℝ`). -/
noncomputable def leb : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

/-- A path `f : ℝ≥0 → E` is càdlàg: right-continuous at every `t`, with a left limit at every `t`
(at `t = 0` the left-limit clause is empty, since `𝓝[<] 0 = ⊥`). -/
def IsCadlag {E : Type*} [TopologicalSpace E] (f : ℝ≥0 → E) : Prop :=
  (∀ t, ContinuousWithinAt f (Set.Ici t) t) ∧ ∀ t, ∃ y, Tendsto f (𝓝[<] t) (𝓝 y)

/-- The left limit `X_{t-}(ω)`, with the convention `X_{0-} = X_0` (Mathlib's `Function.leftLim`,
which returns `X_t` when `t` is isolated on the left or no left limit exists). -/
noncomputable def leftLim {Ω E : Type*} [TopologicalSpace E] (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) :
    E :=
  Function.leftLim (fun s => X s ω) t

/-- The jump `ΔX_t(ω) = X_t(ω) - X_{t-}(ω)`; in particular `ΔX_0 = 0`. -/
noncomputable def jump {Ω E : Type*} [TopologicalSpace E] [Sub E] (X : ℝ≥0 → Ω → E) (t : ℝ≥0)
    (ω : Ω) : E :=
  X t ω - leftLim X t ω

/-- The squared Euclidean norm `|u|² = ∑ᵢ uᵢ²` on `ℝⁿ = Fin n → ℝ`. -/
def sqNorm {n : ℕ} (u : Fin n → ℝ) : ℝ := ∑ i, u i ^ 2

/-- The truncation function `h(u) = u 1_{|u| ≤ 1}` (p. 13), with the Euclidean norm. -/
noncomputable def trunc {n : ℕ} (u : Fin n → ℝ) : Fin n → ℝ := if sqNorm u ≤ 1 then u else 0

/-- The scalar truncation function `h^D(v) = v 1_{|v| ≤ 1}`. -/
noncomputable def truncD (v : ℝ) : ℝ := if |v| ≤ 1 then v else 0

/-- Scalar local martingale (the published `EthierKurtz.IsSourceLocalMartingale`). -/
abbrev IsLocMart {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  EthierKurtz.IsSourceLocalMartingale Q ℱ X

/-- The truncated process `X(h)_t = X_t - X_0 - ∑_{s ≤ t} (ΔX_s - h(ΔX_s))`. The sum has finitely
many nonzero terms on `[0, t]` for a càdlàg path, since `u - h(u) = 0` for `|u| ≤ 1`. -/
noncomputable def truncProc {Ω : Type*} {n : ℕ} (X : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0) (ω : Ω) :
    Fin n → ℝ :=
  X t ω - X 0 ω - ∑' s : Set.Iic t, (jump X s ω - trunc (jump X s ω))

/-- `M(h)_t = X(h)_t - ∫_0^t b_s ds`, the local-martingale part of `X(h)` for drift rate `b`. -/
noncomputable def martPart {Ω : Type*} {n : ℕ} (X b : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0) (ω : Ω) :
    Fin n → ℝ :=
  fun i => truncProc X t ω i - ∫ s in Set.Icc 0 t, b s ω i ∂leb

/-- **Differential characteristics** `(b, c, F)` of an `ℝⁿ`-valued càdlàg process `X` under `Q`,
relative to the truncation `h(u) = u 1_{|u|≤1}` and `A_t = t`, i.e. `B = ∫ b dt`, `C = ∫ c dt`,
`ν(dt, du) = F_t(du) dt` (2.2). Encoded by the martingale-problem characterization of
Jacod–Shiryaev, Theorem II.2.21:
1. `X` is adapted with càdlàg paths; `b`, `c` are predictable, `c` is symmetric positive
   semidefinite, `F` is a predictable kernel with `F_t({0}) = 0` and `∫ (|u|² ∧ 1) F_t(du) < ∞`;
2. `b`, `c` and `∫(|u|² ∧ 1) F_s(du)` are pathwise locally integrable in time, `Q`-a.s.;
3. `M(h) = X(h) - ∫ b ds` is a local martingale (componentwise);
4. `M(h)^i M(h)^j - ∫_0^· (c^{ij}_s + ∫ h^i h^j dF_s) ds` is a local martingale;
5. `∑_{s ≤ ·} g(ΔX_s) - ∫_0^· ∫ g dF_s ds` is a local martingale for every bounded continuous
   `g ≥ 0` vanishing on a neighbourhood of `0`. -/
def IsDiffChar {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X b : ℝ≥0 → Ω → Fin n → ℝ)
    (c : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (F : ℝ≥0 → Ω → Measure (Fin n → ℝ)) : Prop :=
  (∀ ω, IsCadlag fun t => X t ω) ∧ StronglyAdapted ℱ X ∧
  (∀ i, IsStronglyPredictable ℱ fun t ω => b t ω i) ∧
  (∀ i j, IsStronglyPredictable ℱ fun t ω => c t ω i j) ∧
  (∀ t ω, (c t ω).PosSemidef) ∧
  (∀ A : Set (Fin n → ℝ), MeasurableSet A →
    Measurable[ℱ.predictable] fun q : ℝ≥0 × Ω => F q.1 q.2 A) ∧
  (∀ t ω, F t ω {0} = 0) ∧
  (∀ t ω, ∫⁻ u, ENNReal.ofReal (min (sqNorm u) 1) ∂F t ω < ∞) ∧
  (∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    (∀ i, IntegrableOn (fun s => b s ω i) (Set.Icc 0 t) leb) ∧
    (∀ i j, IntegrableOn (fun s => c s ω i j) (Set.Icc 0 t) leb) ∧
    ∫⁻ s in Set.Icc 0 t, ∫⁻ u, ENNReal.ofReal (min (sqNorm u) 1) ∂F s ω ∂leb < ∞) ∧
  (∀ i, IsLocMart Q ℱ fun t ω => martPart X b t ω i) ∧
  (∀ i j, IsLocMart Q ℱ fun t ω =>
    martPart X b t ω i * martPart X b t ω j -
      ∫ s in Set.Icc 0 t, (c s ω i j + ∫ u, trunc u i * trunc u j ∂F s ω) ∂leb) ∧
  (∀ g : (Fin n → ℝ) → ℝ, Continuous g → (∃ K, ∀ u, |g u| ≤ K) → (∀ u, 0 ≤ g u) →
    (∀ᶠ u in 𝓝 0, g u = 0) →
    IsLocMart Q ℱ fun t ω =>
      (∑' s : Set.Iic t, g (jump X s ω)) - ∫ s in Set.Icc 0 t, (∫ u, g u ∂F s ω) ∂leb)

/-- `N` is a continuous local martingale under `Q` with `N_0 = 0` (all paths continuous). -/
def IsContLocMart {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (N : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, Continuous fun t => N t ω) ∧ (∀ ω, N 0 ω = 0) ∧ IsLocMart Q ℱ N

/-- `N` is a purely discontinuous local martingale under `Q` (Jacod–Shiryaev I.4.11): càdlàg,
`N_0 = 0`, a local martingale, and strongly orthogonal to every continuous local martingale
(`N L` is a local martingale for every continuous local martingale `L`). -/
def IsPureDiscLocMart {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (N : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, IsCadlag fun t => N t ω) ∧ (∀ ω, N 0 ω = 0) ∧ IsLocMart Q ℱ N ∧
  ∀ L : ℝ≥0 → Ω → ℝ, IsContLocMart Q ℱ L → IsLocMart Q ℱ fun t ω => N t ω * L t ω

/-- `Xc` is the **continuous (local) martingale part** `X^c` of `X` under `Q`, for the drift rate
`b`: each component of `Xc` is a continuous local martingale and each component of
`M(h) - Xc` is a purely discontinuous local martingale (unique by Jacod–Shiryaev I.4.18). -/
def IsContPart {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X b Xc : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  (∀ i, IsContLocMart Q ℱ fun t ω => Xc t ω i) ∧
  ∀ i, IsPureDiscLocMart Q ℱ fun t ω => martPart X b t ω i - Xc t ω i

/-- `N = W ∗ (μ^X - ν)`, the integral of `W : ℝ≥0 → Ω → ℝⁿ → ℝ` against the compensated jump
measure of `X` under `Q`, for a process `X` whose compensator `ν(dt, du) = F_t(du) dt` has no
atoms in time (so `Ŵ = 0`): `N` is a purely discontinuous local martingale whose jumps are
`ΔN_t = W_t(ΔX_t) 1_{ΔX_t ≠ 0}`, `Q`-a.s. (unique by Jacod–Shiryaev I.4.19; it exists iff
`W ∈ G_loc(μ)`, Jacod–Shiryaev II.1.27–II.1.33). -/
def IsCompJumpIntegral {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (W : ℝ≥0 → Ω → (Fin n → ℝ) → ℝ) (N : ℝ≥0 → Ω → ℝ) : Prop :=
  IsPureDiscLocMart Q ℱ N ∧
  ∀ᵐ ω ∂Q, ∀ t, jump N t ω = if jump X t ω ≠ 0 then W t ω (jump X t ω) else 0

/-- `L = β · Xc`, the stochastic integral of the `ℝⁿ`-valued `β` against a continuous local
martingale `Xc` with `⟨Xc^i, Xc^j⟩ = ∫ c^{ij} ds`, under `Q`: `L` is a continuous local martingale,
`∫_0^t β^⊤ c β ds < ∞` for all `t` a.s. (`β ∈ L²_loc(Xc)`), `L² - ∫ β^⊤ c β ds` is a local
martingale (`⟨L⟩ = ∫ β^⊤cβ`), and `L Xc^i - ∫ (cβ)^i ds` is a local martingale for every `i`
(`⟨L, Xc^i⟩ = ∫ (cβ)^i`). These force `⟨L - β·Xc⟩ = 0`, hence uniqueness. -/
def IsContIntegral {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Xc : ℝ≥0 → Ω → Fin n → ℝ)
    (c : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (β : ℝ≥0 → Ω → Fin n → ℝ) (L : ℝ≥0 → Ω → ℝ) :
    Prop :=
  IsContLocMart Q ℱ L ∧
  (∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntegrableOn (fun s => β s ω ⬝ᵥ (c s ω *ᵥ β s ω)) (Set.Icc 0 t) leb) ∧
  IsLocMart Q ℱ (fun t ω => L t ω ^ 2 - ∫ s in Set.Icc 0 t, β s ω ⬝ᵥ (c s ω *ᵥ β s ω) ∂leb) ∧
  ∀ i, IsLocMart Q ℱ fun t ω => L t ω * Xc t ω i - ∫ s in Set.Icc 0 t, (c s ω *ᵥ β s ω) i ∂leb

/-- The quadratic-variation rate integral `∫_0^t β_s^⊤ c_s β_s ds`, i.e. `⟨β · X^c⟩_t`. -/
noncomputable def qv {Ω : Type*} {n : ℕ} (c : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (β : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Icc 0 t, β s ω ⬝ᵥ (c s ω *ᵥ β s ω) ∂leb

/-- `I = π · X`, the stochastic integral of a predictable `ℝⁿ`-valued `π` against the
semimartingale `X` with characteristics `(b, c, F)` under `Q`, through the canonical decomposition
(2.1) `X = X_0 + B + X^c + h(u) ∗ (μ - ν) + (u - h(u)) ∗ μ`:
`I = ∫_0^· π^⊤ b ds + π · X^c + (π^⊤ h(u)) ∗ (μ - ν) + ∑_{s ≤ ·} π_s^⊤ (ΔX_s - h(ΔX_s))`,
each of the four terms existing (the drift integral pathwise a.s.). This is the class of
strategies whose canonical-decomposition integrals exist separately, a subclass of general
`X`-integrability (Jacod–Shiryaev III.6.30) containing every bounded predictable `π`. -/
def IsStochIntegral {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X b : ℝ≥0 → Ω → Fin n → ℝ)
    (c : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (π : ℝ≥0 → Ω → Fin n → ℝ) (I : ℝ≥0 → Ω → ℝ) :
    Prop :=
  IsStronglyPredictable ℱ π ∧
  ∃ (Xc : ℝ≥0 → Ω → Fin n → ℝ) (Ic Id : ℝ≥0 → Ω → ℝ),
    IsContPart Q ℱ X b Xc ∧ IsContIntegral Q ℱ Xc c π Ic ∧
    IsCompJumpIntegral Q ℱ X (fun t ω u => π t ω ⬝ᵥ trunc u) Id ∧
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      IntegrableOn (fun s => π s ω ⬝ᵥ b s ω) (Set.Icc 0 t) leb ∧
      I t ω = (∫ s in Set.Icc 0 t, π s ω ⬝ᵥ b s ω ∂leb) + Ic t ω + Id t ω +
        ∑' s : Set.Iic t, π s ω ⬝ᵥ (jump X s ω - trunc (jump X s ω))

/-- The **Doléans-Dade exponential** by its explicit formula (Jacod–Shiryaev I.4.64):
`𝓔(N)_t = exp(N_t - N_0 - A_t / 2) ∏_{0 < s ≤ t} (1 + ΔN_s) e^{-ΔN_s}`, where `A = ⟨N^c⟩` is
passed in (`∫ β^⊤cβ ds` for `β · X^c`, `∫ c^D ds` for `D^c`, `0` for a finite-variation `N`).
Times without a jump contribute the factor `1`; for a semimartingale `∑ (ΔN_s)² < ∞` and the
product converges absolutely. Junk value: Lean's `tprod` is `1` when the product is not
multipliable, which does not happen for semimartingale paths. -/
noncomputable def stochExp {Ω : Type*} (N A : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (N t ω - N 0 ω - A t ω / 2) *
    ∏' s : Set.Ioc 0 t, (1 + jump N s ω) * Real.exp (-jump N s ω)

/-- `τ` is a stopping time bounded by `T`: `τ ∈ 𝒯_T`. -/
def IsBoundedStop {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) : Prop :=
  IsStoppingTime ℱ τ ∧ ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)

/-- **Class (DL)** under `Q` for a `[0, ∞]`-valued process `ζ` (for a real process apply it to
`|ζ|`): for every `T`, the family `{ζ_τ : τ a stopping time, τ ≤ T}` is uniformly integrable in the
classical sense, `lim_{K → ∞} sup_{τ ∈ 𝒯_T} E^Q[ζ_τ 1_{ζ_τ > K}] = 0`. -/
def ClassDL {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (ζ : ℝ≥0 → Ω → ℝ≥0∞) : Prop :=
  ∀ T : ℝ≥0, Tendsto (fun K : ℝ≥0 => ⨆ (τ : Ω → WithTop ℝ≥0) (_ : IsBoundedStop ℱ T τ),
      ∫⁻ ω, {ω | (K : ℝ≥0∞) < stoppedValue ζ τ ω}.indicator (stoppedValue ζ τ) ω ∂Q)
    atTop (𝓝 0)

end PowerFIPP.Charact


