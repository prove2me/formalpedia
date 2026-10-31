-- Prove2me | Definitions.Def_TabooRegen_Model
-- name    : TabooRegen_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:15.150355+00:00
-- url     : https://prove2.me/theorems/4f33f8b3-8422-4cc7-87cc-5c85cbbd7eca
-- title:
--   Càdlàg path space, exit times, regeneration times, cycles and taboo-regeneration in the wide sense (Definition 2)
-- statement:
--   Let $S$ be a complete separable metric space and $A\subseteq S$. Adjoin a cemetery point $\Delta\notin S$ and write $\tilde S=S\cup\{\Delta\}$, with $\Delta$ isolated. The **path space** $D_{\tilde S}[0,\infty)$ consists of the functions $x:[0,\infty)\to\tilde S$ that are right continuous with left limits; it carries the σ-algebra $\mathcal D$. For such a path the **exit time** of $A$ is
--
--   $$
--   \gamma(x)=\inf\{t\ge0:\ x(t)\in A^c\},
--   $$
--
--   with $\gamma(x)=\infty$ when $x$ never visits $A^c$, and $i(x)=1$ exactly when $\gamma(x)=\infty$. The standing assumption is that $\gamma$ is measurable on $D_{\tilde S}[0,\infty)$.
--
--   The **model** consists of a probability space $(\Omega,P)$, a process $X=(X(t):t\ge0)$ with càdlàg paths in $S$, regeneration times $0=T(-1)\le T(0)<T(1)<\cdots$ obeying the **taboo convention** $T(n)=\infty$ on $\{\Gamma<T(n)\}$, where $\Gamma=\gamma(X)$ is the exit time of $X$ from $A$, and the **cycle processes**
--
--   $$
--   W_n(t)=\begin{cases}X(T(n-1)+t), & 0\le t<\tau_n,\\ \Delta, & t\ge\tau_n,\end{cases}\qquad \tau_n=T(n)-T(n-1).
--   $$
--
--   $W_0$ is the delay cycle; $\gamma_n=\gamma(W_n)$ and $I_n=i(W_n)$, so $I_n=1$ exactly when $X$ stays in $A$ over the $n$-th cycle. The **cycle law** is $Q=P(\cdot\mid\Gamma\ge T(0))$; when $T(0)=0$, $Q=P$.
--
--   **Definition 2.** $X$ is **taboo-regenerative in the wide sense** if for every $n\ge0$
--
--   $$
--   P\big((W_{n+1},W_{n+2},\dots)\in\cdot\mid T(0),\dots,T(n);\ \Gamma\ge T(n)\big)=P\big((W_1,W_2,\dots)\in\cdot\mid\Gamma\ge T(0)\big).
--   $$
--
--   Every classically regenerative process is taboo-regenerative in the wide sense; the wide sense also covers Markov chains with a taboo splitting construction (Remarks 2–3 of the paper). This is the setting of every statement of the mission.
--
--   **Formalization Note** $\tilde S$ is `S ⊕ Unit` with the sum topology; time is `ℝ≥0` and the regeneration times take values in `ℝ≥0∞`. The σ-algebra on paths is the trace of the cylinder σ-algebra, which equals the Skorohod Borel σ-algebra for separable metric $\tilde S$. The printed requirements "$T(0)<T(1)<\cdots$" and "$T(n)=\infty$ on $\{\Gamma<T(n)\}$" are read as: nondecreasing, strictly increasing while finite, infinite when $\Gamma<T(n)$ and only then. The cycles are carried with their defining equation and their measurability (both consequences of the càdlàg paths). Definition 2 is written without conditional expectations, as $P(C\cap H\cap\{\Gamma\ge T(n)\})=P(H\cap\{\Gamma\ge T(n)\})\,Q(C)$ for all measurable sets $C$ of cycle sequences and $H$ of values of $(T(0),\dots,T(n))$.
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, §2, pp.272–273 (paths, cycles, γ, Γ, Γ°), p.275 (taboo convention, Definition 2)

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

open KurtzProtter91.Integrals (IsCadlag)

/-- The path space `D_S̃[0, ∞)` (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes,
Queueing Systems 46 (2004), §2, pp.272–273: "right continuous with left limits"): càdlàg functions
`[0, ∞) → S̃`, where `S̃ = S ∪ {Δ}`. `IsCadlag` is the referenced
`KurtzProtter91.Integrals.IsCadlag`: right-continuous at every `t ≥ 0`, with a left limit at every
`t > 0`.

**Formalization Note.** `S̃` is `S ⊕ Unit` with the cemetery `Δ = Sum.inr ()`; with Mathlib's sum
topology `Δ` is an isolated point, and `S` keeps its own topology. Time is `ℝ≥0`. -/
def Path (S : Type*) [TopologicalSpace S] : Type _ :=
  {x : ℝ≥0 → S ⊕ Unit // IsCadlag x}

/-- The σ-algebra `𝒟` on `D_S̃[0, ∞)` (Queueing Systems 46 (2004), §2, p.273).

**Formalization Note.** It is the trace on the càdlàg paths of the product (cylinder) σ-algebra:
the smallest σ-algebra making every evaluation `x ↦ x(t)` measurable. For a separable metric `S̃`
this is the Borel σ-algebra of the Skorohod topology that the paper names (Ethier–Kurtz,
Prop. 3.7.1; Billingsley 1999, Thm. 16.6). -/
instance Path.instMeasurableSpace (S : Type*) [TopologicalSpace S] [MeasurableSpace S] :
    MeasurableSpace (Path S) :=
  MeasurableSpace.comap Subtype.val MeasurableSpace.pi

/-- The exit time `γ(x) = inf{t ⩾ 0 : x(t) ∈ Aᶜ}` of `A` for a path `x` in `S̃`
(Queueing Systems 46 (2004), §2, p.273), with value `∞ = ⊤` when `x` never visits `Aᶜ`.
The cemetery `Δ` is not in `Aᶜ ⊆ S`. The paper's `i(x)` is `1` exactly when `γ(x) = ⊤`. -/
noncomputable def exitTime {S : Type*} (A : Set S) (x : ℝ≥0 → S ⊕ Unit) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ∃ s, s ∉ A ∧ x t = Sum.inl s), (t : ℝ≥0∞)

/-- `T(n − 1)` with the convention `T(−1) = 0` (Queueing Systems 46 (2004), §2, p.273). -/
def prevTime {Ω : Type*} (T : ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  if n = 0 then 0 else T (n - 1) ω

/-- The cycle process (Queueing Systems 46 (2004), §2, p.273):
`Wₙ(t) = X(T(n − 1) + t)` for `0 ⩽ t < τₙ` and `Wₙ(t) = Δ` for `t ⩾ τₙ`, with
`τₙ = T(n) − T(n − 1)` and `T(−1) = 0`. `W₀` is the delay cycle. -/
noncomputable def cycleOf {S Ω : Type*} (X : Ω → ℝ≥0 → S) (T : ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    ℝ≥0 → S ⊕ Unit :=
  fun t => if prevTime T n ω + (t : ℝ≥0∞) < T n ω
    then Sum.inl (X ω (prevTime T n ω + (t : ℝ≥0∞)).toNNReal) else Sum.inr ()

/-- The setting of §2 (Queueing Systems 46 (2004), pp.272–275): a process `X` with càdlàg paths in
`S`, a set `A ⊆ S` whose exit time `γ` is measurable on `D_S̃[0, ∞)`, regeneration times
`0 = T(−1) ⩽ T(0) < T(1) < ⋯` subject to the taboo convention `T(n) = ∞` on `{Γ < T(n)}` (p.275),
and the cycle processes `Wₙ`.

**Formalization Note.**
* The probability space is `(Ω, P)`; `X(t)` is a random variable for each `t`.
* The regeneration times take values in `ℝ≥0∞`. The paper's "`T(0) < T(1) < ⋯`" (p.273) and
  "`T(n) = ∞` on `{Γ < T(n)}`" (p.275) are read together as: `T` is nondecreasing, strictly
  increasing while finite, `T(n) = ∞` whenever `Γ < T(n)`, and `T(n) = ∞` only through that
  convention (then `Γ < ∞`).
* The cycles `W n` are carried as data together with their defining equation `cycleOf` and their
  measurability; both follow from the càdlàg paths of `X` and the measurability of the `T(n)` (for
  Polish `S`), so they add no condition.
* "Assume that `γ` is measurable" (p.273) is the field `exit_measurable`. -/
structure Model (S : Type*) [TopologicalSpace S] [MeasurableSpace S] (A : Set S)
    (Ω : Type*) [MeasurableSpace Ω] where
  /-- the probability `P` -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  /-- the process `X = (X(t) : t ⩾ 0)` -/
  X : Ω → ℝ≥0 → S
  cadlag : ∀ ω, IsCadlag (X ω)
  measurable_X : ∀ t, Measurable fun ω => X ω t
  /-- `γ` is measurable on `D_S̃[0, ∞)` (p.273) -/
  exit_measurable : Measurable fun x : Path S => exitTime A x.1
  /-- the regeneration times `T(n)`, `n ⩾ 0` -/
  T : ℕ → Ω → ℝ≥0∞
  measurable_T : ∀ n, Measurable (T n)
  T_mono : ∀ n ω, T n ω ≤ T (n + 1) ω
  T_strict : ∀ n ω, T n ω < ⊤ → T n ω < T (n + 1) ω
  /-- the taboo convention `T(n) = ∞` on `{Γ < T(n)}` (p.275) -/
  taboo : ∀ n ω, exitTime A (fun t => Sum.inl (X ω t)) < T n ω → T n ω = ⊤
  T_top : ∀ n ω, T n ω = ⊤ → exitTime A (fun t => Sum.inl (X ω t)) < ⊤
  /-- the cycle processes `Wₙ` -/
  W : ℕ → Ω → Path S
  measurable_W : ∀ n, Measurable (W n)
  W_eq : ∀ n ω, (W n ω).1 = cycleOf X T n ω

namespace Model

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- The exit time `Γ = inf{t ⩾ 0 : X(t) ∈ Aᶜ} = γ(X)` (Queueing Systems 46 (2004), p.273). -/
noncomputable def Γ (ω : Ω) : ℝ≥0∞ := exitTime A (fun t => Sum.inl (M.X ω t))

/-- `T(n − 1)`, with `T(−1) = 0`. -/
def Tm (n : ℕ) (ω : Ω) : ℝ≥0∞ := prevTime M.T n ω

/-- The cycle length `τₙ = T(n) − T(n − 1)` (Queueing Systems 46 (2004), p.273); `τ₀ = T(0)`. -/
noncomputable def τ (n : ℕ) (ω : Ω) : ℝ≥0∞ := M.T n ω - M.Tm n ω

/-- The exit time `γₙ = γ(Wₙ)` of `A` for the cycle `Wₙ` (Queueing Systems 46 (2004), p.273). -/
noncomputable def γ (n : ℕ) (ω : Ω) : ℝ≥0∞ := exitTime A (M.W n ω).1

/-- The event `{Iₙ = 1}` that `X` stays in `A` over the `n`-th cycle (p.273): `γₙ = ∞`.
Since `Wₙ = Δ` from `τₙ` on, this is also `{γₙ > τₙ}` and `{γₙ ⩾ τₙ}`. -/
def NoExit (n : ℕ) : Set Ω := {ω | M.γ n ω = ⊤}

/-- The cycle law `Q = P( · | Γ ⩾ T(0))`, the law under which Definition 2 (p.275) makes
`(W₁, W₂, …)` the cycles of the non-delayed version. When `T(0) = 0`, `Q = P`. -/
noncomputable def Q : Measure Ω := ProbabilityTheory.cond M.P {ω | M.T 0 ω ≤ M.Γ ω}

/-- **Definition 2** (Queueing Systems 46 (2004), p.275): `X` is *taboo-regenerative in the wide
sense* if for every `n ⩾ 0`
`P((Wₙ₊₁, Wₙ₊₂, …) ∈ · | T(0), …, T(n); Γ ⩾ T(n)) = P((W₁, W₂, …) ∈ · | Γ ⩾ T(0))`.

**Formalization Note.** The conditional law given `σ(T(0), …, T(n))` on the event `{Γ ⩾ T(n)}` is
written without conditional expectations: for every measurable set `C` of cycle sequences and every
measurable set `H` of values of `(T(0), …, T(n))`,
`P(C ∩ H ∩ {Γ ⩾ T(n)}) = P(H ∩ {Γ ⩾ T(n)}) · Q(C)`. -/
def IsWideSenseTabooRegen : Prop :=
  ∀ n : ℕ, ∀ C : Set (ℕ → Path S), MeasurableSet C →
    ∀ H : Set (Fin (n + 1) → ℝ≥0∞), MeasurableSet H →
      M.P ({ω | (fun i : ℕ => M.W (n + 1 + i) ω) ∈ C} ∩
          {ω | (fun i : Fin (n + 1) => M.T i ω) ∈ H} ∩ {ω | M.T n ω ≤ M.Γ ω}) =
        M.P ({ω | (fun i : Fin (n + 1) => M.T i ω) ∈ H} ∩ {ω | M.T n ω ≤ M.Γ ω}) *
          M.Q {ω | (fun i : ℕ => M.W (1 + i) ω) ∈ C}

end Model

end TabooRegen


