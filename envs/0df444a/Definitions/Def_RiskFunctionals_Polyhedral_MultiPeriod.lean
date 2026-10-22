-- Prove2me | Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod
-- name    : RiskFunctionals_Polyhedral_MultiPeriod
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:58.647772+00:00
-- url     : https://prove2.me/theorems/87145f2e-4cfa-4f46-b064-a4926eb32b76
-- title:
--   Multi-period polyhedral probability functionals (3.54), conditions (i)–(ii), the dual set (3.56), the conjugate (3.58), and properties (MA0)–(MA5)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $T\in\mathbb N$, and $\boldsymbol{\mathcal F}=(\mathcal F_0,\mathcal F_1,\dots,\mathcal F_T)$ a **filtration** in $\mathcal F$ with trivial $\mathcal F_0=\{\emptyset,\Omega\}$: $\mathcal F_s\subseteq\mathcal F_t\subseteq\mathcal F$ for $s\le t\le T$. Let $p\in[1,\infty)$ and $\mathcal Y=\times_{t=1}^TL_p(\mathcal F_t)$, the processes $Y=(Y_1,\dots,Y_T)$ with $Y_t$ $\mathcal F_t$-measurable and $p$-integrable; $\mathcal Z=\times_{t=1}^TL_q(\mathcal F_t)$ likewise. The pairing is $\langle Y,Z\rangle=\sum_{t=1}^T\mathbb E(Y_tZ_t)$.
--
--   1. **Data.** Dimensions $k_t\in\mathbb N$, vectors $c_t\in\mathbb R^{k_t}$, sets $V_t\subseteq\mathbb R^{k_t}$ ($t=0,\dots,T$), and vectors $w_{t,\tau}\in\mathbb R^{k_{t-\tau}}$ ($\tau=0,\dots,t$, $t=1,\dots,T$). They are **polyhedral** if every $V_t$ is a non-empty polyhedral set.
--   2. **The functional (3.54).** For $Y\in\mathcal Y$,
--   $$\mathcal R(Y;\boldsymbol{\mathcal F})=\sup\Bigl\{\sum_{t=0}^T\mathbb E(\langle c_t,v_t\rangle)\ :\ v_t\in L_p(\mathcal F_t;\mathbb R^{k_t}),\ v_t\in V_t\ \text{a.s.},\ t=0,\dots,T;\ \sum_{\tau=0}^t\langle w_{t,\tau},v_{t-\tau}\rangle=Y_t\ \text{a.s.},\ t=1,\dots,T\Bigr\}.$$
--   3. **Condition (i):** every $V_t$ is a polyhedral cone and $\langle w_{t,0},V_t\rangle=\mathbb R$ for $t=1,\dots,T$ (complete recourse).
--   4. **Condition (ii) (dual feasibility):** there is $\bar u\in\mathbb R^T$ with $c_0-\sum_{\tau=1}^Tw_{\tau,\tau}\bar u_\tau\in V_0^*$ and $c_t-\sum_{\tau=t}^Tw_{\tau,\tau-t}\bar u_\tau\in V_t^*$, $t=1,\dots,T$.
--   5. **Dual set (3.56):**
--   $$\mathcal Z_*=\Bigl\{Z\in\mathcal Z:\ c_0-\sum_{\tau=1}^Tw_{\tau,\tau}\mathbb E(Z_\tau)\in V_0^*,\ \ c_t-\sum_{\tau=t}^Tw_{\tau,\tau-t}\mathbb E(Z_\tau\mid\mathcal F_t)\in V_t^*\ \text{a.s.},\ t=1,\dots,T\Bigr\}.$$
--   6. **Conjugate (3.58):** $\mathcal R^+(Z)=\inf\{\langle Y,Z\rangle-\mathcal R(Y;\boldsymbol{\mathcal F}):Y\in\mathcal Y\}$.
--   7. **Properties** of a real functional $\mathcal A$ on $\mathcal Y$: (MA1) $\mathcal A(Y_1,\dots,Y_t+C_t,\dots,Y_T)=\mathbb E(C_t)+\mathcal A(Y)$ for every $t$ and every $\mathcal F_{t-1}$-measurable $C_t\in L_p$; (MA1′) the same for constants $C_t=c_t$; (MA1″) the same for constants and $t=1$ only; (MA2) concavity on $\mathcal Y$; (MA3) $Y_t\le\tilde Y_t$ a.s. for all $t$ implies $\mathcal A(Y)\le\mathcal A(\tilde Y)$; (MA4) $\mathcal A(\lambda Y)=\lambda\mathcal A(Y)$ for $\lambda>0$; (MA5) $\mathcal A(Y)\le\sum_{t=1}^T\mathbb E(Y_t)$; continuity on $\mathcal Y$ for the product $L_p$ norm. For a functional $\mathcal A(Y;\boldsymbol{\mathcal F})$ given for every filtration, (MA0) **information monotonicity**: $\mathcal F_t\subseteq\mathcal F'_t$ for all $t$ implies $\mathcal A(Y;\boldsymbol{\mathcal F})\le\mathcal A(Y;\boldsymbol{\mathcal F}')$ for every $Y$ adapted to $\boldsymbol{\mathcal F}$.
--
--   Polyhedral functionals are the multi-period acceptability functionals that arise as optimal values of linear multi-stage stochastic programs with the income process as right-hand side; conditions (i)–(ii) make these values finite.
--
--   **Formalization Note** Time indices are natural numbers; only $0,\dots,T$ (for $v$, $c$, $V$, $k$) and $1,\dots,T$ (for $Y$, $Z$, $\bar u$) are used. The coefficient $w_{t,\tau}$ is stored by the period of the decision it multiplies: the field `W t s` is $w_{t,t-s}$, so the book's $w_{t,\tau}$ is `W t (t-τ)`, $w_{t,0}$ is `W t t`, $w_{\tau,\tau}$ is `W τ 0` and $w_{\tau,\tau-t}$ is `W τ t`; this keeps the type $\mathbb R^{k_s}$ of the coefficient equal to the type of $v_s$. Membership in $L_p(\mathcal F_t)$ is an $\mathcal F_t$-measurable representative that is `MemLp`; $v_0$ is $\mathcal F_0$-measurable, hence constant. The supremum (3.54) and the infimum (3.58) are taken in `EReal` (empty supremum $-\infty$; $r-(+\infty)=-\infty$). The conditional expectation is Mathlib's `P[Z τ | 𝓕 t]`. The properties (MA1)–(MA5) and continuity are stated for real-valued functionals on $\mathcal Y$; (MA0) compares `EReal` values. The book's (MA0) lists $\mathcal F_0,\dots,\mathcal F_{T-1}$ as arguments; here the comparison $\mathcal F_t\subseteq\mathcal F'_t$ is required for all $t\le T$, matching "for all $t$".
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 159, Definition 3.37 (Eq. (3.54)) and conditions (i)–(ii); p. 160, Eq. (3.56); p. 161, Eq. (3.58); pp. 133–134, Definitions 3.14–3.16

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- A filtration `𝓕 = (ℱ₀, ℱ₁, …, ℱ_T)` in `ℱ` with the trivial `ℱ₀ = {∅, Ω}` added
(Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 133):
`ℱ₀ = ⊥`, `ℱ_s ⊆ ℱ_t` for `s ≤ t ≤ T`, and `ℱ_t ⊆ ℱ` (the ambient σ-algebra `mΩ`). Indices
beyond `T` are unconstrained and never used. -/
def IsFiltrationUpTo {Ω : Type*} (mΩ : MeasurableSpace Ω) (T : ℕ)
    (𝓕 : ℕ → MeasurableSpace Ω) : Prop :=
  𝓕 0 = ⊥ ∧ (∀ s t : ℕ, s ≤ t → t ≤ T → 𝓕 s ≤ 𝓕 t) ∧ ∀ t : ℕ, t ≤ T → 𝓕 t ≤ mΩ

/-- Membership in `𝒴 := ×_{t=1}^T L_p(ℱ_t)` (p. 159): an income process `Y = (Y₁, …, Y_T)`
(given as `Y : ℕ → Ω → ℝ`, only the indices `1, …, T` matter) with `Y_t` `ℱ_t`-measurable and
in `L_p`. The same predicate with exponent `q` describes `𝒵 = ×_{t=1}^T L_q(ℱ_t)`. -/
def IsAdaptedLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal) (T : ℕ)
    (𝓕 : ℕ → MeasurableSpace Ω) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, Measurable[𝓕 t] (Y t) ∧ MemLp (Y t) p P

/-- The pairing `Σ_{t=1}^T 𝔼(Y_t Z_t)` of `Y ∈ 𝒴` and `Z ∈ 𝒵` (p. 160, Eq. (3.55)). -/
noncomputable def pairing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : ℕ)
    (Y Z : ℕ → Ω → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∫ ω, Y t ω * Z t ω ∂P

/-- The parameters of a multi-period polyhedral probability functional (p. 159,
Definition 3.37): dimensions `k_t ∈ ℕ`, vectors `c_t ∈ ℝ^{k_t}`, sets `V_t ⊆ ℝ^{k_t}`
(`t = 0, …, T`) and vectors `w_{t,τ} ∈ ℝ^{k_{t−τ}}` (`τ = 0, …, t`, `t = 1, …, T`).

**Indexing of `w`.** The field `W t s` is the book's `w_{t,t−s}`, i.e. the book's `w_{t,τ}` is
`W t (t − τ)`: it is indexed by the period `s = t − τ` of the decision `v_s` it multiplies, so
that its type `ℝ^{k_s}` is definitionally the type of `v_s`. Only `0 ≤ s ≤ t ≤ T` is used. -/
structure MultiPeriodData where
  /-- The dimensions `k_t`. -/
  k : ℕ → ℕ
  /-- The objective vectors `c_t ∈ ℝ^{k_t}`. -/
  c : (t : ℕ) → Fin (k t) → ℝ
  /-- The sets `V_t ⊆ ℝ^{k_t}`. -/
  V : (t : ℕ) → Set (Fin (k t) → ℝ)
  /-- `W t s = w_{t,t−s} ∈ ℝ^{k_s}`, the coefficient of `v_s` in the constraint of period `t`. -/
  W : (t s : ℕ) → Fin (k s) → ℝ

namespace MultiPeriodData

/-- The standing requirement of Definition 3.37 (p. 159): every `V_t`, `t = 0, …, T`, is a
non-empty polyhedral set. -/
def IsPolyhedral (D : MultiPeriodData) (T : ℕ) : Prop :=
  ∀ t : ℕ, t ≤ T → IsPolyhedralSet (D.V t) ∧ (D.V t).Nonempty

/-- Feasibility of `v = (v₀, …, v_T)` for the right-hand side `Y` in the program (3.54)
(p. 159): `v_t ∈ L_p(ℱ_t; ℝ^{k_t})` (an `ℱ_t`-measurable version in `L_p`), `v_t ∈ V_t` almost
surely, `t = 0, …, T`, and `Σ_{τ=0}^t ⟨w_{t,τ}, v_{t−τ}⟩ = Y_t` almost surely, `t = 1, …, T`;
the last sum is written `Σ_{s=0}^t ⟨W t s, v_s⟩` with `s = t − τ`. -/
def Feasible {Ω : Type*} [MeasurableSpace Ω] (D : MultiPeriodData) (P : Measure Ω)
    (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (Y : ℕ → Ω → ℝ)
    (v : (t : ℕ) → Ω → Fin (D.k t) → ℝ) : Prop :=
  (∀ t : ℕ, t ≤ T →
      Measurable[𝓕 t] (v t) ∧ MemLp (v t) p P ∧ ∀ᵐ ω ∂P, v t ω ∈ D.V t) ∧
    ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, ∑ s ∈ Finset.range (t + 1), D.W t s ⬝ᵥ v s ω = Y t ω

/-- The objective `Σ_{t=0}^T 𝔼(⟨c_t, v_t⟩)` of the program (3.54). -/
noncomputable def objective {Ω : Type*} [MeasurableSpace Ω] (D : MultiPeriodData)
    (P : Measure Ω) (T : ℕ) (v : (t : ℕ) → Ω → Fin (D.k t) → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), ∫ ω, D.c t ⬝ᵥ v t ω ∂P

/-- The multi-period polyhedral probability functional (3.54) (p. 159, Definition 3.37),
`ℛ(Y; 𝓕) = sup{Σ_{t=0}^T 𝔼(⟨c_t, v_t⟩) : v feasible for Y}`, a supremum in `EReal` (`−∞` when
nothing is feasible, `+∞` when unbounded). Its dependence on the filtration `𝓕` is through the
measurability of the decisions `v_t`. -/
noncomputable def functional {Ω : Type*} [MeasurableSpace Ω] (D : MultiPeriodData)
    (P : Measure Ω) (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (Y : ℕ → Ω → ℝ) :
    EReal :=
  sSup {x : EReal | ∃ v : (t : ℕ) → Ω → Fin (D.k t) → ℝ, D.Feasible P p T 𝓕 Y v ∧
    x = (D.objective P T v : EReal)}

/-- Condition (i) of p. 159: `V_t` is a polyhedral cone for `t = 0, …, T`, and
`⟨w_{t,0}, V_t⟩ = ℝ` for every `t = 1, …, T` (complete recourse); `w_{t,0}` is `W t t`. -/
def CompleteRecourse (D : MultiPeriodData) (T : ℕ) : Prop :=
  (∀ t : ℕ, t ≤ T → IsPolyhedralCone (D.V t)) ∧
    ∀ t ∈ Finset.Icc 1 T, (fun v => D.W t t ⬝ᵥ v) '' D.V t = Set.univ

/-- Condition (ii) of p. 159 (dual feasibility): there is `ū ∈ ℝ^T` with
`c₀ − Σ_{τ=1}^T w_{τ,τ} ū_τ ∈ V₀*` and `c_t − Σ_{τ=t}^T w_{τ,τ−t} ū_τ ∈ V_t*`, `t = 1, …, T`;
`w_{τ,τ}` is `W τ 0` and `w_{τ,τ−t}` is `W τ t`. `ū` is given as `ℕ → ℝ`, only `ū₁, …, ū_T`
matter. -/
def DualFeasible (D : MultiPeriodData) (T : ℕ) : Prop :=
  ∃ u : ℕ → ℝ, D.c 0 - ∑ τ ∈ Finset.Icc 1 T, u τ • D.W τ 0 ∈ polarCone (D.V 0) ∧
    ∀ t ∈ Finset.Icc 1 T, D.c t - ∑ τ ∈ Finset.Icc t T, u τ • D.W τ t ∈ polarCone (D.V t)

/-- The dual set `𝒵*` of (3.56) (p. 160): the `Z ∈ 𝒵 = ×_{t=1}^T L_q(ℱ_t)` with
`c₀ − Σ_{τ=1}^T w_{τ,τ} 𝔼(Z_τ) ∈ V₀*` and, almost surely,
`c_t − Σ_{τ=t}^T w_{τ,τ−t} 𝔼(Z_τ | ℱ_t) ∈ V_t*`, `t = 1, …, T`. The conditional expectation is
Mathlib's `P[Z τ | 𝓕 t]`, the true one whenever `ℱ_t ⊆ ℱ` and `Z_τ` is integrable. -/
def dualSet {Ω : Type*} [MeasurableSpace Ω] (D : MultiPeriodData) (P : Measure Ω)
    (q : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) : Set (ℕ → Ω → ℝ) :=
  {Z | IsAdaptedLp P q T 𝓕 Z ∧
    D.c 0 - ∑ τ ∈ Finset.Icc 1 T, (∫ ω, Z τ ω ∂P) • D.W τ 0 ∈ polarCone (D.V 0) ∧
    ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P,
      D.c t - ∑ τ ∈ Finset.Icc t T, (P[Z τ | 𝓕 t] ω) • D.W τ t ∈ polarCone (D.V t)}

/-- The conjugate (3.58) (p. 161): `ℛ⁺(Z) = inf{Σ_{t=1}^T 𝔼(Y_t Z_t) − ℛ(Y) : Y ∈ 𝒴}`, an
infimum in `EReal` (with `r − (+∞) = −∞` and `r − (−∞) = +∞` for real `r`). -/
noncomputable def conjugate {Ω : Type*} [MeasurableSpace Ω] (D : MultiPeriodData)
    (P : Measure Ω) (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (Z : ℕ → Ω → ℝ) :
    EReal :=
  sInf {x : EReal | ∃ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y ∧
    x = (pairing P T Y Z : EReal) - D.functional P p T 𝓕 Y}

end MultiPeriodData

/-! ### Properties of multi-period functionals (pp. 133–134, Definitions 3.14–3.16)

They are stated for a real valued functional `𝒜 : 𝒴 → ℝ`, for a fixed filtration `𝓕`, and are
required on `𝒴 = ×_{t=1}^T L_p(ℱ_t)` only. -/

/-- (MA0) Information monotonicity (p. 133), for a functional `𝒜(Y; 𝓕)` given for every
filtration: if `ℱ_t ⊆ ℱ'_t` for all `t`, then `𝒜(Y; 𝓕) ≤ 𝒜(Y; 𝓕')` for every `Y` adapted to `𝓕`.
Values are compared in `EReal`. -/
def InformationMonotone {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal)
    (T : ℕ) (A : (ℕ → MeasurableSpace Ω) → (ℕ → Ω → ℝ) → EReal) : Prop :=
  ∀ 𝓕 𝓕' : ℕ → MeasurableSpace Ω, IsFiltrationUpTo mΩ T 𝓕 → IsFiltrationUpTo mΩ T 𝓕' →
    (∀ t : ℕ, t ≤ T → 𝓕 t ≤ 𝓕' t) →
    ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → A 𝓕 Y ≤ A 𝓕' Y

/-- (MA1) Predictable translation-equivariance (p. 133, Eq. (3.15)):
`𝒜(Y₁, …, Y_t + C_t, …, Y_T; 𝓕) = 𝔼(C_t) + 𝒜(Y₁, …, Y_T; 𝓕)` for every `t = 1, …, T` and every
`ℱ_{t−1}`-measurable `C_t` (in `L_p`, so that the shifted process stays in `𝒴`). -/
def PredictableTranslationEquivariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → ∀ t ∈ Finset.Icc 1 T, ∀ C : Ω → ℝ,
    Measurable[𝓕 (t - 1)] C → MemLp C p P →
    A (Function.update Y t (Y t + C)) = (∫ ω, C ω ∂P) + A Y

/-- (MA1′) Weak translation-equivariance (p. 134, Eq. (3.16)):
`𝒜(Y₁, …, Y_t + c_t, …, Y_T; 𝓕) = c_t + 𝒜(Y₁, …, Y_T; 𝓕)` for every `t = 1, …, T` and every
constant `c_t`. -/
def WeakTranslationEquivariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → ∀ t ∈ Finset.Icc 1 T, ∀ c : ℝ,
    A (Function.update Y t (fun ω => Y t ω + c)) = c + A Y

/-- (MA1″) First period translation-equivariance (p. 134, Eq. (3.17)):
`𝒜(Y₁ + c₁, Y₂, …, Y_T; 𝓕) = c₁ + 𝒜(Y₁, …, Y_T; 𝓕)` for every constant `c₁`. -/
def FirstPeriodTranslationEquivariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → ∀ c : ℝ,
    A (Function.update Y 1 (fun ω => Y 1 ω + c)) = c + A Y

/-- (MA2) Concavity (p. 133): `Y ↦ 𝒜(Y; 𝓕)` is concave on `𝒴`. -/
def ConcaveOnProcesses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal)
    (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y Y' : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → IsAdaptedLp P p T 𝓕 Y' →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      lam * A Y + (1 - lam) * A Y' ≤ A (lam • Y + (1 - lam) • Y')

/-- (MA3) Monotonicity (p. 133): `Y_t ≤ Ỹ_t` a.s. for all `t` implies `𝒜(Y; 𝓕) ≤ 𝒜(Ỹ; 𝓕)`. -/
def MonotoneOnProcesses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal)
    (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y Y' : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → IsAdaptedLp P p T 𝓕 Y' →
    (∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Y t ω ≤ Y' t ω) → A Y ≤ A Y'

/-- (MA4) Positive homogeneity (p. 134, Definition 3.15): `𝒜(λY; 𝓕) = λ𝒜(Y; 𝓕)` for `λ > 0`. -/
def PositivelyHomogeneousOnProcesses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ENNReal) (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → ∀ lam : ℝ, 0 < lam → A (lam • Y) = lam * A Y

/-- (MA5) Strictness (p. 134, Definition 3.16): `𝒜(Y; 𝓕) ≤ Σ_{t=1}^T 𝔼(Y_t)`. -/
def StrictOnProcesses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal)
    (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → A Y ≤ ∑ t ∈ Finset.Icc 1 T, ∫ ω, Y t ω ∂P

/-- Continuity on `𝒴 = ×_{t=1}^T L_p(ℱ_t)` (product norm topology): for every `Y ∈ 𝒴` and
`ε > 0` there is `δ > 0` with `|𝒜(Y') − 𝒜(Y)| < ε` whenever `Y' ∈ 𝒴` and
`‖Y'_t − Y_t‖_p < δ` for `t = 1, …, T`. -/
def ContinuousOnProcesses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal)
    (T : ℕ) (𝓕 : ℕ → MeasurableSpace Ω) (A : (ℕ → Ω → ℝ) → ℝ) : Prop :=
  ∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ Y' : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y' →
      (∀ t ∈ Finset.Icc 1 T, eLpNorm (Y' t - Y t) p P < ENNReal.ofReal δ) →
      |A Y' - A Y| < ε

end RiskFunctionals.Polyhedral


