-- Prove2me | Definitions.Def_MFGLimit_LDP_Model
-- name    : MFGLimit_LDP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:16.753987+00:00
-- url     : https://prove2.me/theorems/ddb85025-a7da-4760-be3b-6f9378c1bc4b
-- title:
--   §2.1–§2.3, pp. 4–7 — ℝ^d, C^k = C([0,T];ℝ^k), C^k_0, P_p, W_p, empirical measures, the noises and initial states, b, f, g, σ, σ₀, H, α̂, b̂, f̂
-- statement:
--   The standing setting of §2 of Delarue, Lacker and Ramanan.
--
--   **Spaces.** $\mathbb R^k$ carries the Euclidean norm $|\cdot|$. For a horizon $T>0$, $\mathcal C^k=C([0,T];\mathbb R^k)$ is the space of continuous paths with the supremum norm $\|x\|_\infty=\sup_{t\in[0,T]}|x_t|$ and its Borel $\sigma$-field, and $\mathcal C^k_0=\{\phi\in\mathcal C^k:\phi_0=0\}$. For a normed space $E$ and $p\ge 1$, $\mathcal P^p(E)$ is the set of probability measures $\mu$ with $\langle\mu,\|\cdot\|^p\rangle<\infty$, and the $p$-Wasserstein distance is
--
--   $$\mathcal W_p(\mu,\nu)=\inf_\pi\Big(\int_{E\times E}\|x-y\|^p\,\pi(dx,dy)\Big)^{1/p},$$
--
--   the infimum over couplings $\pi$ of $\mu$ and $\nu$ (2.1). The empirical measure of $\boldsymbol x=(x_1,\dots,x_n)$ is $m^n_{\boldsymbol x}=\frac1n\sum_{i=1}^n\delta_{x_i}$.
--
--   **Noises and initial states (§2.3).** A filtered probability space $(\Omega,\mathcal F,\mathbb F,\mathbb P)$ carries mutually independent $\mathbb F$-Wiener processes: a $d_0$-dimensional common noise $W$ and $d$-dimensional idiosyncratic noises $B^1,B^2,\dots$ (each a standard Brownian motion, adapted, with increments after time $s$ independent of $\mathcal F_s$), and i.i.d. $\mathcal F_0$-measurable initial states $X^1_0,X^2_0,\dots$ with law $\mu_0$.
--
--   **Model inputs.** An exponent $p^*$, an action space $A$ (Polish), coefficients $b:\mathbb R^d\times\mathcal P^{p^*}(\mathbb R^d)\times A\to\mathbb R^d$, $f:\mathbb R^d\times\mathcal P^{p^*}(\mathbb R^d)\times A\to\mathbb R$, $g:\mathbb R^d\times\mathcal P^{p^*}(\mathbb R^d)\to\mathbb R$, matrices $\sigma\in\mathbb R^{d\times d}$, $\sigma_0\in\mathbb R^{d\times d_0}$, and a selection $\hat\alpha(x,m,y)$ of minimizers of the Hamiltonian
--
--   $$H(x,m,y)=\inf_{a\in A}\big[b(x,m,a)\cdot y+f(x,m,a)\big],$$
--
--   with $\hat b(x,m,y)=b(x,m,\hat\alpha(x,m,y))$ and $\hat f(x,m,y)=f(x,m,\hat\alpha(x,m,y))$ (2.4).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The path space is named `CPath k T` (Mathlib already has a `Path`); time is `ℝ≥0` and paths are continuous maps on `[0, T] ⊂ ℝ≥0`. $\mathcal W_p$ is the published `WassersteinDRO.Duality.wassersteinDistance`, kept in $[0,\infty]$; "$\mu\in\mathcal P^p$" is the predicate `IsPp p μ`, and every condition below quantifies over measures satisfying it. The model data are bundled in a structure `Model`; the minimizing property of $\hat\alpha$, measurability and the other assumptions are stated in Assumption A. Players are indexed from $0$ ($B^{i}$ is `B i`). Brownian motions are the published `Peng1990.SMP.IsStdBrownian`.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 4–7, §2.1–§2.3, (2.1), (2.4)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_MFGLimit_Conc_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

/-- The basis vector `e_i` of `ℝ^k`. -/
noncomputable abbrev ebasis {k : ℕ} (i : Fin k) : MFGLimit.Conc.E k := EuclideanSpace.single i (1 : ℝ)

/-- A vector `(v_1, …, v_k)` of `Fin k → ℝ` (the value of a Brownian motion) read in `ℝ^k`. -/
abbrev toE {k : ℕ} (v : Fin k → ℝ) : MFGLimit.Conc.E k := WithLp.toLp 2 v

/-- The action `M v ∈ ℝ^d` of a `d × k` matrix on `v ∈ ℝ^k`. -/
noncomputable def matVec {d k : ℕ} (M : Matrix (Fin d) (Fin k) ℝ) (v : MFGLimit.Conc.E k) : MFGLimit.Conc.E d :=
  Matrix.toEuclideanLin M v

/-- `Tr[a M] = Σ_{i,j} a_{ij} M_{ji}` for a `d × d` matrix `a` and a `d × d` array `M`. -/
def trMul {d : ℕ} (a : Matrix (Fin d) (Fin d) ℝ) (M : Fin d → Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * M j i

/-- The Hessian array `(∂_{x_i} ∂_{x_j} h(x))_{i,j}` of `h : ℝ^d → ℝ`. -/
noncomputable def hessE {d : ℕ} (h : MFGLimit.Conc.E d → ℝ) (x : MFGLimit.Conc.E d) : Fin d → Fin d → ℝ :=
  fun i j => iteratedFDeriv ℝ 2 h x ![ebasis i, ebasis j]

/-- The path space `C^k = C([0, T]; ℝ^k)`; its Mathlib norm is the sup norm `‖x‖_∞`. -/
abbrev CPath (k : ℕ) (T : ℝ≥0) := C(Set.Icc (0 : ℝ≥0) T, MFGLimit.Conc.E k)

instance instMeasurableSpaceCPath (k : ℕ) (T : ℝ≥0) : MeasurableSpace (CPath k T) := borel _

instance instBorelSpaceCPath (k : ℕ) (T : ℝ≥0) : BorelSpace (CPath k T) := ⟨rfl⟩

/-- The initial time `0 ∈ [0, T]`. -/
def t0 (T : ℝ≥0) : Set.Icc (0 : ℝ≥0) T := ⟨0, le_refl _, (zero_le (a := T))⟩

/-- The terminal time `T ∈ [0, T]`. -/
def tT (T : ℝ≥0) : Set.Icc (0 : ℝ≥0) T := ⟨T, (zero_le (a := T)), le_refl _⟩

/-- A real time `s` read in `[0, T]` (projection onto `[0, T]`; exact for `s ∈ [0, T]`). -/
noncomputable def toIcc (T : ℝ≥0) (s : ℝ) : Set.Icc (0 : ℝ≥0) T :=
  Set.projIcc (0 : ℝ≥0) T (zero_le (a := T)) s.toNNReal

/-- The value `x_s` of a path at a real time `s ∈ [0, T]`. -/
noncomputable def CPath.atR {k : ℕ} {T : ℝ≥0} (x : CPath k T) (s : ℝ) : MFGLimit.Conc.E k := x (toIcc T s)

/-- `C^k_0 = {φ ∈ C^k : φ_0 = 0}`, as an additive subgroup (normed by the sup norm). -/
def C0 (k : ℕ) (T : ℝ≥0) : AddSubgroup (CPath k T) where
  carrier := {φ | φ (t0 T) = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, ContinuousMap.add_apply] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, ContinuousMap.neg_apply] at *
    rw [ha, neg_zero]

/-- The type `C^k_0` of paths started at `0`. -/
abbrev C0T (k : ℕ) (T : ℝ≥0) := ↥(C0 k T)

/-- The `p`-Wasserstein distance (2.1), in `ℝ≥0∞` (finite on `P_p`). -/
noncomputable def Wp {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α] (p : ℝ)
    (μ ν : Measure α) : ℝ≥0∞ :=
  WassersteinDRO.Duality.wassersteinDistance p μ ν

/-- The empirical measure `m^n_x = (1/n) Σ_{i=1}^n δ_{x_i}` of `x = (x_1, …, x_n)`. -/
noncomputable def empMeas {α : Type*} [MeasurableSpace α] {n : ℕ} (x : Fin n → α) : Measure α :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `Z` is an `𝔽`-Wiener process: adapted to `𝔽`, and for every `s` the increments
`(Z_u − Z_s)_{u ≥ s}` are independent of `𝓕_s`. -/
def IsFWiener {k : ℕ} (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (Z : ℝ≥0 → Ω → Fin k → ℝ) :
    Prop :=
  (∀ t, Measurable[𝔽 t] (Z t)) ∧
    ∀ s, Indep (MeasurableSpace.comap (fun ω (u : {u : ℝ≥0 // s ≤ u}) => Z u ω - Z s ω)
      inferInstance) (𝔽 s) P

/-- The standing probabilistic setting of §2.3: a filtered probability space carrying a
`d₀`-dimensional common noise `W` and `d`-dimensional idiosyncratic noises `B 0, B 1, …`, each a
standard Brownian motion and an `𝔽`-Wiener process, mutually independent, and i.i.d.
`𝓕_0`-measurable initial states `X₀ 0, X₀ 1, …` with law `μ₀`. (Players are indexed from `0`.) -/
structure IsSetup {d d₀ : ℕ} (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (X₀ : ℕ → Ω → MFGLimit.Conc.E d)
    (μ₀ : Measure (MFGLimit.Conc.E d)) : Prop where
  prob : IsProbabilityMeasure P
  W_brownian : Peng1990.SMP.IsStdBrownian P W
  W_wiener : IsFWiener 𝔽 P W
  B_brownian : ∀ i, Peng1990.SMP.IsStdBrownian P (B i)
  B_wiener : ∀ i, IsFWiener 𝔽 P (B i)
  noises_indep : iIndep (fun o : Option ℕ => Option.elim o
      (MeasurableSpace.comap (fun ω (t : ℝ≥0) => W t ω) inferInstance)
      (fun i => MeasurableSpace.comap (fun ω (t : ℝ≥0) => B i t ω) inferInstance)) P
  X₀_meas : ∀ i, Measurable[𝔽 0] (X₀ i)
  X₀_indep : iIndepFun X₀ P
  X₀_ident : ∀ i, IdentDistrib (X₀ i) (X₀ 0) P P
  initial_noises_indep : Indep
    (MeasurableSpace.comap (fun ω (i : ℕ) => X₀ i ω) inferInstance)
    (⨆ o : Option ℕ, Option.elim o
      (MeasurableSpace.comap (fun ω (t : ℝ≥0) => W t ω) inferInstance)
      (fun i => MeasurableSpace.comap (fun ω (t : ℝ≥0) => B i t ω) inferInstance)) P
  law : μ₀ = P.map (X₀ 0)

/-- The model inputs of §2.3: the exponent `p*`, the coefficients `b`, `f`, `g` (only their values
on `ℝ^d × P_{p*}(ℝ^d)` matter), the volatilities `σ ∈ ℝ^{d×d}`, `σ₀ ∈ ℝ^{d×d₀}`, and a selection
`α̂(x, m, y)` of minimizers of the Hamiltonian (A(1) states that it minimizes). -/
structure Model (d d₀ : ℕ) (A : Type*) where
  pStar : ℝ
  b : MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → A → MFGLimit.Conc.E d
  f : MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → A → ℝ
  g : MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → ℝ
  σ : Matrix (Fin d) (Fin d) ℝ
  σ₀ : Matrix (Fin d) (Fin d₀) ℝ
  αhat : MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d → A

namespace Model

variable {d d₀ : ℕ} {A : Type*} (M : Model d d₀ A)

/-- The Hamiltonian `H(x, m, y) = inf_{a ∈ A} [b(x, m, a)·y + f(x, m, a)]`. -/
noncomputable def H (x : MFGLimit.Conc.E d) (m : Measure (MFGLimit.Conc.E d)) (y : MFGLimit.Conc.E d) : ℝ :=
  ⨅ a, (inner ℝ (M.b x m a) y + M.f x m a)

/-- `b̂(x, m, y) = b(x, m, α̂(x, m, y))` (2.4). -/
def bhat (x : MFGLimit.Conc.E d) (m : Measure (MFGLimit.Conc.E d)) (y : MFGLimit.Conc.E d) : MFGLimit.Conc.E d := M.b x m (M.αhat x m y)

/-- `f̂(x, m, y) = f(x, m, α̂(x, m, y))` (2.4). -/
def fhat (x : MFGLimit.Conc.E d) (m : Measure (MFGLimit.Conc.E d)) (y : MFGLimit.Conc.E d) : ℝ := M.f x m (M.αhat x m y)

end Model

end MFGLimit.LDP


