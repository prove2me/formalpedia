-- Prove2me | Definitions.Def_ClosedLoopMFG_SignGame_Example
-- name    : ClosedLoopMFG_SignGame_Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:23:22.157974+00:00
-- url     : https://prove2.me/theorems/a3bba1b3-d577-428a-b599-696458f36759
-- title:
--   The mean-sign game of Section 7.3: b = a, f = 0, g = x·m̄, A = [−1,1], λ = δ₀, the sign feedback (7.13) and H^±_0 (7.11)
-- statement:
--   The $d=1$ mean field game of Section 7.3 has coefficients
--
--   $$
--   b(t,x,m,a)=a,\qquad f\equiv0,\qquad g(x,m)=x\,\overline m,\qquad A=[-1,1],\qquad \lambda=\delta_0,
--   $$
--
--   where $\overline m=\int_{\mathbb R}y\,m(dy)$ is the mean of $m$. With $\operatorname{sgn}(x)=1$ for $x>0$, $-1$ for $x<0$ and $\operatorname{sgn}(0)=0$, the feedback $\alpha^*_{t_0}(t,x)=\operatorname{sgn}(x)\,\mathbf 1_{(t_0,T]}(t)$ defines, for $t_0=0$, the Markovian control of every player in the $n$-player game (7.13):
--
--   $$
--   \alpha^{n,i}_0(t,x_1,\dots,x_n)=\alpha^*_0\Big(t,\frac1n\sum_{k=1}^n x_k\Big)=\operatorname{sgn}\Big(\frac1n\sum_{k=1}^n x_k\Big)\mathbf 1_{(0,T]}(t).
--   $$
--
--   The file also defines
--
--   1. the payoff $J^n_i=\mathbb E[X^i_T\,\overline{\mu}^n_T]$ of player $i$ on a solution, and Markovian $\varepsilon$-Nash equilibria of this game;
--   2. the **mean process** $\overline\mu^n_t=\frac1n\sum_{k=1}^n X^k_t$, a $C([0,T];\mathbb R)$-valued random variable, and its law;
--   3. the path $t\mapsto W^1_t$ of player 1's Brownian motion on $[0,T]$, the pair $(\overline\mu^n,W^1)$ and its law on $C([0,T];\mathbb R)^2$;
--   4. the paths $H^\pm_0(t)=\pm(t-0)^+=\pm t$ of (7.11) and the probability measure $\tfrac12\delta_{H^+_0}+\tfrac12\delta_{H^-_0}$ on $C([0,T];\mathbb R)$.
--
--   Assumption A fails here: $g$ is unbounded.
--
--   **Formalization Note** $\mathbb R^1$ is `EuclideanSpace ℝ (Fin 1)` and its real coordinate is `y 0`; the drift $a$ is the vector with coordinate $a$. $\operatorname{sgn}$ is Mathlib's `Real.sign`, which is $0$ at $0$. The mean $\overline m$ is a Bochner integral (junk $0$ without a first moment); it is only ever applied to empirical measures, which have one. The law of the mean process is a probability measure because the mean path is a continuous function of the state paths; the law of $(\overline\mu^n,W^1)$ is the push-forward measure, whose measurability is asserted where it is used.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, pp. 47–49, Section 7.3, (7.11), (7.13)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ClosedLoopMFG_SignGame_Model
import Definitions.Def_ClosedLoopMFG_SignGame_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.SignGame

/-- The control set `A = [−1, 1] ⊂ ℝ` (p. 47). -/
def signA : Set ℝ := Set.Icc (-1) 1

/-- The drift `b(t, x, m, a) = a`, with `a ∈ ℝ` read as the vector of `ℝ^1` with coordinate `a`
(p. 47). -/
noncomputable def signB : ℝ → EthierKurtz.SDEState 1 → PR 1 → ℝ → EthierKurtz.SDEState 1 :=
  fun _ _ _ a => EuclideanSpace.single (0 : Fin 1) a

/-- The running reward `f ≡ 0` (p. 47). -/
def signF : ℝ → EthierKurtz.SDEState 1 → PR 1 → ℝ → ℝ := fun _ _ _ _ => 0

/-- The mean `m̄ = ∫_ℝ y m(dy)` of `m ∈ P(ℝ)`, the real coordinate of `ℝ^1` being `y 0`. -/
noncomputable def meanOf (m : PR 1) : ℝ := ∫ y, y 0 ∂m.meas

/-- The terminal reward `g(x, m) = x m̄` (p. 47). -/
noncomputable def signG : EthierKurtz.SDEState 1 → PR 1 → ℝ := fun x m => x 0 * meanOf m

/-- The initial law `λ = δ_0` (p. 47). -/
noncomputable def signLam : PR 1 :=
  (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure (EthierKurtz.SDEState 1))

/-- The feedback `α*_{t₀}(t, x) = sgn(x) 1_{(t₀, T]}(t)` (p. 47), with `sgn(0) = 0`
(`Real.sign`). -/
noncomputable def alphaStar (T : ℝ≥0) (t₀ t x : ℝ) : ℝ :=
  Real.sign x * Set.indicator (Set.Ioc t₀ (T : ℝ)) (fun _ => (1 : ℝ)) t

/-- The control (7.13) with `t₀ = 0`: `α^{n,i}_0(t, x) = α*_0(t, (1/n) Σ_{k=1}^n x_k)`, the same
for every player `i` (p. 49). -/
noncomputable def signControl (n : ℕ) (T : ℝ≥0) : ℝ → (Fin n → EthierKurtz.SDEState 1) → ℝ :=
  fun t x => alphaStar T 0 t ((n : ℝ)⁻¹ * ∑ k, x k 0)

/-- The profile `α^n = (α^{n,1}_0, …, α^{n,n}_0)`. -/
noncomputable def signProfile (n : ℕ) (T : ℝ≥0) :
    Fin n → ℝ → (Fin n → EthierKurtz.SDEState 1) → ℝ :=
  fun _ => signControl n T

/-- The drift functionals of the n-player sign game under a Markovian profile `α`. -/
noncomputable def signDrift {n : ℕ} [NeZero n] (T : ℝ≥0)
    (α : Fin n → ℝ → (Fin n → EthierKurtz.SDEState 1) → ℝ) :
    Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path 1 T) → EthierKurtz.SDEState 1 :=
  driftOf signB (markovProfile (T := T) α)

/-- Player `i`'s payoff `J^n_i = E[X^i_T μ̄^n_T]` on a solution `S` of the sign game under the
Markovian profile `α` (`f ≡ 0`). -/
noncomputable def signPayoff {n : ℕ} [NeZero n] {T : ℝ≥0}
    {α : Fin n → ℝ → (Fin n → EthierKurtz.SDEState 1) → ℝ}
    (S : NSol n 1 T signLam (signDrift T α)) (i : Fin n) : ℝ :=
  payoff S i (runOf signF (markovProfile (T := T) α)) (termOf signG)

/-- A Markovian `ε`-Nash equilibrium of the n-player sign game. -/
def IsSignMarkovianNash {n : ℕ} [NeZero n] (T : ℝ≥0) (ε : ℝ)
    (α : Fin n → ℝ → (Fin n → EthierKurtz.SDEState 1) → ℝ) : Prop :=
  IsMarkovianNash T signLam signA signB signF signG ε α

/-- The real coordinate `ℝ^1 → ℝ`, `y ↦ y 0`, as a continuous map. -/
noncomputable def coord0 : C(EthierKurtz.SDEState 1, ℝ) :=
  ⟨fun y => y 0, (EuclideanSpace.proj (0 : Fin 1)).continuous⟩

/-- The mean path map `x ↦ (t ↦ (1/n) Σ_k x_k(t))` from `(𝒞^1)^n` to `C([0, T]; ℝ)`. -/
noncomputable def meanPathMap (n : ℕ) (T : ℝ≥0) : (Fin n → ClosedLoopMFG.Limit.Path 1 T) → RPath T :=
  fun x => ((n : ℝ)⁻¹ • ∑ k, coord0.comp (x k : C(Set.Icc (0 : ℝ) T, EthierKurtz.SDEState 1))
    : C(Set.Icc (0 : ℝ) T, ℝ))

theorem continuous_meanPathMap (n : ℕ) (T : ℝ≥0) : Continuous (meanPathMap n T) := by
  have h : Continuous (fun x : Fin n → C(Set.Icc (0 : ℝ) T, EthierKurtz.SDEState 1) =>
      (n : ℝ)⁻¹ • ∑ k, coord0.comp (x k)) :=
    (continuous_const_smul ((n : ℝ)⁻¹)).comp (continuous_finsetSum Finset.univ fun k _ =>
      (ContinuousMap.continuous_postcomp coord0).comp (continuous_apply k))
  exact h

/-- The mean process `μ̄^n_t = (1/n) Σ_k X^k_t` of a solution, a `C([0, T]; ℝ)`-valued random
variable. -/
noncomputable def meanPath {n : ℕ} [NeZero n] {T : ℝ≥0}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path 1 T) → EthierKurtz.SDEState 1}
    (S : NSol n 1 T signLam B) : S.Ω → RPath T :=
  fun ω => meanPathMap n T (S.X ω)

/-- The law of the mean process, an element of `P(C([0, T]; ℝ))`. -/
noncomputable def meanLaw {n : ℕ} [NeZero n] {T : ℝ≥0}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path 1 T) → EthierKurtz.SDEState 1}
    (S : NSol n 1 T signLam B) : ProbabilityMeasure (RPath T) :=
  ProbabilityMeasure.map ⟨S.P, inferInstance⟩
    ((continuous_meanPathMap n T).measurable.comp S.hX_meas).aemeasurable

/-- The path `t ↦ W^i_t` on `[0, T]` of player `i`'s Brownian motion (real coordinate), a
`C([0, T]; ℝ)`-valued random variable. -/
noncomputable def bmPath {n : ℕ} [NeZero n] {T : ℝ≥0}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path 1 T) → EthierKurtz.SDEState 1}
    (S : NSol n 1 T signLam B) (i : Fin n) : S.Ω → RPath T :=
  fun ω => (⟨fun s => S.W i (s : ℝ).toNNReal ω 0,
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
      (((S.hW i).1.2.1 ω).comp (continuous_real_toNNReal.comp continuous_subtype_val))⟩ :
      C(Set.Icc (0 : ℝ) T, ℝ))

/-- The pair `(μ̄^n, W^1)` of a solution: the mean process and player 1's Brownian path. -/
noncomputable def ywMap {n : ℕ} [NeZero n] {T : ℝ≥0}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path 1 T) → EthierKurtz.SDEState 1}
    (S : NSol n 1 T signLam B) : S.Ω → RPath T × RPath T :=
  fun ω => (meanPath S ω, bmPath S 0 ω)

/-- The law of `(μ̄^n, W^1)` on `C([0, T]; ℝ) × C([0, T]; ℝ)` (a push-forward measure). -/
noncomputable def ywLaw {n : ℕ} [NeZero n] {T : ℝ≥0}
    {B : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.Path 1 T) → EthierKurtz.SDEState 1}
    (S : NSol n 1 T signLam B) : Measure (RPath T × RPath T) :=
  S.P.map (ywMap S)

/-- `H^±_0(t) = ±(t − 0)^+ = ±t` on `[0, T]` ((7.11), p. 48). -/
def Hplus (T : ℝ≥0) : RPath T := ⟨fun t => (t : ℝ), continuous_subtype_val⟩

/-- `H^−_0(t) = −t`. -/
def Hminus (T : ℝ≥0) : RPath T := ⟨fun t => -(t : ℝ), continuous_subtype_val.neg⟩

/-- The mixture `½ δ_{H^+_0} + ½ δ_{H^−_0}` on `C([0, T]; ℝ)`. -/
noncomputable def halfMix (T : ℝ≥0) : ProbabilityMeasure (RPath T) :=
  ⟨(2⁻¹ : ℝ≥0∞) • Measure.dirac (Hplus T) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (Hminus T),
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩⟩

end ClosedLoopMFG.SignGame


