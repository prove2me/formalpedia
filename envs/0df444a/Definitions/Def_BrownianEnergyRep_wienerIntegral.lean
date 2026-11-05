-- Prove2me | Definitions.Def_BrownianEnergyRep_wienerIntegral
-- name    : BrownianEnergyRep_wienerIntegral
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:45.025218+00:00
-- url     : https://prove2.me/theorems/cf7fe710-7e1b-4da0-8563-15da09daf9c8
-- title:
--   The Wiener integral $I(a)=\int_0^T\langle a(s),dw_s\rangle$
-- statement:
--   For $a\in L^2([0,T];\mathfrak g)$, the Wiener integral $I(a)=\int_0^T\langle a(s),dw_s\rangle$ is the $L^2(\nu)$ limit of the sums $\sum_i\langle c_i,w_{t_{i+1}}-w_{t_i}\rangle$ along step functions $\sum_ic_i1_{(t_i,t_{i+1}]}$ that converge to $a$ in $L^2$. It is the phase in the energy representation and the exponent in the densities of Theorem 2.14.
--
--   **Formalization Note** The predicate `IsWienerIntegral` is the limit description, and `wienerIntegral` is a representative chosen by `Classical.epsilon`. The item `wiener_integral_isometry` says that it satisfies the predicate and is unique $\nu$-a.e. for $a\in L^2$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Definition 5.7, p.18

import Mathlib
import Definitions.Def_BrownianEnergyRep_WienerPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- Data of a `𝔤`-valued step function: times and coefficients. -/
structure StepData (E : Type*) where
  k : ℕ
  time : Fin (k + 1) → ℝ
  coeff : Fin k → E

/-- The times are nondecreasing and lie in `[0,T]`. -/
def StepData.Valid {E : Type*} (σ : StepData E) (T : ℝ) : Prop :=
  Monotone σ.time ∧ ∀ i, σ.time i ∈ Icc 0 T

/-- The step function `Σᵢ cᵢ 1_{(tᵢ, tᵢ₊₁]}`. -/
noncomputable def StepData.fn {E : Type*} [NormedAddCommGroup E] (σ : StepData E) : ℝ → E :=
  fun t => ∑ i : Fin σ.k, (Ioc (σ.time i.castSucc) (σ.time i.succ)).indicator (fun _ => σ.coeff i) t

/-- Its Wiener integral `Σᵢ ⟨cᵢ, w_{tᵢ₊₁} − w_{tᵢ}⟩`. -/
noncomputable def StepData.sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℝ} [Fact (0 < T)] (σ : StepData E) (w : ↥(WienerPath E T)) : ℝ :=
  ∑ i : Fin σ.k, ⟪σ.coeff i, wAt w (σ.time i.succ) - wAt w (σ.time i.castSucc)⟫

/-- `X` is the Wiener integral `∫₀ᵀ ⟨a(s), dw_s⟩` of `a` (arXiv:1511.07378v1, Definition 5.7, p.18): the `L²(ν)`
limit of the finite sums along step functions converging to `a` in `L²([0,T]; 𝔤)`. -/
def IsWienerIntegral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℝ} [Fact (0 < T)] (ν : Measure ↥(WienerPath E T)) (a : ℝ → E)
    (X : ↥(WienerPath E T) → ℝ) : Prop :=
  MemLp X 2 ν ∧ ∃ σ : ℕ → StepData E, (∀ j, (σ j).Valid T) ∧
    Tendsto (fun j => eLpNorm (fun t => (σ j).fn t - a t) 2 (volume.restrict (Ioc 0 T)))
      atTop (𝓝 0) ∧
    Tendsto (fun j => eLpNorm (fun w => (σ j).sum w - X w) 2 ν) atTop (𝓝 0)

/-- The Wiener integral `I(a) = ∫₀ᵀ ⟨a(s), dw_s⟩` (arXiv:1511.07378v1, Definition 5.7, p.18).

**Formalization Note** A representative chosen by `Classical.epsilon`. For `a ∈ L²([0,T]; 𝔤)` it
is a Wiener integral and is unique `ν`-a.e. (`wiener_integral_isometry`). -/
noncomputable def wienerIntegral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℝ} [Fact (0 < T)] (ν : Measure ↥(WienerPath E T)) (a : ℝ → E) :
    ↥(WienerPath E T) → ℝ :=
  Classical.epsilon (IsWienerIntegral ν a)

end BrownianEnergyRep


