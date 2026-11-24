-- Prove2me | Definitions.Def_InterpOptStop_SAA_Supplement_CubeBellman
-- name    : InterpOptStop_SAA_Supplement_CubeBellman
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:45:05.390499+00:00
-- url     : https://prove2.me/theorems/5cf1733a-0c53-45f0-95bb-4372b5e66fa8
-- title:
--   Continuous cube, Euclidean regularity and Bellman continuation values
-- statement:
--   The physical state space is the full continuous cube $[0,1]^n$. For points in it use Euclidean distance $d_2(x,y)=\sqrt{\sum_i(x_i-y_i)^2}$, and define the Lipschitz condition by $|f(x)-f(y)|\le Ld_2(x,y)$. Given probability transition kernels $K_t$, define the finite backward recursion
--   $$C_T^*=0,\quad C_t^*(x)=\int J_{t+1}^*(y)K_t(x,dy),\quad J_t^*(x)=\max\{g(t,x),\beta C_t^*(x)\}.$$
--   The Bellman policy stops when $g(t,x)>\beta C_t^*(x)$, with ties going to go. The separate density predicate states the source almost-sure bound $K_t(x(t),A)\le\lambda\operatorname{vol}(A)$ for $t<T$. Its volume is physical $n$-dimensional Lebesgue measure; no clock density is imposed. The unrestricted value is obtained by forgetting the cube subtype, extending rewards by zero and policies by go off the cube, and using the shared clock-lift value. Lipschitz rewards on the compact cube are bounded and measurable; finite backward recursion with probability kernels gives genuine integrals. The continuation Lipschitz condition is an explicit theorem hypothesis, not a stored approximation conclusion.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, EC.1.5, Bellman recursion and Assumptions EC.1–EC.4, p. ec24; Euclidean norm on p. ec27

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_TimedStopping
import Definitions.Def_InterpOptStop_SAA_Supplement_MarkovLaw

open MeasureTheory ProbabilityTheory

namespace InterpOptStop.SAA.Supplement

abbrev Cube (n : ℕ) := {x : Fin n → ℝ // ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- Explicit Euclidean distance, rather than the sup norm of the ambient function type. -/
noncomputable def euclidean {n : ℕ} (x y : Cube n) : ℝ :=
  Real.sqrt (∑ i, (x.val i - y.val i) ^ 2)

def EuclideanLipschitz {n : ℕ} (L : ℝ) (f : Cube n → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ L * euclidean x y

/-- Forget the subtype, retaining the entire continuous physical cube. -/
noncomputable def physicalLaw {n T : ℕ} (μ : Measure (Fin T → Cube n)) :
    Measure (Fin T → Fin n → ℝ) := μ.map (fun p k => (p k).val)

/-- Zero extension outside the physical state space changes no admissible trajectory. -/
noncomputable def extendReward {n T : ℕ} (g : Fin T → Cube n → ℝ)
    (k : Fin T) (x : Fin n → ℝ) : ℝ :=
  if h : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1 then g k ⟨x, h⟩ else 0

noncomputable def extendPolicy {n T : ℕ} (π : Fin T → Cube n → Act) : TimedPolicy n T :=
  fun k x => if h : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1 then π k ⟨x, h⟩ else Act.go

noncomputable def cubeValue {n T : ℕ} (μ : Measure (Fin T → Cube n)) (β : ℝ)
    (g : Fin T → Cube n → ℝ) (π : Fin T → Cube n → Act) : ℝ :=
  timedValue (physicalLaw μ) β (extendReward g) (extendPolicy π)

noncomputable def cubeOptimalValue {n T : ℕ} (μ : Measure (Fin T → Cube n)) (β : ℝ)
    (g : Fin T → Cube n → ℝ) : ℝ := optimalValue (physicalLaw μ) β (extendReward g)

/-- A finite backward recursion. With r remaining periods, the next call has r-1.
At the terminal period the continuation reward is zero (never stopping pays zero). -/
noncomputable def bellmanTail {n T : ℕ} (β : ℝ) (g : Fin T → Cube n → ℝ)
    (K : Fin T → Kernel (Cube n) (Cube n)) : ℕ → Fin T → Cube n → ℝ
  | 0, _, _ => 0
  | r + 1, k, x => max (g k x) (β *
      if h : k.val + 1 < T then
        ∫ y, bellmanTail β g K r ⟨k.val + 1, h⟩ y ∂(K k x)
      else 0)

noncomputable def continuation {n T : ℕ} (β : ℝ) (g : Fin T → Cube n → ℝ)
    (K : Fin T → Kernel (Cube n) (Cube n)) (k : Fin T) (x : Cube n) : ℝ :=
  if h : k.val + 1 < T then
    ∫ y, bellmanTail β g K (T - (k.val + 1)) ⟨k.val + 1, h⟩ y ∂(K k x)
  else 0

noncomputable def optimalPolicy {n T : ℕ} (β : ℝ) (g : Fin T → Cube n → ℝ)
    (K : Fin T → Kernel (Cube n) (Cube n)) (k : Fin T) (x : Cube n) : Act :=
  if g k x > β * continuation β g K k x then Act.stop else Act.go

/-- EC.4 is an almost-sure bound at times before the last transition.
No density condition is imposed on the deterministic initial state or on null current states. -/
def DensityBound {n T : ℕ} (μ : Measure (Fin T → Cube n))
    (K : Fin T → Kernel (Cube n) (Cube n)) (lam : ℝ) : Prop :=
  ∀ (k : Fin T), k.val + 1 < T → ∀ A : Set (Cube n), MeasurableSet A →
    ∀ᵐ p ∂μ, K k (p k) A ≤ ENNReal.ofReal lam * volume (Subtype.val '' A)

end InterpOptStop.SAA.Supplement


