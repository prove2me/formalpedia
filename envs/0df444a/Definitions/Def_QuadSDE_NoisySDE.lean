-- Prove2me | Definitions.Def_QuadSDE_NoisySDE
-- name    : QuadSDE_NoisySDE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:26.658369+00:00
-- url     : https://prove2.me/theorems/b84ccc98-9339-4b49-b2d5-6b6827dd9ef0
-- title:
--   Noise of APX-SDE and pathwise solutions of $dX=f(X)\,dt+\sqrt q\,dW$
-- statement:
--   Let $(\Omega,P)$ be a probability space. The **noise setting** of APX-SDE consists of
--   1. $W(t)\in\mathbb R^N$, $t\ge0$, a vector of $N$ independent standard Wiener processes;
--   2. $Z\in\mathbb R^N$ with i.i.d. entries $Z_i\sim\mathcal N(0,1)$;
--   3. $Z$ independent of the whole process $W$.
--
--   Given a drift $f:\mathbb R^N\to\mathbb R^N$, a rate $q$, an initial random vector $\xi$ and a horizon $T\ge0$, a process $X$ **solves**
--   $$dX(t)=f(X(t))\,dt+\sqrt q\,dW(t),\qquad X(0)=\xi \qquad (2)$$
--   on $[0,T]$ if for $P$-almost every $\omega$ the path $t\mapsto X(t,\omega)$ is continuous on $[0,T]$ and
--   $$X(t,\omega)=\xi(\omega)+\int_0^t f(X(s,\omega))\,ds+\sqrt q\,W(t,\omega)\qquad\text{for all }t\in[0,T].$$
--   In APX-SDE the initial vector is $\xi=Y+\sqrt p\,Z$.
--
--   **Formalization Note** The Wiener process is the published `Peng1990.SMP.IsStdBrownian` (time $\mathbb R_{\ge0}$). Because the noise is additive, the SDE needs no stochastic integral: the integral equation, path by path, is the solution concept. No adaptedness or moment condition is imposed; for a locally Lipschitz drift the equation determines the path from $\xi(\omega)$ and $W(\cdot,\omega)$, so every such solution agrees almost surely with the strong solution.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §1, Eq. (2) and Problem 2, p. 2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §1, p. 2 (Eq. (2)): the
two noise sources of APX-SDE on a probability space `(Ω, P)`. `B = W` is a vector of `N`
independent standard Wiener processes; `Z ∈ ℝ^N` has i.i.d. `𝒩(0, 1)` entries; and `Z` is
independent of `W` ("The two sources of noise are mutually independent").

**Formalization Note.** The Wiener process is the published `Peng1990.SMP.IsStdBrownian` (each
`B t` measurable, each coordinate a Mathlib `IsBrownianReal`, coordinates mutually independent),
with time `ℝ≥0`. The law of `Z` is the product of `N` standard normal laws. Independence of `Z` and
`W` is independence of `Z` and the whole path-valued map `ω ↦ (t ↦ B t ω)`. -/
structure NoiseSetting {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin N → ℝ) (Z : Ω → Fin N → ℝ) : Prop where
  brownian : Peng1990.SMP.IsStdBrownian P B
  gaussian : P.map Z = Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  indep : IndepFun Z (fun ω t => B t ω) P

/-- Eq. (2), p. 2: `X` solves `dX(t) = f(X(t)) dt + √q dW(t)`, `X(0) = ξ`, on the horizon `[0, T]`,
pathwise: for `P`-almost every `ω`, the path `t ↦ X(t, ω)` is continuous on `[0, T]` and
`X(t, ω) = ξ(ω) + ∫₀ᵗ f(X(s, ω)) ds + √q W(t, ω)` for every `t ≤ T`.

**Formalization Note.** The noise is additive, so the SDE needs no stochastic integral: the
integral equation is the definition of a (strong) solution with continuous paths. No adaptedness
or moment condition is imposed: for a locally Lipschitz `f` the integral equation determines the
continuous path from `ξ(ω)` and `W(·, ω)`, so every such `X` agrees a.s. with the strong solution.
Time is `ℝ≥0`; the Lebesgue integral runs over the real interval `[0, t]`. -/
def SolvesPathwise {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (q : ℝ) (B : ℝ≥0 → Ω → Fin N → ℝ)
    (ξ : Ω → Fin N → ℝ) (X : ℝ≥0 → Ω → Fin N → ℝ) (T : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ≥0 => X t ω) (Set.Iic T) ∧
    ∀ t : ℝ≥0, t ≤ T →
      X t ω = ξ ω + (∫ s in (0 : ℝ)..(t : ℝ), f (X s.toNNReal ω)) + Real.sqrt q • B t ω

end QuadSDE


