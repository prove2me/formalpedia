-- Prove2me | Definitions.Def_GraphonCheeger_cutDist
-- name    : GraphonCheeger_cutDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:12.729896+00:00
-- url     : https://prove2.me/theorems/4f5c1450-56e8-4307-8075-e199b5e5379b
-- title:
--   Cut norm $\|F\|_\square$ and cut distance $\delta_\square(W_1,W_2)$ over all probability spaces
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and $F$ an integrable function on $\Omega^2$. The **cut norm** of $F$ is
--
--   $$\|F\|_\square=\sup_{S,T}\Bigl|\int_{S\times T}F(x,y)\,d\mu(x)\,d\mu(y)\Bigr|,$$
--
--   the supremum over all pairs of measurable sets $S,T\subseteq\Omega$.
--
--   For graphons $W_1$ on $(\Omega_1,\mu_1)$ and $W_2$ on $(\Omega_2,\mu_2)$, possibly on different spaces, the **cut distance** is
--
--   $$\delta_\square(W_1,W_2)=\inf_{\varphi_1,\varphi_2}\bigl\|W_1^{\varphi_1}-W_2^{\varphi_2}\bigr\|_\square,$$
--
--   where the infimum is over all probability spaces $(\Omega,\nu)$ and all measure-preserving maps $\varphi_1:\Omega\to\Omega_1$, $\varphi_2:\Omega\to\Omega_2$, and the cut norm is taken on $(\Omega,\nu)$.
--
--   The cut distance is the metric of graph-limit theory: a graph sequence converges to a graphon when the cut distance from its step graphons tends to $0$.
--
--   **Formalization Note** For non-integrable $F$ the Lean integral is $0$, so `cutNorm` is only meaningful on integrable functions, as in the paper; every use is on differences of graphons on probability spaces, which are bounded and measurable. The common space of the infimum ranges over the universe `Type (max u v)` when $\Omega_1:$ `Type u` and $\Omega_2:$ `Type v`. The value is unchanged: any common space pushes forward along $(\varphi_1,\varphi_2)$ to a coupling on $\Omega_1\times\Omega_2$, which lies in that universe, and the cut norm on the coupling is at most the cut norm on the original space. The defining set is nonempty (the product coupling) and bounded below by $0$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Appendix A, (A.3) and (A.5), p.81

import Mathlib
import Definitions.Def_GraphonCheeger_IsGraphon

open MeasureTheory

namespace GraphonCheeger

/-!
# Cut norm and cut distance

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), Appendix A, (A.3) and (A.5), p.81.

**Formalization Note.**
* `cutNorm μ F` is (A.3): the supremum over pairs of measurable sets `S, T ⊆ Ω` of
  `|∫_{S×T} F d(µ ⊗ µ)|`. The paper defines it for integrable `F` only, where the set of values
  is bounded by the `L¹` norm. For a non-integrable `F` Lean's integral is `0`, so the value is
  junk (`0`); every use in the mission is on a difference of graphons on a probability space,
  which is bounded and measurable, hence integrable.
* `cutDist μ₁ W₁ μ₂ W₂` is (A.5): the infimum over all probability spaces `(Ω, F, ν)` and
  measure-preserving maps `φ₁ : Ω → Ω₁`, `φ₂ : Ω → Ω₂` of `‖W₁^{φ₁} − W₂^{φ₂}‖_□`. The common
  space ranges over `Type (max u v)` when `Ω₁ : Type u` and `Ω₂ : Type v`. This does not change
  the value: any common space pushes forward, via `(φ₁, φ₂)`, to a coupling on `Ω₁ × Ω₂`, which
  lies in `Type (max u v)`, and the cut norm on the coupling is at most the cut norm on the
  original space (measurable rectangles of `Ω₁ × Ω₂` pull back to measurable rectangles). The
  defining set is bounded below by `0` and is nonempty for probability measures (the product
  coupling).
-/

universe u v

/-- The **cut norm** `‖F‖_□ = sup_{S,T} |∫_{S×T} F(x, y) dµ(x) dµ(y)|` ((A.3), p.81), the
supremum over all pairs of measurable subsets `S, T` of `Ω`. -/
noncomputable def cutNorm {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → Ω → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ S T : Set Ω, MeasurableSet S ∧ MeasurableSet T ∧
    r = |∫ p in S ×ˢ T, F p.1 p.2 ∂(μ.prod μ)|}

/-- The **cut distance** `δ_□(W₁, W₂) = inf_{φ₁, φ₂} ‖W₁^{φ₁} − W₂^{φ₂}‖_□` ((A.5), p.81): the
infimum over all probability spaces `(Ω, ν)` and measure-preserving maps `φ₁ : Ω → Ω₁`,
`φ₂ : Ω → Ω₂`. -/
noncomputable def cutDist {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) (W₁ : Ω₁ → Ω₁ → ℝ) (μ₂ : Measure Ω₂) (W₂ : Ω₂ → Ω₂ → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ (Ω : Type (max u v)) (_ : MeasurableSpace Ω) (ν : Measure Ω)
    (_ : IsProbabilityMeasure ν) (φ₁ : Ω → Ω₁) (φ₂ : Ω → Ω₂),
    MeasurePreserving φ₁ ν μ₁ ∧ MeasurePreserving φ₂ ν μ₂ ∧
    r = cutNorm ν (fun x y => pullback φ₁ W₁ x y - pullback φ₂ W₂ x y)}

end GraphonCheeger


