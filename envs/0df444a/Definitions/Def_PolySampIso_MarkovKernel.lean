-- Prove2me | Definitions.Def_PolySampIso_MarkovKernel
-- name    : PolySampIso_MarkovKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:22.104709+00:00
-- url     : https://prove2.me/theorems/492e3224-41ee-4aba-8538-fa47dccba546
-- title:
--   Markov operators, kernel powers, reversibility and ½-laziness
-- statement:
--   For a Markov kernel $K$ on a measurable space $\Omega$ and a function $f$, the **Markov operator** is $(Kf)(x)=\int f(y)\,K(x,dy)$, and $K^N$ is the $N$-fold composite ($K^0$ the identity kernel). A measure $\mu$ is pushed forward as $(\mu K)(S)=\int K(x,S)\,\mu(dx)$.
--
--   $K$ is **reversible** with respect to $\mu$ if $\int_A K(x,B)\,\mu(dx)=\int_B K(x,A)\,\mu(dx)$ for all measurable $A,B$ (detailed balance), and **$\tfrac12$-lazy** if $K(x,\cdot)\ge\tfrac12\delta_x$ for every $x$, i.e. it places at least half its mass on the current point.
--
--   A randomized map $O(x,\omega)$ driven by noise $\omega\sim P$ defines the kernel $x\mapsto\mathrm{Law}(O(x,\omega))$; this is how Algorithms 6 and 7 become kernels.
--
--   **Formalization Note** The kernel of a randomized map is Mathlib's pushforward of $\delta_x\otimes P$; it is the zero kernel if the map is not jointly measurable (every map used in the mission is measurable).
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.1, pp.7–8 (PDF pp.9–10); laziness §5.2, p.42 (PDF p.44); reversibility p.43 (PDF p.45)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# Markov kernels: operators, powers, reversibility, laziness

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.1, pp.7–8 (PDF pp.9–10): "For a Markov kernel
K, we let the measure µK be defined in the natural way, i.e., (µK)(S) := ∫ K(x, S)µ(dx) … we may
write Kf to mean the function defined as (Kf)(x) := ∫ f(y)K(x, dy)." §5.2, p.42 (PDF p.44):
"the algorithm is 1/2-lazy, meaning that its Markov kernel from any x ∈ X places at least half its
mass on x." Reversibility (p.43, "M is reversible with respect to µ") is detailed balance.

**Formalization Note.**
* `μK` is Mathlib's `K ∘ₘ μ`; `kapply K f` is `Kf`; `kpow K N` is the `N`-fold composite `K^N`.
* `IsHalfLazy K`: `K(x, ·) ≥ ½ δ_x` for every `x` (equivalently `K(x, {x}) ≥ ½` when singletons
  are measurable).
* `IsReversible K μ`: `∫_A K(x, B) μ(dx) = ∫_B K(x, A) μ(dx)` for all measurable `A, B`.
* `randKernel O P` is the Markov kernel `x ↦ Law(O(x, ω))`, `ω ∼ P`, of a randomized map `O`
  driven by the noise law `P` (the kernel is the zero kernel if `O` is not jointly measurable;
  every randomized map used in this mission is measurable).
-/

/-- The Markov operator `(Kf)(x) = ∫ f(y) K(x, dy)`. -/
noncomputable def kapply {α : Type*} [MeasurableSpace α] (K : Kernel α α) (f : α → ℝ) :
    α → ℝ :=
  fun x => ∫ y, f y ∂(K x)

/-- The `N`-th power `K^N` of a kernel (`K^0` is the identity kernel). -/
noncomputable def kpow {α : Type*} [MeasurableSpace α] (K : Kernel α α) : ℕ → Kernel α α
  | 0 => Kernel.id
  | k + 1 => K ∘ₖ kpow K k

/-- `K` is reversible with respect to `μ` (detailed balance). -/
def IsReversible {α : Type*} [MeasurableSpace α] (K : Kernel α α) (μ : Measure α) : Prop :=
  ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
    ∫⁻ x in A, K x B ∂μ = ∫⁻ x in B, K x A ∂μ

/-- `K` is ½-lazy: `K(x, ·)` places at least half its mass on `x`. -/
def IsHalfLazy {α : Type*} [MeasurableSpace α] (K : Kernel α α) : Prop :=
  ∀ x, (2⁻¹ : ℝ≥0∞) • Measure.dirac x ≤ K x

/-- The kernel `x ↦ Law(O(x, ω))`, `ω ∼ P`, of a randomized map `O` with noise law `P`. -/
noncomputable def randKernel {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace Ω] (O : α → Ω → β) (P : Measure Ω) [IsFiniteMeasure P] : Kernel α β :=
  (Kernel.id ×ₖ Kernel.const α P).map (Function.uncurry O)

end PolySampIso


