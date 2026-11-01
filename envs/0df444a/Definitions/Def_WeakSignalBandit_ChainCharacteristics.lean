-- Prove2me | Definitions.Def_WeakSignalBandit_ChainCharacteristics
-- name    : WeakSignalBandit_ChainCharacteristics
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:08.558509+00:00
-- url     : https://prove2.me/theorems/82c73cd4-301c-4603-8d71-10eb5c731f6d
-- title:
--   Scaled kernel $K^n=n\Pi^n$, its moments $a^n,b^n,\Delta^n_\epsilon,m^n_p,\tilde a^n,\tilde b^n$, and Markov chains with transition kernel $\Pi$
-- statement:
--   Let $\Pi^n$ be a transition kernel on $\mathbb R^d$ (here $\mathbb R^\iota$, Euclidean norm $|\cdot|$) and $K^n(z,A)=n\,\Pi^n(z,A)$ the **scaled transition kernel** (A.6). For $z\in\mathbb R^d$, coordinates $k,l$, $\epsilon>0$ and $p>0$:
--
--   1. truncated characteristics
--   $$a^n_{k,l}(z)=\int_{x:|z-x|\le1}(x_k-z_k)(x_l-z_l)\,K^n(z,dx),\qquad b^n_k(z)=\int_{x:|z-x|\le1}(x_k-z_k)\,K^n(z,dx),$$
--   $$\Delta^n_\epsilon(z)=K^n(z,\{x:|x-z|>\epsilon\});$$
--   2. moments and untruncated characteristics
--   $$m^n_p(z)=\int|x-z|^p\,K^n(z,dx),\qquad \tilde a^n_{k,l}(z)=\int(x_k-z_k)(x_l-z_l)\,K^n(z,dx),\qquad \tilde b^n_k(z)=\int(x_k-z_k)\,K^n(z,dx).$$
--   3. A process $(Z_i)_{i\in\mathbb N}$ on a probability space is a **time-homogeneous Markov chain with transition kernel $\Pi$** if every $Z_i$ is a random variable and $\mathbb P(Z_{i+1}\in B\mid Z_0,\dots,Z_i)=\Pi(Z_i,B)$ almost surely, for every $i$ and every Borel set $B$ (A.4).
--
--   These are the quantities in which the Stroock–Varadhan diffusion approximation (Theorem 11) and the truncation lemma (Lemma 12) are stated.
--
--   **Formalization Note** The functions take the kernel $K=K^n$ as an argument. $m^n_p$ is valued in $[0,\infty]$ (a lower Lebesgue integral), so an infinite moment is never read as $0$; $\Delta^n_\epsilon$ is a real number, which is exact because $K^n$ is $n$ times a probability kernel.
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (A.4)–(A.6) p.31; the functions a^n, b^n, Δ^n_ε, m^n_p, ã^n, b̃^n, p.32

import Mathlib
import Definitions.Def_WeakSignalBandit_DiffusionLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WeakSignalBandit

variable {ι : Type*} [Fintype ι]

/-- The scaled transition kernel `K^n(z, A) = n Π^n(z, A)` of a transition kernel `Π^n` (`T` in Lean).
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (A.6) p.31. -/
noncomputable def scaledKernel (T : Sp ι → Measure (Sp ι)) (n : ℕ) (z : Sp ι) : Measure (Sp ι) :=
  (n : ℝ≥0∞) • T z

/-- The truncated second moments
`a^n_{k,l}(z) = ∫_{x : |z − x| ≤ 1} (x_k − z_k)(x_l − z_l) K^n(z, dx)` of a kernel `K` (here `K`
plays the role of `K^n`).
Kuang, Wager, arXiv:2101.09855v7, §A.1, p.32 ("Finally, define the functions"). -/
noncomputable def truncDiff (K : Sp ι → Measure (Sp ι)) (z : Sp ι) (k l : ι) : ℝ :=
  ∫ x in Metric.closedBall z 1, (x k - z k) * (x l - z l) ∂(K z)

/-- The truncated first moments `b^n_k(z) = ∫_{x : |z − x| ≤ 1} (x_k − z_k) K^n(z, dx)`.
Kuang, Wager, arXiv:2101.09855v7, §A.1, p.32. -/
noncomputable def truncDrift (K : Sp ι → Measure (Sp ι)) (z : Sp ι) (k : ι) : ℝ :=
  ∫ x in Metric.closedBall z 1, (x k - z k) ∂(K z)

/-- The mass of long jumps `Δ^n_ε(z) = K^n(z, {x : |x − z| > ε})`.
Kuang, Wager, arXiv:2101.09855v7, §A.1, p.32.

**Formalization Note** The value is the real number `K(z, ·)(…)`; for the kernels used here
(`n` times a probability kernel) it is finite, so `toReal` loses nothing. -/
noncomputable def jumpMass (K : Sp ι → Measure (Sp ι)) (ε : ℝ) (z : Sp ι) : ℝ :=
  (K z {x | ε < ‖x - z‖}).toReal

/-- The `p`-th absolute moment `m^n_p(z) = ∫ |x − z|^p K^n(z, dx)`, valued in `[0, ∞]`.
Kuang, Wager, arXiv:2101.09855v7, §A.1, p.32.

**Formalization Note** The moment is a lower Lebesgue integral in `ℝ≥0∞`, so an infinite moment is
`∞` (never a junk `0`). -/
noncomputable def momentP (K : Sp ι → Measure (Sp ι)) (p : ℝ) (z : Sp ι) : ℝ≥0∞ :=
  ∫⁻ x, ‖x - z‖ₑ ^ p ∂(K z)

/-- The untruncated second moments `ã^n_{k,l}(z) = ∫ (x_k − z_k)(x_l − z_l) K^n(z, dx)`.
Kuang, Wager, arXiv:2101.09855v7, §A.1, p.32. -/
noncomputable def fullDiff (K : Sp ι → Measure (Sp ι)) (z : Sp ι) (k l : ι) : ℝ :=
  ∫ x, (x k - z k) * (x l - z l) ∂(K z)

/-- The untruncated first moments `b̃^n_k(z) = ∫ (x_k − z_k) K^n(z, dx)`.
Kuang, Wager, arXiv:2101.09855v7, §A.1, p.32. -/
noncomputable def fullDrift (K : Sp ι → Measure (Sp ι)) (z : Sp ι) (k : ι) : ℝ :=
  ∫ x, (x k - z k) ∂(K z)

/-- The natural σ-algebra `σ(Z_0, …, Z_i)` of a process `Z` up to step `i`. -/
abbrev natSigma {Ω : Type*} (Z : ℕ → Ω → Sp ι) (i : ℕ) : MeasurableSpace Ω :=
  ⨆ j ≤ i, MeasurableSpace.comap (Z j) inferInstance

/-- `Z` is a time-homogeneous Markov chain in `ℝ^ι` with transition kernel `Π` (`T` in Lean) under `ℙ` (`Pr` in Lean):
every `Z_i` is a random variable, and for every step `i` and Borel set `B`,
`ℙ(Z_{i+1} ∈ B | Z_0, …, Z_i) = Π(Z_i, B)` almost surely.
Kuang, Wager, arXiv:2101.09855v7, (A.4) p.31 ("`Π^n(z, A) = ℙ(Z^n_{i+1} ∈ A | Z^n_i = z)`").

**Formalization Note** The Markov property is stated with respect to the whole past
`σ(Z_0, …, Z_i)`, which is what "Markov chain with transition kernel `Π`" means; the conditional
probability is the conditional expectation of the indicator. -/
def IsMarkovChain {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (T : Kernel (Sp ι) (Sp ι)) (Z : ℕ → Ω → Sp ι) : Prop :=
  (∀ i, Measurable (Z i)) ∧
  ∀ (i : ℕ) (B : Set (Sp ι)), MeasurableSet B →
    condExp (natSigma Z i) Pr ((Z (i + 1) ⁻¹' B).indicator fun _ => (1 : ℝ)) =ᵐ[Pr]
      fun ω => (T (Z i ω) B).toReal

end WeakSignalBandit


