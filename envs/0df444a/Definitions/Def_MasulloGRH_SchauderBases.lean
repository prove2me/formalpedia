-- Prove2me | Definitions.Def_MasulloGRH_SchauderBases
-- name    : MasulloGRH_SchauderBases
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:22:20.067599+00:00
-- url     : https://prove2.me/theorems/a33edbc4-f5c5-4037-8408-7fcfc1360c3b
-- title:
--   Schauder bases in locally convex spaces: equicontinuous, unconditional, absolute, boundedly complete, shrinking
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$, $(x_m)_{m\ge0}$ a sequence in $E$ and $(f_m)_{m\ge0}$ a sequence of continuous linear functionals on $E$.
--
--   1. $(x_m)$ is a **Schauder basis** with coefficient functionals $(f_m)$ if the sequence is bi-orthogonal, $f_m(x_n)=\delta_{m,n}$, and for every $u\in E$ the series
--   $$\sum_{m\ge0}f_m(u)\,x_m$$
--   converges in $E$ to $u$.
--   2. The **basic projections** are $P_k=\sum_{0\le m\le k}f_m\cdot x_m$. The basis is **equicontinuous** if $(P_k)_{k\ge0}$ is an equicontinuous sequence of operators on $E$.
--   3. The basis is **unconditional** if for every $u$ the sequence $(f_m(u)x_m)$ is unconditionally summable.
--   4. The basis is **absolute** if for every continuous seminorm $q$ on $E$ there is a continuous seminorm $q'$ with
--   $$\sum_{m\ge0}q\big(f_m(u)x_m\big)\le q'(u)\qquad\text{for all }u\in E .$$
--   5. The basis is **boundedly complete** if for every sequence of scalars $(\alpha_m)$ such that the partial sums $\sum_{m\le k}\alpha_mx_m$ are bounded in $E$, the series $\sum_m\alpha_mx_m$ converges in $E$.
--   6. The basis is **shrinking** if $(f_m)$ is a Schauder basis of the strong dual $E'_\beta$: $\varphi=\sum_{m\ge0}\varphi(x_m)f_m$ in $E'_\beta$ for every $\varphi\in E'$.
--   7. The basis is **regular** if some $0$-neighbourhood contains no $x_m$, and **normalized** if it is regular and bounded.
--
--   The exponential system $(e^{2\pi imx})_{m\in\mathbb Z}$ in $C^\infty(\mathbb T)$ is the model example; the draft constructs analogous bases on spaces of adelic $\theta$-functions.
--
--   **Formalization Note** Convergence of a series is convergence of the partial sums over $m\le k$. Equicontinuity of the linear maps $P_k$ is stated at $0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 4, §4.1, Definition 4.1.1.1 (p. 157) and Definition 4.1.2.1 (p. 158)

import Definitions.Def_MasulloGRH_LocallyConvex

/-!
# Schauder bases in locally convex spaces

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Chapter 4, §4.1:
Definition 4.1.1.1 (p. 157) and Definition 4.1.2.1 (p. 158).
-/

namespace MasulloGRH

open Topology Filter

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- The basic projection `P_k = ∑_{m ≤ k} f_m · x_m` of a sequence `(x_m, f_m)`. -/
def basicProjection (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (k : ℕ) (u : E) : E :=
  ∑ m ∈ Finset.range (k + 1), f m u • x m

/-- Definition 4.1.1.1: `(x_m)` is a Schauder basis of `E` with coefficient functionals `(f_m)`:
the sequence `(x_m, f_m)` is bi-orthogonal, every `f_m` is continuous, and for every `u ∈ E` the
series `∑_{m ≥ 0} f_m(u) x_m` converges in `E` to `u`. -/
structure IsSchauderBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop where
  biorthogonal : ∀ m n, f m (x n) = if m = n then 1 else 0
  expansion : ∀ u : E, Tendsto (fun k => basicProjection x f k u) atTop (𝓝 u)

/-- Definition 4.1.2.1(1): the basis is equicontinuous: the sequence of basic projections
`P_k = ∑_{m ≤ k} f_m · x_m` is equicontinuous. -/
def IsEquicontinuousBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : E), ∀ k : ℕ, ∀ u ∈ V, basicProjection x f k u ∈ U

/-- Definition 4.1.2.1(2): the basis is unconditional: for every `u` the sequence
`(f_m(u) x_m)` is unconditionally summable. -/
def IsUnconditionalBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  ∀ u : E, Summable (fun m => f m u • x m)

/-- Definition 4.1.2.1(3): the basis is absolute: for every continuous seminorm `q` on `E` there
is a continuous seminorm `q'` with `∑_{m ≥ 0} q(f_m(u) x_m) ≤ q'(u)` for all `u`. -/
def IsAbsoluteBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  ∀ q : Seminorm ℂ E, Continuous q → ∃ q' : Seminorm ℂ E, Continuous q' ∧
    ∀ u : E, Summable (fun m => q (f m u • x m)) ∧ ∑' m, q (f m u • x m) ≤ q' u

/-- Definition 4.1.2.1(4): the basis is boundedly complete: whenever the partial sums of
`∑ α_m x_m` form a bounded sequence, the series converges in `E`. -/
def IsBoundedlyCompleteBasis (x : ℕ → E) : Prop :=
  ∀ α : ℕ → ℂ,
    Bornology.IsVonNBounded ℂ (Set.range fun k => ∑ m ∈ Finset.range (k + 1), α m • x m) →
    ∃ v : E, Tendsto (fun k => ∑ m ∈ Finset.range (k + 1), α m • x m) atTop (𝓝 v)

/-- `(f_m)` is a Schauder basis of the strong dual `E'_β` whose coefficient functionals are the
evaluations at the `x_m`: for every `φ ∈ E'` the series `∑_m φ(x_m) f_m` converges to `φ` in
`E'_β`. -/
def IsDualSchauderBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  (∀ m n, f m (x n) = if m = n then 1 else 0) ∧
    ∀ φ : StrongDual ℂ E, Tendsto (fun k => ∑ m ∈ Finset.range (k + 1), φ (x m) • f m) atTop (𝓝 φ)

/-- Definition 4.1.2.1(5): the basis is shrinking: `(f_m)` is a Schauder basis of `E'_β`. -/
def IsShrinkingBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop := IsDualSchauderBasis x f

/-- Definition 4.1.2.1(6): the basis is regular: some `0`-neighbourhood contains no `x_m`. -/
def IsRegularBasis (x : ℕ → E) : Prop := ∃ U ∈ 𝓝 (0 : E), ∀ m, x m ∉ U

/-- Definition 4.1.2.1(6): the basis is normalized: regular and bounded. -/
def IsNormalizedBasis (x : ℕ → E) : Prop :=
  IsRegularBasis x ∧ Bornology.IsVonNBounded ℂ (Set.range x)

end

end MasulloGRH


