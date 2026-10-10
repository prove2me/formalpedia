-- Prove2me | Definitions.Def_QuasiHemiVI_Existence_WeakConv
-- name    : QuasiHemiVI_Existence_WeakConv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:39.185211+00:00
-- url     : https://prove2.me/theorems/3c2fb406-b3bf-4a84-81a8-b707b58c21d1
-- title:
--   Weak convergence, sequential weak closedness and reflexivity in a real normed space
-- statement:
--   Let $E$ be a real normed space with dual $E^*$.
--
--   1. A sequence $(x_n)$ in $E$ **converges weakly** to $x_0\in E$, written $x_n\rightharpoonup x_0$, if $\ell(x_n)\to\ell(x_0)$ for every $\ell\in E^*$.
--   2. A set $A\subseteq E$ is **sequentially weakly closed** if $x_0\in A$ whenever $x_n\in A$ for all $n$ and $x_n\rightharpoonup x_0$.
--   3. $E$ is **reflexive** if the canonical embedding $E\to E^{**}$, $x\mapsto(\ell\mapsto\ell(x))$, is surjective.
--
--   These are the notions of weak convergence ($\rightharpoonup$), "weakly closed" and "reflexive Banach space" used throughout Sections 2 and 3 of the paper.
--
--   **Formalization Note** In a reflexive space a bounded set is weakly closed if and only if it is sequentially weakly closed (Eberlein–Šmulian), so for the bounded solution sets of the mission the two readings of "weakly closed" agree; the proofs in the paper establish the sequential form.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1247 (setting: V real reflexive Banach space), p. 1249 (Theorem 2.7: sequentially weakly closed), p. 1250 (⇀ in (HK), (3.1))

import Mathlib

namespace QuasiHemiVI.Existence

open Filter Topology

/-- Weak convergence `x n ⇀ x₀` in a real normed space `E`: `ℓ (x n) → ℓ x₀` for every continuous
linear functional `ℓ ∈ E*`. -/
def WeakConv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : ℕ → E) (x₀ : E) : Prop :=
  ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun n => ℓ (x n)) atTop (𝓝 (ℓ x₀))

/-- A set `A ⊆ E` is sequentially weakly closed: the weak limit of every sequence of `A` that
converges weakly lies in `A`. -/
def IsSeqWeaklyClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Set E) : Prop :=
  ∀ (x : ℕ → E) (x₀ : E), (∀ n, x n ∈ A) → WeakConv x x₀ → x₀ ∈ A

/-- A real normed space `E` is reflexive: the canonical embedding `E → E**` is surjective. -/
def IsReflexive (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)

end QuasiHemiVI.Existence


