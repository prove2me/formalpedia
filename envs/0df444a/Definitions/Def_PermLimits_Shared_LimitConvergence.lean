-- Prove2me | Definitions.Def_PermLimits_Shared_LimitConvergence
-- name    : PermLimits_Shared_LimitConvergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:57:49.421386+00:00
-- url     : https://prove2.me/theorems/8adac0dd-349a-4717-b54b-0210d9d7cf19
-- title:
--   Weak, rectangular and density convergence of limit permutations
-- statement:
--   1. **Weak convergence.** Probability measures $\mu_n$ on $[0,1]^2$ converge weakly to $\mu$, written $\mu_n\Rightarrow\mu$, if
--   $$\lim_{n\to\infty}\int f\,d\mu_n=\int f\,d\mu$$
--   for every bounded continuous $f:[0,1]^2\to\mathbb R$. For the corresponding random points this is convergence in distribution $(X_n,Y_n)\xrightarrow{d}(X,Y)$.
--
--   Let $Z,Z_1,Z_2,\dots$ be limit permutations with associated random points $(X_n,Y_n)$ and $(X,Y)$. Then:
--
--   2. $Z_n\Rightarrow Z$ if $(X_n,Y_n)\xrightarrow{d}(X,Y)$;
--   3. $Z_n\xrightarrow{\square}Z$ if $\lim_{n}d_\square(Z_n,Z)=0$;
--   4. $Z_n\xrightarrow{t}Z$ if $\lim_n t(\tau,Z_n)=t(\tau,Z)$ for every permutation $\tau$.
--
--   These are the three notions of convergence on $\mathcal Z$ whose equivalence is the core of the existence proof.
--
--   **Formalization Note** $[0,1]^2$ is compact, so the test functions are all continuous real functions on it. Weak convergence of limit permutations is weak convergence of the laws $\mu_{Z_n}$ to $\mu_Z$. In item 4, $\tau$ ranges over permutations of every length.
--
--   This definition is shared by both missions of this series: mission 1 (`01-limit-existence`, existence and uniqueness of the limit permutation) (Lemma 2.1, p. 7; Lemma 5.3, p. 16; Eq. (49), p. 17) and mission 2 (`02-cauchy-rectangular`, convergent sequences are Cauchy for the rectangular distance) (Lemma 2.1, p. 7; Lemma 5.3, p. 16; Eq. (49), p. 17).
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 7, Eq. (9), and p. 16, Definition 5.2

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_RectDist

/-!
# Three notions of convergence of limit permutations

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2: weak convergence, Eq. (9) (p. 7), and Definition 5.2 (p. 16).

A definition bundle: weak convergence of measures on `[0,1]²`, and the convergences `Z_n ⇒ Z`,
`Z_n →□ Z`, `Z_n →ᵗ Z` of Definition 5.2.
-/

namespace PermLimits.Shared

open MeasureTheory Filter Topology unitInterval

/-- **Weak convergence** `μ_n ⇒ μ` of measures on `[0,1]²` (Hoppen et al., arXiv:1103.5844v2,
Sect. 2.2, Eq. (9), p. 7): `∫ f dμ_n → ∫ f dμ` for every bounded continuous `f : [0,1]² → ℝ`.
For random points this is convergence in distribution `(X_n, Y_n) →ᵈ (X, Y)`.

**Formalization Note.** `[0,1]²` is compact, so every continuous `f` is bounded; the test
functions are `C(I × I, ℝ)`. The predicate is applied to probability measures. -/
def WeakConvMeasures (μs : ℕ → Measure (I × I)) (μ : Measure (I × I)) : Prop :=
  ∀ f : C(I × I, ℝ), Tendsto (fun n => ∫ p, f p ∂(μs n)) atTop (𝓝 (∫ p, f p ∂μ))

/-- **`Z_n ⇒ Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 5.2 (1), p. 16): the random
points associated with `Z_n` converge in distribution to the one associated with `Z`, i.e.
`μ_{Z_n} ⇒ μ_Z`. -/
def WeakConv (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ) : Prop :=
  WeakConvMeasures (fun n => limitMeasure (Zs n)) (limitMeasure Z)

/-- **`Z_n →□ Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 5.2 (2), p. 16):
`lim_n d□(Z_n, Z) = 0`. -/
def RectConv (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ) : Prop :=
  Tendsto (fun n => rectDist (Zs n) Z) atTop (𝓝 0)

/-- **`Z_n →ᵗ Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 5.2 (3), p. 16):
`lim_n t(τ, Z_n) = t(τ, Z)` for every permutation `τ`.

**Formalization Note.** `τ` ranges over permutations of every length `k`; for `k = 0` the clause
is `1 → 1`. -/
def DensityConv (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ) : Prop :=
  ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)),
    Tendsto (fun n => limitDensity τ (Zs n)) atTop (𝓝 (limitDensity τ Z))

end PermLimits.Shared


