-- Prove2me | Definitions.Def_HardCoreBochner_IsDownClosedLaw
-- name    : HardCoreBochner_IsDownClosedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:06.525892+00:00
-- url     : https://prove2.me/theorems/9f25f53b-ad19-4f7e-be8b-db3a30afcdc4
-- title:
--   Distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$
-- statement:
--   Let $V$ be a finite set. A family $X\subseteq\{0,1\}^V$ is **downward-closed** if $\tau\subseteq\sigma\in X$ implies $\tau\in X$. A distribution $\mu$ on $\{0,1\}^V$ is **fully supported on $X$** if $\mu(\sigma)>0$ exactly for $\sigma\in X$.
--
--   This predicate says that $\mu$ is a probability distribution on $\{0,1\}^V$ whose support $X=\{\sigma:\mu(\sigma)>0\}$ is downward-closed:
--
--   1. $\mu(\sigma)\ge 0$ for every $\sigma$;
--   2. $\sum_\sigma \mu(\sigma)=1$ (so $X$ is non-empty);
--   3. if $\tau\subseteq\sigma$ and $\mu(\sigma)>0$ then $\mu(\tau)>0$.
--
--   This is the general setting of Theorem 1.2; the hard-core model on the independent sets of a graph is the main example.
--
--   **Formalization Note** Configurations are functions $V\to\{\mathrm{false},\mathrm{true}\}$; $v\in\sigma$ means $\sigma(v)=\mathrm{true}$ and $\tau\subseteq\sigma$ is the pointwise order. $X$ is not a separate argument: it is the support of $\mu$.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §1, p.3 (PDF p.3): 'µ is a distribution that is fully supported on a downward-closed set family X ⊆ {0, 1}^V for V finite'; Theorem 1.2, p.3

import Mathlib

namespace HardCoreBochner

open scoped BigOperators

/-- A **distribution fully supported on a non-empty downward-closed set family** `X ⊆ {0,1}^V`.
Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.3: "µ is a distribution that is fully supported on a downward-closed set family
X ⊆ {0, 1}^V for V finite"; Theorem 1.2, p.3: "Let X ⊆ {0, 1}^V be a non-empty downward-closed set
family and suppose µ is a distribution fully supported on X".

The family `X` is the support `{σ | 0 < µ σ}`, so "fully supported on X" is built in: µ is
nonnegative, sums to one (hence X is non-empty), and X is downward-closed (`τ ⊆ σ ∈ X ⇒ τ ∈ X`).

**Formalization Note** Configurations are `V → Bool`, i.e. literally `{0,1}^V`; `σ v = true`
means `v ∈ σ`, and `τ ≤ σ` (pointwise, `false < true`) means `τ ⊆ σ`. -/
structure IsDownClosedLaw {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) : Prop where
  /-- µ is nonnegative. -/
  nonneg : ∀ σ, 0 ≤ μ σ
  /-- µ is a probability distribution. -/
  sum_eq_one : ∑ σ, μ σ = 1
  /-- The support of µ is downward-closed. -/
  downClosed : ∀ σ τ : V → Bool, τ ≤ σ → 0 < μ σ → 0 < μ τ

end HardCoreBochner


