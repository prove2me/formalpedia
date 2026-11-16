-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Supplement_TarskiStar
-- name    : TarskiBootstrap_Dimensional_Supplement_TarskiStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:27.590761+00:00
-- url     : https://prove2.me/theorems/1f30ccbc-7867-4418-a29a-20de6ceaed0f
-- title:
--   Tarski$^*(n,k)$ instances and solutions
-- statement:
--   A **Tarski$^*(n,k)$ instance** is a pair $(f,\sigma)$ of a monotone map $f:[n]^k\to[n]^k$ and a monotone sign function $\sigma:[n]^k\to\{-1,0,1\}$, monotone meaning $\sigma(x)\le\sigma(y)$ whenever $x\preceq y$. The oracle at $x$ returns $(f(x),\sigma(x))$. A point $x$ is a **solution** if
--
--   $$
--   \bigl(x\preceq f(x)\ \wedge\ \sigma(x)\ge0\bigr)\ \vee\ \bigl(x\succeq f(x)\ \wedge\ \sigma(x)\le0\bigr).
--   $$
--
--   No bounded-increment restriction is imposed on $f$. This is the intermediate problem through which the hidden-sign construction passes.
--
--   **Formalization Note** Signs are Mathlib's `SignType`, ordered $-1<0<1$.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 2.3, PDF/printed p. 6, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Grid

namespace TarskiBootstrap.Dimensional.Supplement

/-- Definition 2.3, PDF/printed p. 6: a `Tarski*(n, k)` instance is a monotone
`f : [n]^k → [n]^k` together with a monotone sign function `σ : [n]^k → {-1, 0, 1}`
(`σ(x) ≤ σ(y)` whenever `x ⪯ y`); no bounded-increment condition is imposed. -/
def IsTarskiStarInstance {n k : ℕ+} (f : Grid n k → Grid n k)
    (σ : Grid n k → SignType) : Prop :=
  Monotone f ∧ Monotone σ

/-- Definition 2.3: `x` solves the `Tarski*` instance `(f, σ)` iff
`x ⪯ f(x) ∧ σ(x) ≥ 0` or `x ⪰ f(x) ∧ σ(x) ≤ 0`. -/
def IsTarskiStarSolution {n k : ℕ+} (f : Grid n k → Grid n k)
    (σ : Grid n k → SignType) (x : Grid n k) : Prop :=
  (x ≤ f x ∧ 0 ≤ σ x) ∨ (f x ≤ x ∧ σ x ≤ 0)

end TarskiBootstrap.Dimensional.Supplement


