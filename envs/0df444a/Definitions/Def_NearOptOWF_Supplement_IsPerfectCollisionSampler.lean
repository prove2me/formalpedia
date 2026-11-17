-- Prove2me | Definitions.Def_NearOptOWF_Supplement_IsPerfectCollisionSampler
-- name    : NearOptOWF_Supplement_IsPerfectCollisionSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:08:13.422195+00:00
-- url     : https://prove2.me/theorems/78c92e6d-5619-40c6-9c13-995421cd96d2
-- title:
--   Perfect collision sampler
-- statement:
--   A randomized algorithm $A$, run on $(1^n, f)$ for a circuit $f:\{0,1\}^n\to\{0,1\}^{n-1}$, is read as a **collision finder**: an output of length $2n$ whose halves $x\ne x'$ satisfy $f(x)=f(x')$ is the collision $(x,x')$, and any other output is $\bot$. $A$ is a **perfect collision sampler** if for every $n$ and every such $f$:
--
--   1. **Functional equivalence.** If $f, f'$ are functionally equivalent, every collision $(x, x')$ is output by $A(f)$ and $A(f')$ with the same probability, so $A(f)$ and $A(f')$ are identically distributed.
--   2. **Uniformity on pre-images.** For every $y\in\mathrm{Im}(f)$ and any two unordered pairs $\{x_1,x_1'\}$, $\{x_2,x_2'\}$ of distinct pre-images of $y$,
--   $$
--   \Pr[A(f) = (x_1,x_1')] + \Pr[A(f) = (x_1',x_1)] = \Pr[A(f) = (x_2,x_2')] + \Pr[A(f) = (x_2',x_2)],
--   $$
--   so conditioned on outputting a collision on $y$, the pair $\{x,x'\}$ is uniform over $\{\{x,x'\} : x\ne x',\ f(x)=f(x')=y\}$.
--
--   **Formalization Note** "Polynomial-size circuits" is quantified as all circuits. $n-1$ is truncated at $n = 0$, where no collision exists.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §5.1, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_NearOptOWF_Supplement_rawProb
import Definitions.Def_NearOptOWF_FunEquiv
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- `A` is a **perfect collision sampler** for circuits mapping `{0,1}ⁿ` to `{0,1}^{n−1}`
(Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §5.1, p.24 (PDF p.26)). `A` is run on `(1ⁿ, f)`; an output of length `2n` whose halves `x ≠ x′`
satisfy `f(x) = f(x′)` is a collision `(x, x′)`, any other output is `⊥`. For every `n` and every circuit
`f` with `n − 1` output wires:

1. **functional equivalence**: if `f, f′` are functionally equivalent, every collision `(x, x′)` is
   output by `A(f)` and `A(f′)` with the same probability (so the output distributions are identical);
2. **uniformity on pre-images**: for every `y ∈ Im(f)`, every unordered pair `{x, x′}` of distinct
   pre-images of `y` has the same probability `Pr[out = (x, x′)] + Pr[out = (x′, x)]` (so conditioned on a
   collision on `y`, the pair is uniform over `{{x, x′} : x ≠ x′, f(x) = f(x′) = y}`).

**Formalization Note** "Polynomial-size circuits" is quantified as all circuits (each circuit is of
constant, hence polynomial, size). `n − 1` is natural subtraction; at `n = 0` there are no collisions and
both clauses are empty. -/
def IsPerfectCollisionSampler (A : Inverter) : Prop :=
  (∀ (n : ℕ) (f f' : MCircuit n), f.outs.length = n - 1 → f'.outs.length = n - 1 → FunEquiv f f' →
    ∀ x x' : List Bool, x.length = n → x'.length = n → x ≠ x' → f.eval x = f.eval x' →
      rawProb A [unary n, f.code] (x ++ x') = rawProb A [unary n, f'.code] (x ++ x')) ∧
  (∀ (n : ℕ) (f : MCircuit n), f.outs.length = n - 1 → ∀ y x₁ x₁' x₂ x₂' : List Bool,
    x₁.length = n → x₁'.length = n → x₂.length = n → x₂'.length = n → x₁ ≠ x₁' → x₂ ≠ x₂' →
    f.eval x₁ = y → f.eval x₁' = y → f.eval x₂ = y → f.eval x₂' = y →
      rawProb A [unary n, f.code] (x₁ ++ x₁') + rawProb A [unary n, f.code] (x₁' ++ x₁) =
        rawProb A [unary n, f.code] (x₂ ++ x₂') + rawProb A [unary n, f.code] (x₂' ++ x₂))

end NearOptOWF.Supplement


