-- Prove2me | Definitions.Def_NearOptOWF_Supplement_IsPerfectPreimageSampler
-- name    : NearOptOWF_Supplement_IsPerfectPreimageSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:06:51.50523+00:00
-- url     : https://prove2.me/theorems/104c5e19-52af-4f87-86de-fc11ce129878
-- title:
--   Perfect pre-image sampler
-- statement:
--   Fix an output length $m(n)$. A randomized algorithm $A$, run on $(1^n, f, y)$, is read as an **inverter**: its output $x$ is a pre-image when $|x| = n$ and $f(x) = y$, and is $\bot$ otherwise. $A$ is a **perfect pre-image sampler** for all circuits $f:\{0,1\}^n\to\{0,1\}^{m(n)}$ if for every $n$:
--
--   1. **Functional equivalence.** If $f, f'$ are functionally equivalent circuits, then for every $y$ and every pre-image $x$ of $y$,
--   $$\Pr[A(f,y) = x] = \Pr[A(f',y) = x],$$
--   so $A(f,y)$ and $A(f',y)$ are identically distributed (the probability of $\bot$ is the complement).
--   2. **Uniformity on pre-images.** For every $f$ and every $y\in\mathrm{Im}(f)$, all $x, x'\in f^{-1}(y)$ satisfy $\Pr[A(f,y) = x] = \Pr[A(f,y) = x']$, so conditioned on not outputting $\bot$, the output is uniform on $f^{-1}(y)$.
--
--   A perfect pre-image sampler behaves as if it read the truth table of $f$ and returned a uniform pre-image.
--
--   **Formalization Note** The paper's class "all polynomial-size circuits" is quantified as all circuits: each single circuit has size bounded by a constant, hence polynomial, function.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 4.2, p.13 (PDF p.15); class of Theorem 4.3

import Mathlib
import Definitions.Def_NearOptOWF_Supplement_rawProb
import Definitions.Def_NearOptOWF_FunEquiv
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- `A` is a **perfect pre-image sampler** for all circuits mapping `{0,1}ⁿ` to `{0,1}^{m(n)}`
(Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 4.2, p.13 (PDF p.15); class of Theorem 4.3).
`A` is run on `(1ⁿ, f, y)`; its output `x` counts as a pre-image when `|x| = n` and `f(x) = y`, and as
`⊥` otherwise. For every `n` and every circuit `f` with `m(n)` output wires:

1. **functional equivalence**: if `f, f′` are functionally equivalent, then for every `y` and every
   pre-image `x` of `y`, `A(f, y)` and `A(f′, y)` output `x` with the same probability (so the two
   output distributions, with `⊥` for everything else, are identical);
2. **uniformity on pre-images**: for every `y ∈ Im(f)`, all pre-images `x, x′ ∈ f⁻¹(y)` are output
   with the same probability (so conditioned on not `⊥` the output is uniform on `f⁻¹(y)`).

**Formalization Note** "Polynomial-size circuits" is quantified as all circuits: each single circuit
has size bounded by a (constant) polynomial, so the two classes coincide. The functional-equivalence
clause is stated on valid outputs; the probability of `⊥` is the complement and agrees as well. -/
def IsPerfectPreimageSampler (A : Inverter) (m : ℕ → ℕ) : Prop :=
  (∀ (n : ℕ) (f f' : MCircuit n), f.outs.length = m n → f'.outs.length = m n → FunEquiv f f' →
    ∀ y x : List Bool, x.length = n → f.eval x = y →
      rawProb A [unary n, f.code, y] x = rawProb A [unary n, f'.code, y] x) ∧
  (∀ (n : ℕ) (f : MCircuit n), f.outs.length = m n → ∀ y x x' : List Bool,
    x.length = n → f.eval x = y → x'.length = n → f.eval x' = y →
      rawProb A [unary n, f.code, y] x = rawProb A [unary n, f.code, y] x')

end NearOptOWF.Supplement


