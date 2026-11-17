-- Prove2me | Definitions.Def_ApproxDegComp_Supplement_noisyR
-- name    : ApproxDegComp_Supplement_noisyR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:59:29.700932+00:00
-- url     : https://prove2.me/theorems/4157e4af-cc2f-4c49-93b3-442e2d0591d9
-- title:
--   Noisy randomized query complexity $\mathrm{noisyR}(f)$
-- statement:
--   A **noisy randomized algorithm** $A$ is a probability distribution with finite support over finite noisy decision trees. On input $x$ it samples a tree and runs it against the noisy oracle. Its cost on $x$ is
--
--   $$\mathrm{cost}(A,x)=\mathbb E\Big[\sum_{t=1}^{T}\gamma_t^2\Big],$$
--
--   the expectation being over the internal randomness of $A$ and the oracle's answers, where $T$ is the number of queries made. Let $f:D\subseteq\{0,1\}^n\to\{0,1\}$ be a possibly partial Boolean function. $A$ **computes $f$ with error $\varepsilon$** if $\Pr[A(x)\ne f(x)]\le\varepsilon$ for every $x\in D$. The **noisy randomized query complexity** is
--
--   $$\mathrm{noisyR}_\varepsilon(f)=\inf_A\ \max_{x\in D}\ \mathrm{cost}(A,x),$$
--
--   the infimum over all noisy randomized algorithms computing $f$ with error at most $\varepsilon$, and $\mathrm{noisyR}(f)=\mathrm{noisyR}_{1/3}(f)$.
--
--   Noisy queries can be cheaper than ordinary ones (a strength-$\gamma$ query costs only $\gamma^2$); Theorem 31 shows they save at most a logarithmic factor.
--
--   **Formalization Note** An algorithm is a probability mass function on noisy trees whose support is finite; probabilities and costs are finite sums over the support. The maximum over the finite set $D$ is a supremum over $D$, and the infimum is the infimum of a set of reals. That set is nonempty (the tree querying every coordinate once with $\gamma=1$ has error $0$) and bounded below by $0$, both proved in a sanity file. For empty $D$ the maximum is read as $0$; every statement that uses $\mathrm{noisyR}$ assumes $f$ non-constant, so $D\neq\emptyset$.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definitions 7–8, p.12

import Mathlib
import Definitions.Def_ApproxDegComp_Supplement_NoisyTree
import Definitions.Def_NoPerfectRandComp_PartialFn

namespace ApproxDegComp

namespace Supplement

/-- **Noisy randomized algorithm** (Definition 7, p.12).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 7,
p.12: "Let A be a noisy oracle randomized algorithm. Then it is a finite support distribution over
finite noisy decision trees."

**Formalization Note** A probability mass function on `NoisyTree ι` whose support is finite. -/
structure NoisyAlg (ι : Type) where
  /-- the distribution of the tree run by the algorithm -/
  dist : PMF (NoisyTree ι)
  /-- the distribution has finite support -/
  finite_support : dist.support.Finite

namespace NoisyAlg

variable {ι : Type}

/-- `Pr[A(x) = v]`, over the internal randomness of `A` and the noisy oracle answers on input `x`
(Definition 7, p.12). -/
noncomputable def outProb (A : NoisyAlg ι) (x : ι → Bool) (v : Bool) : ℝ :=
  ∑ t ∈ A.finite_support.toFinset, (A.dist t).toReal * t.outProb x v

/-- `cost(A, x) = E[∑_{t=1}^T γ_t²]`, the expectation over the internal randomness of `A` and the
noisy oracle answers when `A` is run on `x` (Definition 7, p.12). -/
noncomputable def cost (A : NoisyAlg ι) (x : ι → Bool) : ℝ :=
  ∑ t ∈ A.finite_support.toFinset, (A.dist t).toReal * t.cost x

end NoisyAlg

/-- **Noisy randomized query complexity** `noisyR_ε(f)` and `noisyR(f) = noisyR_{1/3}(f)`
(Definition 8, p.12). Pednekar–Podder, STOC 2027 submission (manuscript sha256 b9a66c7f…),
Definition 8, p.12: "The noisy randomized query complexity of f : D → {0,1} is
noisyR_ϵ(f) = inf_A max_{x∈D} {cost(A, x)}, where infimum is taken over all noisy randomized query
algorithms computing f with error at most ϵ." Definition 7: A computes f with error up to ϵ if
`Pr[A(x) ≠ f(x)] ≤ ϵ` for all `x ∈ D`.

**Formalization Note** `f` is a `NoPerfectRandComp.PartialFn` on `ι` (domain `f.dom`). The maximum
over the finite set `D` is `⨆ x : f.dom`; the infimum is `sInf` of a set of reals. The set is
nonempty (the tree querying every coordinate once with `γ = 1` and outputting `f` computes `f`
with error `0`) and bounded below by `0` (costs are nonnegative); both are checked in
`Solutions/verification/ApproxDegComp_Supplement_sanity.lean`, so `sInf` is the true infimum.
For empty `D` the maximum is the real `sSup ∅ = 0`; the statements using `noisyR` assume `f`
non-constant, hence `D ≠ ∅`. -/
noncomputable def noisyREps {ι : Type} (ε : ℝ) (f : NoPerfectRandComp.PartialFn ι) : ℝ :=
  sInf {c : ℝ | ∃ A : NoisyAlg ι, (∀ x ∈ f.dom, A.outProb x (!f.val x) ≤ ε) ∧
    c = ⨆ x : f.dom, A.cost x}

/-- `noisyR(f) = noisyR_{1/3}(f)` (Definition 8, p.12: "When ϵ = 1/3, the subscript ϵ is
dropped"). -/
noncomputable def noisyR {ι : Type} (f : NoPerfectRandComp.PartialFn ι) : ℝ :=
  noisyREps (1 / 3) f

end Supplement

end ApproxDegComp


