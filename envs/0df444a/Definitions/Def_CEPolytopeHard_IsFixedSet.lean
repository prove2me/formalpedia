-- Prove2me | Definitions.Def_CEPolytopeHard_IsFixedSet
-- name    : CEPolytopeHard_IsFixedSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:39.589554+00:00
-- url     : https://prove2.me/theorems/a4c3d3cb-04d6-4124-bb87-5d4a043df54e
-- title:
--   $\varepsilon$-fixed set (Definition 3.2)
-- statement:
--   Let $X \subseteq \mathbb R^d$ and $f : X \to X$. A finite set $S = \{x_1, \dots, x_k\} \subseteq X$ is an **$\varepsilon$-fixed set** of $f$ if there are a stochastic matrix $P$ on $S$ and a stationary distribution $\mu$ of $P$ with
--   $$
--   \mathbb E_{i \sim \mu}\Big\| x_i - \mathbb E_{j \sim P(i)} f(x_j) \Big\|_2 \le \varepsilon
--   $$
--   (normalized norm). An exact fixed set satisfies $S \subseteq \operatorname{conv} f(S)$. The module also defines the predicate with the chain $P$ and the distribution $\mu$ given, and the distribution on points carried by a weight vector on $S$ ("the corresponding stationary distribution", Theorem 3.3).
--
--   **Formalization Note** The chain is indexed by the points of $S$, which are distinct since $S$ is a set.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Definition 3.2, p.13

import Mathlib
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_IsStochastic

set_option autoImplicit false

namespace CEPolytopeHard

/-- An **ε-fixed set with a given chain** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Definition 3.2, p.13: "An ϵ-fixed set of f is a finite
set S = {x_1, . . . , x_k} ⊂ X such that there is some Markov chain transition function
P : [k] → ∆([k]), and stationary distribution µ of P, such that
E_{i∼µ} ∥x_i − E_{j∼P(i)} f(x_j)∥₂ ≤ ϵ"): the finite set `S ⊆ X`, the stochastic matrix `P`
indexed by the points of `S`, and its stationary distribution `μ` satisfy
`∑_{x ∈ S} μ_x ‖x − ∑_{y ∈ S} P_{xy} f(y)‖₂ ≤ ε`.

**Formalization Note** The chain is indexed by the elements of `S` (the paper's `S` is a set, so
its points are distinct). `‖·‖₂` is the normalized norm `nnorm` (p.9). -/
def IsFixedSetWith {ι : Type*} [Fintype ι] (X : Set (ι → ℝ)) (f : (ι → ℝ) → ι → ℝ) (ε : ℝ)
    (S : Finset (ι → ℝ)) (P : Matrix S S ℝ) (μ : S → ℝ) : Prop :=
  (↑S : Set (ι → ℝ)) ⊆ X ∧ IsStochastic P ∧ IsStationary P μ ∧
    ∑ x : S, μ x * nnorm ((x : ι → ℝ) - ∑ y : S, P x y • f (y : ι → ℝ)) ≤ ε

/-- An **ε-fixed set** (Definition 3.2, p.13): a finite set `S ⊆ X` for which some transition
matrix with some stationary distribution witnesses `IsFixedSetWith`. -/
def IsFixedSet {ι : Type*} [Fintype ι] (X : Set (ι → ℝ)) (f : (ι → ℝ) → ι → ℝ) (ε : ℝ)
    (S : Finset (ι → ℝ)) : Prop :=
  ∃ (P : Matrix S S ℝ) (μ : S → ℝ), IsFixedSetWith X f ε S P μ

/-- the distribution on points carried by a weight vector `μ` on a finite set `S` ("the
corresponding stationary distribution µ", Theorem 3.3, p.13) -/
noncomputable def weightsDist {ι : Type*} (S : Finset (ι → ℝ)) (μ : S → ℝ) : (ι → ℝ) →₀ ℝ :=
  ∑ x : S, Finsupp.single (x : ι → ℝ) (μ x)

end CEPolytopeHard


