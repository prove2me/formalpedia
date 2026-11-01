-- Prove2me | Definitions.Def_RelaxRoundPoA_IsExactMaximizer
-- name    : RelaxRoundPoA_IsExactMaximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:58.232898+00:00
-- url     : https://prove2.me/theorems/5ada79c3-9dbc-42fe-a127-359c8e3530c1
-- title:
--   Exact declared welfare maximizer
-- statement:
--   Let $F\subseteq\Omega'$ be the mechanism's set of feasible outcomes. A mechanism $M=(f,p)$ is an **exact declared welfare maximizer** over $F$ if for every profile $b$ drawn from the weight classes, almost surely $f(b)\in F$ and
--
--   $$
--   \sum_{i\in N}b_i(y)\le\sum_{i\in N}b_i\bigl(f(b)\bigr)\qquad\text{for all }y\in F.
--   $$
--
--   For a relaxation $F$ is the whole relaxed outcome space $\Omega'$. Exactness is what lets a VCG mechanism be built on the same outcome rule in the proof of Lemma 1.
--
--   **Formalization Note** The outcome rule may be randomized; a deterministic maximizer is the case of a Dirac law.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Exact declared welfare maximizer.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §3, p.8: the outcome rule computes "an optimal
solution `x'` to a relaxed problem `Π'` that maximizes the declared welfare. That is, it maximizes
`∑_{i∈N} b_i(x')`"; Theorem 3 and Lemma 1 require `f'` (resp. `f`) to be "an exact declared welfare
maximizer".

`IsExactMaximizer Val Feas M` says: for every profile `b` drawn from `Val`, almost every outcome `x`
of `M` on `b` is feasible (`x ∈ Feas`) and maximizes the declared welfare over `Feas`:
`∑_i b_i(y) ≤ ∑_i b_i(x)` for all `y ∈ Feas`.

**Formalization Note** The outcome rule may be randomized (p.6); a deterministic rule is the case of
a Dirac outcome law. `Feas` is the feasible outcome set: the whole relaxed space `Set.univ` for a
relaxation, `Ω` for the original problem. -/
def IsExactMaximizer {N : Type*} [Fintype N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0)) (Feas : Set Ω') (M : Mechanism N Ω') : Prop :=
  ∀ b, IsProfile Val b →
    ∀ᵐ x ∂(M.outcome b), x ∈ Feas ∧ ∀ y ∈ Feas, ∑ i, b i y ≤ ∑ i, b i x

end RelaxRoundPoA


