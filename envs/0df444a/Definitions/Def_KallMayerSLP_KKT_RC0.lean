-- Prove2me | Definitions.Def_KallMayerSLP_KKT_RC0
-- name    : KallMayerSLP_KKT_RC0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:31.664075+00:00
-- url     : https://prove2.me/theorems/fc73cd28-0c4d-45e4-8d12-d3619ef85397
-- title:
--   Regularity condition RC 0
-- statement:
--   The program (3.1) satisfies the **regularity condition RC 0** if for every optimal solution $\hat x$ of (3.1) and every direction $z\in\mathbb R^n$,
--   $$
--   z^{\mathsf T}\nabla g_i(\hat x)\le 0\quad\forall i\in I(\hat x)\qquad\Longrightarrow\qquad z^{\mathsf T}\nabla f(\hat x)\ge 0,
--   $$
--   where $I(\hat x)=\{i\mid g_i(\hat x)=0\}$ is the active set.
--
--   RC 0 is the condition under which the Farkas lemma turns optimality into the KKT conditions (proof of Proposition 3.4); Remark 3.1 shows it holds for linear constraints and can fail for nonlinear ones.
--
--   **Formalization Note** $\nabla$ is Mathlib's `gradient`, which is meaningful under the book's standing assumption that $f$ and the $g_i$ are continuously differentiable; every theorem that uses RC 0 assumes it.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, p.63 (PDF 74), RC 0

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_IsOptimal
import Definitions.Def_KallMayerSLP_KKT_activeSet

open scoped RealInnerProductSpace

namespace KallMayerSLP.KKT

/-- **Regularity condition `RC 0`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, p.63 (PDF 74):
"`RC 0` For any optimum `x̂` of (3.1) holds that
`zᵀ∇gᵢ(x̂) ≤ 0 ∀i ∈ I(x̂)` implies `zᵀ∇f(x̂) ≥ 0`."

**Formalization Note.** `zᵀv` is the inner product `⟪z, v⟫` on `EuclideanSpace ℝ (Fin n)`, and
`∇` is Mathlib's `gradient`. The book's standing assumption (p.62) is that `f` and every `gᵢ` are
continuously differentiable; `gradient` returns `0` at a point of non-differentiability, so this
predicate has its intended meaning only under that assumption, which every theorem using it
states. The quantifier "for every `z`" ranges over all of `ℝⁿ`. -/
def RC0 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x, IsOptimal f g x → ∀ z : EuclideanSpace ℝ (Fin n),
    (∀ i ∈ activeSet g x, ⟪z, gradient (g i) x⟫ ≤ 0) → 0 ≤ ⟪z, gradient f x⟫

end KallMayerSLP.KKT


