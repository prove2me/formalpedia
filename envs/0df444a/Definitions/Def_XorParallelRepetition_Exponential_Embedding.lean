-- Prove2me | Definitions.Def_XorParallelRepetition_Exponential_Embedding
-- name    : XorParallelRepetition_Exponential_Embedding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:24.896142+00:00
-- url     : https://prove2.me/theorems/21c4254b-8cdd-49a8-9ee5-e20658821cbe
-- title:
--   Definition 1.6 — commuting embeddings
-- statement:
--   Let $\Psi$ be a generalized XOR game. A **commuting embedding** of $\Psi$ consists of a complex Hilbert space $V$, of any dimension, unitaries $U_i(x)$ on $V$ for every player $i$ and question $x\in\Sigma_i$, and a non-zero vector $v\in V$ such that
--
--   1. $U_i(x)$ and $U_j(y)$ commute whenever $i\ne j$, for all questions $x\in\Sigma_i$ and $y\in\Sigma_j$;
--   2. for every supported challenge $(x,t)$,
--
--   $$
--   \Bigl(\prod_{i}U_i(x_i)\Bigr)v=\omega_p^{t}\,v.
--   $$
--
--   Operators of one player are not required to commute, and no power of them is prescribed. An embedding of dimension one is an Abelian embedding (Definition 1.2), so having no commuting embedding is the stronger property.
--
--   The notion connects the BLR transformation (Lemma 1.7) with ordered contradictions (Lemma 2.3).
--
--   **Formalization Note** The product over players is `Finset.noncommProd`, whose value does not depend on the order because distinct players commute. The Hilbert space is taken in the universe of the question types.
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Definition 1.6, printed p. 7, PDF p. 7

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames

/-!
# Commuting embeddings

Source: Braverman and Minzer, STOC 2027 submission #195, Definition 1.6 (printed/PDF p. 7),
applied to generalized games as in Lemma 2.3 (p. 9).
-/

namespace XorParallelRepetition.Exponential

universe u

variable {p : ℕ} {ι : Type}

/-- A commuting embedding of `Ψ` on the complex Hilbert space `V` (Definition 1.6): unitaries
`U i x`, such that operators of **distinct** players commute, together with a non-zero vector `v`
with `U₁(x₁) ⋯ U_k(x_k) v = ω_p^t v` for every supported challenge `(x, t)`.  Operators of one
player need not commute with each other, and no power of them is prescribed.  Because operators
of distinct players commute, the product over players does not depend on the order. -/
structure CommutingEmbedding [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι)
    (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] where
  /-- The operator of player `i` on question `x`. -/
  U : ∀ i, Ψ.Q i → (V →L[ℂ] V)
  /-- Every operator is unitary. -/
  unitary_mem : ∀ i x, U i x ∈ unitary (V →L[ℂ] V)
  /-- Operators of distinct players commute. -/
  commute : ∀ i j, i ≠ j → ∀ (x : Ψ.Q i) (y : Ψ.Q j), Commute (U i x) (U j y)
  /-- The common vector. -/
  v : V
  /-- The vector is non-zero. -/
  v_ne_zero : v ≠ 0
  /-- The eigenvalue equation on the support. -/
  eigen : ∀ ω ∈ Ψ.μ.support,
    (Finset.univ.noncommProd (fun i => U i (ω.1 i))
        (fun i _ j _ hij => commute i j hij (ω.1 i) (ω.1 j))) v = phase p ω.2 • v

/-- `Ψ` has a commuting embedding: there is a complex Hilbert space, of any dimension, carrying
one. -/
def HasCommutingEmbedding [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι) : Prop :=
  ∃ (V : Type u) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V),
    Nonempty (CommutingEmbedding Ψ V)

end XorParallelRepetition.Exponential


