-- Prove2me | Definitions.Def_SpinGirth5_Interaction
-- name    : SpinGirth5_Interaction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:31.209752+00:00
-- url     : https://prove2.me/theorems/5afdead1-11ba-4431-8b16-d303b8b32692
-- title:
--   Multi-spin system: symmetric interaction matrix $A\in[0,1]^{q\times q}$ and external field $\lambda\ge 0$
-- statement:
--   A **multi-spin system** on $q$ colours consists of an interaction matrix $A\in\mathbb R^{q\times q}$ and an external field $\lambda\in\mathbb R^q$ such that
--
--   1. $A$ is symmetric, $A_{a,b}=A_{b,a}$;
--   2. every entry satisfies $0\le A_{a,b}\le 1$;
--   3. $\lambda_a\ge 0$ for every colour $a$.
--
--   Its **deficit matrix** is $B:=\mathbf 1\mathbf 1^{\top}-A$, i.e. $B_{a,b}=1-A_{a,b}\in[0,1]$. The condition $A\le 1$ costs nothing, because the Gibbs distribution is invariant under a global scaling of $A$.
--
--   These are the standing assumptions of the paper on $(A,\lambda)$; every Gibbs distribution, the star law of §5 and the Potts model are built from such a pair.
--
--   **Formalization Note** The colour set is `Fin q`. The condition $q\ge 2$ is not part of the structure; it is stated in the theorems that assume it.
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §1.1, p.4; §5, p.19; Condition 4, p.4 (B := 11ᵀ − A)

import Mathlib

namespace SpinGirth5

/-- A **multi-spin system** on `q` colours: a symmetric interaction matrix `A ∈ [0, 1]^{q×q}`
and an external field `λ ∈ ℝ^q_{≥0}`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, §1.1, p.4: "Let A ∈ R^{q×q}_{≥0} be a symmetric matrix, and let
λ ∈ R^q_{≥0}. […] without loss of generality, we will assume A ∈ [0, 1]^{q×q} throughout"; §5,
p.19: "A ∈ [0, 1]^{q×q} is the symmetric interaction matrix and λ ∈ R^q_{≥0} is the external
field".

**Formalization Note** The four fields are the paper's standing assumptions on `(A, λ)`; the
condition `q ≥ 2` is not bundled and is stated where the paper states it. -/
structure Interaction (q : ℕ) where
  /-- The interaction matrix `A`. -/
  A : Matrix (Fin q) (Fin q) ℝ
  /-- The external field `λ`. -/
  lam : Fin q → ℝ
  symm : ∀ a b, A a b = A b a
  nonneg : ∀ a b, 0 ≤ A a b
  le_one : ∀ a b, A a b ≤ 1
  lam_nonneg : ∀ a, 0 ≤ lam a

/-- The deficit matrix `B := 11ᵀ − A` (Chen, Liu, arXiv:2608.25491, Condition 4, p.4). -/
def Interaction.B {q : ℕ} (S : Interaction q) : Matrix (Fin q) (Fin q) ℝ :=
  fun a b => 1 - S.A a b

end SpinGirth5


