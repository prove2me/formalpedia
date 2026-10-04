-- Prove2me | Definitions.Def_CookSensitivity_ChvatalRank_ChvatalClosure
-- name    : CookSensitivity_ChvatalRank_ChvatalClosure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:37:21.984548+00:00
-- url     : https://prove2.me/theorems/ccfef7da-11bd-4402-b30f-5a48a7a635a4
-- title:
--   Chvátal closure $P'$, iterates $P^{(t)}$, Chvátal rank of a polyhedron and of a matrix
-- statement:
--   Let $S \subseteq \mathbb{Q}^n$. If every vector of $S$ satisfies $ax \le \beta$, where $a$ is an integral vector and $\beta$ a rational number, then every integral vector of $S$ satisfies the **Chvátal cut** $ax \le \lfloor \beta \rfloor$. The **Chvátal closure** is
--   $$S' = \{x \in \mathbb{Q}^n : ax \le \lfloor\beta\rfloor \text{ for all } a \in \mathbb{Z}^n,\ \beta \in \mathbb{Q} \text{ with } ay \le \beta \ \forall y \in S\}.$$
--   Iterate it: $S^{(0)} = S$ and $S^{(i)} = (S^{(i-1)})'$ for $i \ge 1$.
--
--   The **Chvátal rank** of $S$ is the least $t \in \mathbb{N}$ with $S^{(t)} = S_I$ (the integer hull), and $+\infty$ if there is no such $t$. The **Chvátal rank of an integral matrix** $A$ is
--   $$\sup_{b \in \mathbb{Z}^m} \operatorname{rank}\{x : Ax \le b\},$$
--   the supremum over all integral right-hand sides $b$, valued in $\mathbb{N} \cup \{+\infty\}$.
--
--   The paper (after Chvátal, Gomory and Schrijver) uses these notions for polyhedra; Schrijver showed that $P'$ is again a polyhedron and that the Chvátal rank of a rational polyhedron is finite. The main theorem of the paper bounds the rank of a matrix in terms of $n$ and $\Delta(A)$.
--
--   **Formalization Note** The closure is defined for every set, not only polyhedra, so the iterates need no lemma that $P'$ is a polyhedron; on polyhedra it is the paper's $P'$. For $S = \emptyset$ the cut with $a = 0$, $\beta = -\tfrac12$ gives $\emptyset' = \emptyset$. `chvatalRank` is the infimum in `ℕ∞` over $t$ with $S^{(t)} = S_I$, so it is `⊤` when no such $t$ exists; `chvatalRankMatrix` is the supremum in `ℕ∞` over `b : Fin m → ℤ`.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 259, §3 (Chvátal cut, P', P^(i), Chvátal rank of P and of a matrix A)

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

/-- The Chvátal closure `S′`: the set of vectors satisfying every Chvátal cut `ax ≤ ⌊β⌋` of `S`,
where `a` ranges over integral vectors and `β` over rationals with `ay ≤ β` for all `y ∈ S`. -/
def chvatalClosure {n : ℕ} (S : Set (Fin n → ℚ)) : Set (Fin n → ℚ) :=
  {x | ∀ (a : Fin n → ℤ) (β : ℚ),
    (∀ y ∈ S, (fun i => (a i : ℚ)) ⬝ᵥ y ≤ β) → (fun i => (a i : ℚ)) ⬝ᵥ x ≤ (⌊β⌋ : ℚ)}

/-- The iterated Chvátal closure: `S^(0) = S` and `S^(i) = (S^(i-1))′`. -/
def chvatalIter {n : ℕ} (t : ℕ) (S : Set (Fin n → ℚ)) : Set (Fin n → ℚ) :=
  (chvatalClosure)^[t] S

/-- The Chvátal rank of `S`: the least `t` with `S^(t) = S_I`, and `⊤` if there is none. -/
noncomputable def chvatalRank {n : ℕ} (S : Set (Fin n → ℚ)) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : chvatalIter t S = integerHull S), (t : ℕ∞)

/-- The Chvátal rank of an integral matrix `A`: the supremum over all integral vectors `b` of
the Chvátal rank of `{x : Ax ≤ b}`. -/
noncomputable def chvatalRankMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ∞ :=
  ⨆ b : Fin m → ℤ, chvatalRank (polyhedron A (fun i => (b i : ℚ)))

end CookSensitivity.ChvatalRank


