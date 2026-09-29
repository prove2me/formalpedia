-- Prove2me | Definitions.Def_buchholz_walk_sum
-- name    : buchholz_walk_sum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-23T22:44:50.536928+00:00
-- url     : https://prove2.me/theorems/538f093f-13fc-4e15-be5c-16e236786e79
-- statement:
--   **Matched-walk vocabulary for the Buchholz even-moment method.**
--
--   For the coordinate Rademacher matrix
--   $$S_\varepsilon=p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_i e_j^{\top},$$
--   the trace moment $\operatorname{tr}((S_\varepsilon S_\varepsilon^{\top})^n)$ expands over alternating closed row/column walks
--   $$i_0-j_0-i_1-j_1-\cdots-i_{n-1}-j_{n-1}-i_0.$$
--   This definition file introduces the cyclic successor on the walk, the multiplicity with which a coordinate edge $(i,j)$ appears, the predicate that every coordinate edge appears with even multiplicity, the coefficient product of one walk, and the resulting matched-walk sum $W_n(\Omega,p,X)$.
--
--   The matched-walk sum is the intermediate object produced after applying Rademacher sign orthogonality: odd edge multiplicities average to zero, while even multiplicities survive.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Sections 2-3; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_matrix_completion_gram_schatten

/-!
Matched closed-walk vocabulary for the even-moment proof of the
noncommutative Khintchine inequality.

For a rectangular matrix `S`, the trace of `(S * Sᵀ)^n` expands over alternating
row/column closed walks

`i₀ -- j₀ -- i₁ -- j₁ -- ... -- iₙ₋₁ -- jₙ₋₁ -- i₀`.

After averaging the coordinate Rademacher signs, only walks in which every
coordinate edge `(i,j)` appears with even multiplicity survive.  Buchholz's
combinatorial estimate bounds the surviving sum by the pair-partition count
times the larger row/column Gram trace.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Cyclic successor on a nonempty `Fin n`; the proof of nonemptiness is
available from the element itself. -/
def buchholzCyclicSucc {n : Nat} (k : Fin n) : Fin n :=
  ⟨(k.1 + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2)⟩

/-- Number of times a coordinate edge `c = (i,j)` appears in the alternating
closed walk encoded by row vertices `rows : Fin n → Fin n1` and column vertices
`cols : Fin n → Fin n2`.  Each column vertex `j_k` touches the two row vertices
`i_k` and `i_{k+1}`. -/
noncomputable def buchholzEdgeMultiplicity {n n1 n2 : Nat}
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2)
    (c : Fin n1 × Fin n2) : Nat :=
  ((Finset.univ : Finset (Fin n)).filter
      (fun k => (rows k, cols k) = c)).card +
    ((Finset.univ : Finset (Fin n)).filter
      (fun k => (rows (buchholzCyclicSucc k), cols k) = c)).card

/-- A walk is matched when every coordinate edge appears an even number of
times; these are exactly the sign monomials that survive Rademacher averaging. -/
def buchholzWalkMatched {n n1 n2 : Nat}
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) : Prop :=
  ∀ c : Fin n1 × Fin n2, Even (buchholzEdgeMultiplicity rows cols c)

/-- The unsigned coefficient product attached to an alternating closed walk in
the sampled coordinate matrix `p⁻¹ δ_ij X_ij e_i e_jᵀ`, with signs removed. -/
noncomputable def buchholzWalkProduct {n n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) : Real :=
  ∏ k : Fin n,
    ((if (rows k, cols k) ∈ Omega then p⁻¹ * X (rows k) (cols k) else 0) *
      (if (rows (buchholzCyclicSucc k), cols k) ∈ Omega then
        p⁻¹ * X (rows (buchholzCyclicSucc k)) (cols k)
       else 0))

/-- The matched-walk sum obtained from expanding
`E_ε trace((S_ε S_εᵀ)^n)` and applying Rademacher sign orthogonality. -/
noncomputable def buchholzMatchedWalkSum {n1 n2 : Nat}
    (n : Nat) (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : Real :=
  ∑ rows : Fin n → Fin n1,
    ∑ cols : Fin n → Fin n2,
      if buchholzWalkMatched rows cols then
        buchholzWalkProduct Omega p X rows cols
      else
        0

end MatrixCompletion


