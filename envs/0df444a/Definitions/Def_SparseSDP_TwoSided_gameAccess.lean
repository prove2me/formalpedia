-- Prove2me | Definitions.Def_SparseSDP_TwoSided_gameAccess
-- name    : SparseSDP_TwoSided_gameAccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:38.667044+00:00
-- url     : https://prove2.me/theorems/a6442327-2f1c-4c74-a627-8fe5f19c3d9c
-- title:
--   Row access to the realified, capped, lifted game matrices
-- statement:
--   The matrices of the game that the solver actually runs: realify, cap the thresholds at $R$, then lift, on the index $\mathrm{Fin}(n+n+1)$ with the extra coordinate last. `gameMat` is that family.
--
--   `gameRead` generates a row of $D_j(g)$ from the sparse oracle: read the threshold (capped on the query, p. 18), read the corresponding row of $C$ or $A_j$, form the row of $\Phi$ (`phiRow`), and merge the diagonal term (`mergeDiag`), in $O(s)$ operations: "A row of a payoff matrix is generated in $O(s)$ time by reading the corresponding original row and merging the diagonal term" (p. 19). Each row of $D_j(g)$ has at most $2s+1$ nonzeros.
--
--   **Formalization Note** The diagonal coefficient is $-g/R$ for $D_0$ and $\min(b_j,R)/R$ for $D_j$, and the block sign is $+1$ and $-1$ respectively, per Eq. (44).
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §2.6.1, p. 18; §2.6.2, p. 19; Eq. (369), p. 67; p. 68

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Dall
import Definitions.Def_SparseSDP_TwoSided_realify
import Definitions.Def_SparseSDP_TwoSided_SparseOracle

open Matrix

namespace SparseSDP.TwoSided

variable {n m : ℕ} {I : Instance ℂ n m}

/-- The index of the lifted matrices: `Fin N ⊕ Unit ≃ Fin (N + 1)`, the extra coordinate last. -/
def liftIdx (N : ℕ) : Fin N ⊕ Unit ≃ Fin (N + 1) :=
  (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv

/-- The position in `Fin (n + n + 1)` of a coordinate of `Fin n ⊕ Fin n`. -/
def pos (x : Fin n ⊕ Fin n) : Fin (n + n + 1) := liftIdx (n + n) (Sum.inl (finSumFinEquiv x))

/-- The matrices of the realified, capped target-value game on `Fin (n + n + 1)`: realify, cap, then
lift (§2.6.1, p. 18, and the order stated on p. 68). -/
noncomputable def gameMat (I : Instance ℂ n m) (R g : ℝ) (j : Fin (m + 1)) :
    Mat (n + n + 1) :=
  reindex (liftIdx (n + n)) (liftIdx (n + n)) (Dall (capInst (realInst I) R) R g j)

/-- Row `h` of `Φ(M)`, from the sparse row of `M` (Eq. (369)). A top-block row holds `Re` then `−Im`,
a bottom-block row `Im` then `Re`. -/
noncomputable def phiRow (h : Fin n ⊕ Fin n) (row : List (Fin n × ℂ)) : SparseRow (n + n + 1) :=
  row.flatMap fun p =>
    match h with
    | Sum.inl _ => [(pos (Sum.inl p.1), p.2.re), (pos (Sum.inr p.1), -p.2.im)]
    | Sum.inr _ => [(pos (Sum.inl p.1), p.2.im), (pos (Sum.inr p.1), p.2.re)]

/-- Merge the diagonal term `a` at column `i` into a row ("merging the diagonal term", p. 19). -/
def mergeDiag {d : ℕ} (i : Fin d) (a : ℝ) (row : SparseRow d) : SparseRow d :=
  if i ∈ row.map Prod.fst then row.map fun p => if p.1 = i then (p.1, p.2 + a) else p
  else (i, a) :: row

/-- Read the identifier, the sign of the matrix block and the diagonal coefficient of `Dⱼ(g)`
(Eq. (44)): `D₀ = +C − (g/R) I`, `Dⱼ = −Aⱼ + (min(bⱼ, R)/R) I`, the cap applied on the threshold
query (p. 18). -/
noncomputable def gameCoef (orc : SparseOracle I) (R g : ℝ) (j : Fin (m + 1)) :
    Prog (Option (Fin m) × ℝ × ℝ) :=
  Fin.cases (op 2 (none, 1, -(g / R)))
    (fun j' => do
      let b ← qB orc j'
      op 2 (some j', -1, min b R / R)) j

/-- Row `i` of `Dⱼ(g)`, generated from the corresponding original row "by reading the corresponding
original row and merging the diagonal term" (p. 19), in `O(s)` operations. -/
noncomputable def gameRead (orc : SparseOracle I) (R g : ℝ) (j : Fin (m + 1))
    (i : Fin (n + n + 1)) : Prog (SparseRow (n + n + 1)) := do
  let (ident, sgn, dg) ← gameCoef orc R g j
  match (liftIdx (n + n)).symm i with
  | Sum.inr _ => op 1 [(i, dg)]
  | Sum.inl a =>
    let h := finSumFinEquiv.symm a
    let row ← readRow orc ident (Sum.elim _root_.id _root_.id h)
    let phi := (phiRow h row).map fun p => (p.1, sgn * p.2)
    op (6 * row.length + 1) (mergeDiag i dg phi)

/-- The row reader of the game at target `g`. -/
noncomputable def gameAccess (orc : SparseOracle I) (R g : ℝ) :
    RowAccess (n + n + 1) (m + 1) where
  read := gameRead orc R g

end SparseSDP.TwoSided


