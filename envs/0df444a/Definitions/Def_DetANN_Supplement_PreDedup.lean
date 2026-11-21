-- Prove2me | Definitions.Def_DetANN_Supplement_PreDedup
-- name    : DetANN_Supplement_PreDedup
-- status  : Definition
-- author  : @milia
-- created : 2026-11-21T03:39:29.514635+00:00
-- url     : https://prove2.me/theorems/e5631cf1-5ddf-44ec-8b82-38baa36e48aa
-- title:
--   The deduplicated difference table of the construction program
-- statement:
--   Definitions describing the dedupe step of the program `pre` (definition `DetANN_Supplement_PreProg`).
--   - $\mathrm{ddStep}(l,v)$ appends $v$ to the list $l$ unless $v\in l$.
--   - $\mathrm{ddJ}$ and $\mathrm{ddI}$ are the inner loop over $j$ and the outer loop over $i$; $\mathrm{ddList}(x,n)$ starts from the empty list and applies $\mathrm{ddStep}$ to $x_i-x_j$ for the pairs $i<j<n$ in lexicographic order.
--   - $\mathrm{ptSeq}(P)$ is the sequence $i\mapsto P_i$ for $i<n$ and $0$ otherwise, for $P:\mathrm{Fin}\,n\to\mathbb R^d$.
--   - $\mathrm{TableAt}(\mathrm{mem},D_b,l)$ says that entry $m$ of $l$ is stored in the real cells $D_b+md,\dots,D_b+md+d-1$.
--   - $\mathrm{pairB}(d,L_m)=10d+10+L_m(12d+8)$ is the step bound of one pair for a table of at most $L_m$ entries.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib

/-!
# Milestone 21 (`DetANN.Supplement.theorem_3_2`): the dedupe of the construction program

The differences `x i - x j` (`i < j < n`) are appended in order to a list, skipping those already
present (`ddStep`, `ddJ`, `ddI`, `ddList`); `ptSeq P` lists the points of `P` by index; `TableAt mem Db l`
says that entry `m` of `l` is stored at the real cells `Db + m·d, …, Db + m·d + d - 1`; `pairB` is the
step bound of one pair.
-/

namespace DetANN.Supplement.Thm32

variable {d : ℕ}

/-- Append `v` unless it is already present. -/
noncomputable def ddStep (l : List (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d)) :
    List (EuclideanSpace ℝ (Fin d)) :=
  if v ∈ l then l else l ++ [v]

/-- The inner loop: `j, j+1, …, j+kk-1`. -/
noncomputable def ddJ (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ℕ → ℕ → List (EuclideanSpace ℝ (Fin d)) → List (EuclideanSpace ℝ (Fin d))
  | _, 0, l => l
  | j, kk + 1, l => ddJ x i (j + 1) kk (ddStep l (x i - x j))

/-- The outer loop: `i, i+1, …, i+kk-1`, each with `j` from `i+1` to `n-1`. -/
noncomputable def ddI (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ℕ → ℕ → List (EuclideanSpace ℝ (Fin d)) → List (EuclideanSpace ℝ (Fin d))
  | _, 0, l => l
  | i, kk + 1, l => ddI x n (i + 1) kk (ddJ x i (i + 1) (n - (i + 1)) l)

/-- The table after all pairs `i < j < n`, starting from the empty list. -/
noncomputable def ddList (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  ddI x n 0 n []

/-- The points as a sequence indexed by `ℕ`. -/
noncomputable def ptSeq {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin d)) (i : ℕ) : EuclideanSpace ℝ (Fin d) :=
  if h : i < n then P ⟨i, h⟩ else 0

/-- The list `l` is stored at `Db`, entry `m` at `Db + m·d`. -/
def TableAt (mem : ℤ → ℝ) (Db : ℤ) (l : List (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ (m : ℕ) (v : EuclideanSpace ℝ (Fin d)), l[m]? = some v → ∀ c : Fin d,
    mem (Db + ((m * d + c : ℕ) : ℤ)) = v c

/-- The step bound of one pair `(i, j)` of the dedupe loop, for a table of at most `Lm` entries. -/
def pairB (d Lm : ℕ) : ℕ := 10 * d + 10 + Lm * (12 * d + 8)

end DetANN.Supplement.Thm32


