-- Prove2me | Definitions.Def_SelectedSubset3SUM_Integer_Supplement_SelectedProduct
-- name    : SelectedSubset3SUM_Integer_Supplement_SelectedProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:49:58.951574+00:00
-- url     : https://prove2.me/theorems/4cfda244-b44b-4134-b226-789faea21e27
-- title:
--   Selected-entries matrix multiplication, Real 3SUM and the cost profiles of the real reductions
-- statement:
--   All programs here run on the published comparison–addition RAM: a word RAM with an integer bank, together with a real bank supporting the constant $0$, addition, negation, copy, load, store and comparison, at unit cost; a deterministic run is a run on the all-false coin tape.
--
--   **Selected-entries matrix multiplication.** An instance consists of an $a\times D$ zero–one matrix $X$, a $D\times b$ zero–one matrix $Y$, and a list of $w$ wanted pairs $(i,j)$ (repetitions allowed). The task is to write $(XY)[i,j]=|\{k: X[i,k]=Y[k,j]=1\}|$ for every wanted pair, i.e. to count the triangles through each wanted left–right edge of a tripartite graph. The input is presented densely: $a,D,b,w$, then $X$ and $Y$ row by row, then the pairs. A cost profile $M(a,D,b,w)$ is **achieved** if one deterministic program computes every instance within $K\,M(a,D,b,w)$ steps, for a constant $K>0$, and its input length is also at most $K\,M(a,D,b,w)$. This is the paper's $M_{\text{selected-entries}}(a,D,b\mid w)$.
--
--   **Real 3SUM.** Given real lists $A,B,C$, decide whether $a+b=c$ for some $a\in A$, $b\in B$, $c\in C$. The input has integer cells $n,d,|A|,|B|,|C|$ and real cells $A$, $B$, $C$; the answer is $1$ or $0$ in integer output cell $0$.
--
--   **Cost profiles.** With $w(n,d)=\lceil n^2/d^{1+\delta}\rceil$,
--
--   $$\mathrm{APSP}:\ d^\delta\, n\, M\bigl(n,\lceil d^{4+2\delta}\rceil,n,w\bigr)+\frac{n^3}{d^\delta},\qquad \mathrm{3SUM}:\ d^\delta\, M\bigl(n,\lceil d^{12+2\delta}\rceil,n,w\bigr)+\frac{n^2}{d^\delta},$$
--
--   and the soft-O factor is $(1+\log(n+1))^e$. Real APSP input is integer cells $n,d$ and the presence flags of the weight matrix, with its real weights in the real bank, as in the published Real APSP definitions.
--
--   These objects state Theorems 4.8 and 5.9 as conditional reductions to an actual selected-entries solver.
--
--   **Formalization Note** Real exponents are rounded up to naturals. Since $d\ge1$, the budget $w$ never exceeds $n^2$.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), §1 (definition of M_selected-entries(n,d,n|w)), pp.1–2; Theorem 4.8 and Lemma 4.7, pp.16–17; §5 and Theorem 5.9, pp.17–21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Mathlib
import Definitions.Def_RealAPSP_Problems

namespace SelectedSubset3SUM.Integer.Supplement

/-! Chan--Itakura--Ma--Yu, STOC 2027 submission #1421 (October 2026), §1 pp.1--2 and §§4--5,
pp.14--21. Selected-entries matrix multiplication, the deterministic run interface of the
real reductions, and Real 3SUM. Machine: the published comparison--addition RAM
`RealAPSP.Program` (word RAM with integer bank, real bank with `0`, `+`, negation, copy,
load/store and comparison; unit cost; `RealAPSP.Runs` is a run on the all-false coin tape,
i.e. deterministic). -/

/-- The `(i,j)` entry of the product `XY` of an `a × D` and a `D × b` zero--one matrix:
the number of `k` with `X[i,k] = Y[k,j] = 1` (triangle count through `(i,j)`). -/
def selProduct {a D b : ℕ} (X : Fin a → Fin D → Bool) (Y : Fin D → Fin b → Bool)
    (i : Fin a) (j : Fin b) : ℤ :=
  ∑ k, if X i k && Y k j then 1 else 0

/-- Integer input of a selected-entries instance: `a, D, b, w`, then `X` and `Y` row-major
as `0/1`, then the `w` wanted pairs `(i,j)` (repetitions allowed). -/
def selInts {a D b : ℕ} (X : Fin a → Fin D → Bool) (Y : Fin D → Fin b → Bool)
    (wanted : List (Fin a × Fin b)) : List ℤ :=
  [(a : ℤ), (D : ℤ), (b : ℤ), (wanted.length : ℤ)] ++
    RealAPSP.rowMajor (fun i k => if X i k then (1 : ℤ) else 0) ++
    RealAPSP.rowMajor (fun k j => if Y k j then (1 : ℤ) else 0) ++
    wanted.flatMap fun p => [((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)]

/-- The word-size parameter of a selected-entries instance. -/
def selWidth (a D b w : ℕ) : ℕ := a + D + b + w + 2

/-- Output: integer output cell `l` holds `(XY)[i_l, j_l]` for the `l`-th wanted pair. -/
def SelOutput {a D b : ℕ} (X : Fin a → Fin D → Bool) (Y : Fin D → Fin b → Bool)
    (wanted : List (Fin a × Fin b)) (σ : RealAPSP.State) : Prop :=
  ∀ l : Fin wanted.length,
    σ.imem (RealAPSP.outCell l) = selProduct X Y (wanted.get l).1 (wanted.get l).2

/-- `M_selected-entries(a, D, b | w) ≤ M a D b w` up to a constant: one deterministic program
computes the `w` wanted entries of every `a × D` by `D × b` zero--one product within
`K · M(a,D,b,w)` steps, and the presentation of its dense input is also within that budget. -/
def SelectedEntriesSolver (M : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ (S : RealAPSP.Program) (K : ℝ), 0 < K ∧
    ∀ (a D b : ℕ) (X : Fin a → Fin D → Bool) (Y : Fin D → Fin b → Bool)
      (wanted : List (Fin a × Fin b)),
      ((selInts X Y wanted).length : ℝ) ≤ K * M a D b wanted.length ∧
      RealAPSP.Runs S (selWidth a D b wanted.length) (selInts X Y wanted) []
        (K * M a D b wanted.length) (SelOutput X Y wanted)

/-- The soft-O factor `(1 + log(n+1))^e`. -/
noncomputable def softLog (n e : ℕ) : ℝ := (1 + Real.log ((n : ℝ) + 1)) ^ e

/-- The wanted-entry budget `⌈n² / d^{1+δ}⌉`. -/
noncomputable def wantedBudget (δ : ℝ) (n d : ℕ) : ℕ := ⌈(n : ℝ) ^ 2 / (d : ℝ) ^ (1 + δ)⌉₊

/-- `d^δ n M(n, ⌈d^{4+2δ}⌉, n | ⌈n²/d^{1+δ}⌉) + n³/d^δ` (Theorem 4.8). -/
noncomputable def apspCost (M : ℕ → ℕ → ℕ → ℕ → ℝ) (δ : ℝ) (n d : ℕ) : ℝ :=
  (d : ℝ) ^ δ * n * M n ⌈(d : ℝ) ^ (4 + 2 * δ)⌉₊ n (wantedBudget δ n d) +
    (n : ℝ) ^ 3 / (d : ℝ) ^ δ

/-- `d^δ M(n, ⌈d^{12+2δ}⌉, n | ⌈n²/d^{1+δ}⌉) + n²/d^δ` (Theorem 5.9). -/
noncomputable def threeSumCost (M : ℕ → ℕ → ℕ → ℕ → ℝ) (δ : ℝ) (n d : ℕ) : ℝ :=
  (d : ℝ) ^ δ * M n ⌈(d : ℝ) ^ (12 + 2 * δ)⌉₊ n (wantedBudget δ n d) +
    (n : ℝ) ^ 2 / (d : ℝ) ^ δ

/-- Real 3SUM input: integer cells `n, d, |A|, |B|, |C|`; real cells `A`, then `B`, then `C`. -/
def threeSumInts (n d : ℕ) (A B C : List ℝ) : List ℤ :=
  [(n : ℤ), (d : ℤ), (A.length : ℤ), (B.length : ℤ), (C.length : ℤ)]

def threeSumReals (A B C : List ℝ) : List ℝ := A ++ B ++ C

/-- The answer of Real 3SUM: some `c ∈ C` equals `a + b` with `a ∈ A`, `b ∈ B`. -/
def ThreeSumYes (A B C : List ℝ) : Prop := ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b = c

/-- Output of Real 3SUM: integer output cell `0` is `1` on a yes-instance and `0` otherwise. -/
def ThreeSumOutput (A B C : List ℝ) (σ : RealAPSP.State) : Prop :=
  (ThreeSumYes A B C → σ.imem (RealAPSP.outCell 0) = 1) ∧
  (¬ ThreeSumYes A B C → σ.imem (RealAPSP.outCell 0) = 0)

/-- Real APSP input: integer cells `n, d`, then the presence flags of `w` row-major. -/
def apspInts {n : ℕ} (d : ℕ) (w : RealAPSP.Mat ℝ n) : List ℤ :=
  [(n : ℤ), (d : ℤ)] ++ RealAPSP.flagCells w

end SelectedSubset3SUM.Integer.Supplement


