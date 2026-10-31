-- Prove2me | Definitions.Def_SinkhornHall_Model
-- name    : SinkhornHall_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:27.76629+00:00
-- url     : https://prove2.me/theorems/1424e523-9497-4f83-b52e-679f59d6f8e5
-- title:
--   Matrix scaling model: $\Gamma$, stable sets, Hall blockers, $R(y)$, $C(x)$, the Sinkhorn iteration and step 2
-- statement:
--   Let $A=(A_{ij})$ be a nonnegative real matrix with rows indexed by a finite set $I$ and columns by a finite set $J$. Its **support graph** $G(A)$ is the bipartite graph joining row $i$ and column $j$ exactly when $A_{ij}>0$. This bundle defines the combinatorial and algorithmic objects of the paper.
--
--   1. **Neighbourhood.** For a set of rows $X$, $\Gamma(X)=\{j : A_{ij}>0 \text{ for some } i\in X\}$.
--   2. **Stable sets.** $X\sqcup Y$ (rows $X$, columns $Y$) is stable if $A_{ij}=0$ for all $i\in X$, $j\in Y$.
--   3. **Hall blocker** (marginals $(r,c)=(\mathbf 1,\mathbf 1)$): a set of rows $X$ with $|\Gamma(X)|<|X|$.
--   4. **Counts and extreme entries.** $m$ is the number of positive entries of $A$ (called `numEdges`), $A_{\min}$ the least positive entry and $A_{\max}$ the largest entry.
--   5. **Normalization vectors.** For marginals $r$, $c$:
--   $$R(y)_i=\frac{r_i}{\sum_j A_{ij}y_j},\qquad C(x)_j=\frac{c_j}{\sum_i A_{ij}x_i}.$$
--   6. **Approximate $(r,c)$-scalability.** For every $\varepsilon>0$ there are positive vectors $x,y$ such that the scaled matrix $\tilde A_{ij}=A_{ij}x_iy_j$ satisfies $\|\tilde A\mathbf 1-r\|_1+\|\tilde A^\top\mathbf 1-c\|_1<\varepsilon$.
--   7. **Perfect matching** of a square matrix $A\in\mathbb R^{n\times n}$: a permutation $\sigma$ with $A_{i\sigma(i)}>0$ for every $i$.
--   8. **The Sinkhorn vector iteration** of §4.1 with $(r,c)=(\mathbf 1,\mathbf 1)$: step 0 sets $x=\mathbf 1$, $y=C(\mathbf 1)$; each repetition of step 1 sets $x\leftarrow R(y)$, then $y\leftarrow C(x)$. The pair after $\ell$ repetitions is $(x^{(\ell)},y^{(\ell)})$.
--   9. **Step 2 outputs.** For $x,y\in\mathbb R^n$, a set $X$ is an output of step 2 if, for some orderings $x_{i_1}\ge\dots\ge x_{i_n}$ and $y_{j_1}\le\dots\le y_{j_n}$ and some $k^*$ with
--   $$(x_{i_{k^*}}y_{j_{k^*}})^n\ \ge\ x_1\cdots x_n\,y_1\cdots y_n,$$
--   one has $X=\{i_1,\dots,i_{k^*}\}$.
--
--   These objects are shared by every statement of the mission: the goal theorem speaks only about the Sinkhorn iteration, step 2 and Hall blockers.
--
--   **Formalization Note** Indices are finite types (`Fin n` in the square setting, 0-based, so $k^*$ becomes `k = k* − 1` and the output is `σ '' {0, …, k}`). Step 2 is a relation, not a function: it records every tie-break of the two sorts and every admissible $k^*$. $A_{\min}$ and $A_{\max}$ are the real `sInf`/`sSup` of finite sets, which are the minimum and maximum whenever the sets are nonempty, as they are under the hypotheses of every statement. Divisions in $R(y)$, $C(x)$ have positive denominators under those hypotheses.
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, §2 pp.4–6 (scalings, stable sets, (2.1) Γ, Hall blocker, R(y), C(x), approximate scalability); Corollary 2.6 p.7 (A_min); §4 and §4.1 p.15 (A_max, m, perfect matching, Algorithm: Sinkhorn & Sorting Scaling Vectors, steps 0–2)

import Mathlib

open Finset

namespace SinkhornHall

/-!
Model of Hayashi–Hirai–Sakabe, *Finding Hall blockers by matrix scaling*, arXiv:2204.07425v2
(§1 Notation p.4, §2 pp.4–6, §4 and §4.1 p.15): the support graph of a nonnegative matrix, stable
sets, the neighbourhood map `Γ`, Hall blockers, perfect matchings of the support, `A_min`, `A_max`,
the number of nonzero entries, the row/column normalization vectors `R(y)`, `C(x)`, approximate
`(r, c)`-scalability, the Sinkhorn vector iteration of §4.1 and the step-2 output relation.
-/

section General

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

open Classical in
/-- **The neighbourhood map `Γ`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, (2.1), p.5:
"Γ(X) := {j ∈ [m] | j is adjacent to a node in X in G(A)}", where `G(A)` joins row `i` and column
`j` iff `A_ij > 0` (p.5).

`Gamma A X` is the set of columns `j` with `0 < A i j` for some row `i ∈ X`.

**Formalization Note.** Rows and columns are finite types `ι`, `κ` (the paper's `[n]`, `[m]`).
Adjacency is through *positive* entries only; a zero entry is not an edge. -/
noncomputable def Gamma (A : Matrix ι κ ℝ) (X : Finset ι) : Finset κ :=
  Finset.univ.filter (fun j => ∃ i ∈ X, 0 < A i j)

/-- **Stable sets of the support graph `G(A)`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.5: "A subset X ⊔ Y of vertices is said to be
stable if there is no edge ij with i ∈ X and j ∈ Y."

`IsStable A X Y` says that `A i j > 0` for no row `i ∈ X` and column `j ∈ Y`. -/
def IsStable (A : Matrix ι κ ℝ) (X : Finset ι) (Y : Finset κ) : Prop :=
  ∀ i ∈ X, ∀ j ∈ Y, ¬ 0 < A i j

/-- **Hall blocker** (for the marginals `(r, c) = (1, 1)` of §4).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.5 ("A subset X violating this condition
[r(X) ≤ c(Γ(X))] … is also called a Hall blocker"), specialised to `(r, c) = (1, 1)` as in §4
(p.15) and the abstract ("a vertex subset X having neighbors Γ(X) with |X| > |Γ(X)|").

`IsHallBlocker A X` says `|Γ(X)| < |X|` for the row set `X`. -/
def IsHallBlocker (A : Matrix ι κ ℝ) (X : Finset ι) : Prop :=
  (Gamma A X).card < X.card

open Classical in
/-- **Number of nonzero entries `m` of §4.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4, p.15: "m by the number of nonzero elements of A
(the number of edges of G)".

`numEdges A` is the number of pairs `(i, j)` with `0 < A i j`.

**Formalization Note.** Named `numEdges` because §2 uses `m` for the number of columns. For a
nonnegative matrix the nonzero entries are exactly the positive ones. -/
noncomputable def numEdges (A : Matrix ι κ ℝ) : ℕ :=
  (Finset.univ.filter (fun p : ι × κ => 0 < A p.1 p.2)).card

/-- **`A_min`, the least positive entry.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Corollary 2.6, p.7: "Let A_min := min{A_ij | i, j :
A_ij > 0}".

**Formalization Note.** Written as the real `sInf` of the finite set of positive entries, which is
its minimum whenever `A` has a positive entry (every statement of the mission assumes this, through
"no zero row" and a nonempty row set). On a matrix with no positive entry Lean's `sInf ∅ = 0`;
no statement relies on that value. -/
noncomputable def Amin (A : Matrix ι κ ℝ) : ℝ :=
  sInf {a : ℝ | ∃ i j, 0 < A i j ∧ A i j = a}

/-- **`A_max`, the largest entry.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4, p.15: "define A_max by the maximum of entries A_ij
of A".

**Formalization Note.** The real `sSup` of the finite set of entries, i.e. its maximum when the
matrix has at least one entry; for an empty matrix Lean's `sSup ∅ = 0`, a case excluded by every
statement that uses `Amax`. -/
noncomputable def Amax (A : Matrix ι κ ℝ) : ℝ :=
  sSup {a : ℝ | ∃ i j, A i j = a}

/-- **Row-normalization vector `R(y)`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.6: "The row-normalization vector R(y) ∈ ℝⁿ
relative to column-scaling vector y is defined by R(y)_i := r_i / Σ_j A_ij y_j."

**Formalization Note.** For a nonnegative `A` without zero rows and a positive `y` the denominator
is positive; Lean's `x / 0 = 0` is never reached under the hypotheses of the mission's
statements. -/
noncomputable def rowNorm (A : Matrix ι κ ℝ) (r : ι → ℝ) (y : κ → ℝ) : ι → ℝ :=
  fun i => r i / ∑ j, A i j * y j

/-- **Column-normalization vector `C(x)`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, p.6: "The column-normalization vector C(x) ∈ ℝᵐ
relative to row-scaling vector x is defined by C(x)_j := c_j / Σ_i A_ij x_i."

**Formalization Note.** As for `rowNorm`: the denominator is positive for a nonnegative `A`
without zero columns and a positive `x`. -/
noncomputable def colNorm (A : Matrix ι κ ℝ) (c : κ → ℝ) (x : ι → ℝ) : κ → ℝ :=
  fun j => c j / ∑ i, A i j * x i

/-- **Approximate `(r, c)`-scalability.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2, pp.4–5: "If there is a scaling Ã of A such that
(Ã1, Ã⊤1) is arbitrarily close (r, c) (under some norm of ℝ^{n+m}), then A is approximately
(r, c)-scalable", where a scaling is `Ã_ij = A_ij x_i y_j` for positive vectors `x`, `y` (p.4).

`ApproxScalable A r c`: for every `ε > 0` there are positive `x`, `y` with
`Σ_i |(Ã1)_i − r_i| + Σ_j |(Ã⊤1)_j − c_j| < ε`.

**Formalization Note.** The paper allows "some norm of ℝ^{n+m}"; all norms on a finite-dimensional
space are equivalent, and the `ℓ₁` norm is used, as in Lemma 2.2. -/
def ApproxScalable (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (x : ι → ℝ) (y : κ → ℝ), (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
    (∑ i, |(∑ j, A i j * x i * y j) - r i|) + (∑ j, |(∑ i, A i j * x i * y j) - c j|) < ε

end General

section Square

variable {n : ℕ}

/-- **Perfect matching of the support graph `G(A)`** of a square matrix.
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4, p.15 ("G has a perfect matching"), with `G = G(A)`
and `n := |U| = |V|`.

`HasPerfectMatching A` says there is a permutation `σ` of `Fin n` with `0 < A i (σ i)` for every
row `i`.

**Formalization Note.** The two colour classes both have `n` elements, so a perfect matching is a
bijection from rows to columns along edges, i.e. a permutation along positive entries. -/
def HasPerfectMatching (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i, 0 < A i (σ i)

/-- **The Sinkhorn vector iteration of §4.1, steps 0 and 1.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4.1, Algorithm: Sinkhorn & Sorting Scaling Vectors,
p.15: "0: Let x = y := 1, and let y ← C(x). 1: Repeat row- and column-normalization ℓ times:
x ← R(y), y ← C(x)." Here `(r, c) := (1, 1)` (§4, p.15).

`sinkhorn A ℓ` is the pair `(x, y)` after step 0 followed by `ℓ` repetitions of step 1:
`sinkhorn A 0 = (1, C(1))` and `sinkhorn A (ℓ + 1) = (x', C(x'))` with `x' = R(y)` for
`(x, y) = sinkhorn A ℓ`.

**Formalization Note.** `ℓ = 0` is the state right after step 0. Row and column indices are
`Fin n` (0-based). -/
noncomputable def sinkhorn (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => (1, colNorm A 1 1)
  | ℓ + 1 =>
      let x' := rowNorm A 1 (sinkhorn A ℓ).2
      (x', colNorm A 1 x')

/-- **Admissible outputs of step 2 of the algorithm.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4.1, Algorithm: Sinkhorn & Sorting Scaling Vectors,
step 2, p.15: "Sort x, y as x_{i₁} ≥ x_{i₂} ≥ ⋯ ≥ x_{iₙ}, y_{j₁} ≤ y_{j₂} ≤ ⋯ ≤ y_{jₙ}. Choose
index k* such that (x_{i_{k*}} y_{j_{k*}})ⁿ ≥ x₁x₂⋯xₙy₁y₂⋯yₙ. Output {i₁, …, i_{k*}}."

`IsStep2Output x y X` holds iff there are permutations `σ`, `τ` of `Fin n` and `k : Fin n` with
`x ∘ σ` antitone (`i_t = σ (t − 1)`), `y ∘ τ` monotone (`j_t = τ (t − 1)`),
`∏ x · ∏ y ≤ (x (σ k) · y (τ k))ⁿ`, and `X = σ '' {0, …, k}`.

**Formalization Note.** Step 2 leaves the tie-breaking of both sorts and the choice of `k*` open;
this relation records every admissible choice. Indices are 0-based: `k = k* − 1`, so the output
`σ '' {0, …, k}` has `k*` elements. -/
def IsStep2Output (x y : Fin n → ℝ) (X : Finset (Fin n)) : Prop :=
  ∃ (σ τ : Equiv.Perm (Fin n)) (k : Fin n),
    Antitone (x ∘ σ) ∧ Monotone (y ∘ τ) ∧
    (∏ i, x i) * (∏ j, y j) ≤ (x (σ k) * y (τ k)) ^ n ∧
    X = (Finset.univ.filter (fun t : Fin n => t ≤ k)).image σ

end Square

end SinkhornHall


