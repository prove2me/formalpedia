-- Prove2me | Definitions.Def_BBCode_Setting
-- name    : BBCode_Setting
-- status  : Definition
-- author  : @Winningatmath
-- created : 2026-10-16T17:57:18.554078+00:00
-- url     : https://prove2.me/theorems/85b13a18-c2e2-469a-a260-a017e5bd6f85
-- title:
--   Bivariate-bicycle codes: circulants, $H_X=[A\mid B]$, $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$, logicals and distances
-- statement:
--   Setting for bivariate-bicycle (BB) quantum codes.
--
--   Fix $l,m\ge1$ and $G=\mathbb Z_l\times\mathbb Z_m$. The monomial $x^iy^j$ of $\mathbb F_2[x,y]/(x^l-1,y^m-1)$ is $(i,j)\in G$, and a polynomial is the finite set of its monomials. The **circulant** of $P$ is the $G\times G$ binary matrix with entry $1$ at $(g,h)$ iff $h-g\in P$. For polynomials $A,B$ the code acts on $n=2lm$ qubits $G\sqcup G$ with
--   $$H_X=[\,A\mid B\,],\qquad H_Z=[\,B^{\mathsf T}\mid A^{\mathsf T}\,]$$
--   over $\mathbb F_2$.
--
--   1. A **nontrivial Z-logical** is $v\in\mathbb F_2^n$ with $H_Xv=0$ and $v\notin\operatorname{row}(H_Z)$; a **nontrivial X-logical** is $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$.
--   2. The **weight** $|v|$ is the number of nonzero coordinates.
--   3. The Z-distance (resp. X-distance) is exactly $d$ when some nontrivial Z-logical (X-logical) has weight $d$ and all have weight $\ge d$.
--   4. The code encodes $k$ logical qubits when $\operatorname{rank}H_X+\operatorname{rank}H_Z+k=n$.
--   5. `IsCode A B n k d` means $n=2lm$, $k$ logical qubits, and $d_X=d_Z=d$.
--   6. The **Tanner graph** joins each qubit to the X- and Z-checks with a $1$ in its column; the code is **connected** when this graph is connected.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** $k$ is stated additively to avoid truncated natural subtraction; each distance predicate includes the existence of a logical of weight exactly $d$, so it cannot hold vacuously.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, §2 'Setting and engines' (p. 2); conventions as in Bravyi et al., Nature 627, 778 (2024), Table 3, https://doi.org/10.1038/s41586-024-07107-7

import Mathlib

/-!
Bivariate-bicycle (BB) quantum codes, following §2 of Daugherty–Ryan–Ward,
"New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits"
(Zenodo 10.5281/zenodo.23382175, v1.0.0, 2026-10-14), and Bravyi et al.,
Nature 627, 778 (2024).
-/

namespace BBCode

open Matrix

/-- The group `ℤ_l × ℤ_m`. The monomial `x^i y^j` of `𝔽₂[x,y]/(x^l - 1, y^m - 1)` is the
element `(i, j)`. -/
abbrev Grp (l m : ℕ) := ZMod l × ZMod m

/-- A polynomial of `𝔽₂[x,y]/(x^l - 1, y^m - 1)`, given by its support: the finite set of
monomials `(i, j)` whose coefficient is `1`. -/
abbrev Poly (l m : ℕ) := Finset (Grp l m)

/-- The `lm × lm` circulant of a polynomial `P`: row `g` has a `1` in column `g + t`
for each monomial `t ∈ P`, and `0` elsewhere. -/
def circulant {l m : ℕ} (P : Poly l m) : Matrix (Grp l m) (Grp l m) (ZMod 2) :=
  fun g h => if h - g ∈ P then 1 else 0

/-- The physical qubits: two blocks of `lm` qubits, `n = 2lm` in total. -/
abbrev Qubit (l m : ℕ) := Grp l m ⊕ Grp l m

/-- The X-check matrix `H_X = [A | B]`. -/
def HX {l m : ℕ} (A B : Poly l m) : Matrix (Grp l m) (Qubit l m) (ZMod 2) :=
  Matrix.fromCols (circulant A) (circulant B)

/-- The Z-check matrix `H_Z = [Bᵀ | Aᵀ]`. -/
def HZ {l m : ℕ} (A B : Poly l m) : Matrix (Grp l m) (Qubit l m) (ZMod 2) :=
  Matrix.fromCols (circulant B)ᵀ (circulant A)ᵀ

/-- The row space of a binary matrix: the `𝔽₂`-span of its rows. -/
def rowSpace {r c : Type} (H : Matrix r c (ZMod 2)) : Submodule (ZMod 2) (c → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range H)

/-- The Hamming weight of a binary vector: the number of nonzero coordinates. -/
def weight {ι : Type} [Fintype ι] (v : ι → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

/-- A nontrivial Z-logical operator: `H_X v = 0` and `v ∉ row(H_Z)`. -/
def IsZLogical {l m : ℕ} [NeZero l] [NeZero m] (A B : Poly l m) (v : Qubit l m → ZMod 2) :
    Prop :=
  HX A B *ᵥ v = 0 ∧ v ∉ rowSpace (HZ A B)

/-- A nontrivial X-logical operator: `H_Z v = 0` and `v ∉ row(H_X)`. -/
def IsXLogical {l m : ℕ} [NeZero l] [NeZero m] (A B : Poly l m) (v : Qubit l m → ZMod 2) :
    Prop :=
  HZ A B *ᵥ v = 0 ∧ v ∉ rowSpace (HX A B)

/-- The Z-distance is exactly `d`: some nontrivial Z-logical has weight `d`, and every
nontrivial Z-logical has weight at least `d`. -/
def HasZDistance {l m : ℕ} [NeZero l] [NeZero m] (A B : Poly l m) (d : ℕ) : Prop :=
  (∃ v, IsZLogical A B v ∧ weight v = d) ∧ ∀ v, IsZLogical A B v → d ≤ weight v

/-- The X-distance is exactly `d`. -/
def HasXDistance {l m : ℕ} [NeZero l] [NeZero m] (A B : Poly l m) (d : ℕ) : Prop :=
  (∃ v, IsXLogical A B v ∧ weight v = d) ∧ ∀ v, IsXLogical A B v → d ≤ weight v

/-- The code encodes `k` logical qubits: `k = n - rank H_X - rank H_Z` with `n = 2lm`
(stated additively to avoid truncated subtraction). -/
def NumLogical {l m : ℕ} [NeZero l] [NeZero m] (A B : Poly l m) (k : ℕ) : Prop :=
  (HX A B).rank + (HZ A B).rank + k = 2 * (l * m)

/-- The BB code of `(A, B)` is an `[[n, k, d]]` code with `d_X = d_Z = d`. -/
def IsCode {l m : ℕ} [NeZero l] [NeZero m] (A B : Poly l m) (n k d : ℕ) : Prop :=
  n = 2 * (l * m) ∧ NumLogical A B k ∧ HasXDistance A B d ∧ HasZDistance A B d

/-- The Tanner graph: qubits are joined to the X- and Z-checks that act on them. -/
def tannerGraph {l m : ℕ} (A B : Poly l m) :
    SimpleGraph (Qubit l m ⊕ (Grp l m ⊕ Grp l m)) :=
  SimpleGraph.fromRel fun u w =>
    match u, w with
    | Sum.inl q, Sum.inr (Sum.inl c) => HX A B c q = 1
    | Sum.inl q, Sum.inr (Sum.inr c) => HZ A B c q = 1
    | _, _ => False

/-- A BB code is connected (indecomposable) when its Tanner graph is connected. -/
def IsConnected {l m : ℕ} (A B : Poly l m) : Prop :=
  (tannerGraph A B).Connected

end BBCode


