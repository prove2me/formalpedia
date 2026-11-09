-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit
-- name    : SubsetSumPartialMatch_SubsetSum_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:14.210288+00:00
-- url     : https://prove2.me/theorems/4912d729-f01a-41c9-a43a-6a516d8c71d3
-- title:
--   Depth-2 linear circuits, colored volume and the exponent region $K(s)$
-- statement:
--   A **depth-2 linear circuit** $C=(L_C,R_C)$ from input gates $I$ to output gates $J$ is a finite set of middle gates with integer matrices $L_C$ (rows $I$, columns the middle gates) and $R_C$ (rows the middle gates, columns $J$). It is an **EXACT$_\mathbb Z$ circuit** for $M$ if $L_CR_C=M$ over the integers; coefficients may be negative and cancellations are allowed. The degree $\deg_L(C,x)$ counts the nonzero entries of row $x$ of $L_C$, $\deg_R(C,y)$ the nonzero entries of column $y$ of $R_C$, and $\deg_L(C)$, $\deg_R(C)$ are their maxima.
--
--   A **coloring** assigns a color to every middle gate. The part $C_\zeta$ retains all input and output gates and just the middle gates of color $\zeta$. The **$t$-colored volume** is
--   $$\rho_C(t)=\sum_{\zeta}\deg_L(C_\zeta)^t\,\deg_R(C_\zeta)^{1-t},$$
--   summed over the colors in use. The Kronecker power $M^{\otimes d}$ is indexed by $d$-tuples, with entry $\prod_i M_{x_i,y_i}$.
--
--   $K(s)$ consists of the pairs $(l,r)$ with $l,r\ge0$ such that for every $\varepsilon>0$, every sufficiently large $n$ has an EXACT$_\mathbb Z$ circuit for $P_{n,s}$ with degrees at most $2^{(l+\varepsilon)n}$ and $2^{(r+\varepsilon)n}$.
--
--   For Lemma 3.7: $\mathcal Y_B$ is the set of queries with $|S(y)|=k/2$ such that $S(y)\setminus B$ contains exactly $ak$ positions with $y_i=1$ and exactly $ak$ positions with $y_i=0$; $x\oplus z$ is bitwise XOR; and the expectation over $z$ is the uniform average over the $z\in\{0,1\}^k$ vanishing on $B$. Lists of edges are written for the machine as a middle-gate name followed by its coefficient.
--
--   **Formalization Note** The middle-gate set is any finite type. In Lean $0^0=1$, so $\rho_C(0)$ and $\rho_C(1)$ are exactly the sums of the right and of the left degrees of the color classes, as the source says on p. 21; a color class with a zero degree contributes $0$ for $0<t<1$. The set $\mathcal Y_B$ may be empty.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 15 (§3.1), p. 16 (definition of $K(s)$), p. 18 (colorings), p. 21 (colored volume), p. 23 (definition of $\mathcal Y_B$)

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_PartialMatch

namespace SubsetSumPartialMatch.SubsetSum

/-- A depth-2 linear circuit `C = (L_C, R_C)` over the integers: a finite set of middle gates, a
matrix from the input gates `I` to them and a matrix from them to the output gates `J`. -/
structure LinCircuit (I J : Type) where
  Mid : Type
  midFintype : Fintype Mid
  L : Matrix I Mid ℤ
  R : Matrix Mid J ℤ

attribute [instance] LinCircuit.midFintype

namespace LinCircuit

variable {I J : Type}

/-- `C` is an EXACT_Z circuit for `M`: `L_C R_C = M` over the integers. -/
def Computes (C : LinCircuit I J) (M : Matrix I J ℤ) : Prop := C.L * C.R = M

/-- `deg_L(C, x)`: the number of edges at input gate `x`. -/
def degLAt (C : LinCircuit I J) (x : I) : ℕ :=
  (Finset.univ.filter fun e => C.L x e ≠ 0).card

/-- `deg_R(C, y)`: the number of edges at output gate `y`. -/
def degRAt (C : LinCircuit I J) (y : J) : ℕ :=
  (Finset.univ.filter fun e => C.R e y ≠ 0).card

/-- `deg_L(C)`: the maximum of `deg_L(C, x)` over the input gates. -/
def degL [Fintype I] (C : LinCircuit I J) : ℕ := Finset.univ.sup C.degLAt

/-- `deg_R(C)`: the maximum of `deg_R(C, y)` over the output gates. -/
def degR [Fintype J] (C : LinCircuit I J) : ℕ := Finset.univ.sup C.degRAt

end LinCircuit

/-- The Kronecker power `M^{⊗d}`, indexed by `d`-tuples of rows and of columns. -/
def tensorPow {I J : Type} (M : Matrix I J ℤ) (d : ℕ) : Matrix (Fin d → I) (Fin d → J) ℤ :=
  fun x y => ∏ i, M (x i) (y i)

/-- A colored circuit: a depth-2 linear circuit with a color in `Z` on every middle gate. -/
structure ColoredCircuit (I J Z : Type) extends LinCircuit I J where
  color : Mid → Z

namespace ColoredCircuit

variable {I J Z : Type}

open Classical in
/-- The colors in use. -/
noncomputable def colors (C : ColoredCircuit I J Z) : Finset Z := Finset.univ.image C.color

open Classical in
/-- `C_ζ`: all input and output gates, and just the middle gates of color `ζ`. -/
noncomputable def part (C : ColoredCircuit I J Z) (ζ : Z) : LinCircuit I J where
  Mid := {e : C.Mid // C.color e = ζ}
  midFintype := inferInstance
  L := fun x e => C.L x e.1
  R := fun e y => C.R e.1 y

/-- All middle gates have one color. -/
def SingleColored (C : ColoredCircuit I J Z) : Prop :=
  ∀ e f : C.Mid, C.color e = C.color f

/-- The `t`-colored volume `ρ_C(t) = ∑_ζ deg_L(C_ζ)^t deg_R(C_ζ)^{1-t}`. In Lean `0 ^ 0 = 1`,
so `ρ_C(1)` and `ρ_C(0)` are exactly the sums of the left and of the right degrees of the color
classes, as the source says. -/
noncomputable def volume [Fintype I] [Fintype J] (C : ColoredCircuit I J Z) (t : ℝ) : ℝ :=
  ∑ ζ ∈ C.colors, ((C.part ζ).degL : ℝ) ^ t * ((C.part ζ).degR : ℝ) ^ (1 - t)

end ColoredCircuit

/-- `K(s)`: the pairs `(l, r)` with `l, r ≥ 0` such that for every `ε > 0` every sufficiently large
`n` has an EXACT_Z circuit for `P_{n,s}` with degrees at most `2^{(l+ε)n}` and `2^{(r+ε)n}`. -/
def K (s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    ∃ C : LinCircuit (BinStr n) (PMCol n s), C.Computes (pm n s) ∧
      (C.degL : ℝ) ≤ (2 : ℝ) ^ ((p.1 + ε) * n) ∧ (C.degR : ℝ) ≤ (2 : ℝ) ^ ((p.2 + ε) * n)}

/-- A list of edges at one gate as machine words: each edge is the name of its middle gate
followed by its coefficient. -/
def edgeWords {M : Type} (name : M → ℤ) (coef : M → ℤ) (es : List M) : List ℤ :=
  es.flatMap fun e => [name e, coef e]

/-- `Y_B`: the queries `y` with `|S(y)| = k/2` such that `S(y) ∖ B` contains exactly `ak` positions
with `y_i = 1` and exactly `ak` positions with `y_i = 0`. -/
def structuredCols (k : ℕ) (a : ℝ) (B : Finset (Fin k)) : Set (QueryStr k) :=
  {y | 2 * (specified y).card = k ∧
    ((Finset.univ.filter fun i => i ∉ B ∧ y i = some true).card : ℝ) = a * k ∧
    ((Finset.univ.filter fun i => i ∉ B ∧ y i = some false).card : ℝ) = a * k}

noncomputable instance (k : ℕ) (S : Set (QueryStr k)) : Fintype S := Fintype.ofFinite S

/-- The restriction of `P_1^{⊗k}` to a set of columns. -/
def pmRestrict {k : ℕ} (S : Set (QueryStr k)) : Matrix (BinStr k) S ℤ :=
  fun x y => pmEntry x y.1

/-- The bitwise XOR `x ⊕ z`. -/
def xorStr {k : ℕ} (x z : BinStr k) : BinStr k := fun i => xor (x i) (z i)

/-- The expectation of `f(z)` for `z ∈ {0,1}^k` uniform subject to `z_i = 0` for all `i ∈ B`. -/
noncomputable def offAverage {k : ℕ} (B : Finset (Fin k)) (f : BinStr k → ℝ) : ℝ :=
  (∑ z ∈ Finset.univ.filter (fun z : BinStr k => ∀ i ∈ B, z i = false), f z) /
    ((Finset.univ.filter fun z : BinStr k => ∀ i ∈ B, z i = false).card : ℝ)

end SubsetSumPartialMatch.SubsetSum


