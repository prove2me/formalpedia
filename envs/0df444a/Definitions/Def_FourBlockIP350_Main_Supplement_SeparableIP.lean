-- Prove2me | Definitions.Def_FourBlockIP350_Main_Supplement_SeparableIP
-- name    : FourBlockIP350_Main_Supplement_SeparableIP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:07.527519+00:00
-- url     : https://prove2.me/theorems/97300a66-a89f-4ed1-a868-94545d7e94ce
-- title:
--   Separable convex 4-block integer programs given by a comparison oracle, $F_K$ and $H_{K,r}$
-- statement:
--   This file defines the separable convex 4-block integer program of Appendix B and the objects used in its analysis. The constraint data are those of the mission's 4-block instance $I$: block dimension $k$, $n$ bricks, the matrix $\begin{pmatrix} Z & E\end{pmatrix}$ with nonuniform blocks, the right-hand side $b$ and the variable bounds $\ell\le u$. A point is $z=(x,y)$ with global part $x\in\mathbb Z^k$ and local part $y\in\mathbb Z^{nk}$.
--
--   1. **Objective.** Given functions $\phi_j:\mathbb R\to\mathbb R$, one per coordinate $j$ of $z$,
--   $$\Phi(z)=\sum_{j}\phi_j(z_j)=\Phi^{(0)}(x)+\sum_{i=1}^n\Phi^{(i)}(y^{(i)}).$$
--   The objective is **separable convex** when every $\phi_j$ is convex on all of $\mathbb R$; it is finite-valued by construction.
--   2. **Comparison oracle.** A map $O$ on bit words is a comparison oracle for $\Phi$ if, for all integer points $z,z'\in\mathbb Z^{(n+1)k}$ (inside or outside the bounds), on the word $\operatorname{enc}(z,z')$ it answers which of $\Phi(z)<\Phi(z')$, $\Phi(z)=\Phi(z')$, $\Phi(z)>\Phi(z')$ holds.
--   3. **Instance length.** $|I|$ is the binary length of $k$, $n$, the full constraint matrix, $b$ and the bounds. The objective is not input data; it is accessible only through the oracle. The linear cost vector carried by the mission's instance structure is not part of this encoding and plays no role.
--   4. **Residual and lexicographic witnesses.** $\|b-Zx-Ey\|_1$ is the residual norm. With $Y=\{y\in\mathbb Z^{nk}:\ell^{(1:n)}\le y\le u^{(1:n)}\}$ and
--   $$r(x)=\min_{y\in Y}\|b-Zx-Ey\|_1,\qquad (B.1)$$
--   a vector $y_x$ is a lexicographic witness for $x$ if $y_x\in Y$ attains $r(x)$ and minimizes $\Phi(x,\cdot)$ among the vectors of $Y$ attaining $r(x)$ (B.2). Pairs $(r,p)$ are compared lexicographically, the integer first.
--   5. **Penalized value function.** For real $K$,
--   $$F_K(x)=\min_{y\in Y}\{\Phi(x,y)+K\|b-Zx-Ey\|_1\},\qquad x\in\mathbb Z^k,\qquad (B.5)$$
--   taken as an infimum in the extended reals (so it is $+\infty$ if $Y$ is empty), and $H_{K,r}(v)=F_K(r+Nv)$ as a real number.
--   6. **Congruence and answers.** $x\equiv q\pmod M$ coordinatewise. An answer is either an integer point or "infeasible"; it is **correct** if the point satisfies all equations and bounds and $\Phi$ at it is at most $\Phi$ at every feasible point, or if no feasible integer point exists. There is no unbounded outcome: the bounds are finite.
--
--   These are the shared objects of Lemmas B.3–B.7 and Theorem B.2.
--
--   **Formalization Note** The instance reuses the published `FourBlock` structure, its residual $b-Zx-Ey$, the boxes and the period $M=kN$; its cost vector $c$ is ignored. $F_K$ is an `EReal` infimum, so no default value of a real infimum is used; statements that need a real number assert finiteness explicitly.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), pp. 21–24, §B.1 (4-Block IP), comparison oracle O_Φ, Y, Eqs. (B.1), (B.2), (B.5), (B.6), Lemma B.5

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BinaryEncoding
import Definitions.Def_FourBlockIP350_Main_Penalty

namespace FourBlockIP350.Main.Supplement

open FourBlockIP350.Main
open scoped BigOperators

/-- The separable objective of (4-Block IP), p. 21:
`Φ(z) = Σ_j φ_j(z_j)` over all `(n+1)k` global and local coordinates. -/
noncomputable def Phi {k n : ℕ} (φ : BlockCol k n → ℝ → ℝ) (z : BlockCol k n → ℤ) : ℝ :=
  ∑ j, φ j (z j : ℝ)

/-- Every component `φ_j : ℝ → ℝ` is convex on all of `ℝ` (finite-valued by its type). -/
def SeparableConvex {k n : ℕ} (φ : BlockCol k n → ℝ → ℝ) : Prop :=
  ∀ j, ConvexOn ℝ Set.univ (φ j)

/-- The query word `enc(z, z')` for two integer points of `ℤ^{(n+1)k}`. -/
def encQuery {k n : ℕ} (z z' : BlockCol k n → ℤ) : List Bool :=
  encVector (blockOrder k n) z ++ encVector (blockOrder k n) z'

/-- `O` is a comparison oracle for `Φ`: on the encoding of any two integer points (inside or
outside the bounds) it answers which of `Φ(z) < Φ(z')`, `=`, `>` holds. -/
def IsPhiOracle {k n : ℕ} (φ : BlockCol k n → ℝ → ℝ) (O : List Bool → Ordering) : Prop :=
  ∀ z z' : BlockCol k n → ℤ, O (encQuery z z') = compare (Phi φ z) (Phi φ z')

/-- `|I|` for (4-Block IP): `k`, `n`, the full constraint matrix, the right-hand side and the
bounds. The cost vector `c` of `FourBlock` is ignored; the objective is not input data. -/
def encConstraints {k n : ℕ} (I : FourBlock k n) : List Bool :=
  encNat k ++ encNat n ++
  encList encInt ((blockOrder k n).flatMap fun r =>
    (blockOrder k n).map fun j => I.program.matrix r j) ++
  encVector (blockOrder k n) I.b ++
  encList encEndpoint ((blockOrder k n).map I.lower) ++
  encList encEndpoint ((blockOrder k n).map I.upper)

/-- `‖b − Zx − Ey‖₁`. -/
def resNorm {k n : ℕ} (I : FourBlock k n) (x : ZVec k) (y : LocalCol k n → ℤ) : ℤ :=
  ∑ r, |residual I x y r|

/-- `y` is a vector `y_x` of (B.2): `y ∈ Y` attains `r(x)` of (B.1), and minimizes `Φ(x, ·)`
among the vectors of `Y` attaining `r(x)`. -/
def IsLexWitness {k n : ℕ} (I : FourBlock k n) (φ : BlockCol k n → ℝ → ℝ)
    (x : ZVec k) (y : LocalCol k n → ℤ) : Prop :=
  LocalBox I y ∧ (∀ y', LocalBox I y' → resNorm I x y ≤ resNorm I x y') ∧
  ∀ y', LocalBox I y' → resNorm I x y' = resNorm I x y →
    Phi φ (joinPoint x y) ≤ Phi φ (joinPoint x y')

/-- Lexicographic order on pairs (integer residual, real objective). -/
def LexLE (r₁ : ℤ) (p₁ : ℝ) (r₂ : ℤ) (p₂ : ℝ) : Prop :=
  r₁ < r₂ ∨ (r₁ = r₂ ∧ p₁ ≤ p₂)

/-- Lexicographic three-way comparison of `(r₁, p₁)` and `(r₂, p₂)`. -/
noncomputable def lexCompare (r₁ : ℤ) (p₁ : ℝ) (r₂ : ℤ) (p₂ : ℝ) : Ordering :=
  if r₁ < r₂ then .lt else if r₂ < r₁ then .gt else compare p₁ p₂

def encOrdering : Ordering → List Bool
  | .lt => [false, false]
  | .eq => [false, true]
  | .gt => [true, false]

/-- (B.5): `F_K(x) = min_{y ∈ Y} {Φ(x, y) + K‖b − Zx − Ey‖₁}`, as an infimum in `EReal`
(`⊤` if `Y` is empty). -/
noncomputable def FK {k n : ℕ} (I : FourBlock k n) (φ : BlockCol k n → ℝ → ℝ) (K : ℝ)
    (x : ZVec k) : EReal :=
  sInf {v | ∃ y, LocalBox I y ∧
    v = ((Phi φ (joinPoint x y) + K * (resNorm I x y : ℝ) : ℝ) : EReal)}

/-- `H_{K,r}(v) = F_K(r + N v)` (Lemma B.5), as a real number. -/
noncomputable def HK {k n : ℕ} (I : FourBlock k n) (φ : BlockCol k n → ℝ → ℝ) (K : ℝ)
    (N : ℕ) (r v : ZVec k) : ℝ :=
  (FK I φ K (r + (N : ℤ) • v)).toReal

/-- `x ≡ q (mod M)` coordinatewise. -/
def CongrMod {k : ℕ} (M : ℕ) (x q : ZVec k) : Prop :=
  ∀ j, x j ≡ q j [ZMOD (M : ℤ)]

/-- Outcomes of Theorem B.2 (finite bounds: no unbounded outcome). -/
inductive SepAnswer (V : Type)
  | optimum (point : V → ℤ)
  | infeasible

def encSepAnswer {V : Type} (order : List V) : SepAnswer V → List Bool
  | .infeasible => [false]
  | .optimum z => true :: encVector order z

/-- A correct answer: an optimal integral solution for `Φ`, or a correct infeasibility report. -/
def SepCorrect {k n : ℕ} (I : FourBlock k n) (φ : BlockCol k n → ℝ → ℝ) :
    SepAnswer (BlockCol k n) → Prop
  | .optimum z => Feasible I.program z ∧ ∀ w, Feasible I.program w → Phi φ z ≤ Phi φ w
  | .infeasible => ¬ ∃ z, Feasible I.program z

end FourBlockIP350.Main.Supplement


