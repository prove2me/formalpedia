-- Prove2me | Definitions.Def_PQNormIPM1352_Main_Barrier
-- name    : PQNormIPM1352_Main_Barrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:17.367617+00:00
-- url     : https://prove2.me/theorems/f8ce152f-6359-4d0e-9985-5dc92350212f
-- title:
--   The conic program (5), its feasible set $K$, the barrier (6) and the data of Algorithm 1
-- statement:
--   Let $p \ge q > 1$ and let $A$ be given by a sparsity pattern with $s$ entries in an $m\times n$ matrix, with values $a \in \mathbb R^s$. Write $\alpha = 1/q^*$ and $\beta = 1/p$. A point of $\mathbb R^{m+n+s}$ is $x = (z, y, \gamma)$ with $z \in \mathbb R^m$, $y \in \mathbb R^n$ and $\gamma(k)$ the variable of the $k$-th entry $(i,j) = (\mathrm{row}(k), \mathrm{col}(k))$, written $\gamma(i,j)$.
--
--   1. The **feasible set** of program (5) is
--   $$K = \Big\{ (z,y,\gamma) : z \ge 0,\ y \ge 0,\ \sum_i z(i) \le 1,\ \sum_j y(j) \le 1,\ |\gamma(i,j)| \le z(i)^{1/q^*} y(j)^{1/p} \ \ \forall (i,j) \in S \Big\},$$
--   and $\|A\|_{p\to q} = \max_{x\in K} \sum_{(i,j)\in S} A(i,j)\,\gamma(i,j)$; as a minimization, the cost vector is $c = -\bar a$ with $\bar a = (0, 0, a)$.
--   2. The **barrier** (6) is
--   $$F(z,y,\gamma) = -\sum_{(i,j)\in S}\Big(\log\big(z(i)^{2/q^*}y(j)^{2/p} - \gamma(i,j)^2\big) + \tfrac1q \log z(i) + \tfrac1{p^*}\log y(j)\Big) - \log\Big(1 - \sum_{i'} z(i')\Big) - \log\Big(1 - \sum_{j'} y(j')\Big).$$
--   The terms $\frac1q\log z(i)$ and $\frac1{p^*}\log y(j)$ occur once per entry.
--   3. The **analytic center** of Lemma 7: $z_0(i) = \frac{(1 + 1/q^*)\,d_i}{1 + (1 + 1/q^*)\,s}$, $y_0(j) = \frac{(1 + 1/p)\,e_j}{1 + (1 + 1/p)\,s}$, $\gamma_0 = 0$.
--   4. $\nu = 3s + 2$, $\eta_0 = \sqrt2/(10\sqrt s)$, and the iteration count
--   $$T(s,\varepsilon) = \max\Big(\big\lceil 100\sqrt s\,\log(s/\varepsilon)\big\rceil,\ \big\lceil 21\sqrt\nu\,\log\big(7\nu/(6\varepsilon\eta_0)\big)\big\rceil\Big),$$
--   with negative ceilings read as $0$.
--   5. The returned vector $u = (y_T / Y_T)^{1/p}$ (entrywise), $Y_T = \sum_j y_T(j)$, of Step 12 of Algorithm 1.
--   6. With $w = (z, y)$, the Hessian of $F$ has the block form $H = \begin{pmatrix} H_w & H_{w\gamma}\\ H_{w\gamma}^\top & H_\gamma\end{pmatrix}$ (26); its Schur complement with respect to $\gamma$ is $H\setminus\gamma = H_w - H_{w\gamma}H_\gamma^{-1}H_{w\gamma}^\top$. Further $V = \begin{pmatrix} \mathbf 1_m/(1-Z) & 0\\ 0 & \mathbf 1_n/(1-Y)\end{pmatrix} \in \mathbb R^{(m+n)\times 2}$ with $Z = \sum_i z(i)$, $Y = \sum_j y(j)$, and $D = \mathrm{Diag}(z, y)$.
--
--   **Formalization Note** Coordinates are $z(i) = x_i$, $y(j) = x_{m+j}$, $\gamma(k) = x_{m+n+k}$ (0-based). Logarithms and real powers use Lean's total conventions outside their natural domains; every statement about $F$ is restricted to $\mathrm{int}(K)$, where all arguments are positive. The first term of $T$ is Step 4 of Algorithm 1 as printed; the second is the iteration count of the proof of Theorem 5 (Appendix A, p. 25), added because footnote 4 (p. 11) proves the printed count sufficient only for $s \ge 20$; the two coincide for every $s \ge 16$ (checked numerically). Two helpers convert between arrays $\mathbb N \to \mathbb R$ used by the programs and points of $\mathbb R^{m+n+s}$.
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), §3, pp. 7–8 (program (5), K, barrier (6), ā); Algorithm 1, p. 9; Lemma 7, p. 9; Lemma 8, p. 10; footnote 4, p. 11; §5, p. 12 and eq. (26), p. 26; Theorem 10 proof, p. 13

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Norms
import Definitions.Def_PQNormIPM1352_Main_Sparse
import Definitions.Def_PQNormIPM1352_Main_IPM

/-!
# The conic program (5), its feasible set `K`, the barrier (6), and the IPM data of Algorithm 1

Pirazzini–Spielman, STOC 2027 submission #1352, §3 (pp. 7–8: program (5), the set `K`, the
barrier (6), `ā = (0, 0, a)`), §4 (Algorithm 1, p. 9: `x₀`, `η₀`, `T`, the returned vector `u`)
and §5 (p. 12, block form (26) of the Hessian; Theorem 10's `V` and `D`).

Variables: `x = (z, y, γ) ∈ ℝ^{m+n+s}` with `z(i) = x(i)` (`i < m`), `y(j) = x(m + j)` (`j < n`) and
`γ(k) = x(m + n + k)` (`k < s`) for the `k`-th entry of the pattern (0-based indices).
-/

open Matrix

namespace PQNormIPM1352.Main

noncomputable section

variable {m n s : ℕ}

/-- Coordinate of `z(i)` in `ℝ^{m+n+s}`. -/
def zIdx (n s : ℕ) (i : Fin m) : Fin (m + n + s) := ⟨i.1, by have := i.2; omega⟩

/-- Coordinate of `y(j)` in `ℝ^{m+n+s}`. -/
def yIdx (m s : ℕ) (j : Fin n) : Fin (m + n + s) := ⟨m + j.1, by have := j.2; omega⟩

/-- Coordinate of `γ(k)` in `ℝ^{m+n+s}`. -/
def gIdx (m n : ℕ) (k : Fin s) : Fin (m + n + s) := ⟨m + n + k.1, by have := k.2; omega⟩

/-- Coordinate of the row/column variable `w = (z, y)`. -/
def wIdx (m n s : ℕ) : Fin m ⊕ Fin n → Fin (m + n + s)
  | Sum.inl i => zIdx n s i
  | Sum.inr j => yIdx m s j

namespace SparsePattern

/-- The feasible set `K ⊆ ℝ^{m+n+s}` of program (5) (§3, p. 7): `z ≥ 0`, `y ≥ 0`, `∑ z(i) ≤ 1`,
`∑ y(j) ≤ 1`, and `|γ(i,j)| ≤ z(i)^{1/q*} y(j)^{1/p}` for every `(i,j) ∈ S`. -/
def setK (P : SparsePattern m n s) (p q : ℝ) : Set (Vec (m + n + s)) :=
  {x | (∀ i, 0 ≤ x (zIdx n s i)) ∧ (∀ j, 0 ≤ x (yIdx m s j)) ∧
    ∑ i, x (zIdx n s i) ≤ 1 ∧ ∑ j, x (yIdx m s j) ≤ 1 ∧
    ∀ k, |x (gIdx m n k)| ≤
      x (zIdx n s (P.row k)) ^ (1 / conjExp q) * x (yIdx m s (P.col k)) ^ (1 / p)}

/-- The barrier (6) (§3, p. 8):
`F(z,y,γ) = −∑_{(i,j)∈S} ( log(z(i)^{2/q*} y(j)^{2/p} − γ(i,j)²) + (1/q) log z(i) + (1/p*) log y(j) )
 − log(1 − ∑ z(i')) − log(1 − ∑ y(j'))`.
The terms `(1/q) log z(i)` and `(1/p*) log y(j)` appear once per entry `(i,j)`. Only values on
`int(K)` are meaningful. -/
def barrierF (P : SparsePattern m n s) (p q : ℝ) (x : Vec (m + n + s)) : ℝ :=
  -(∑ k, (Real.log (x (zIdx n s (P.row k)) ^ (2 / conjExp q) * x (yIdx m s (P.col k)) ^ (2 / p)
          - x (gIdx m n k) ^ 2)
        + 1 / q * Real.log (x (zIdx n s (P.row k)))
        + 1 / conjExp p * Real.log (x (yIdx m s (P.col k)))))
    - Real.log (1 - ∑ i, x (zIdx n s i)) - Real.log (1 - ∑ j, x (yIdx m s j))

/-- The cost vector `c = −ā`, `ā = (0, 0, a)` (§3, p. 8): minimizing `⟨c, x⟩` over `K` is
maximizing `∑_{(i,j)∈S} A(i,j) γ(i,j)`. -/
def cvec (_P : SparsePattern m n s) (a : Fin s → ℝ) : Vec (m + n + s) :=
  ∑ k, (-(a k)) • EuclideanSpace.single (gIdx m n k) (1 : ℝ)

/-- The analytic-center formula of Lemma 7 (p. 9) and Step 6 of Algorithm 1:
`z₀(i) = (1 + 1/q*) dᵢ / (1 + (1 + 1/q*) s)`, `y₀(j) = (1 + 1/p) eⱼ / (1 + (1 + 1/p) s)`, `γ₀ = 0`. -/
def initPoint (P : SparsePattern m n s) (p q : ℝ) : Vec (m + n + s) :=
  (∑ i, ((1 + 1 / conjExp q) * P.rowDeg i / (1 + (1 + 1 / conjExp q) * s)) •
      EuclideanSpace.single (zIdx n s i) (1 : ℝ)) +
    ∑ j, ((1 + 1 / p) * P.colDeg j / (1 + (1 + 1 / p) * s)) •
      EuclideanSpace.single (yIdx m s j) (1 : ℝ)

/-- The vector `u = (y_T / Y_T)^{1/p}` (entrywise) returned in Step 12 of Algorithm 1, computed from
the final iterate `x = (z, y, γ)`, with `Y_T = ∑ⱼ y(j)`. -/
def outputVec (_P : SparsePattern m n s) (p : ℝ) (x : Vec (m + n + s)) : Fin n → ℝ :=
  fun j => (x (yIdx m s j) / ∑ j', x (yIdx m s j')) ^ (1 / p)

/-- The block `H_w = ∇²_{ww} F` of the Hessian (26), `w = (z, y)`, at `x`. -/
def hessW (P : SparsePattern m n s) (p q : ℝ) (x : Vec (m + n + s)) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  fun u v => hessMat (P.barrierF p q) x (wIdx m n s u) (wIdx m n s v)

/-- The block `H_{wγ}` of the Hessian (26). -/
def hessWG (P : SparsePattern m n s) (p q : ℝ) (x : Vec (m + n + s)) :
    Matrix (Fin m ⊕ Fin n) (Fin s) ℝ :=
  fun u k => hessMat (P.barrierF p q) x (wIdx m n s u) (gIdx m n k)

/-- The block `H_γ` of the Hessian (26). -/
def hessG (P : SparsePattern m n s) (p q : ℝ) (x : Vec (m + n + s)) : Matrix (Fin s) (Fin s) ℝ :=
  fun k l => hessMat (P.barrierF p q) x (gIdx m n k) (gIdx m n l)

/-- The Schur complement `H \ γ = H_w − H_{wγ} H_γ⁻¹ H_{wγ}ᵀ` of the Hessian with respect to `γ`
(§5, p. 12). -/
def schurGamma (P : SparsePattern m n s) (p q : ℝ) (x : Vec (m + n + s)) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  P.hessW p q x - P.hessWG p q x * (P.hessG p q x)⁻¹ * (P.hessWG p q x)ᵀ

/-- The `(m+n) × 2` matrix `V = (1_m/(1 − Z), 0; 0, 1_n/(1 − Y))` of §5, p. 13 and Algorithm 4,
Step 6, with `Z = ∑ z(i)`, `Y = ∑ y(j)`. -/
def rank2V (_P : SparsePattern m n s) (x : Vec (m + n + s)) : Matrix (Fin m ⊕ Fin n) (Fin 2) ℝ :=
  fun u c =>
    match u with
    | Sum.inl _ => if c = 0 then 1 / (1 - ∑ i, x (zIdx n s i)) else 0
    | Sum.inr _ => if c = 1 then 1 / (1 - ∑ j, x (yIdx m s j)) else 0

/-- The diagonal scaling `D = Diag(z, y)` of Theorem 10 (p. 12). -/
def diagD (_P : SparsePattern m n s) (x : Vec (m + n + s)) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.diagonal fun u => x (wIdx m n s u)

end SparsePattern

/-- An array `ℕ → ℝ` read as a point of `ℝᴺ` (its first `N` entries). -/
def arrVec (N : ℕ) (f : ℕ → ℝ) : Vec N := WithLp.toLp 2 fun i => f i

/-- A finite family `Fin N → ℝ` as an array `ℕ → ℝ` (`0` beyond `N`). -/
def finArr {N : ℕ} (f : Fin N → ℝ) : ℕ → ℝ := fun i => if h : i < N then f ⟨i, h⟩ else 0

/-- The complexity parameter `ν = 3s + 2` of Lemma 6 (p. 8). -/
def nuParam (s : ℕ) : ℝ := 3 * s + 2

/-- The initial barrier parameter `η₀ = √2 / (10 √s)` (Algorithm 1, Step 6; Lemma 8, p. 10). -/
def eta0 (s : ℕ) : ℝ := Real.sqrt 2 / (10 * Real.sqrt s)

/-- The iteration count of Algorithm 1 under the reading of footnote 4 (p. 11):
`T = max(⌈100 √s log(s/ε)⌉, ⌈21 √ν log(7ν / (6 ε η₀))⌉)` with `ν = 3s + 2`, ceilings truncated at
`0` (`Nat.ceil`). The first term is Step 4 as printed; the second is the count of the proof of
Theorem 5 (p. 25). -/
def iterCount (s : ℕ) (ε : ℝ) : ℕ :=
  max ⌈100 * Real.sqrt s * Real.log (s / ε)⌉₊
    ⌈21 * Real.sqrt (nuParam s) * Real.log (7 * nuParam s / (6 * ε * eta0 s))⌉₊

end

end PQNormIPM1352.Main


