-- Prove2me | Definitions.Def_SepQPTardos_Main_Layouts
-- name    : SepQPTardos_Main_Layouts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:16.851553+00:00
-- url     : https://prove2.me/theorems/d2b91905-bc6e-48ba-9a49-7bb6b11689e9
-- title:
--   Input and output layouts and correct outputs for problem (1), integer-matrix LPs, compression, convex QPs and the local solver
-- statement:
--   Every algorithmic statement of the mission concerns one admissible program run on a fixed memory layout. Integers (dimensions) and 0/1 indicators of index sets are stored as reals; all unlisted cells hold $0$.
--
--   1. **Problem (1).** Input: $r$, $m$, $A$ row by row, then $b$, $c$, $q$. The complete input length is $L=r+m+\langle A\rangle+\langle b\rangle+\langle c\rangle+\langle q\rangle$. An output is **correct** if cell $0$ holds a status code and either (status $0$) cells $1..m$ hold an optimal $x$ and cells $m+1..m+r$ hold $\pi$ with $(x,\pi)$ satisfying (8); or (status $1$) cells $1..r$ hold a Farkas certificate $y$; or (status $2$) cells $1..m$ hold a feasible $x$ and cells $m+1..2m$ an unboundedness direction $d$.
--   2. **Linear programs with integer constraint matrices.** The LP is $\min c^\top x$ subject to $D_1x=d_1$, $D_2x\le d_2$, $x_j\ge0$ for $j\in S$ and $x_j$ free otherwise, with $D_1\in\mathbb Z^{p_1\times n}$, $D_2\in\mathbb Z^{p_2\times n}$. A correct output is either an optimal primal–dual pair (status $0$: primal feasibility, dual feasibility of $(y_1,y_2)$ with $y_2\le0$ and $(D_1^\top y_1+D_2^\top y_2)_j\le c_j$ on $S$, $=c_j$ off $S$, and complementary slackness), or a Farkas certificate $(z_1,z_2)$ with $z_2\ge0$, $(D_1^\top z_1+D_2^\top z_2)_j\ge0$ on $S$, $=0$ off $S$, $d_1^\top z_1+d_2^\top z_2<0$ (status $1$), or a feasible $x$ and a ray $d$ with $D_1d=0$, $D_2d\le0$, $d_S\ge0$, $c^\top d<0$ (status $2$).
--   3. **Frank–Tardos compression.** Input $d$, $T$, $w\in\mathbb Q^d$. A correct output holds in cells $0..d-1$ an integer vector $\bar w$ with $\operatorname{sign}(w^\top a)=\operatorname{sign}(\bar w^\top a)$ for every $a\in\mathbb Z^d$ with $\|a\|_1\le T-1$, and $\|\bar w\|_\infty\le 2^{4d^3}T^{d(d+2)}$.
--   4. **Rational convex QPs** $\min\frac12x^\top Mx+c^\top x$ subject to $Dx\le d$. A correct output is status $0$ with an optimal point in cells $1..n$, status $1$ if no point is feasible, or status $2$ if the program is feasible and its objective is unbounded below on the feasible set.
--   5. **Local near-point solver.** Input $r,m,A,q,c$, the indicator of $F$, $a$, $\varepsilon$, $B$. A correct output holds in cells $0..m-1$ a point $x\in P_F(b)$, $b=Aa$, with $\|x-z\|_\infty\le\varepsilon$ for some optimum $z$ on $P_F(b)$, eq. (10).
--
--   The layouts are total: every instance of the stated shape is an input. The promises of a statement (for example $T\ge2$, or the box condition of Proposition 3.1) are hypotheses of that statement, and nothing is asserted on inputs that violate them.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), Theorem 1.1, p. 2; §2 interfaces (i)–(iii), p. 4; §2.2 certificates, p. 5; Proposition 3.1, p. 6

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Encoding
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

noncomputable section

namespace SepQPTardos.Main

/-!
# Problems solved by programs: input layouts, output layouts and correctness of outputs

Cui–Li–Miao, STOC 2027 submission #829 (October 2026), Theorem 1.1 (p. 2), the interfaces
(i)–(iii) of §2 (p. 4) and Proposition 3.1 (p. 6). Every layout is total: any instance of the
stated shape is a valid input, and the promise of a statement is a hypothesis of that
statement. All memory cells not listed hold `0`. Integers `r, m, n, …` and the 0/1 indicator
of an index set are stored as reals.

1. **Problem (1)** (`qpInput`, `QPOutputCorrect`). Input: `r, m`, then `A` row-major, then
   `b`, `c`, `q`. Output: cell `0` holds a status code. Status `0`: cells `1…m` hold `x` and
   cells `m+1…m+r` hold `π`, and `x` is optimal and `(x, π)` satisfies (8). Status `1`: cells
   `1…r` hold `y` with `Aᵀy ≥ 0`, `bᵀy < 0`. Status `2`: cells `1…m` hold a feasible `x` and
   cells `m+1…2m` hold `d` with `Ad = 0`, `d ≥ 0`, `d_N = 0`, `cᵀd < 0`.
2. **LP with an integer constraint matrix**, interface (i) (`lpInput`, `LPOutputCorrect`):
   `min cᵀx` s.t. `D₁x = d₁`, `D₂x ≤ d₂`, `xⱼ ≥ 0` for `j ∈ S`, the other variables free.
   Input: `p₁, p₂, n`, `D₁`, `D₂` row-major, the 0/1 indicator of `S`, `d₁`, `d₂`, `c`.
   Output: status `0` with `x, y₁, y₂` (primal feasible, dual feasible, complementary
   slackness), status `1` with a Farkas certificate `(z₁, z₂)`, or status `2` with a feasible
   `x` and a ray `d` of negative cost.
3. **Frank–Tardos compression**, interface (ii) (`ftInput`, `FTOutputCorrect`). Input: `d, T`,
   then `w`. Output: cells `0…d−1` hold the integer vector `w̄`.
4. **Rational convex QP**, interface (iii) (`cqpInput`, `CQPOutputCorrect`):
   `min ½xᵀMx + cᵀx` s.t. `Dx ≤ d`. Input: `n, p`, `M`, `D` row-major, `d`, `c`. Output:
   status `0` with an optimal `x` in cells `1…n`, status `1` (infeasible), or status `2`
   (feasible and unbounded below).
5. **Local near-point solver**, Proposition 3.1 (`localInput`, `LocalOutputCorrect`). Input:
   `r, m`, `A`, `q`, `c`, the 0/1 indicator of `F`, `a`, `ε`, `B`. Output: cells `0…m−1` hold
   `x`; it lies in `P_F(b)`, `b = Aa`, and within `ℓ∞` distance `ε` of an optimum on `P_F(b)`.
-/

variable {r m : ℕ}

/-! ### 1. Problem (1) -/

/-- Input memory for an instance `(A, b, c, q)` of (1): `r, m, A (row-major), b, c, q`. -/
noncomputable def qpInput (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℚ) (c q : Fin m → ℚ) :
    ℤ → ℝ :=
  listMem ([(r : ℝ), (m : ℝ)] ++ matList (castMat A) ++ vecList (castVec b) ++
    vecList (castVec c) ++ vecList (castVec q))

/-- The complete input length `L = r + m + ⟨A⟩ + ⟨b⟩ + ⟨c⟩ + ⟨q⟩`. -/
def qpInputLen (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℚ) (c q : Fin m → ℚ) : ℕ :=
  r + m + intMatLen A + vecLen b + vecLen c + vecLen q

/-- The output memory `mem` answers the instance `(A, b, c, q)` of (1) correctly. -/
def QPOutputCorrect (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℚ) (c q : Fin m → ℚ)
    (mem : ℤ → ℝ) : Prop :=
  (mem 0 = 0 ∧ IsOptimal (castMat A) (castVec b) (castVec q) (castVec c) (readVec mem 1 m) ∧
      KKT (castMat A) (castVec b) (castVec q) (castVec c) (readVec mem 1 m)
        (readVec mem (1 + m) r)) ∨
  (mem 0 = 1 ∧ InfeasCert (castMat A) (castVec b) (readVec mem 1 r)) ∨
  (mem 0 = 2 ∧ UnbddCert (castMat A) (castVec b) (castVec q) (castVec c) (readVec mem 1 m)
      (readVec mem (1 + m) m))

/-! ### 2. Linear programs with an integer constraint matrix -/

section LP
variable {p₁ p₂ n : ℕ}

/-- Primal feasibility: `D₁x = d₁`, `D₂x ≤ d₂`, `xⱼ ≥ 0` for `j ∈ S`. -/
def LPFeasible (D₁ : Matrix (Fin p₁) (Fin n) ℝ) (D₂ : Matrix (Fin p₂) (Fin n) ℝ)
    (S : Fin n → Bool) (d₁ : Fin p₁ → ℝ) (d₂ : Fin p₂ → ℝ) (x : Fin n → ℝ) : Prop :=
  D₁ *ᵥ x = d₁ ∧ (∀ i, (D₂ *ᵥ x) i ≤ d₂ i) ∧ ∀ j, S j = true → 0 ≤ x j

/-- Dual feasibility for `max d₁ᵀy₁ + d₂ᵀy₂`: `y₂ ≤ 0`, `(D₁ᵀy₁ + D₂ᵀy₂)ⱼ ≤ cⱼ` for `j ∈ S`
and `= cⱼ` for `j ∉ S`. -/
def LPDualFeasible (D₁ : Matrix (Fin p₁) (Fin n) ℝ) (D₂ : Matrix (Fin p₂) (Fin n) ℝ)
    (S : Fin n → Bool) (c : Fin n → ℝ) (y₁ : Fin p₁ → ℝ) (y₂ : Fin p₂ → ℝ) : Prop :=
  (∀ i, y₂ i ≤ 0) ∧
    ∀ j, (S j = true → (D₁ᵀ *ᵥ y₁ + D₂ᵀ *ᵥ y₂) j ≤ c j) ∧
      (S j = false → (D₁ᵀ *ᵥ y₁ + D₂ᵀ *ᵥ y₂) j = c j)

/-- Complementary slackness: `y₂ᵢ (D₂x − d₂)ᵢ = 0` and `xⱼ (c − D₁ᵀy₁ − D₂ᵀy₂)ⱼ = 0`
for `j ∈ S`. -/
def LPCompSlack (D₁ : Matrix (Fin p₁) (Fin n) ℝ) (D₂ : Matrix (Fin p₂) (Fin n) ℝ)
    (S : Fin n → Bool) (d₂ : Fin p₂ → ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) (y₁ : Fin p₁ → ℝ)
    (y₂ : Fin p₂ → ℝ) : Prop :=
  (∀ i, y₂ i * ((D₂ *ᵥ x) i - d₂ i) = 0) ∧
    ∀ j, S j = true → x j * (c j - (D₁ᵀ *ᵥ y₁ + D₂ᵀ *ᵥ y₂) j) = 0

/-- Farkas certificate of infeasibility: `z₂ ≥ 0`, `(D₁ᵀz₁ + D₂ᵀz₂)ⱼ ≥ 0` for `j ∈ S` and
`= 0` for `j ∉ S`, and `d₁ᵀz₁ + d₂ᵀz₂ < 0`. -/
def LPInfeasCert (D₁ : Matrix (Fin p₁) (Fin n) ℝ) (D₂ : Matrix (Fin p₂) (Fin n) ℝ)
    (S : Fin n → Bool) (d₁ : Fin p₁ → ℝ) (d₂ : Fin p₂ → ℝ) (z₁ : Fin p₁ → ℝ)
    (z₂ : Fin p₂ → ℝ) : Prop :=
  (∀ i, 0 ≤ z₂ i) ∧
    (∀ j, (S j = true → 0 ≤ (D₁ᵀ *ᵥ z₁ + D₂ᵀ *ᵥ z₂) j) ∧
      (S j = false → (D₁ᵀ *ᵥ z₁ + D₂ᵀ *ᵥ z₂) j = 0)) ∧
    d₁ ⬝ᵥ z₁ + d₂ ⬝ᵥ z₂ < 0

/-- Unboundedness certificate: a feasible `x` and a ray `d` with `D₁d = 0`, `D₂d ≤ 0`,
`d_S ≥ 0` and `cᵀd < 0`. -/
def LPUnbddCert (D₁ : Matrix (Fin p₁) (Fin n) ℝ) (D₂ : Matrix (Fin p₂) (Fin n) ℝ)
    (S : Fin n → Bool) (d₁ : Fin p₁ → ℝ) (d₂ : Fin p₂ → ℝ) (c : Fin n → ℝ)
    (x d : Fin n → ℝ) : Prop :=
  LPFeasible D₁ D₂ S d₁ d₂ x ∧ D₁ *ᵥ d = 0 ∧ (∀ i, (D₂ *ᵥ d) i ≤ 0) ∧
    (∀ j, S j = true → 0 ≤ d j) ∧ c ⬝ᵥ d < 0

/-- The 0/1 indicator of a set of variables, as reals. -/
def boolVec (S : Fin n → Bool) : Fin n → ℝ := fun j => if S j then 1 else 0

/-- Input memory of an LP: `p₁, p₂, n, D₁, D₂ (row-major), 1_S, d₁, d₂, c`. -/
noncomputable def lpInput (D₁ : Matrix (Fin p₁) (Fin n) ℤ) (D₂ : Matrix (Fin p₂) (Fin n) ℤ)
    (S : Fin n → Bool) (d₁ : Fin p₁ → ℚ) (d₂ : Fin p₂ → ℚ) (c : Fin n → ℚ) : ℤ → ℝ :=
  listMem ([(p₁ : ℝ), (p₂ : ℝ), (n : ℝ)] ++ matList (castMat D₁) ++ matList (castMat D₂) ++
    vecList (boolVec S) ++ vecList (castVec d₁) ++ vecList (castVec d₂) ++ vecList (castVec c))

/-- Complete input length of an LP. -/
def lpInputLen (D₁ : Matrix (Fin p₁) (Fin n) ℤ) (D₂ : Matrix (Fin p₂) (Fin n) ℤ)
    (d₁ : Fin p₁ → ℚ) (d₂ : Fin p₂ → ℚ) (c : Fin n → ℚ) : ℕ :=
  p₁ + p₂ + n + intMatLen D₁ + intMatLen D₂ + vecLen d₁ + vecLen d₂ + vecLen c

/-- The output memory answers the LP correctly. Status `0`: `x` (cells `1…n`), `y₁` (cells
`n+1…n+p₁`), `y₂` (cells `n+p₁+1…n+p₁+p₂`) form an optimal primal–dual pair. Status `1`:
`z₁` (cells `1…p₁`), `z₂` (cells `p₁+1…p₁+p₂`) certify infeasibility. Status `2`: `x`
(cells `1…n`) is feasible and `d` (cells `n+1…2n`) is a ray of negative cost. -/
def LPOutputCorrect (D₁ : Matrix (Fin p₁) (Fin n) ℤ) (D₂ : Matrix (Fin p₂) (Fin n) ℤ)
    (S : Fin n → Bool) (d₁ : Fin p₁ → ℚ) (d₂ : Fin p₂ → ℚ) (c : Fin n → ℚ)
    (mem : ℤ → ℝ) : Prop :=
  (mem 0 = 0 ∧
      LPFeasible (castMat D₁) (castMat D₂) S (castVec d₁) (castVec d₂) (readVec mem 1 n) ∧
      LPDualFeasible (castMat D₁) (castMat D₂) S (castVec c) (readVec mem (1 + n) p₁)
        (readVec mem (1 + n + p₁) p₂) ∧
      LPCompSlack (castMat D₁) (castMat D₂) S (castVec d₂) (castVec c) (readVec mem 1 n)
        (readVec mem (1 + n) p₁) (readVec mem (1 + n + p₁) p₂)) ∨
  (mem 0 = 1 ∧ LPInfeasCert (castMat D₁) (castMat D₂) S (castVec d₁) (castVec d₂)
      (readVec mem 1 p₁) (readVec mem (1 + p₁) p₂)) ∨
  (mem 0 = 2 ∧ LPUnbddCert (castMat D₁) (castMat D₂) S (castVec d₁) (castVec d₂) (castVec c)
      (readVec mem 1 n) (readVec mem (1 + n) n))

end LP

/-! ### 3. Frank–Tardos compression -/

/-- Input memory for compression: `d, T, w`. -/
noncomputable def ftInput {d : ℕ} (w : Fin d → ℚ) (T : ℕ) : ℤ → ℝ :=
  listMem ([(d : ℝ), (T : ℝ)] ++ vecList (castVec w))

/-- Complete input length of a compression instance: `d + ⟨T⟩ + ⟨w⟩`. -/
def ftInputLen {d : ℕ} (w : Fin d → ℚ) (T : ℕ) : ℕ := d + intLen T + vecLen w

/-- The output memory holds in cells `0…d−1` an integer vector `w̄` with
`sign(wᵀa) = sign(w̄ᵀa)` for every `a ∈ ℤ^d` with `‖a‖₁ ≤ T − 1` (eq. (2)), and
`‖w̄‖∞ ≤ 2^{4d³} T^{d(d+2)}`. -/
def FTOutputCorrect {d : ℕ} (w : Fin d → ℚ) (T : ℕ) (mem : ℤ → ℝ) : Prop :=
  ∃ wbar : Fin d → ℤ, readVec mem 0 d = castIntVec wbar ∧
    (∀ a : Fin d → ℤ, (∑ i, (a i).natAbs) + 1 ≤ T →
      SignType.sign (∑ i, (w i : ℝ) * (a i : ℝ)) =
        SignType.sign (∑ i, (wbar i : ℝ) * (a i : ℝ))) ∧
    ∀ i, (wbar i).natAbs ≤ 2 ^ (4 * d ^ 3) * T ^ (d * (d + 2))

/-! ### 4. Rational convex quadratic programs -/

section CQP
variable {n p : ℕ}

/-- The objective `½xᵀMx + cᵀx`. -/
def cqpObj (M : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (x ⬝ᵥ (M *ᵥ x)) + c ⬝ᵥ x

/-- Feasibility `Dx ≤ d`. -/
def cqpFeasible (D : Matrix (Fin p) (Fin n) ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, (D *ᵥ x) i ≤ d i

/-- Input memory of a convex QP: `n, p, M (row-major), D (row-major), d, c`. -/
noncomputable def cqpInput (M : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin p) (Fin n) ℚ)
    (d : Fin p → ℚ) (c : Fin n → ℚ) : ℤ → ℝ :=
  listMem ([(n : ℝ), (p : ℝ)] ++ matList (castQMat M) ++ matList (castQMat D) ++
    vecList (castVec d) ++ vecList (castVec c))

/-- Complete binary input length of a convex QP. -/
def cqpInputLen (M : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin p) (Fin n) ℚ)
    (d : Fin p → ℚ) (c : Fin n → ℚ) : ℕ :=
  n + p + ratMatLen M + ratMatLen D + vecLen d + vecLen c

/-- The output memory answers the convex QP correctly: status `0` and cells `1…n` hold an
optimal point; status `1` and the QP is infeasible; or status `2` and the QP is feasible with
objective unbounded below on its feasible set. -/
def CQPOutputCorrect (M : Matrix (Fin n) (Fin n) ℚ) (D : Matrix (Fin p) (Fin n) ℚ)
    (d : Fin p → ℚ) (c : Fin n → ℚ) (mem : ℤ → ℝ) : Prop :=
  (mem 0 = 0 ∧ cqpFeasible (castQMat D) (castVec d) (readVec mem 1 n) ∧
      ∀ y, cqpFeasible (castQMat D) (castVec d) y →
        cqpObj (castQMat M) (castVec c) (readVec mem 1 n) ≤ cqpObj (castQMat M) (castVec c) y) ∨
  (mem 0 = 1 ∧ ∀ y, ¬ cqpFeasible (castQMat D) (castVec d) y) ∨
  (mem 0 = 2 ∧ (∃ y, cqpFeasible (castQMat D) (castVec d) y) ∧
      ∀ K : ℝ, ∃ y, cqpFeasible (castQMat D) (castVec d) y ∧ cqpObj (castQMat M) (castVec c) y < K)

end CQP

/-! ### 5. The local near-point solver of Proposition 3.1 -/

/-- The 0/1 indicator of an index set `F`, as reals. -/
noncomputable def finsetVec (F : Finset (Fin m)) : Fin m → ℝ :=
  fun e => by classical exact if e ∈ F then 1 else 0

/-- Input memory of the local solver: `r, m, A (row-major), q, c, 1_F, a, ε, B`. -/
noncomputable def localInput (A : Matrix (Fin r) (Fin m) ℤ) (q c : Fin m → ℚ)
    (F : Finset (Fin m)) (a : Fin m → ℚ) (ε : ℚ) (B : ℕ) : ℤ → ℝ :=
  listMem ([(r : ℝ), (m : ℝ)] ++ matList (castMat A) ++ vecList (castVec q) ++
    vecList (castVec c) ++ vecList (finsetVec F) ++ vecList (castVec a) ++
    [(ε : ℝ), (B : ℝ)])

/-- Complete input length of a local-solver instance. -/
def localInputLen (A : Matrix (Fin r) (Fin m) ℤ) (q c : Fin m → ℚ) (a : Fin m → ℚ) (ε : ℚ)
    (B : ℕ) : ℕ :=
  r + m + intMatLen A + vecLen q + vecLen c + m + vecLen a + ratLen ε + intLen B

/-- The output `x` (cells `0…m−1`) lies in `P_F(b)` with `b = Aa`, and is within `ℓ∞`
distance `ε` of some optimum `z` of `Φ` on `P_F(b)` (eq. (10)). -/
def LocalOutputCorrect (A : Matrix (Fin r) (Fin m) ℤ) (q c : Fin m → ℚ) (F : Finset (Fin m))
    (a : Fin m → ℚ) (ε : ℚ) (mem : ℤ → ℝ) : Prop :=
  readVec mem 0 m ∈ PF A (castMat A *ᵥ castVec a) F ∧
    ∃ z, IsMinimizer (PF A (castMat A *ᵥ castVec a) F) (Phi (castVec q) (castVec c)) z ∧
      ∀ e, |readVec mem 0 m e - z e| ≤ (ε : ℝ)

end SepQPTardos.Main


