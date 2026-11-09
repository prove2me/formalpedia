-- Prove2me | Definitions.Def_CyclicForrelation_Even_cyclicTrace
-- name    : CyclicForrelation_Even_cyclicTrace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:44.883263+00:00
-- url     : https://prove2.me/theorems/65d16c2a-71f7-4740-ae3a-0c6baee3c093
-- title:
--   The Boolean cube, normalized Hadamard matrix, and cyclic trace
-- statement:
--   For a natural dimension $n$, let $G=\mathbb F_2^n$ and $N=2^n$. Write $x\cdot y=\sum_i x_i y_i$ in $\mathbb F_2$, $\chi_a(x)=(-1)^{a\cdot x}$, $U(x,y)=N^{-1/2}\chi_x(y)$, and $D_f=\operatorname{diag}(f(x))$. An input is any tuple of sign functions $f_0,\ldots,f_{k-1}:G\to\{-1,1\}$. Define
--   $$W(f)=D_{f_0}U\cdots D_{f_{k-1}}U,\qquad T_k(f)=\frac1N\operatorname{Tr}W(f).$$
--   The cyclic kernel and corresponding finite-sum expression are
--   $$h_f(x)=\prod_{j=0}^{k-1}f_j(x_j)(-1)^{\sum_{j=0}^{k-1}x_j\cdot x_{j+1}},\qquad N^{-k/2-1}\sum_{x\in G^k}h_f(x),\quad x_k=x_0.$$
--   The target for a single combined Boolean oracle on $\{0,\ldots,k-1\}\times G$ is the normalized trace of its curried tuple. These are concrete finite real matrices and finite sums. Orthogonality and the bound $|T_k|\le1$ are consequences, not input promises.
--
--   **Formalization Note** The cube is `Fin n → ZMod 2`, signs use Bool, and indices start at zero. Real powers are used for fractional and negative exponents. The ordered list product fixes the source's multiplication order. The wraparound successor includes the closing edge even for the last index. Dimension zero is included, with $N=1$.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 3, Eq. (2); p. 5, footnote 4; p. 16, cyclic kernel

import Mathlib

namespace CyclicForrelation.Even

abbrev Cube (n : ℕ) := Fin n → ZMod 2
abbrev OracleTuple (n k : ℕ) := Fin k → Cube n → Bool

def cubeSize (n : ℕ) : ℕ := 2 ^ n

/-- False denotes +1; true denotes -1. There is no promise on an oracle tuple. -/
def signValue (b : Bool) : ℝ := if b then -1 else 1

def binaryDot {n : ℕ} (x y : Cube n) : ZMod 2 := ∑ i, x i * y i

def characterBit {n : ℕ} (a x : Cube n) : Bool := decide (binaryDot a x = 1)

def character {n : ℕ} (a x : Cube n) : ℝ := signValue (characterBit a x)

noncomputable def hadamard (n : ℕ) : Matrix (Cube n) (Cube n) ℝ :=
  fun x y => character x y / Real.sqrt (cubeSize n)

noncomputable def phaseOracle {n : ℕ} (f : Cube n → Bool) : Matrix (Cube n) (Cube n) ℝ :=
  Matrix.diagonal (fun x => signValue (f x))

/-- Ordered product D_f0 U ... D_f(k-1) U, with no commutations. -/
noncomputable def cyclicOperator {n k : ℕ} (f : OracleTuple n k) :
    Matrix (Cube n) (Cube n) ℝ :=
  ((List.finRange k).map (fun j => phaseOracle (f j) * hadamard n)).prod

noncomputable def cyclicTrace {n k : ℕ} (f : OracleTuple n k) : ℝ :=
  Matrix.trace (cyclicOperator f) / (cubeSize n : ℝ)

/-- Wraparound successor; its argument certifies k is positive. -/
def cycleNext {k : ℕ} (j : Fin k) : Fin k :=
  ⟨(j.val + 1) % k, Nat.mod_lt _ (by have hj := j.isLt; omega)⟩

/-- The product of all oracle signs and all cycle-edge characters, including the closing edge. -/
def cycleKernel {n k : ℕ} (f : OracleTuple n k) (x : Fin k → Cube n) : ℝ :=
  (∏ j, signValue (f j (x j))) *
    signValue (decide ((∑ j, binaryDot (x j) (x (cycleNext j))) = 1))

/-- The finite-sum expression in Eq. (2); all exponents are real. -/
noncomputable def cyclicSum {n k : ℕ} (f : OracleTuple n k) : ℝ :=
  (cubeSize n : ℝ) ^ (-(k : ℝ) / 2 - 1) * ∑ x, cycleKernel f x

/-- Regard a query as one oracle index and one cube location. -/
noncomputable def traceTarget (n k : ℕ) (f : (Fin k × Cube n) → Bool) : ℝ :=
  cyclicTrace (fun j x => f (j, x))

end CyclicForrelation.Even


