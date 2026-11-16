-- Prove2me | Definitions.Def_LinSysAmp_Supplement_Problems
-- name    : LinSysAmp_Supplement_Problems
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:47:26.712223+00:00
-- url     : https://prove2.me/theorems/874f01d7-b590-44f6-b02a-5d7a1206478a
-- title:
--   Matrix multiplication oracles, success and expected agreement (Definition 3.2, display (7), §6.3)
-- statement:
--   Let $F=\mathbb F_q$ be a finite field and $n\ge1$.
--
--   1. **Agreement.** For vectors $c,c'\in F^n$, $\mathrm{agr}(c,c')$ is the fraction of coordinates $i$ with $c_i=c'_i$; for matrices $C,C'\in F^{n\times n}$, $\mathrm{agr}(C,C')$ is the fraction of the $n^2$ entries on which they agree.
--   2. **Expected coordinate agreement of a LINEQ oracle** (display (7)): for a randomized algorithm $O$ on pairs $(M,c)$,
--   $$\mathbb E_{M\leftarrow GL_n(\mathbb F_q),\,c\leftarrow\mathbb F_q^n,\,O}\Big[\tfrac1n\big|\{i:O(M,c)_i=(M^{-1}c)_i\}\big|\Big].$$
--   3. **MM oracle** (Definition 3.2): a randomized map from a pair $(A,B)$ of $n\times n$ matrices to a distribution on $n\times n$ matrices. It **solves $\mathrm{MM}_{n,q}$ with probability $\alpha$** if $\Pr_{A,B,O}[O(A,B)=AB]\ge\alpha$, where $A,B\leftarrow\mathbb F_q^{n\times n}$ are independent and uniform (not restricted to invertible matrices).
--   4. **Expected agreement of an MM oracle** (§6.3): $\mathbb E_{A,B,O}[\mathrm{agr}(O(A,B),AB)]$ with the same input distribution.
--
--   These are the hypotheses of Theorems 5.1, 6.1 and 6.3. The module also turns a LINEQ oracle and an MM oracle into interfaces of the oracle machine: a LINEQ call reads $n^2+n$ cells (the matrix row-major, then the right-hand side) and writes the $n$ coordinates of its answer; an MM call reads $2n^2$ cells and writes $n^2$. Hence every call is made on $n\times n$ inputs.
--
--   **Formalization Note** Probabilities and expectations are normalized finite sums; $GL_n(\mathbb F_q)$ is the published subtype of matrices with nonzero determinant, and $M^{-1}$ is the true inverse on it.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Definition 3.2, p.13 (PDF p.15); display (7), p.33 (PDF p.35); §6.3, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_LinSysAmp_Machine
import Definitions.Def_LinSysAmp_lineqSuccess
import Definitions.Def_LinSysAmp_Supplement_OracleMachine

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

/-!
# Matrix multiplication and approximate linear-system oracles (Definition 3.2, (7), §6.3)

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…):
Definition 3.2, p.13 (PDF p.15); display (7) of Theorem 6.1, p.33 (PDF p.35); §6.3, p.36
(PDF p.38).

**Formalization Note.**
* An **MM oracle** is a randomized map `MMOracle n F` from a pair of `n × n` matrices to a
  distribution on `n × n` matrices. "Solves `MM_{n,q}` with probability `α`" is
  `α ≤ mmSuccess O`, where `A, B` are independent and uniform in `F^{n×n}` (not in `GL_n`).
* The **expected agreement** of an MM oracle (§6.3) averages, over `A, B` uniform and the coins,
  the fraction of the `n²` entries of the answer that agree with `AB`.
* The **expected coordinate agreement** of a LINEQ oracle (display (7)) averages, over
  `M ← GL_n(F)`, `c ← Fⁿ` and the coins, the fraction `(1/n)|{i : O(M,c)_i = (M⁻¹c)_i}|`.
* Each kind of oracle is turned into an interface of the machine `LinSysAmp.Supplement.OracleMachine`
  (mode and handles ignored): a LINEQ call reads `n² + n` cells (the matrix row-major, then the
  right-hand side) and writes `n` cells; an MM call reads `2n²` cells (both matrices row-major) and
  writes `n²` cells. Hence every call is made on `n × n` inputs.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `agr(c, c′)`: the fraction of the coordinates where two vectors agree (`0` when `n = 0`).
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3 and (7), pp.27, 33.) -/
noncomputable def agrVec {n : ℕ} (c c' : Fin n → F) : ℝ :=
  ((Finset.univ.filter fun i => c i = c' i).card : ℝ) / n

/-- `agr(C, C′)`: the fraction of the entries `(a, b) ∈ [n]²` where two matrices agree.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §6.3, p.36 (PDF p.38).) -/
noncomputable def agrMat {n : ℕ} (C C' : Matrix (Fin n) (Fin n) F) : ℝ :=
  ((Finset.univ.filter fun p : Fin n × Fin n => C p.1 p.2 = C' p.1 p.2).card : ℝ) / (n : ℝ) ^ 2

/-- Display (7): `E_{M ← GL_n(F), c ← Fⁿ, O}[(1/n)|{i : O(M, c)_i = (M⁻¹c)_i}|]`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Theorem 6.1, display (7), p.33 (PDF p.35).) -/
noncomputable def lineqAgreement {n : ℕ} (O : LinSysAmp.Oracle n F) : ℝ :=
  ((Fintype.card (LinSysAmp.InvMat n F) : ℝ) * (Fintype.card F : ℝ) ^ n)⁻¹ *
    ∑ M : LinSysAmp.InvMat n F, ∑ c : Fin n → F, ∑ w : Fin n → F,
      (O M.1 c w).toReal * agrVec w (M.1⁻¹ *ᵥ c)

/-- An oracle for `n × n` matrix multiplication: a randomized map from `(A, B)` to a distribution
on candidate products. (arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 3.2, p.13.) -/
abbrev MMOracle (n : ℕ) (F : Type*) :=
  Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F → PMF (Matrix (Fin n) (Fin n) F)

/-- Definition 3.2: `Pr_{A, B ← F^{n×n}, O}[O(A, B) = AB]`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 3.2, p.13 (PDF p.15).) -/
noncomputable def mmSuccess {n : ℕ} (O : MMOracle n F) : ℝ :=
  ((Fintype.card F : ℝ) ^ (n * n) * (Fintype.card F : ℝ) ^ (n * n))⁻¹ *
    ∑ A : Matrix (Fin n) (Fin n) F, ∑ B : Matrix (Fin n) (Fin n) F, (O A B (A * B)).toReal

/-- §6.3: the expected agreement `E_{A, B, O}[agr(O(A, B), AB)]`, `A, B ← F^{n×n}` independent.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §6.3, p.36 (PDF p.38).) -/
noncomputable def mmAgreement {n : ℕ} (O : MMOracle n F) : ℝ :=
  ((Fintype.card F : ℝ) ^ (n * n) * (Fintype.card F : ℝ) ^ (n * n))⁻¹ *
    ∑ A : Matrix (Fin n) (Fin n) F, ∑ B : Matrix (Fin n) (Fin n) F,
      ∑ C : Matrix (Fin n) (Fin n) F, (O A B C).toReal * agrMat C (A * B)

/-- The machine interface of a LINEQ oracle: a call reads `n² + n` cells (the matrix row-major,
then the right-hand side) and writes the `n` coordinates of the answer.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def lineqIface {n : ℕ} (O : LinSysAmp.Oracle n F) : Iface F Unit where
  inLen _ := n * n + n
  call _ x _ := (O (unflatMat n x 0) (unflatVec n x (n * n))).map fun w => (List.ofFn w, none)

/-- The machine interface of an MM oracle: a call reads `2n²` cells (`A` then `B`, row-major) and
writes the `n²` entries of the answer row-major.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 3.2, p.13 (PDF p.15).) -/
noncomputable def mmIface {n : ℕ} (O : MMOracle n F) : Iface F Unit where
  inLen _ := n * n + n * n
  call _ x _ := (O (unflatMat n x 0) (unflatMat n x (n * n))).map fun C => (flatMat C, none)

end LinSysAmp.Supplement


