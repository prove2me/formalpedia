-- Prove2me | Definitions.Def_EllipticRootFinding_Online_Complexity
-- name    : EllipticRootFinding_Online_Complexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:02:50.326221+00:00
-- url     : https://prove2.me/theorems/a8e627a4-1f75-45aa-ad4a-b4f7bfeef517
-- title:
--   The Section 3 soft-O bound and feasible exponents of matrix multiplication
-- statement:
--   For constants $C, \kappa$ and a quantity $\varphi \ge 0$, the **soft-O bound** of Section 3 is
--   $$\mathrm{softOBound}(C, \kappa, \varphi) = C\,\varphi\,\log\bigl(e + \varphi\bigr)^{\kappa},$$
--   with the natural logarithm and a real power. A cost $\varphi_1$ is $\tilde O(\varphi_2)$ when there are $C, \kappa > 0$ such that $\varphi_1 \le \mathrm{softOBound}(C, \kappa, \varphi_2)$ on the whole domain; every item states this with the constants chosen before the field and the input.
--
--   A real number $\omega$ is a **feasible exponent of matrix multiplication**, $\mathrm{FeasibleMatMul}(\omega)$, when there are a program $P$ of the machine and a constant $C > 0$ such that for every finite field $F$ of characteristic greater than $3$, every $n \ge 0$ and all $n \times n$ matrices $A, B$ over $F$, the program on input $[n, A, B]$ (entries in row-major order) outputs $AB$ within
--   $$C\, n^{\omega}$$
--   counted field operations.
--
--   **Formalization Note.** Feasibility is required in the same uniform machine as the algorithms that use it, so the linear algebra of the paper's subroutines must be built on this program; the classical algorithm shows that $\omega = 3$ is feasible.
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 12, §3 (definitions of Õ and of ω)

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine

namespace EllipticRootFinding.Online

/-!
# The Section 3 soft-O bound and feasible exponents of matrix multiplication

Spaenlehauer, arXiv:2610.32508 (version held), p. 12 (§3): "We write φ1 = Õ(φ2) if there exist
constants C, κ > 0 such that for all x ∈ X, φ1(x) ≤ C φ2(x) log(exp(1) + φ2(x))^κ", and
"We write ω ∈ [2, 3] for a feasible exponent of matrix multiplication".
-/

/-- The Section 3 soft-O bound `C · φ · log(exp 1 + φ)^κ` (natural logarithm, real power). -/
noncomputable def softOBound (C κ φ : ℝ) : ℝ :=
  C * φ * Real.log (Real.exp 1 + φ) ^ κ

/-- Encoding of an `n × n` matrix: its entries in row-major order. -/
def matVal {F : Type} {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Val F :=
  Val.ofList ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => Val.fld (A i j))

/-- `ω` is a feasible exponent of matrix multiplication: one program of the machine multiplies two
`n × n` matrices over every finite field of characteristic greater than `3`, for every `n`, within
`C · n^ω` counted field operations, `C > 0` fixed before the field and `n`. The input is
`[n, A, B]`, the output is `A * B`. -/
def FeasibleMatMul (ω : ℝ) : Prop :=
  ∃ P : Program, ∃ C : ℝ, 0 < C ∧
    ∀ (F : Type) [Field F] [Fintype F], 3 < ringChar F →
      ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) F),
        Computes P (Val.ofList [Val.int (n : ℤ), matVal A, matVal B])
          (fun out => out = matVal (A * B)) (C * (n : ℝ) ^ ω)

end EllipticRootFinding.Online


