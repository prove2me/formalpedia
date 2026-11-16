-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_AlgProg
-- name    : BorderDiffEq_Supplement_AlgProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:53:44.582023+00:00
-- url     : https://prove2.me/theorems/f812422f-0f47-4c27-80e7-9f7d853cc6a5
-- title:
--   Algebraic programs that output formulas, with counted field operations
-- statement:
--   An **algebraic program** is a decision tree over a growing list of registers holding field elements. The registers start with the answers of the black-box queries. Each step appends one register — a rational constant, or the sum, difference, product or quotient of two registers — or tests whether a register is zero and branches. A leaf outputs a formula whose constant leaves are register indices.
--
--   Running a program over a field $F$ of characteristic zero returns the output formula over $F$ (each constant leaf replaced by the value of its register) and the number of operations performed on the path taken; constants, arithmetic operations and zero tests each count one. This is the cost model of the reconstruction algorithm of Theorem 2.7, which counts field operations.
--
--   **Formalization Note** A missing register reads as $0$ and a quotient by $0$ is $0$ (Lean's convention; a program can test first). The same program runs over every field of characteristic zero. `AlgProg.code` (with `Formula.code`) writes a program as a prefix code in natural numbers, used to state that a program is computed by an algorithm.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.7, p.9; §8.1–8.2, pp.57–62

import Mathlib
import Definitions.Def_BorderDiffEq_Supplement_Formula

namespace BorderDiffEq.Supplement

/-- **Algebraic programs that output formulas** (cost model for the reconstruction algorithm of
Theorem 2.7, Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic
Circuits via Differential Equations*, manuscript (STOC 2027 submission), p.9, and §8.1–8.2,
pp.57–62, which count field operations): a program is a decision tree over a list of registers
holding field elements. The registers initially hold the answers to the black-box queries. Each
step appends one new register (a rational constant, or the sum, difference, product or quotient of
two registers) or tests whether a register is zero and branches. A leaf returns a formula whose
constant leaves are register indices.

**Formalization Note.** Registers are indexed by `ℕ` (`getD i 0` reads register `i`, a missing one
as `0`); a quotient by zero is `0` (Lean's convention; a program can test first). The same program
runs over every field of characteristic zero (constants are rationals). `run` returns the output
formula, with each constant leaf replaced by its register's value, and the number of operations
on the path taken (constants, arithmetic operations and zero tests each count one). `code` writes
a program as a list of natural numbers (a prefix code), so that "the program is computed by an
algorithm from the parameters" can be stated with Mathlib's `Computable`. -/
inductive AlgProg (σ : Type) : Type where
  /-- stop and output the formula; its constant leaves are register indices -/
  | ret : Formula ℕ σ → AlgProg σ
  /-- append the rational constant `q` -/
  | const : ℚ → AlgProg σ → AlgProg σ
  /-- append `rᵢ + rⱼ` -/
  | add : ℕ → ℕ → AlgProg σ → AlgProg σ
  /-- append `rᵢ - rⱼ` -/
  | sub : ℕ → ℕ → AlgProg σ → AlgProg σ
  /-- append `rᵢ * rⱼ` -/
  | mul : ℕ → ℕ → AlgProg σ → AlgProg σ
  /-- append `rᵢ / rⱼ` -/
  | div : ℕ → ℕ → AlgProg σ → AlgProg σ
  /-- if `rᵢ = 0` continue with the first program, otherwise with the second -/
  | ifZero : ℕ → AlgProg σ → AlgProg σ → AlgProg σ

namespace AlgProg

variable {σ F : Type}

/-- Run the program on the registers `regs`: the output formula over `F` and the number of
operations performed. -/
noncomputable def run [Field F] : AlgProg σ → List F → Formula F σ × ℕ
  | ret φ, regs => (φ.map fun i => regs.getD i 0, 0)
  | const q p, regs => let r := run p (regs ++ [(q : F)]); (r.1, r.2 + 1)
  | add i j p, regs => let r := run p (regs ++ [regs.getD i 0 + regs.getD j 0]); (r.1, r.2 + 1)
  | sub i j p, regs => let r := run p (regs ++ [regs.getD i 0 - regs.getD j 0]); (r.1, r.2 + 1)
  | mul i j p, regs => let r := run p (regs ++ [regs.getD i 0 * regs.getD j 0]); (r.1, r.2 + 1)
  | div i j p, regs => let r := run p (regs ++ [regs.getD i 0 / regs.getD j 0]); (r.1, r.2 + 1)
  | ifZero i p₁ p₂, regs =>
      have := Classical.propDecidable (regs.getD i 0 = 0)
      if regs.getD i 0 = 0 then let r := run p₁ regs; (r.1, r.2 + 1)
      else let r := run p₂ regs; (r.1, r.2 + 1)

/-- A prefix code of the program as a list of natural numbers, given a code `v` of the
variables: a tag (`0` = `ret`, …, `6` = `ifZero`), the data of the step (`Encodable.encode q` for a
rational constant, register indices), then the codes of the continuation(s); the output formula is
written with `Formula.code`. -/
def code (v : σ → ℕ) : AlgProg σ → List ℕ
  | ret φ => 0 :: φ.code id v
  | const q p => [1, Encodable.encode q] ++ code v p
  | add i j p => [2, i, j] ++ code v p
  | sub i j p => [3, i, j] ++ code v p
  | mul i j p => [4, i, j] ++ code v p
  | div i j p => [5, i, j] ++ code v p
  | ifZero i p₁ p₂ => [6, i] ++ code v p₁ ++ code v p₂

end AlgProg

end BorderDiffEq.Supplement


