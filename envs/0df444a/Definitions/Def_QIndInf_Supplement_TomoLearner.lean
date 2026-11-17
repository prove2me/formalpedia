-- Prove2me | Definitions.Def_QIndInf_Supplement_TomoLearner
-- name    : QIndInf_Supplement_TomoLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:26:49.521613+00:00
-- url     : https://prove2.me/theorems/6bf23c5e-50e5-4ad1-9558-f4b1a78c1aff
-- title:
--   Definition 6.1 — non-i.i.d. state tomography learners and their success probability
-- statement:
--   A **tomography learner** receives the parameters $\mathsf{param}=(1^s,1^t,1^n,1^{\epsilon^{-1}},1^{\delta^{-1}})$ and one copy of the $n(i-1)$-qubit state on $(R_1,\dots,R_{i-1})$; the round $i$ is read off the number of input registers. It performs a measurement procedure whose overall POVM $M=\{E_x\}$ on $R_1\dots R_{i-1}$ (adaptive choices and internal randomness included) depends only on $\mathsf{param}$ and $i$, and outputs $h=(M,x)$ and a classical description of an $n$-qubit state $\sigma$ determined by $\mathsf{param}$, $i$ and $x$.
--
--   The **target** conditional state of $R_i$ is
--   $$\rho_{R_i|h}=\frac{\mathrm{Tr}_{R_1\dots R_{i-1}}\big[(E_x\otimes I_{R_i})\rho_{R_1\dots R_i}\big]}{\mathrm{Tr}(E_x\rho_{R_1\dots R_{i-1}})},$$
--   and the **success probability** for $m$ rounds is
--   $$\Pr\big[\mathrm{TD}(\sigma,\rho_{R_i|h})\le\epsilon:\ i\leftarrow[m],\ (h,\sigma)\leftarrow L(\mathsf{param},\rho_{R_1\dots R_{i-1}})\big],$$
--   the record $x$ at round $i$ having probability $\mathrm{Tr}(E_x\rho_{R_1\dots R_{i-1}})$. Theorem 6.2 bounds the number of rounds after which this probability is at least $1-\delta$.
--
--   **Formalization Note** The learner is a structure indexed by $(s,t,n,a,b,j)$ with $\epsilon=1/a$, $\delta=1/b$, $j=i-1$: a finite POVM (positive semidefinite effects summing to the identity) and a density operator for each record. It receives neither $m$ nor the source. On records of probability zero the target is the zero matrix; they carry weight zero.
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §6, Definition 6.1, Eqs. (121)–(123), p.29

import Mathlib
import Definitions.Def_QIndInf_QuantumProcess
import Definitions.Def_WildeQIT_traceDist

set_option autoImplicit false

namespace QIndInf.Supplement

open QIndInf
open scoped ComplexOrder

/-- **A learner for non-i.i.d. state tomography** (Definition 6.1). At round `i = j + 1` it
receives the parameters `param = (1^s, 1^t, 1^n, 1^{ε⁻¹}, 1^{δ⁻¹})` and one copy of the
`n(i−1)`-qubit state on `R₁ … R_{i−1}` (the round is read off the number of input registers). It
performs a measurement procedure; `effect … x` is the POVM `M = {E_x}` the whole procedure induces
on `R₁ … R_{i−1}` (adaptive choices and internal randomness included), and `out … x` is the
`n`-qubit state `σ` it outputs on the record `x`, so `h = (M, x)`.

arXiv:2609.36912 (PDF of 2026-11-02), §6, Definition 6.1, items 1–3, p.29.

**Formalization Note.**
* The fields are indexed by `(s, t, n, a, b, j)` with `ε = 1/a`, `δ = 1/b` and `j = i − 1`: the
  POVM depends only on `param` and `i`, and `σ` only on `param`, `i` and `x` (Definition 6.1,
  item 3). The learner gets neither `m` nor the source.
* Outcome sets are finite (`Fin (K …)`); the effects are positive semidefinite and sum to the
  identity; every output is a density operator (a "classical description of an `n`-qubit state",
  at any precision). -/
structure TomoLearner where
  /-- Number of measurement records at round `j + 1`. -/
  K : (s t n a b j : ℕ) → ℕ
  /-- The POVM `E_x` on `R₁ … R_j`. -/
  effect : (s t n a b j : ℕ) → Fin (K s t n a b j) → Matrix (Regs n j) (Regs n j) ℂ
  effect_psd : ∀ s t n a b j x, (effect s t n a b j x).PosSemidef
  effect_sum : ∀ s t n a b j, ∑ x, effect s t n a b j x = 1
  /-- The output state `σ` on the record `x`. -/
  out : (s t n a b j : ℕ) → Fin (K s t n a b j) → Matrix (Reg n) (Reg n) ℂ
  out_density : ∀ s t n a b j x, WildeQIT.IsDensityOperator (out s t n a b j x)

/-- **Target conditional state `ρ_{R_i|h}`** (Eq. (122)):
`Tr_{R₁…R_{i−1}}[(E_x ⊗ I_{R_i}) ρ_{R₁…R_i}] / Tr(E_x ρ_{R₁…R_{i−1}})`, for `i = j + 1`, an effect
`E` on `R₁ … R_j` and the source `ρ`.

arXiv:2609.36912 (PDF of 2026-11-02), §6, Eq. (122), p.29.

**Formalization Note.** `(Tr_{<i}[(E ⊗ I)ρ])_{r r'} = ∑_{a,b} E_{a b} ρ_{(b,r),(a,r')}`, where
`(b, r)` is the configuration `Fin.snoc b r` of `R₁ … R_i`. On records of probability zero the
state is the zero matrix (`0⁻¹ = 0`); they carry weight zero. -/
noncomputable def tomoTarget {n : ℕ} (ρ : QuantumProcess n) (j : ℕ)
    (E : Matrix (Regs n j) (Regs n j) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  ((E * ρ.state j).trace)⁻¹ •
    Matrix.of fun r r' => ∑ a : Regs n j, ∑ b : Regs n j,
      E a b * ρ.state (j + 1) (Fin.snoc b r) (Fin.snoc a r')

/-- **Success probability of a tomography learner** (left side of Eq. (123)):
`Pr[TD(σ, ρ_{R_i|h}) ≤ ε : i ← [m], (h, σ) ← L(param, ρ_{R₁…R_{i−1}})]`, the record `x` at round
`i = j + 1` having probability `Tr(E_x ρ_{R₁…R_j})`; `TD = ½·WildeQIT.traceDist`, `ε = 1/a`.

arXiv:2609.36912 (PDF of 2026-11-02), §6, Definition 6.1, Eq. (123), p.29. -/
noncomputable def tomoSuccessProb (L : TomoLearner) (s t a b : ℕ) {n : ℕ} (ρ : QuantumProcess n)
    (m : ℕ) : ℝ :=
  (1 / (m : ℝ)) * ∑ j : Fin m, ∑ x : Fin (L.K s t n a b j.val),
    ((L.effect s t n a b j.val x * ρ.state j.val).trace).re *
      (if (1 / 2 : ℝ) * WildeQIT.traceDist (L.out s t n a b j.val x)
            (tomoTarget ρ j.val (L.effect s t n a b j.val x)) ≤ 1 / (a : ℝ)
        then 1 else 0)

end QIndInf.Supplement


