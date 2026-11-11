-- Prove2me | Definitions.Def_QIndInf_outcomeProb
-- name    : QIndInf_outcomeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:58.787686+00:00
-- url     : https://prove2.me/theorems/b1c88204-f8b0-4e73-8fad-340a387932aa
-- title:
--   History operator $\mathcal A_{h<i}$, outcome law $D^{\mathcal I,\rho}_{<i}$, post-measurement state $\rho_{<i|h<i}$
-- statement:
--   Let $\mathcal I_l=\{\mathcal E^{(l)}_x\}_{x\in X_l}$, $l=1,\dots,j$, be quantum instruments on the $n$-qubit registers $R_l$ (finite families of completely positive maps whose sum is trace preserving, Definition 3.1), and let $x=(x_1,\dots,x_j)$ be outcomes. The **history operator** is the tensor product
--
--   $$
--   \mathcal A_{h}=\mathcal E^{(1)}_{x_1}\otimes\cdots\otimes\mathcal E^{(j)}_{x_j}\qquad\text{(Eq. (51))}.
--   $$
--
--   For a source $\rho$ the **probability of the outcomes** and the **post-measurement state** of the first $j$ registers are
--
--   $$
--   D^{\mathcal I,\rho}_{<i}(x)=\mathrm{Tr}\big[\mathcal A_h(\rho_{R_1\dots R_j})\big],\qquad \rho_{<i|h<i}=\frac{\mathcal A_h(\rho_{R_1\dots R_j})}{D^{\mathcal I,\rho}_{<i}(x)}\qquad\text{(Eqs. (52), (53))},
--   $$
--
--   with $i=j+1$. The post-measurement state is what the learner receives.
--
--   **Formalization Note** Instruments are the published `QuantumInstrument (Fin (2^n)) (Fin k)` (finite Kraus families per outcome, completeness $\sum_x\sum K^\dagger K=1$, input register = output register); a finite outcome set of size $k$ is `Fin k`. The tensor product is the published `QAlgorithms.piSuperop`. The probability is the real part of the trace. On a history of probability zero the post-measurement state is the zero matrix ($0^{-1}=0$ in Lean); such histories carry weight zero wherever they occur.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eqs. (51)–(53), pp.18–19; Definition 3.1, p.15

import Mathlib
import Definitions.Def_QIndInf_QuantumProcess
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments

set_option autoImplicit false

namespace QIndInf

open QAlgorithms QAlgorithms.CopyMeasurements

/-- **The history operator `A_{h<i}`** (Eq. (51)): for instruments `I₁, …, I_j` on the registers
`R₁, …, R_j` and outcomes `x₁, …, x_j`, the tensor product
`A_h = E^{(1)}_{x₁} ⊗ ⋯ ⊗ E^{(j)}_{x_j}` of the outcome branches, a superoperator on `R₁ … R_j`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eq. (51), p.18; instruments as in Definition 3.1,
p.15.

**Formalization Note.** An instrument on `R_l` with outcome set `X_l` is
`QAlgorithms.CopyMeasurements.QuantumInstrument (Fin (2^n)) (Fin k_l)`: for each outcome a finite
family of Kraus operators on the `n`-qubit register, with `∑_x ∑ K† K = 1` (every completely
positive map in finite dimension has a finite Kraus family; a finite outcome set of size `k_l` is
`Fin k_l`). The branch `E_x` is `instrumentBranch I x`. The tensor product is the published
`QAlgorithms.piSuperop`, which acts on every operator through its matrix-unit expansion.
Register `R_l` of the paper is coordinate `l − 1`. -/
noncomputable def histOp {n j : ℕ} {k : Fin j → ℕ}
    (I : (l : Fin j) → QuantumInstrument (Reg n) (Fin (k l))) (x : (l : Fin j) → Fin (k l)) :
    Superop (Regs n j) (Regs n j) :=
  piSuperop fun l => instrumentBranch (I l) (x l)

/-- **Outcome probability `D^{I,ρ}_{<i}(x₁,…,x_j)`** (Eq. (52)): the probability of the outcomes
`x₁, …, x_j` when `I₁, …, I_j` are applied to the first `j` registers of the source,
`Tr[A_h(ρ_{R₁…R_j})]`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eq. (52), p.18 (= Eq. (64), p.20).

**Formalization Note.** `σ` is any family of operators indexed by the number of registers (the
`state` field of a `QuantumProcess`, or a reference family such as `refState`); `σ j` is the
reduced state on `R₁ … R_j`. The real part of the trace is taken (the trace is real for
positive semidefinite inputs). -/
noncomputable def outcomeProb {n j : ℕ} (σ : (m : ℕ) → Matrix (Regs n m) (Regs n m) ℂ)
    {k : Fin j → ℕ} (I : (l : Fin j) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l)) : ℝ :=
  (histOp I x (σ j)).trace.re

/-- **Post-measurement state of the past registers `ρ_{<i|h<i}`** (Eq. (53)):
`A_h(ρ_{R₁…R_j}) / D^{I,ρ}_{<i}(x)`, the learner's input.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eq. (53), p.19.

**Formalization Note.** On a history of probability zero Lean's `0⁻¹ = 0` makes this the zero
matrix; such histories carry weight zero in every expectation of this development, as in the
paper, where they are never sampled. -/
noncomputable def condPast {n j : ℕ} (σ : (m : ℕ) → Matrix (Regs n m) (Regs n m) ℂ)
    {k : Fin j → ℕ} (I : (l : Fin j) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l)) : Matrix (Regs n j) (Regs n j) ℂ :=
  ((outcomeProb σ I x : ℂ))⁻¹ • histOp I x (σ j)

end QIndInf


