-- Prove2me | Definitions.Def_QIndInf_QuantumProcess
-- name    : QIndInf_QuantumProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:51.650373+00:00
-- url     : https://prove2.me/theorems/fa2bb230-237b-4685-9e4d-812c683d5349
-- title:
--   Quantum sources on $n$-qubit registers and source models
-- statement:
--   An $n$-qubit **register** $R$ has computational basis indexed by $\{0,\dots,2^n-1\}$; the registers $R_1,\dots,R_j$ together are indexed by strings $a=(a_1,\dots,a_j)$. For an operator $\rho$ on $R_1\cdots R_{j+1}$ the **partial trace over the last register** is
--
--   $$
--   (\mathrm{Tr}_{R_{j+1}}\rho)_{a,b}=\sum_{r}\rho_{(a,r),(b,r)} .
--   $$
--
--   A **quantum source** on $n$-qubit registers is a family $(\rho_{R_1\dots R_m})_{m\ge0}$ of density operators (positive semidefinite, trace one), one on each number $m$ of registers, that is consistent:
--
--   $$
--   \mathrm{Tr}_{R_{m+1}}\,\rho_{R_1\dots R_{m+1}}=\rho_{R_1\dots R_m}\qquad(m\ge0).
--   $$
--
--   A **source model** assigns to every register size $n$, time bound $t$ and program $T\in\{0,1\}^*$ a quantum source $\rho^{T}$ on $n$-qubit registers.
--
--   In the paper the source class $\mathcal C_{n,m}[s,t]$ (Eq. (50)) consists of the $m$-register states prepared by circuits that a Turing machine $T$ with $|T|\le s$ outputs within $t$ steps, over a fixed universal gate set and encoding (p.15), with the output padded by $|0\rangle$ or partially traced to $mn$ qubits (p.16, after Eq. (40)). That construction is one source model, and its states are consistent in the sense above. Every statement of this mission quantifies over all source models, so it applies to the paper's.
--
--   **Formalization Note** Registers are `Fin (2^n)`; $j$ registers are `Fin j → Fin (2^n)`, register $R_i$ being coordinate $i-1$, and $(a,r)$ is `Fin.snoc a r`. Density operators are the published `WildeQIT.IsDensityOperator`.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eq. (50), p.18; conventions p.15 and p.16 (after Eq. (40))

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

namespace QIndInf

/-- One `n`-qubit register `R`: its computational basis is indexed by `Fin (2 ^ n)`.

Hiroka, Hsieh, Shirakawa, *Universal Inductive Inference of Quantum States*, arXiv:2609.36912
(PDF of 2026-11-02), §4.1, p.18: "for each i ∈ [m], let R_i be an n-qubit register". -/
abbrev Reg (n : ℕ) : Type := Fin (2 ^ n)

/-- `j` consecutive `n`-qubit registers `R₁ … R_j`, indexed by `Fin j → Fin (2 ^ n)`.

**Formalization Note.** Register `R_i` of the paper (`i ∈ [j]`, 1-based) is the coordinate
`i − 1 : Fin j`. For `j = 0` the index type is a singleton (the trivial system). -/
abbrev Regs (n j : ℕ) : Type := Fin j → Fin (2 ^ n)

/-- Partial trace over the **last** register `R_{j+1}` of an operator on `R₁ … R_{j+1}`:
`(Tr_{R_{j+1}} ρ)_{a b} = ∑_r ρ_{(a,r),(b,r)}`, where `(a, r)` is the configuration `a` of the
first `j` registers followed by the configuration `r` of the last one (`Fin.snoc a r`).

arXiv:2609.36912 (PDF of 2026-11-02), §3.3, p.16 (the remark after Eq. (40): "the partial trace of
an n-qubit time-bounded universal density matrix over its last k qubits") and §4.1, p.18 ("Let
ρ_{<i} and ρ_{≤i} be the reduced states on registers (R₁, …, R_{i−1}) and (R₁, …, R_i)"). -/
def traceLast {n j : ℕ} (ρ : Matrix (Regs n (j + 1)) (Regs n (j + 1)) ℂ) :
    Matrix (Regs n j) (Regs n j) ℂ :=
  Matrix.of fun a b => ∑ r : Fin (2 ^ n), ρ (Fin.snoc a r) (Fin.snoc b r)

/-- **A quantum source on `n`-qubit registers**: for every number `m` of registers a density
operator `ρ_{R₁…R_m}` on `R₁ … R_m`, such that tracing out the last register of the
`(m+1)`-register state gives the `m`-register state.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eq. (50), p.18, with the conventions of p.16 (after
Eq. (40)): a Turing machine `T` whose `t`-step run `T^t` outputs a circuit determines, for every
`m`, the `mn`-qubit state prepared by that circuit, padded with `|0⟩` or partially traced to `mn`
qubits. Those states are consistent under tracing out the last register. A `QuantumProcess n`
is exactly such a consistent family of states, without reference to circuits.

**Formalization Note.** `state m` is a matrix indexed by `Regs n m` (register `R_i` = coordinate
`i − 1`). `density m` says it is positive semidefinite with trace one
(`WildeQIT.IsDensityOperator`). `consistent m` is `Tr_{R_{m+1}} ρ_{R₁…R_{m+1}} = ρ_{R₁…R_m}`, so
`state j` is the reduced state `ρ_{<j+1}` of every longer source. -/
structure QuantumProcess (n : ℕ) where
  /-- The state `ρ_{R₁…R_m}` on `m` registers. -/
  state : (m : ℕ) → Matrix (Regs n m) (Regs n m) ℂ
  /-- Each `state m` is a density operator. -/
  density : ∀ m, WildeQIT.IsDensityOperator (state m)
  /-- Tracing out the last register of `state (m + 1)` gives `state m`. -/
  consistent : ∀ m, traceLast (state (m + 1)) = state m

/-- **Source model**: a map from a register size `n`, a time bound `t` and a program
`T ∈ {0,1}*` (a binary Turing-machine description) to the quantum source it generates.

arXiv:2609.36912 (PDF of 2026-11-02), Eq. (50), p.18, and p.15 ("we fix an arbitrary finite
universal quantum gate set G and a binary encoding of quantum circuits over G. For a Turing machine
T and a time bound t ∈ N, T^t denotes the t-time execution of T").

**Formalization Note.** The paper's class `C_{n,m}[s,t]` is the set of `m`-register states
`(gen n t T).state m` with `|T| ≤ s` for the one map `gen` fixed by the paper's encoding (run `T`
for `t` steps, read the output as a circuit over `G`, pad or trace to `mn` qubits, Eq. (40)). The
statements of this development quantify over **every** source model, so they apply to the
paper's model in particular. -/
abbrev SourceModel : Type := (n t : ℕ) → List Bool → QuantumProcess n

end QIndInf


