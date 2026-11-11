-- Prove2me | Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm
-- name    : QuantumCycleColoring_FourColor_CycleAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:00:03.219205+00:00
-- url     : https://prove2.me/theorems/f3384f91-02f3-48aa-98c4-0436c481ffcc
-- title:
--   One-way one-round anonymous quantum algorithms on a directed cycle and their output law
-- statement:
--   The **directed $n$-cycle** has nodes $v_\ell$, $\ell\in\mathbb Z_n$, and edges $v_\ell\to v_{\ell+1}$. A colouring $c:\mathbb Z_n\to[q]$ is **proper** if $c_\ell\ne c_{\ell+1}$ for every $\ell$.
--
--   In a **one-way one-round anonymous quantum algorithm** all nodes are identical. In its general finite-dimensional form every node $v_\ell$ prepares the same **density matrix** $\rho$ (PSD, trace one) on a kept register $A_\ell$ and a message register $B_\ell$, sends $B_\ell$ to $v_{\ell+1}$, and measures the same $q$-outcome POVM $\{P_i\}$ on the pair $(B_{\ell-1},A_\ell)$ (received register first), outputting the outcome $c_\ell$. By the Born rule, the probability of the colour vector $c$ is
--
--   $$\Pr[c]=\mathrm{Tr}\Big[\Big(\bigotimes_{\ell\in\mathbb Z_n}(P_{c_\ell})_{B_{\ell-1}A_\ell}\Big)\ \rho^{\otimes n}\Big].$$
--
--   From it are defined the **collision probability** of the edge $(i,i+1)$, $\Pr[c_i=c_{i+1}]=\sum_{c:\,c_i=c_{i+1}}\Pr[c]$, and the probability $\sum_{c\text{ proper}}\Pr[c]$ that the output is a proper colouring. Finally, for a matrix $\Lambda$ the **normal-form state** is $|\Psi\rangle\langle\Psi|$ with $|\Psi\rangle=\mathrm{vec}(\bar\Lambda)\in\mathbb C^N\otimes\mathbb C^N$ (§6.1, eq. (26)).
--
--   These are the objects of the main theorem: its conclusion is a lower bound on the collision probability of every such algorithm, computed from this output law and not from the energy formula.
--
--   **Formalization Note** A global basis index is a map $x:\mathbb Z_n\to a\times b$ ($A_\ell=(x_\ell)_1$, $B_\ell=(x_\ell)_2$). The entry of the tensor product is the product of the entries of the factors because every coordinate of $x$ occurs in exactly one factor; the probability is the real part of the trace. The node set is `ZMod n` with `NeZero n`.
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Definitions 3.8–3.10 (pp.19–20); §6.1, proof of Theorem 6.1, eq. (26) and the display after it (p.41)

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped ComplexOrder

/-!
# One-way one-round anonymous quantum algorithms on a directed cycle

Tom Gur, Longcheng Li, *Impossibility of One-Way One-Round Quantum 4-Coloring via Matrix-Space
Stability*, STOC 2027 submission #515 (October 2026), Definitions 3.8–3.10 (pp.19–20) and §6.1
(pp.40–41).

The directed `n`-cycle has nodes `ℓ : ZMod n` and edges `ℓ → ℓ + 1`. In the most general
finite-dimensional form of a one-way one-round anonymous algorithm, every node prepares the same
state `ρ` on a kept register `A` (index type `a`) and a message register `B` (index type `b`),
sends `B` to its successor, and measures the same `q`-outcome POVM `P` on the pair
(received `B_{ℓ-1}`, own `A_ℓ`), indexed by `b × a`, outputting the outcome as its colour.
Private randomness and workspace are absorbed into `a` and the mixed state `ρ`.
-/

namespace QuantumCycleColoring.FourColor

open Matrix

/-- A density matrix: positive semidefinite with trace one. -/
def IsDensityMatrix {m : Type} [Fintype m] (ρ : Matrix m m ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Definition 3.9, p.19: a proper colouring of the directed `n`-cycle, `c_ℓ ≠ c_{ℓ+1}` for all `ℓ`. -/
def IsProperCycleColoring {n q : ℕ} (c : ZMod n → Fin q) : Prop :=
  ∀ ℓ : ZMod n, c ℓ ≠ c (ℓ + 1)

/-- The Born-rule probability that the `n` nodes of the directed cycle output the colour vector
`c`, when every node prepares `ρ` on `A_ℓ B_ℓ`, sends `B_ℓ` to node `ℓ + 1`, and measures the POVM
`P` on `B_{ℓ-1} A_ℓ`:
`Pr[c] = Tr[(⊗_ℓ P_{c_ℓ} on B_{ℓ-1} A_ℓ) · ρ^{⊗ n}]`.
A global basis index is `x : ZMod n → a × b` (node `ℓ` holds `A_ℓ = (x ℓ).1`, `B_ℓ = (x ℓ).2`);
every coordinate of `x` occurs in exactly one factor `P_{c_ℓ}`, so the product of entries is the
entry of the tensor product. -/
noncomputable def outputProb (n : ℕ) [NeZero n] {q : ℕ} {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) (P : Fin q → Matrix (b × a) (b × a) ℂ)
    (c : ZMod n → Fin q) : ℝ :=
  (∑ x : ZMod n → a × b, ∑ y : ZMod n → a × b,
      (∏ ℓ : ZMod n, P (c ℓ) ((x (ℓ - 1)).2, (x ℓ).1) ((y (ℓ - 1)).2, (y ℓ).1)) *
        ∏ ℓ : ZMod n, ρ (y ℓ) (x ℓ)).re

/-- The probability of a collision on the edge `(i, i+1)`: `Pr[c_i = c_{i+1}]`. -/
noncomputable def collisionProb (n : ℕ) [NeZero n] {q : ℕ} {a b : Type} [Fintype a]
    [DecidableEq a] [Fintype b] [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ)
    (P : Fin q → Matrix (b × a) (b × a) ℂ) (i : ZMod n) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : ZMod n → Fin q => c i = c (i + 1)), outputProb n ρ P c

/-- The probability that the output is a proper colouring of the directed `n`-cycle
(`IsProperCycleColoring c`, written out so that the filter is decidable). -/
noncomputable def properColoringProb (n : ℕ) [NeZero n] {q : ℕ} {a b : Type} [Fintype a]
    [DecidableEq a] [Fintype b] [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ)
    (P : Fin q → Matrix (b × a) (b × a) ℂ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : ZMod n → Fin q => ∀ ℓ : ZMod n, c ℓ ≠ c (ℓ + 1)), outputProb n ρ P c

/-- §6.1, eq. (26), p.41: the pure bipartite state `|Ψ⟩⟨Ψ|` with `|Ψ⟩ = vec(Λ̄) ∈ ℂ^N ⊗ ℂ^N`, first
factor `A`, second factor `B`. -/
noncomputable def vecConjState {d : Type} (Λ : Matrix d d ℂ) : Matrix (d × d) (d × d) ℂ :=
  ketBra (vecM (conjM Λ))

end QuantumCycleColoring.FourColor


