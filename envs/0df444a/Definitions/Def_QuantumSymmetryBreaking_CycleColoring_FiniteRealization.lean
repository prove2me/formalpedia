-- Prove2me | Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization
-- name    : QuantumSymmetryBreaking_CycleColoring_FiniteRealization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:00.028786+00:00
-- url     : https://prove2.me/theorems/2f176d67-0311-4665-b9f9-2dcb91825646
-- title:
--   §5 — energy of bipartite operators, POVMs and word products of matrix families
-- statement:
--   Let $A=B=\mathbb C^N$. For $M\in L(A\otimes B)$ the energy (Definition 5.1) is
--   $$
--   E(M)=\operatorname{Tr}(\mathsf A\mathsf B),\qquad \mathsf A=\operatorname{Tr}_A(M)^\top,\quad \mathsf B=\operatorname{Tr}_B(M).
--   $$
--   A $q$-outcome POVM on a register is a family of PSD matrices $P_1,\dots,P_q$ with $\sum_aP_a=I$ (§3). For matrices $U_1,\dots,U_s\in\mathbb C^{N\times N}$ and a word $w=(i_1,\dots,i_k)$ in the generators, $U_w=U_{i_1}U_{i_2}\cdots U_{i_k}$, with $U_w=I_N$ for the empty word; this is the source's $U_g$ when $w$ spells $g$ (Lemma 5.7 (U2)).
--
--   The energy controls the probability of a monochromatic edge in the one-round cycle colouring (Lemma 5.2); the word products are the finite-dimensional representations of $G$ used to evaluate polynomials of $\mathbb C[G\times G]$.
--
--   **Formalization Note** The energy is the published $\Lambda$-energy `QuantumCycleColoring.FourColor.energy` at $\Lambda=I$; it takes the real part of the trace, which is real for PSD $M$. The basis of $\mathbb C^N\otimes\mathbb C^N$ is indexed by `Fin N × Fin N`, first factor $A$.
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, §3 p.10 (POVM), Definition 5.1 p.21 (energy), Lemma 5.7 (U2) p.23 — PDF pp.13, 24, 26

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped ComplexOrder

/-!
# Finite-dimensional realization: energy, POVMs and word products of matrix families

Maxime Flin, Longcheng Li, Jukka Suomela, *Quantum Advantage for Distributed Symmetry Breaking*,
STOC 2027 submission #863 (October 2026), §3 p.10 (POVM), Definition 5.1 p.21 (energy), and
Lemma 5.7 (U2) p.23 (the products `U_g = U_{i_1} ⋯ U_{i_k}` along a word).

`ℂ^N ⊗ ℂ^N` has standard basis indexed by `Fin N × Fin N`, the first factor being `A` and the second
`B`. The energy is the published `QuantumCycleColoring.FourColor.energy` with `Λ = I`.
-/

namespace QuantumSymmetryBreaking.CycleColoring

open QuantumCycleColoring.FourColor

/-- Definition 5.1, p.21: the energy of `M ∈ L(ℂ^N ⊗ ℂ^N)`,
`E(M) = Tr(A B)` with `A = Tr_A(M)^⊤` and `B = Tr_B(M)`. This is the published `Λ`-energy at `Λ = I`,
which takes the real part of the trace (the trace is real for PSD `M`). -/
noncomputable abbrev energyE {N : ℕ} (M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) : ℝ :=
  energy (1 : Matrix (Fin N) (Fin N) ℂ) M

/-- §3, p.10: a `q`-outcome POVM on a register with basis `m`: PSD matrices `P_1, …, P_q` with
`∑_a P_a = I`. -/
def IsPOVM {m : Type} [Fintype m] [DecidableEq m] {q : ℕ} (P : Fin q → Matrix m m ℂ) : Prop :=
  (∀ a, (P a).PosSemidef) ∧ ∑ a, P a = 1

/-- Lemma 5.7 (U2), p.23: for a word `w = (i_1, …, i_k)` in the generators, the product
`U_w = U_{i_1} U_{i_2} ⋯ U_{i_k}` (the empty word gives `I_N`). -/
def wordMat {s N : ℕ} (U : Fin s → Matrix (Fin N) (Fin N) ℂ) (w : List (Fin s)) :
    Matrix (Fin N) (Fin N) ℂ :=
  (w.map U).prod

end QuantumSymmetryBreaking.CycleColoring


