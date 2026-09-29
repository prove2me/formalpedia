-- Prove2me | Definitions.Def_ThornStringBits_Defs
-- name    : ThornStringBits_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T01:29:58.326462+00:00
-- url     : https://prove2.me/theorems/cec438f8-1316-444e-9c10-4b7abf16ea9f
-- title:
--   Discretized light-cone string: cyclic Laplacian, bond potential, normal-mode frequencies
-- statement:
--   Three definitions modelling the discretized light-cone string of Thorn's paper (p. 4): $M$ "string bits" on a closed chain, bit $i$ bonded to bit $i+1$ with indices taken modulo $M$.
--
--   1. **Cyclic Laplacian.** For $M\in\mathbb N$, $L_M$ is the real $M\times M$ matrix, indexed by $\{0,\dots,M-1\}$,
--   $$ (L_M)_{ij} = 2\,\delta_{ij} - [\,j \equiv i+1 \pmod M\,] - [\,i \equiv j+1 \pmod M\,], $$
--   so that $(L_M x)_i = 2x_i - x_{i+1} - x_{i-1}$ for $M\ge 3$. For $M=2$ the two off-diagonal entries equal $-2$ (both bonds join the same pair of bits), and $L_1 = 0$.
--
--   2. **Bond potential.** For $x\in\mathbb R^M$,
--   $$ V_M(x) = \sum_{i=0}^{M-1} \bigl(x_{(i+1) \bmod M} - x_i\bigr)^2 , $$
--   the nearest-neighbour term of the Hamiltonian $P^- = \frac1\epsilon\sum_i \frac1{2T_0}\bigl(-\nabla_i^2 + T_0^2 (x_{i+1}-x_i)^2\bigr)$, for one transverse coordinate per bit.
--
--   3. **Positive normal-mode frequencies.** For $M\in\mathbb N$ and $\epsilon\in\mathbb R$,
--   $$ \Omega_{M,\epsilon} = \{\,\omega>0 \;:\; \epsilon^2\omega^2 \text{ is an eigenvalue of } L_M \,\}. $$
--   The Hamilton equations of $P^-$ read $\ddot x = -\epsilon^{-2} L_M x$, so these are the angular frequencies of the chain's oscillation modes, i.e. its excitation-level spacings (with $\hbar=1$); the tension $T_0$ drops out.
--
--   These objects are the shared vocabulary of the mission's goal theorem and milestones.
--
--   **Formalization Note** Eigenvalues are those of the real linear map $x\mapsto L_M x$ on $\mathbb R^M$ (a nonzero real eigenvector is required). Transverse space is taken one-dimensional; for $d-2$ transverse dimensions the modes decouple coordinate-wise and the frequency set is unchanged.
-- source:
--   C. B. Thorn, *Reformulating String Theory with the 1/N Expansion*, arXiv:hep-th/9405069v1 (1994; talk at the First Int. A. D. Sakharov Conf., 1991), https://arxiv.org/abs/hep-th/9405069, p. 4 (discretized string, M-particle wave function and Hamiltonian P^-).

import Mathlib

namespace ThornStringBits

/-- The cyclic nearest-neighbour (discrete) Laplacian on `M` string bits,
`(L x)_i = 2 x_i - x_{i+1} - x_{i-1}` with indices taken modulo `M`. -/
noncomputable def cycLaplacian (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j =>
    (if i = j then 2 else 0)
      - (if j.val = (i.val + 1) % M then 1 else 0)
      - (if i.val = (j.val + 1) % M then 1 else 0)

/-- The nearest-neighbour potential energy of the closed discretized string,
`∑_i (x_{i+1} - x_i)^2` (indices modulo `M`), for bits with one real transverse
coordinate each. -/
noncomputable def chainPotential (M : ℕ) (x : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, (x ⟨(i.val + 1) % M, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ - x i) ^ 2

/-- The positive normal-mode angular frequencies of the discretized light-cone
string with `M` bits and lattice parameter `ε`: those `ω > 0` for which
`ε² ω²` is an eigenvalue of the cyclic Laplacian (the equations of motion of
`P⁻` are `ẍ = -(1/ε²) L x`). -/
noncomputable def positiveModeFreqs (M : ℕ) (ε : ℝ) : Set ℝ :=
  {ω : ℝ | 0 < ω ∧
    Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian M)) (ε ^ 2 * ω ^ 2)}

end ThornStringBits


