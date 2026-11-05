-- Prove2me | Definitions.Def_BaconOQEC_syndProj
-- name    : BaconOQEC_syndProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:14.158445+00:00
-- url     : https://prove2.me/theorems/0df20167-aca1-4e2d-a3f1-ffa034ecb815
-- title:
--   Syndrome projector $\Pi_s$ onto $\mathcal H_{s^X,s^Z}$
-- statement:
--   The commuting generators split the Hilbert space $\mathcal H = (\mathbb C^2)^{\otimes n^2}$ into joint eigenspaces,
--
--   $$
--   \mathcal H = \bigoplus_{s^X,s^Z} \mathcal H_{s^X,s^Z}.
--   $$
--
--   The orthogonal projector onto $\mathcal H_{s^X,s^Z}$ is
--
--   $$
--   \Pi_s = \prod_{i}\tfrac12\big(I + (-1)^{s^X_i}S^X_i\big)\prod_j\tfrac12\big(I + (-1)^{s^Z_j}S^Z_j\big)
--    = 2^{-2(n-1)}\sum_{u,v\in\mathbb Z_2^{n-1}} (-1)^{u\cdot s^X + v\cdot s^Z}\, P\Big(\sum_i u_i a(S^X_i),\ \sum_j v_j b(S^Z_j)\Big),
--   $$
--
--   where $a(S^X_i)$ is the $X$-part of $S^X_i$ and $b(S^Z_j)$ the $Z$-part of $S^Z_j$. The code sector is $\Pi_0$.
--
--   **Formalization Note** Syndrome bit $0$ is eigenvalue $+1$. The expansion uses that a product of $X$-type generators is the $X$-type Pauli operator of the summed bit matrix, likewise for $Z$, and that $P(A,0)P(0,B) = P(A,B)$ for $P = X^aZ^b$, so no phase arises. The milestone `BaconOQEC.syndProj_props` proves that these are complementary orthogonal projectors of the paper's dimension.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.B, eqs. (14)–(15), p.6

import Mathlib
import Definitions.Def_BaconOQEC_pauliXZ
import Definitions.Def_BaconOQEC_SX
import Definitions.Def_BaconOQEC_SZ

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.B, eqs. (14)–(15), p.6: the orthogonal projector `Π_s` onto the
subspace `H_{s^X,s^Z}` of the decomposition "H = ⊕_{s^X,s^Z} H_{s^X,s^Z}", labelled by the
eigenvalues `s^X_i`, `s^Z_i` of the generators `S^X_i`, `S^Z_i`:
`Π_s = ∏_i ½(I + (−1)^{s^X_i} S^X_i) · ∏_j ½(I + (−1)^{s^Z_j} S^Z_j)`, expanded as
`Π_s = 2^{−2m} Σ_{u, v ∈ Z₂^m} (−1)^{u·s^X + v·s^Z} P(Σ_i u_i a(S^X_i), Σ_j v_j b(S^Z_j))`.

**Formalization Note.** `n − 1 = m`. The syndrome `s = (s^X, s^Z)` has bit `0` for eigenvalue `+1` and
bit `1` for `−1`; the code sector is `s = 0`. The expansion uses that `∏_i (S^X_i)^{u_i}` is the
`X`-type Pauli `P(Σ_i u_i a_i, 0)` and `∏_j (S^Z_j)^{v_j}` the `Z`-type `P(0, Σ_j v_j b_j)`, whose
product is `P(Σ u_i a_i, Σ v_j b_j)` (with `P = X^a Z^b`, no phase arises). Milestone
`BaconOQEC.syndProj_props` proves that these are complementary orthogonal projectors of trace
`2^{n² − 2(n − 1)}` on which `S^X_i`, `S^Z_j` act as `(−1)^{s^X_i}`, `(−1)^{s^Z_j}`. -/
noncomputable def syndProj {m : ℕ} (s : (Fin m → ZMod 2) × (Fin m → ZMod 2)) :
    Matrix (Qubits ((m + 1) * (m + 1))) (Qubits ((m + 1) * (m + 1))) ℂ :=
  ((2 : ℂ)⁻¹ ^ (2 * m)) • ∑ u : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
    ((-1 : ℂ) ^ (u ⬝ᵥ s.1 + v ⬝ᵥ s.2).val) •
      pauliXZ (∑ i, u i • (SX i).1) (∑ j, v j • (SZ j).2)

end BaconOQEC


