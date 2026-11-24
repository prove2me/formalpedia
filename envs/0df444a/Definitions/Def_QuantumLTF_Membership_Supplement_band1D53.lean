-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
-- name    : QuantumLTF_Membership_Supplement_band1D53
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-24T07:20:00.906831+00:00
-- url     : https://prove2.me/theorems/6b6675ea-5586-4900-ad14-9d9ccbaa90d4
-- title:
--   1D Hermite degree-band mass and n-register degree-band state slice
-- statement:
--   Let $\gamma_1$ denote the standard Gaussian measure on $\mathbb{R}$ and let $f_{e_0}(x) = \mathrm{sign}(x_0)$ be the homogeneous linear threshold function along the first coordinate unit vector $e_0 = (1) \in \mathbb{S}^{0} \subset \mathbb{R}^1$. For each integer cutoff $K \ge 0$, `p1D53 K` denotes the one-dimensional Hermite degree-band mass on $B_K = \{K, K+1, \dots, 2K\}$:
--   $$
--   p_K := \sum_{k = K}^{2K} \widehat{f_{e_0}}(k)^2,
--   $$
--   where $\widehat{f_{e_0}}(k) = \int_{\mathbb{R}} \mathrm{sign}(x) h_k(x)\, d\gamma_1(x)$ is the $k$-th normalized probabilists' Hermite coefficient of $\mathrm{sign}$.
--
--   For $n, q, a, K \in \mathbb{N}$ and an $(nq + a)$-qubit state vector $F \in \mathbb{C}^{2^{nq+a}}$ representing $n$ degree registers of $q$ qubits each (most significant bit first) followed by $a$ internal ancilla qubits, `bandSlice53 n q a K F` denotes the $nq$-qubit projection $\Pi_{B_K} F$ supported on the degree-band computational basis states with all $a$ ancilla qubits set to $0$:
--   $$
--   (\Pi_{B_K} F)(z) = \sum_{\substack{\alpha \in \{0,\dots,2K\}^n \\ K \le |\alpha| \le 2K}} \mathbf{1}\{z = \mathrm{enc}_q(\alpha)\}\, F(\mathrm{enc}_q(\alpha), 0^a),
--   $$
--   where $\mathrm{enc}_q(\alpha)$ encodes each coordinate $\alpha_i$ in $q$ qubits (most significant bit first) and $|\alpha| = \sum_{i=1}^n \alpha_i$.
--
--   These two definitions provide the rotation-invariant target band weight $p_K$ and the unnormalized degree-band slice used in the high-degree projection analysis of Theorem 5.3.
--
--   **Formalization Note** `p1D53 K` specializes `bandWeight` to the unit vector `EuclideanSpace.single (0 : Fin 1) 1`, and `bandSlice53` mirrors the indexing convention of `bandKet` and `projDist` using `flatReg`, `natToBits`, and `Fin.append`.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 2.3 (p. 20, PDF p. 21) and Section 5.2, Eqs. (167)-(171) (pp. 63-64, PDF pp. 64-65).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **1D Hermite degree-band mass `p_K`**. Krivcenko, Nguyen, de Wolf,
*Fast Quantum Algorithms for Learning Linear Threshold Functions*, arXiv:2609.40331,
Lemma 2.3 (p. 20) and §5.2 Eq. (169) (p. 63): the Hermite mass in degrees
`B_K = {K, …, 2K}` of the 1D homogeneous LTF `sign(x_0)`. -/
noncomputable def p1D53 (K : ℕ) : ℝ :=
  bandWeight (EuclideanSpace.single (0 : Fin 1) 1) K

/-- **Degree-band slice `Π_{B_K} F̃` on `n` degree registers**. Krivcenko, Nguyen, de Wolf,
*Fast Quantum Algorithms for Learning Linear Threshold Functions*, arXiv:2609.40331,
§5.2, Eqs. (167)–(171) (pp. 63–64): extracts the amplitudes of `F` supported on the
degree-band basis states `(natToBits q α_1, …, natToBits q α_n, 0^a)` with
`K ≤ ∑_i α_i ≤ 2K` and all `a` internal ancillas equal to `false`. -/
noncomputable def bandSlice53 (n q a K : ℕ)
    (F : EuclideanSpace ℂ (Qubits (n * q + a))) : EuclideanSpace ℂ (Qubits (n * q)) :=
  WithLp.toLp 2 fun z => ∑ α : Fin n → Fin (2 * K + 1),
    if z = flatReg n q (fun i => natToBits q (α i)) ∧
        K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
      F (Fin.append (flatReg n q (fun i => natToBits q (α i))) (fun _ : Fin a => false))
    else 0

end QuantumLTF.Membership.Supplement


