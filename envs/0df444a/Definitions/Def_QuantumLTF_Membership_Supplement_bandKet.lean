-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
-- name    : QuantumLTF_Membership_Supplement_bandKet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:38:12.717957+00:00
-- url     : https://prove2.me/theorems/c804449a-ca0e-4ff9-a41e-eb5141922c45
-- title:
--   Band state $|F_w^{B_K}\rangle=\Pi_{B_K}|F_w\rangle/\sqrt{p_K}$
-- statement:
--   The normalized projection of the Hermite state onto the degree band $B_K=\{K,\dots,2K\}$,
--   $$|F_w^{B_K}\rangle=\frac{1}{\sqrt{p_K}}\sum_{K\le|\alpha|\le2K}\widehat f_w(\alpha)|\alpha\rangle ,$$
--   on $n$ degree registers of $q$ qubits each. The degree $\alpha_i$ is written in binary, most significant bit first, in register $i$ (qubits $iq,\dots,iq+q-1$).
--
--   **Formalization Note** The theorems assume $2K+1\le D\le 2^q$, so the binary encoding is injective on the degrees that occur. $p_K>0$, since the sign function has Hermite mass in every odd degree.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Eq. (169), p. 63 (PDF p. 64); Theorem 5.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **The band state `|F_w^{B_K}⟩ := Π_{B_K}|F_w⟩/√p_K` on `n` degree registers.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331,
Eq. (169), p. 63 (PDF p. 64), and Theorem 5.3. The amplitude at the string
`(natToBits q α_1, …, natToBits q α_n)` (register `i` on wires `i q, …, i q + q − 1`, most significant
bit first) is `f̂_w(α)/√p_K` when `K ≤ |α| ≤ 2K`, and every other amplitude is `0`.

**Formalization Note.** The degrees satisfy `α_i ≤ 2K`; the theorems assume `2K + 1 ≤ D ≤ 2^q`, so
`natToBits q` is injective on them and the sum below has at most one nonzero term. `p_K > 0` (the sign
function has nonzero Hermite mass in every odd degree), so the division is not the junk `x/0 = 0`. -/
noncomputable def bandKet (n q K : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Qubits (n * q)) :=
  WithLp.toLp 2 fun z => ∑ α : Fin n → Fin (2 * K + 1),
    if z = flatReg n q (fun i => natToBits q (α i)) ∧
        K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then
      ((hermCoeff w (fun i => (α i : ℕ)) / Real.sqrt (bandWeight w K) : ℝ) : ℂ)
    else 0

end QuantumLTF.Membership.Supplement


