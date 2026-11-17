-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_projDist
-- name    : QuantumLTF_Membership_Supplement_projDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:38:47.203481+00:00
-- url     : https://prove2.me/theorems/94db9613-71ea-4867-9351-096e0d64a326
-- title:
--   Low-degree distance $\|P_D^{\otimes n}|\tilde F\rangle-P_D^{\otimes n}|F_w\rangle\|$
-- statement:
--   For a vector $\tilde F$ on $n$ degree registers of $q$ qubits followed by $a$ ancilla qubits,
--   $$\|P_D^{\otimes n}\tilde F-P_D^{\otimes n}F_w\|^2=\sum_{\alpha\in[D]_0^n}\big|\tilde F(\alpha,0^a)-\widehat f_w(\alpha)\big|^2 ,$$
--   where $\tilde F(\alpha,0^a)$ is the amplitude of $\tilde F$ at the string of binary degrees $\alpha_1,\dots,\alpha_n$ followed by $a$ zeros. As on p. 62, $P_D$ includes the projector $|0\rangle\langle0|_{\mathrm{anc}}$ on the clean internal workspace.
--
--   **Formalization Note** The formula is this distance when $D\le 2^q$, which every theorem using it assumes ($M\ge D$, p. 58).
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §5.1, pp. 57, 60–62 (PDF pp. 58, 61–63), Eq. (159)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **`‖P_D^{⊗n} F̃ − P_D^{⊗n} F_w‖`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §5.1, pp. 57, 60–62 (PDF pp. 58, 61–63): `P_D := Σ_{k<D}
|k⟩⟨k|`, `|F_w⟩ := Σ_{α ∈ ℕⁿ} f̂_w(α)|α⟩` (Eq. (159)), so `P_D^{⊗n}|F_w⟩ = Σ_{α ∈ [D]_0^n} f̂_w(α)|α⟩`.
`F̃` is a vector on `n` degree registers of `q` qubits (`M = 2^q`) followed by `a` ancilla wires. The
degree `k < D` of register `i` is the basis state `natToBits q k` (most significant bit first) on
wires `i q, …, i q + q − 1` (`flatReg`), and, as p. 62 says, "`P_D` denotes the projector
`P_D ⊗ |0⟩⟨0|_anc`": `P_D^{⊗n} F̃` keeps the amplitudes of `F̃` at the strings
`(natToBits q α_1, …, natToBits q α_n, 0…0)` with `α ∈ [D]^n`. Hence

`‖P_D^{⊗n}F̃ − P_D^{⊗n}F_w‖² = Σ_{α ∈ [D]^n} |F̃(α, 0) − f̂_w(α)|²`.

**Formalization Note.** The formula is the distance only when `D ≤ 2^q` (`natToBits q` injective on
`[D]`); every theorem using it assumes `D ≤ M` (standing assumption, PDF p. 58). -/
noncomputable def projDist (n q a D : ℕ) (w : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℂ (Qubits (n * q + a))) : ℝ :=
  Real.sqrt (∑ α : Fin n → Fin D,
    ‖F (Fin.append (flatReg n q fun i => natToBits q (α i)) (fun _ : Fin a => false)) -
      (hermCoeff w (fun i => (α i : ℕ)) : ℂ)‖ ^ 2)

end QuantumLTF.Membership.Supplement


