-- Prove2me | Definitions.Def_MagnonCode_AQEDC_sMinus
-- name    : MagnonCode_AQEDC_sMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:34.040486+00:00
-- url     : https://prove2.me/theorems/cc8d807e-2d33-4d6b-bf39-2172de70d6a3
-- title:
--   The lowering operators $s^-_m=|0\rangle\langle1|$ and $S_-=\sum_ms^-_m$
-- statement:
--   On $(\mathbb C^2)^{\otimes n}$, the operator $s^-_m$ is $|0\rangle\langle1|$ on qubit $m$ and the identity on the other qubits. The total lowering operator is
--
--   $$
--   S_-=\sum_{m=1}^ns^-_m.
--   $$
--
--   These are the lowering operators of the tensor product spin representation, and they generate the descendant states of the magnon code.
--
--   **Formalization Note** The basis states $|0\rangle,|1\rangle$ are the elements $0,1$ of `Fin 2`.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, p. 53

import Mathlib

namespace MagnonCode.AQEDC

/-- **The lowering operator at a site** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 53): `s⁻_m = |0⟩⟨1|` on qubit `m`, the identity
on the other qubits. The entry at `(y, x)` is `1` iff `x m = 1` and `y` is `x` with site `m` set to `0`.

**Formalization Note** The basis states `|0⟩, |1⟩` are `0, 1 : Fin 2`. -/
def sMinus {n : ℕ} (m : Fin n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun y x => if x m = 1 ∧ y = Function.update x m 0 then 1 else 0

/-- **The total lowering operator** (p. 53): `S₋ = Σ_{m=1}^n s⁻_m`. -/
def SMinus (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ m : Fin n, sMinus m

end MagnonCode.AQEDC


