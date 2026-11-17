-- Prove2me | Definitions.Def_CutRankSched_Supplement_Gate_unitary
-- name    : CutRankSched_Supplement_Gate_unitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:38:50.908809+00:00
-- url     : https://prove2.me/theorems/06b13f54-429e-4408-b7da-cbd6eb10c728
-- title:
--   The unitary of a gate
-- statement:
--   In the computational basis $|b\rangle$, $b\in\mathbb F_2^m$:
--
--   1. $H_q|b\rangle = 2^{-1/2}\sum_{a_q\in\{0,1\}}(-1)^{a_qb_q}\,|b[q\mapsto a_q]\rangle$;
--   2. $S_q = \mathrm{diag}(1, i)$ on qubit $q$;
--   3. $\mathrm{CNOT}_{c,t}|b\rangle = |b[t\mapsto b_t+b_c]\rangle$;
--   4. $T_q=\mathrm{diag}(1,e^{i\pi/4})$ and $T^\dagger_q=\mathrm{diag}(1,e^{-i\pi/4})$ on qubit $q$.
--
--   Then $T_q=e^{i\pi/8}R_{+1}(Z_q)$ and $T_q^\dagger=e^{-i\pi/8}R_{-1}(Z_q)$, the rotations about $Z$ "up to global phase" of the source.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4, and Theorem 4.1, p.6

import Mathlib
import Definitions.Def_CutRankSched_Supplement_pauliOp
import Definitions.Def_CutRankSched_Supplement_Gate

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The unitary matrix of a gate (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §4.1, p.6), in the computational basis
`|b⟩`, `b : Fin m → ZMod 2`:
* `H_q|b⟩ = 2^{−1/2} Σ_{a_q} (−1)^{a_q b_q} |b[q ↦ a_q]⟩`;
* `S_q = diag(1, i)` on qubit `q`;
* `CNOT_{c,t}|b⟩ = |b[t ↦ b_t + b_c]⟩`;
* `T_q = diag(1, e^{iπ/4})`, `T†_q = diag(1, e^{−iπ/4})` on qubit `q`.

**Formalization Note** `T_q = e^{iπ/8} R_{+}(Z_q)` and `T†_q = e^{−iπ/8} R_{−}(Z_q)`: the paper's
"rotation about `Z`, up to global phase" (p.4). -/
noncomputable def Gate.unitary {m : ℕ} : Gate m → Op m
  | .H q => fun a b =>
      if ∀ r, r ≠ q → a r = b r then
        ((Real.sqrt 2)⁻¹ : ℂ) * (-1 : ℂ) ^ (a q * b q).val else 0
  | .S q => fun a b => if a = b then Complex.I ^ (b q).val else 0
  | .CNOT c t _ => fun a b => if a = Function.update b t (b t + b c) then 1 else 0
  | .T q => fun a b =>
      if a = b then Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) ^ (b q).val else 0
  | .Tdg q => fun a b =>
      if a = b then Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) ^ (b q).val else 0

end Supplement

end CutRankSched


