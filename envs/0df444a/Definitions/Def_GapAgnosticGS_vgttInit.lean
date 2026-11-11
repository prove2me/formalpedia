-- Prove2me | Definitions.Def_GapAgnosticGS_vgttInit
-- name    : GapAgnosticGS_vgttInit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:06.970538+00:00
-- url     : https://prove2.me/theorems/cbbb0fb2-421c-4e33-9af5-8fa294babe55
-- title:
--   Initial state of Algorithm 2
-- statement:
--   For an input $|\Psi\rangle_I$, the initial state of Algorithm 2 is
--
--   $$|\Psi\rangle_I\,|0\rangle_A\,\big(|0\rangle_{C}|0\rangle_{P}\big)^{\otimes m}\,|0\rangle_{C_{m+1}}\,|1\rangle_F ,$$
--
--   as in line 3: "Initialize registers $A,(C_1,P_1),\dots,(C_m,P_m),C_{m+1}$ to $|0\rangle$ and $F$ to $|1\rangle$".
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Algorithm 2, line 3, p.27 (PDF p.28)

import Definitions.Def_QAlgorithms_Defs_Basic

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Algorithm 2, line 3, p.27 (PDF p.28): "Initialize registers A, (C_1, P_1), …,
(C_m, P_m), C_{m+1} to |0⟩ and F to |1⟩", with the input `|Ψ⟩_I = ψ` on the selector register.
The initial vector of `vgtt`: `ψ ⊗ |a₀⟩_A ⊗ (|0⟩_C|p₀⟩_P)^{⊗m} ⊗ |0⟩_{C_{m+1}} ⊗ |1⟩_F` (`p₀` is the
zero state of the workspace `P`). -/
noncomputable def vgttInit {n : ℕ} {A P : Type} [DecidableEq A] [DecidableEq P] (m : ℕ)
    (a₀ : A) (p₀ : P) (ψ : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool) :=
  WithLp.toLp 2 fun x =>
    if x.1.2 = a₀ ∧ x.2.1 = (fun _ => (false, p₀)) ∧ x.2.2 = (false, true) then ψ x.1.1 else 0

end GapAgnosticGS


