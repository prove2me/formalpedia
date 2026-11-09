-- Prove2me | Definitions.Def_AgnosticTNS_Run_psiHat
-- name    : AgnosticTNS_Run_psiHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:53.296994+00:00
-- url     : https://prove2.me/theorems/4e1b00a3-6b9a-46b5-b583-a387cf8401b4
-- title:
--   Output state $|\hat\psi\rangle$ of Algorithm 1
-- statement:
--   The output of a run of Algorithm 1 is
--   $$
--   |\hat\psi\rangle=U_1^\dagger U_2^\dagger\cdots U_c^\dagger\big(|0^{|Q|}\rangle_Q\otimes|\hat\varphi\rangle_{R_L}\big),
--   $$
--   with the tensor product in the canonical ordering of the qudits.
--
--   **Formalization Note** The vector $|0\rangle_Q\otimes|\hat\varphi\rangle_{R_L}$ is taken with $Q=[n]\setminus R_L$, which is the projected set by the residual-subsystem invariant (p.20).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1 line 22, p.19; Eq. (3.49), p.22

import Mathlib
import Definitions.Def_AgnosticTNS_Run_Ucomp
open Matrix

namespace AgnosticTNS

/-- **The output state `|ψ̂⟩ = U_1† ⋯ U_c† (|0^{|Q|}⟩_Q ⊗ |φ̂⟩_{R_L})`**, Algorithm 1 line 22, p.19
(Eq. (3.49), p.22) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).

**Formalization Note** The vector `|0⟩_Q ⊗ |φ̂⟩_{R_L}` is written as the configuration function that
equals `φ̂(x|_{R_L})` when every qudit outside `R_L` has label `0`, and `0` otherwise; by the
residual-subsystem invariant (p.20) the projected set `Q` is exactly `[n] ∖ R_L`. -/
noncomputable def Run.psiHat {d n : ℕ} {Ls : LearningSequence n} (run : Run d n Ls)
    (p : Fin Ls.L → ℕ) : (Fin n → Fin d) → ℂ :=
  (run.Ucomp p)ᴴ *ᵥ fun x =>
    if ∀ i, i ∉ run.R Ls.root → (x i : ℕ) = 0 then run.φhat (fun a => x a.1) else 0

end AgnosticTNS


