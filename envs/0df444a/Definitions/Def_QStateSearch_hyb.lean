-- Prove2me | Definitions.Def_QStateSearch_hyb
-- name    : QStateSearch_hyb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:22.961212+00:00
-- url     : https://prove2.me/theorems/3ba14d59-9e69-45e5-b9dd-be0d8beb7040
-- title:
--   Hybrid oracle schedule $\Omega_t$
-- statement:
--   For $\psi\in\mathbb C^D$ and $t\ge0$, the hybrid schedule answers the first $t$ query slots with the identity $I$ and all later slots with $R_\psi$. Its final classical–quantum state is the paper's $\Omega^\psi_t$; $t=0$ is the real experiment with $R_\psi$, and $t=q$ is the experiment with the identity oracle.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 4, p.13

import Mathlib
import Definitions.Def_QStateSearch_refl

namespace QStateSearch

/-- The hybrid oracle schedule `Ω_t`: the first `t` query slots (0-based slots `s < t`) use the
identity `I` and the remaining slots use `R_ψ`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 4, p.13: "For t = 0, …, q, let Ω^ψ_t be the final state of the verifier and
public transcript when the first t calls use I and the remaining calls use R_ψ." -/
noncomputable def hyb {D : ℕ} (ψ : EuclideanSpace ℂ (Fin D)) (t : ℕ) : ℕ → Matrix (Fin D) (Fin D) ℂ :=
  fun s => if s < t then 1 else refl ψ

end QStateSearch


