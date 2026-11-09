-- Prove2me | Definitions.Def_QStateSearch_fid
-- name    : QStateSearch_fid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:50.658194+00:00
-- url     : https://prove2.me/theorems/9a47191f-3cb9-4996-a76a-5bb797c3eaa9
-- title:
--   Average output fidelity $\langle\psi|\rho_{\mathrm{out}}|\psi\rangle$
-- statement:
--   When every query uses $R_\psi$ and the prover is $P$, the **output fidelity** of $V$ is
--   $$
--   F(V,P,\psi)=\sum_h\mathrm{ov}(\psi,\phi_h)=\langle\psi|\rho_{\mathrm{out}}|\psi\rangle ,
--   $$
--   where $\phi_h$ are the final branch vectors and $\rho_{\mathrm{out}}$ is the final state of the oracle-input register, averaged over the protocol's randomness. The paper defines fidelity as "$\langle\psi|\rho|\psi\rangle$ for the verifier's output $\rho$, averaged over the hidden state and the protocol's randomness"; the average over the hidden state is taken in Theorem 4(c).
--
--   **Formalization Note** The verifier's output register is its $D$-dimensional oracle-input register at the end of the run; any other output register can be swapped there by a final unitary step.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Theorem 1, p.2; p.3

import Mathlib
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_transcripts
import Definitions.Def_QStateSearch_branch
import Definitions.Def_QStateSearch_overlap
import Definitions.Def_QStateSearch_refl

namespace QStateSearch

/-- The average fidelity `⟨ψ|ρ_out|ψ⟩` of the verifier's output with `ψ`, when every query uses
`R_ψ` and the prover is `P`: `∑_h overlap ψ φ_h` over the complete transcripts, where the output
register is the oracle-input register `Fin D` at the end of the run.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Theorem 1, p.2, and p.3: "Fidelity means ⟨ψ|ρ|ψ⟩ for the verifier's output ρ, averaged
over the hidden state and the protocol's randomness."

**Formalization Note.** The verifier's output register is taken to be its `D`-dimensional
oracle-input register at the end of the run (any other output register can be swapped there by
a final unitary step). `ρ_out` is its reduced state summed over transcripts, so `fid` is the
average over the protocol's randomness; the average over the hidden state is the integral
against the Haar measure in `theorem_4`. -/
noncomputable def fid {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (P : Prover) (ψ : EuclideanSpace ℂ (Fin D)) : ℝ :=
  ∑ h ∈ transcripts V.steps [], overlap ψ (branch (fun _ => refl ψ) P V.steps V.init [] 0 h)

end QStateSearch


