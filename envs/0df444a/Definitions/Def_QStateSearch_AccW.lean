-- Prove2me | Definitions.Def_QStateSearch_AccW
-- name    : QStateSearch_AccW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:17.715969+00:00
-- url     : https://prove2.me/theorems/f14f5b41-23da-4c55-a10a-1406950932ba
-- title:
--   $\mathrm{Acc}_W(V,P)$
-- statement:
--   For an oracle $W$, $\mathrm{Acc}_W(V,P)$ is the verifier's acceptance probability when interacting with the deterministic prover $P$ and every query uses $W$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, p.9

import Mathlib
import Definitions.Def_QStateSearch_acc

namespace QStateSearch

/-- `AccW V O P = Acc_O(V, P)`: the acceptance probability of `V` with prover `P` when every
query uses the oracle `O`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, p.9: "When the oracle is W, let Acc_W(V, P) be the verifier's acceptance
probability when interacting with P." -/
noncomputable def AccW {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (O : Matrix (Fin D) (Fin D) ℂ) (P : Prover) : ℝ :=
  acc V (fun _ => O) P

end QStateSearch


