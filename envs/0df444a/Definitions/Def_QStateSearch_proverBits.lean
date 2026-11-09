-- Prove2me | Definitions.Def_QStateSearch_proverBits
-- name    : QStateSearch_proverBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:48.481242+00:00
-- url     : https://prove2.me/theorems/df361ecc-af43-4a76-af15-f07c727391ea
-- title:
--   Total padded prover communication $B$
-- statement:
--   The total padded prover-to-verifier communication of $V$ is
--   $$
--   B(V)=\sum_{\text{prover messages}} b,
--   $$
--   the sum of the padded lengths of all prover-message steps. The theorems assume $B(V)\le B$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, p.10

import Mathlib
import Definitions.Def_QStateSearch_Verifier

namespace QStateSearch

/-- The total padded prover-to-verifier communication `B` of a verifier: the sum of the
padded lengths `b` of all its prover-message steps.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, p.10: "Let B be the total padded prover-to-verifier communication in the
protocol." -/
def proverBits {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) : ℕ :=
  (V.steps.map fun s => match s with
    | .pmsg b _ => b
    | _ => 0).sum

end QStateSearch


