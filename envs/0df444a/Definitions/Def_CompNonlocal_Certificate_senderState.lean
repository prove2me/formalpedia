-- Prove2me | Definitions.Def_CompNonlocal_Certificate_senderState
-- name    : CompNonlocal_Certificate_senderState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:36.823813+00:00
-- url     : https://prove2.me/theorems/abd733ad-2157-4d1c-9753-8d9441a43017
-- title:
--   The sender's register $S=(y,\mathrm{td})$ jointly with $X=x$
-- statement:
--   The verifier's (sender's) retained register $S=(y,\mathrm{td})$, unnormalized, jointly with the event $X=x$: block diagonal in the question outcome, its trace is $\Pr[X=x]$ and $\omega_{S|x}$ is it divided by $\Pr[X=x]$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §6.3, p.30 and §8.1, p.35

import Mathlib
import Definitions.Def_CompNonlocal_Certificate

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The verifier's (sender's) retained register `S = (y, td)` jointly with the event `X = x`,
unnormalized. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and
Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §6.3, p.30 ("Let S hold the
verifier's retained information (y, td), and let ω_{S|x} denote its state conditioned on X = x")
and §8.1, p.35 ("retain st_S := (y, td) in register S").

**Formalization Note** The classical part of `S` is recorded by the question outcome `o` (which
contains `y = o.drop (lx κ)`). The matrix is block diagonal in `o`: block `o` is `td_o` when
`o.take (lx κ) = x` and `0` otherwise; its trace is `Pr[X = x]`, and `ω_{S|x}` is it divided by
`Pr[X = x]`. -/
noncomputable def Certificate.senderState (c : Certificate) (κ : ℕ) (x : Str) :
    Matrix (Bits (c.Qg κ).outC.length × Bits (c.Qg κ).outQ.length)
      (Bits (c.Qg κ).outC.length × Bits (c.Qg κ).outQ.length) ℂ :=
  Matrix.of fun S S' =>
    if S.1 = S'.1 ∧ (List.ofFn S.1).take (c.lx κ) = x then c.td κ (List.ofFn S.1) S.2 S'.2 else 0

end CompNonlocal


