-- Prove2me | Definitions.Def_NondetConn_Supplement_solves
-- name    : NondetConn_Supplement_solves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:05:38.915106+00:00
-- url     : https://prove2.me/theorems/38ecd41a-06a9-4dc5-9240-643ab38329a2
-- title:
--   Worst-case error for receiver-output communication protocols
-- statement:
--   Let $f:X×Y\to Z$ be a two-party function with a promise on its inputs. A randomized protocol **solves $f$ with error at most $\varepsilon$** if, on every promised pair $(x,y)$, the probability that the receiver of the last message outputs a value different from $f(x,y)$ is at most $\varepsilon$.
--
--   The probability averages the finite public coin and the local private message and output kernels. For a zero-bit transcript, where there is no receiver of a last message, both local outputs are required to be correct.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §3 Communication complexity, p.8 (PDF p.10)

import Definitions.Def_NondetConn_Supplement_lastSpeaker

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- A randomized two-party protocol solves `f` with worst-case error at most `ε` on the
promised inputs. Only the receiver of the last message is required to output correctly.

For a nonempty transcript, Bob is checked when Alice sent the last bit, and Alice is checked
when Bob sent the last bit. For a zero-bit transcript both local outputs are checked; this
only fixes the otherwise undefined receiver convention at communication cost zero. -/
noncomputable def solves {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Z] (P : Protocol X Y Z Z) (promise : X → Y → Prop)
    (f : X → Y → Z) (ε : ℝ) : Prop := by
  classical
  exact ∀ x y, promise x y →
    (∑ ω, (P.publicLaw ω).toReal *
      ∑ z : (P.tree ω).Trace × Z × Z,
        if (match lastSpeaker (P.tree ω) (P.bits ⟨ω, z.1⟩) with
          | some true => z.2.2 ≠ f x y
          | some false => z.2.1 ≠ f x y
          | none => z.2.1 ≠ f x y ∨ z.2.2 ≠ f x y)
        then ((P.tree ω).finiteRun x y z).toReal else 0) ≤ ε

end NondetConn.Supplement


