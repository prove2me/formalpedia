-- Prove2me | Definitions.Def_HierADA_auxRun
-- name    : HierADA_auxRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:03:28.641893+00:00
-- url     : https://prove2.me/theorems/4fdef8ae-0711-4d38-a1e3-4cdcc3b1632c
-- title:
--   Auxiliary execution with correction limits $B_j$
-- statement:
--   The **auxiliary execution** is the execution of Algorithms 1–2 with the parameters $\tau$ and $B_j$ of Section 3.2. When a correction makes $T_j=B_j$, it "performs the correction and then stops accessing the data". It is given $\sum_jB_j+1$ scans per query, which is never exhausted: every scan but the last one of a query ends with a correction, and at most $\sum_jB_j$ corrections happen before a limit is reached.
--
--   Its privacy is established first (Theorem 3.7). Only then is it shown that, on the good event, it reaches no limit and agrees with the original mechanism (Propositions 3.4 and 3.5).
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_params__e3298e
import Definitions.Def_HierADA_run

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **The auxiliary execution with correction limits** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18: "whenever a correction makes `T_j = B_j`, the
auxiliary version performs the correction and then stops accessing the data".

It is `run` with threshold `prm.τ`, the correction limits `prm.B`, and `∑_j B_j + 1` scans per query,
which is never exhausted: every scan but the last of a query ends with a correction, and at most
`∑_j B_j` corrections happen before a limit is reached. -/
noncomputable def auxRun {X : Type} (prm : Params) (n : Fin prm.p → ℕ)
    (S : (j : Fin prm.p) → Fin (n j) → X) (z : Noise) (A : Analyst X) (k : ℕ) :
    RunState X n :=
  run prm.τ n (some prm.B) (∑ j, prm.B j + 1) S z A k

end HierADA


