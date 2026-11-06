-- Prove2me | Definitions.Def_AnytimeAdaVR_pathReport
-- name    : AnytimeAdaVR_pathReport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:24.930051+00:00
-- url     : https://prove2.me/theorems/374d30ef-fff9-4797-b786-76207d026d23
-- title:
--   Report of each path after $n$ local queries
-- statement:
--   For $i\in\{S,M,D\}$ and $n\ge1$, $X_i(n)$ is the report $R_{i,n}$ of path $i$ after $n$ local queries, computed from path $i$'s own samples and coins on the tape. At the end of global round $n$ every path has made exactly $n$ local queries, so these are the reports frozen at checkpoint $n$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.3, pp.9–10

import Mathlib
import Definitions.Def_AnytimeAdaVR_Tape
import Definitions.Def_AnytimeAdaVR_smReport
import Definitions.Def_AnytimeAdaVR_dReport

namespace AnytimeAdaVR

/-- **The report of each path after `n` local queries, read off the tape.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.3, p.9:
"At rounds n = 1, 2, 4, …, freeze the current reports as X_S, X_M, X_D", and p.10: "At the end of
global round r, each path has made exactly r individual gradient evaluations".

`pathReport g xinit i ω n` is `R_{S,n}`, `R_{M,n}` or `R_{D,n}` for `i = S, M, D`, computed from
path `i`'s own sample stream `ω.1 (i, ·)` and coins `ω.2.1 (i, ·)`. -/
noncomputable def pathReport {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (i : Path) (ω : Tape Ξ) (n : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  match i with
  | .S => smReport .S g xinit (fun t => ω.1 (.S, t)) (fun r => ω.2.1 (.S, r)) n
  | .M => smReport .M g xinit (fun t => ω.1 (.M, t)) (fun r => ω.2.1 (.M, r)) n
  | .D => dReport g xinit (fun t => ω.1 (.D, t)) (fun r => ω.2.1 (.D, r)) n

end AnytimeAdaVR


