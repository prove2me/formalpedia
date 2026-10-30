-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_IsValidPolicy
-- name    : OfflineStochMatching_UnitPatience_IsValidPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:37:11.049655+00:00
-- url     : https://prove2.me/theorems/4e69292b-874f-4fc1-987f-8211946e1218
-- title:
--   Probing policy respecting the matching and patience constraints
-- statement:
--   A probing policy $\pi$ is **valid** on $G$ if, for every activeness realization $P$ and every step at which $\pi$ asks to probe an edge $e$ from the current history $h$:
--
--   1. $e$ has not been probed in $h$;
--   2. at each endpoint $x$ of $e$, no edge incident to $x$ has been probed and found active in $h$ ($x$ is unmatched), and fewer than $t_x$ edges incident to $x$ have been probed in $h$ ($x$ has patience left).
--
--   This is the requirement that a probing algorithm satisfy the matching and patience constraints with probability 1.
--
--   **Formalization Note** Validity is required on every realization, including those of probability zero (a policy that violates the constraints only on null realizations has the value of a valid one). Probing each edge at most once loses nothing: a probed edge is either matched or known to be inactive.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §1, p. 1 (an edge whose endpoints are unmatched can be probed); §1, p. 2 (at most t_v edges incident to v can be probed; constraints w.p. 1)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_incident
import Definitions.Def_OfflineStochMatching_UnitPatience_runPolicy

namespace OfflineStochMatching.UnitPatience

/-- **A probing policy that respects the matching and patience constraints.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §1, p. 1: "An edge whose
endpoints are unmatched can be probed"; §1, p. 2: "at most `t_v` of the edges incident to `v`
can be probed"; "a probing algorithm must satisfy these constraints with probability (w.p.) 1".

`IsValidPolicy G π` says: for every activeness realization `P` and every step `n`, if `π` asks to
probe `e` at the history `h = runPolicy π P n`, then
1. `e` has not been probed in `h`, and
2. at each endpoint `x` of `e`: no edge incident to `x` has been probed and found active in `h`
   (`x` is unmatched), and fewer than `t_x` edges incident to `x` have been probed in `h`
   (patience is left).

**Formalization Note.** Validity is required on every realization, including those of
probability zero; a policy that violates the constraints only on null realizations has the value
of a valid one (stop instead). Probing each edge at most once loses nothing: a probed edge is
either matched or known to be inactive, so a re-probe only spends patience. -/
def IsValidPolicy {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V] (G : StochGraph V E)
    (π : Policy E) : Prop :=
  ∀ (P : E → Bool) (n : ℕ) (e : E), π (runPolicy π P n) = some e →
    (∀ b : Bool, (e, b) ∉ runPolicy π P n) ∧
    ∀ x, (x = G.src e ∨ x = G.dst e) →
      (∀ e', (e', true) ∈ runPolicy π P n → e' ∉ incident G x) ∧
      ((((runPolicy π P n).filter (fun eb => decide (eb.1 ∈ incident G x))).length : ℕ) : ℕ∞)
        < G.t x

end OfflineStochMatching.UnitPatience


