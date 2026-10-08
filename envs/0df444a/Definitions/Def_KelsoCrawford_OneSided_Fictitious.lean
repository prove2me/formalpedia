-- Prove2me | Definitions.Def_KelsoCrawford_OneSided_Fictitious
-- name    : KelsoCrawford_OneSided_Fictitious
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:57.096101+00:00
-- url     : https://prove2.me/theorems/688755f6-9a76-4f14-ab36-315e460bf7b2
-- title:
--   Section 4 — the fictitious market with m + 1 identical firms
-- statement:
--   Given a production function $v$ on coalitions of $m$ workers and a strictly increasing, continuous utility function $\mu^i$ for each worker, create $m+1$ fictitious firms. Every firm has production $v(C)$ for coalition $C$, every worker values salary $s$ at any firm as $\mu^i(s)$, and all reservation salaries are zero.
--
--   The employer partition of an allocation groups workers according to their assigned fictitious firm. It omits empty firm groups, so it is a partition of the whole worker set.
--
--   **Formalization Note** Utilities are inputs to this construction; the definition itself does not assume their regularity. The paper treats unemployment utility as $\mu^i(0)$ in this construction, making zero the reservation salary.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1493, Section 4, paragraph before Theorem 3 and proof of Theorem 3

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model

namespace KelsoCrawford.OneSided

def fictitious {W : Type} [Fintype W] (v : Finset W → ℝ)
    (μ : W → ℝ → ℝ) : Market W (Fin (Fintype.card W + 1)) where
  u := fun i _ s => μ i s
  y := fun _ => v
  σ := fun _ _ => 0

noncomputable def employerPartition {W F : Type} [Fintype W] [DecidableEq W]
    (A : Allocation W F) : Finpartition (Finset.univ : Finset W) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker A.assign)

end KelsoCrawford.OneSided


