-- Prove2me | Definitions.Def_MultiServerAppt_alphaStep
-- name    : MultiServerAppt_alphaStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:51.046848+00:00
-- url     : https://prove2.me/theorems/12af9f1d-c2a0-45da-8444-22df09b4bb94
-- title:
--   The arrival map $f(p,\alpha)$, Eq. (15)
-- statement:
--   Given a vector $p$ on the states just before an arrival, with empty-state mass $p_0=1-p\mathbf 1$, the map $f(p,\alpha)$ gives the vector at the arrival.
--
--   1. For $j\ge s+1$: the new vector on $(j,m)$ is $p_{j-1,m}$, as the arriving client waits.
--   2. For $2\le j\le s$: the new vector on $(j,(a,m))$ is $\alpha_a\,p_{j-1,m}$, as the arriving client starts in phase $a$.
--   3. For $j=1$: the new vector on $(1,(a))$ is $\alpha_a\,p_0$.
--
--   This is the empty state's only way back into the transient states.
--
--   **Formalization Note** The vector is written in target coordinates. The Kronecker factor $\alpha$ takes the first coordinate, as on the page. The `dite` on $0<s$ never fails in use, since $1\le s$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (15), p.14

import Mathlib
import Definitions.Def_MultiServerAppt_State

namespace MultiServerAppt

/-- The map `f(p, α)` of Eq. (15): the vector `p` on the states with `j` clients just before an
arrival becomes the vector at the arrival. A state with `j ≥ s` clients moves to `j + 1` and keeps
its phases; a state with `j < s` clients, including the empty one of mass `1 - ∑ p`, moves to `j + 1`
and the arriving client starts service in a phase with law `α`. Kuiper–Lee, Appointment Scheduling
for Multiple Servers, SSRN 3975471, Eq. (15), p.14.

**Formalization Note** The vector is written in target coordinates: `j + 1 ≥ s + 1` comes from `p_j`,
and `j + 1 ≤ s` comes from `α ⊗ p_j`, the arriving client taking the first coordinate as in the
page's Kronecker product. `q = 0` in the saturated part is the block `j + 1 = s + 1`, which reads
`p_s`. The `dite` on `0 < s` is never false in use (`1 ≤ s`). -/
def alphaStep {ι : Type*} [Fintype ι] (α : ι → ℝ) (s i : ℕ) (p : State ι s i → ℝ) :
    State ι s (i + 1) → ℝ
  | .inl r =>
    Fin.cases
      (if hs : 0 < s then
        p (.inr ⟨⟨s - 1, by omega⟩, fun l => r.2 (Fin.cast (by simp; omega) l)⟩)
      else 0)
      (fun q => p (.inl (q, r.2))) r.1
  | .inr r =>
    α (r.2 0) *
      if h : (r.1 : ℕ) = 0 then 1 - ∑ a, p a
      else p (.inr ⟨⟨r.1 - 1, by omega⟩,
        fun l => r.2 (Fin.succ (Fin.cast (by simp; omega) l))⟩)

end MultiServerAppt


