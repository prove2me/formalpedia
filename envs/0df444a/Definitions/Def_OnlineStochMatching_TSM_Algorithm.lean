-- Prove2me | Definitions.Def_OnlineStochMatching_TSM_Algorithm
-- name    : OnlineStochMatching_TSM_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:22:19.469428+00:00
-- url     : https://prove2.me/theorems/4cb28dca-6586-40aa-a58c-d18bd623c779
-- title:
--   The two suggested matchings (TSM) online algorithm and its value ALG (Section 4.2.1)
-- statement:
--   Fix a finite bipartite graph $G = (A, I, E)$ and a blue/red colouring of a maximum flow edge set $E_f$ (see the colouring definition of this mission). Impressions arrive one at a time with types $\omega(0), \omega(1), \dots, \omega(n-1)$. For each type $i$ the algorithm maintains a count $x_i$ of the impressions of type $i$ that have arrived so far. When an impression of type $i$ arrives:
--   1. if $x_i = 0$, let $a'$ be the advertiser along $i$'s blue edge (if $i$ has a blue edge);
--   2. if $x_i = 1$, let $a'$ be the advertiser along $i$'s red edge (if $i$ has a red edge);
--   3. assign the impression to $a'$ if $a'$ is not yet assigned; if $a'$ is already assigned, or $x_i > 1$, or the required edge does not exist, make no assignment.
--
--   In words, the first arrival of each type tries the blue edge and the second tries the red edge; later arrivals are never assigned. The value $\mathrm{ALG}(\omega)$ is the number of arrivals the algorithm assigns.
--
--   The algorithm is the subject of Theorem 5 of the paper; its value is compared with the offline optimum OPT.
--
--   **Formalization Note** $x_i$ seen by arrival $t$ is the number of earlier arrivals $s < t$ of the same type. "The advertiser along $i$'s blue edge" is any advertiser $a$ with $(a, i)$ blue; for a TSM colouring there is at most one (a separate theorem of the mission). The set of assigned advertisers is built arrival by arrival, and ALG counts the arrivals whose tried advertiser was still unassigned. The refinement of footnote 7 (falling back to the red edge when the blue edge fails) is not part of the algorithm.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 7, Section 4.2.1 (the TSM algorithm)

import Mathlib

namespace OnlineStochMatching.TSM

open Finset

variable {A I : Type}

/-- The advertiser along the blue edge of the impression type `i`, if `i` has a blue edge
(Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.1, p. 7). For a TSM colouring `i` has at most one blue edge (the note of
p. 7), so the choice below is forced. -/
noncomputable def blueAd (blue : Finset (A × I)) (i : I) : Option A := by
  classical
  exact if h : ∃ a, (a, i) ∈ blue then some h.choose else none

/-- The advertiser along the red edge of the impression type `i`, if `i` has a red edge (§4.2.1,
p. 7). For a TSM colouring `i` has at most one red edge, so the choice below is forced. -/
noncomputable def redAd (red : Finset (A × I)) (i : I) : Option A := by
  classical
  exact if h : ∃ a, (a, i) ∈ red then some h.choose else none

/-- The count `x_i` of §4.2.1 (p. 7) seen by arrival `t`: the number of earlier arrivals `s < t` of
the same impression type `ω t`. -/
def prevCount [DecidableEq I] {n : ℕ} (ω : Fin n → I) (t : Fin n) : ℕ :=
  (Finset.univ.filter fun s : Fin n => s < t ∧ ω s = ω t).card

/-- The advertiser `a'` that the TSM algorithm tries for arrival `t` (§4.2.1, p. 7): the ad along
the blue edge of `ω t` if `x_{ω t} = 0`, the ad along its red edge if `x_{ω t} = 1`, and none if
`x_{ω t} > 1` or the required edge does not exist. -/
noncomputable def tryAd [DecidableEq I] {n : ℕ} (blue red : Finset (A × I)) (ω : Fin n → I)
    (t : Fin n) : Option A :=
  if prevCount ω t = 0 then blueAd blue (ω t)
  else if prevCount ω t = 1 then redAd red (ω t)
  else none

/-- The set of advertisers already assigned before the arrival with index `k` is processed, when
the TSM algorithm runs on the arrival sequence `ω`: arrival `t` is assigned to its tried ad `a'` if
`a'` is unassigned, and otherwise is not assigned (inserting an assigned ad changes nothing). -/
noncomputable def assignedBefore [DecidableEq A] [DecidableEq I] {n : ℕ}
    (blue red : Finset (A × I)) (ω : Fin n → I) : ℕ → Finset A
  | 0 => ∅
  | k + 1 =>
    if h : k < n then
      match tryAd blue red ω ⟨k, h⟩ with
      | some a => insert a (assignedBefore blue red ω k)
      | none => assignedBefore blue red ω k
    else assignedBefore blue red ω k

/-- Arrival `t` is assigned by the TSM algorithm: it has a tried advertiser `a'` (blue edge on the
first arrival of its type, red edge on the second) and `a'` was unassigned when `t` arrived. -/
def Assigns [DecidableEq A] [DecidableEq I] {n : ℕ} (blue red : Finset (A × I))
    (ω : Fin n → I) (t : Fin n) : Prop :=
  ∃ a, tryAd blue red ω t = some a ∧ a ∉ assignedBefore blue red ω t.val

/-- `ALG(Î)` for the two suggested matchings algorithm (§4.2.1, p. 7, and §2, p. 4): the number of
arrivals of `ω` that the algorithm guided by the colour classes `blue, red` assigns. -/
noncomputable def ALG [DecidableEq A] [DecidableEq I] {n : ℕ} (blue red : Finset (A × I))
    (ω : Fin n → I) : ℕ := by
  classical
  exact (Finset.univ.filter (Assigns blue red ω)).card

end OnlineStochMatching.TSM


