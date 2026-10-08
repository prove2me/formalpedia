-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_experimentKernel
-- name    : YoungConventions_RiskDominance_experimentKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:41.099348+00:00
-- url     : https://prove2.me/theorems/61c64834-976c-411b-be6c-580133e6d173
-- title:
--   The transition kernel $Q^J$ when exactly the players in $J$ experiment
-- statement:
--   For a set $J$ of players, the transition probability from $h$ to $h'$ conditional on exactly the players in $J$ experimenting is
--   $$Q^J_{hh'}=\prod_{j\in J}q_j(s_j\mid h)\prod_{j\notin J}p_j(s_j\mid h)\quad\text{if $h'$ is a successor of $h$ and $s$ is the right-most element of $h'$},$$
--   and $Q^J_{hh'}=0$ if $h'$ is not a successor of $h$.
--
--   These kernels are the building blocks of the perturbed process (2).
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §5, p. 67

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_newest
import Definitions.Def_YoungConventions_AdaptivePlay_IsSuccessor

open Classical

namespace YoungConventions.RiskDominance

/-- **The transition kernel `Q^J` when exactly the players in `J` experiment.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §5, p. 67
(PDF p. 12): "Conditional on this event, the transition probability of moving from `h` to `h′` is
`Q^J_{hh′} = ∏_{j∈J} q_j(s_j|h) ∏_{j∉J} p_j(s_j|h)` if `h′` is a successor of `h` and `s` is the
right-most element of `h′`; `Q^J_{hh′} = 0` if `h′` is not a successor of `h`."

**Formalization Note.** `J` is a `Finset ι`; `j ∉ J` ranges over the complement `Jᶜ` in the finite
player set. -/
noncomputable def experimentKernel {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m] (J : Finset ι)
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) : Matrix (YoungConventions.AdaptivePlay.History S m) (YoungConventions.AdaptivePlay.History S m) ℝ :=
  fun h h' => if YoungConventions.AdaptivePlay.IsSuccessor h h' then
      (∏ j ∈ J, q j h (newest h' j)) * ∏ j ∈ Jᶜ, p j h (newest h' j)
    else 0

end YoungConventions.RiskDominance


