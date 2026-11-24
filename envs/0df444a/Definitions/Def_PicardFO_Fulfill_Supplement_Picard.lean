-- Prove2me | Definitions.Def_PicardFO_Fulfill_Supplement_Picard
-- name    : PicardFO_Fulfill_Supplement_Picard
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:07:41.519985+00:00
-- url     : https://prove2.me/theorems/ce0e7a98-5121-4562-ac0e-23795170ab0a
-- title:
--   Retailer ownership, numerical Picard sweeps, R and the next replenishment time
-- statement:
--   Let $o(n)$ be the process owning retailer $n$; all its orders belong to that process. Sequential simulation and all process runs use the immutable general System definitions. A sweep from cache $\beta$ evaluates the policy on owned orders and otherwise replays the full numerical cached pair if feasible, or zero if infeasible. Each cache entry is taken from its owner. The initialized cache is the zero action path.
--   $$
--   R=\sum_{u=0}^{T}\mathbf1\{q^{\rm seq}_{u,0}>0\},\qquad t_2=\min\bigl(\{u:t_1<u\le T,\ q^{\rm seq}_{u,0}>0\}\cup\{T\}\bigr).
--   $$
--   These definitions retain exact quantities rather than replenishment indicators. No reset-to-$S$ rule is substituted when a cached quantity is positive.
--
--   **Formalization Note** Source orders $1,\ldots,T$ correspond to Lean $0,\ldots,T-1$. The undefined source time zero is an unexecuted zero-action sentinel, retaining the displayed inclusive count without adding an initial replenishment. The minimum is always of a nonempty finite set; without a future replenishment it is $T$. At $T=0$, the count and terminal fallback are both zero. Runs and sweeps are defined beyond the horizon, but a finite prefix depends only on that prefix.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 15, Appendix B.2; Algorithm 1, p. 5

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Supplement_Policy

namespace PicardFO.Fulfill.Supplement

namespace Model
variable {N : ℕ} {Ω ι : Type*}

/-- Sequential numerical actions, using the immutable general sequential run. -/
noncomputable def sequential (D : Model N Ω) (P : Policy N Ω) (x : Stock N)
    (ω : ℕ → Ω) : ℕ → Action := D.system.seqAct (P.action D) x ω

/-- The action of process m for a single sweep with previous cache α. -/
noncomputable def process (D : Model N Ω) (P : Policy N Ω) (x : Stock N)
    (ω : ℕ → Ω) (own : Fin N → ι) (α : ℕ → Action) (m : ι) (t : ℕ) : Action :=
  D.system.procAct (P.action D) ω (fun t => own (D.retailer (ω t))) α m
    (D.system.procState (P.action D) x ω (fun t => own (D.retailer (ω t))) α m t) t

/-- One sweep, delegating to published procAct/procState, with retailer ownership. -/
noncomputable def sweep (D : Model N Ω) (P : Policy N Ω) (x : Stock N)
    (ω : ℕ → Ω) (own : Fin N → ι) (α : ℕ → Action) (t : ℕ) : Action :=
  D.process P x ω own α (own (D.retailer (ω t))) t

/-- Algorithm 1's actual cache, including its zero-action initialization. -/
noncomputable def cached (D : Model N Ω) (P : Policy N Ω) (x : Stock N)
    (ω : ℕ → Ω) (own : Fin N → ι) : ℕ → ℕ → Action :=
  D.system.cache (P.action D) x ω (fun t => own (D.retailer (ω t)))

/-- Source times 1,...,T correspond to Lean 0,...,T-1. Source time 0 is an
unexecuted sentinel with zero action, so the printed sum 0,...,T is retained. -/
def sourceAction (α : ℕ → Action) (t : ℕ) : Action :=
  if t = 0 then (0, 0) else α (t - 1)

open Classical in
/-- The source's inclusive sum R, without counting a fictitious initial replenishment. -/
noncomputable def replenishments (D : Model N Ω) (P : Policy N Ω) (x : Stock N)
    (ω : ℕ → Ω) (T : ℕ) : ℕ :=
  ((Finset.range (T + 1)).filter fun t => 0 < (sourceAction (D.sequential P x ω) t).1).card

open Classical in
/-- Minimum of the future replenishment times union the singleton terminal time.
This implements the explicitly parenthesized terminal fallback on page 15. -/
noncomputable def nextReplenishment (D : Model N Ω) (P : Policy N Ω) (x : Stock N)
    (ω : ℕ → Ω) (T t₁ : ℕ) : ℕ :=
  let future := (Finset.Icc (t₁ + 1) T).filter
    (fun t => 0 < (sourceAction (D.sequential P x ω) t).1)
  (insert T future).min' (Finset.mem_insert_self T future |> fun h => ⟨T, h⟩)

end Model
end PicardFO.Fulfill.Supplement


