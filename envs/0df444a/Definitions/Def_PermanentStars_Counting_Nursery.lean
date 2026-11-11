-- Prove2me | Definitions.Def_PermanentStars_Counting_Nursery
-- name    : PermanentStars_Counting_Nursery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:11.934248+00:00
-- url     : https://prove2.me/theorems/a6c81ac4-938d-4f9f-9e3c-e3fd56796403
-- title:
--   Bounded small stars and deferred-leaf nurseries
-- statement:
--   A nursery vector $d$ records the number of deferred leaves assigned to each center image. Its mass is $\sum_jd_j$ and its support counts nonzero entries. The main state is $(S,d;k,j)$, with nursery and open-star leaves included in $S$.
--
--   The main graph retains basic transitions, restricts Grow to $k<r$, and permits Defer only in a closed state. Defer takes the least uncovered $i$, chooses $j$, assigns label $A_{ij}$, and increments $d_j$. Retained states satisfy $|\operatorname{supp}(d)|\le\alpha_r n$ and the elementary leaf-count invariants. All reachable states satisfy the finite bounds $d_j\le n$ and $\sum_jd_j\le|S|$.
--
--   Different stars may share a center image. Nursery coordinates count leaves, not stars; the final gadget controls large-block counts.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), §§4.1–4.2, pp.7–8; equation (13), p.8

import Definitions.Def_PermanentStars_Counting_Basic
import Definitions.Def_PermanentStars_Counting_Partitions

namespace PermanentStars.Counting

abbrev Nursery (n : ℕ) := Fin n → Fin (n + 1)
abbrev MainState (n : ℕ) := BasicState n × Nursery n

def zeroNursery (n : ℕ) : Nursery n := fun _ => 0

def nurseryMass {n : ℕ} (d : Nursery n) : ℕ := ∑ j, (d j).val

def nurserySupport {n : ℕ} (d : Nursery n) : ℕ :=
  (Finset.univ.filter (fun j => d j ≠ 0)).card

def mainValid {n : ℕ} (P : Cutoffs) (r : ℕ) (s : MainState n) : Prop :=
  basicValid s.1 ∧ nurseryMass s.2 ≤ s.1.1.card ∧
  (∀ k j, s.1.2 = some (k, j) → nurseryMass s.2 + k.val ≤ s.1.1.card) ∧
  (nurserySupport s.2 : ℚ) ≤ P.alpha r * n

/-- Grow is truncated at r; Defer is closed-only and uses the least uncovered leaf. -/
def mainRule {n : ℕ} (P : Cutoffs) (r : ℕ) (s t : MainState n) (l : Label n) : Prop :=
  mainValid P r s ∧ mainValid P r t ∧
  ((s.2 = t.2 ∧ basicRule s.1 t.1 l ∧
      (∀ k j i, s.1.2 = some (k, j) → l = .negVar i j → k.val < r)) ∨
   (∃ i j, s.1.2 = none ∧ leastUncovered s.1.1 i ∧
      t.1 = (insert i s.1.1, none) ∧ l = .var i j ∧
      ∀ v, (t.2 v).val = (s.2 v).val + if v = j then 1 else 0))

def terminal {n : ℕ} (d : Nursery n) : MainState n := ((Finset.univ, none), d)

end PermanentStars.Counting


