-- Prove2me | Definitions.Def_FulfillFlex_horizonLaw
-- name    : FulfillFlex_horizonLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:17.696144+00:00
-- url     : https://prove2.me/theorems/d05da149-eeaf-418c-9e26-63bc4346537f
-- title:
--   The law of the arrival sequence over $T$ days, with abandonment coins
-- statement:
--   One day of the model unfolds as follows. The demand vector $d$ is drawn from $\nu$; the $\sum_j d_j$ arrivals are put in a uniformly random order; and each arrival, at DC $j$ say, carries an independent coin that is *abandon* with probability $\alpha_j$. The law over $T$ days is the concatenation of $T$ independent such days.
--
--   This is the sample space of the mission: a realization is a finite list of pairs (DC, coin), and a policy reads it from left to right.
--
--   **Formalization Note** `arrivalsOf`, `shuffle`, `abandonCoin` and `attachCoins` are the steps above, `dayLaw` is one day and `horizonLaw` is $T$ days. The coin of an arrival is drawn whether or not it is used; the policy reads it only when the arrival finds no local stock. Abandonment probabilities are elements of `unitInterval`, so $\alpha_j\in[0,1]$ holds by type.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), §1.3, pp.4–5

import Mathlib
import Definitions.Def_FulfillFlex_DC

namespace FulfillFlex

/-- One day's arrivals in a canonical order: DC `0` repeated `d 0` times, then DC `1` repeated
`d 1` times, and so on. The length of the list is `∑ j, d j`. -/
def arrivalsOf {N : ℕ} (d : DC N → ℕ) : List (DC N) :=
  (List.finRange (N + 1)).flatMap fun j => List.replicate (d j) j

/-- A uniformly random reordering of a list: a uniform permutation of its positions. -/
noncomputable def shuffle {X : Type} (l : List X) : PMF (List X) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin l.length))).map fun σ => List.ofFn fun i => l.get (σ i)

/-- The coin of an order at a DC with abandonment probability `a`: `true` (abandon) with
probability `a`. -/
noncomputable def abandonCoin (a : unitInterval) : PMF Bool :=
  PMF.bernoulli (Real.toNNReal a) (Real.toNNReal_le_one.mpr a.2.2)

/-- Attach to each arrival of a list an independent abandonment coin, with the abandonment
probability of the arrival's DC. -/
noncomputable def attachCoins {N : ℕ} (α : DC N → unitInterval) :
    List (DC N) → PMF (List (DC N × Bool))
  | [] => PMF.pure []
  | j :: l => (abandonCoin (α j)).bind fun b => (attachCoins α l).map fun w => (j, b) :: w

/-- **The law of one day's arrival sequence.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), §1.3, pp.4–5: "after the demand Dtj is
randomly generated at each DC j, the cumulative demand arrivals across all DCs, ∑j Dtj, are
sequenced uniformly at random", and "each unit of demand at DC j that is not filled locally …
will be abandoned independently with probability αj".

Draw the demand vector `d ∼ ν`, order the `∑ j, d j` arrivals uniformly at random, and attach to
each arrival an independent coin, which is `true` with probability `α_j` for an arrival at DC `j`.

**Formalization Note** The coin of an arrival is drawn whether or not it is used. The policy reads
it only when the arrival finds no local stock, so an order filled locally never abandons. -/
noncomputable def dayLaw {N : ℕ} (ν : PMF (DC N → ℕ)) (α : DC N → unitInterval) :
    PMF (List (DC N × Bool)) :=
  ν.bind fun d => (shuffle (arrivalsOf d)).bind (attachCoins α)

/-- **The law of the arrival sequence over `T` days.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), §1.3, p.4: the daily demand "is assumed
to be i.i.d. across days". The `T` days are independent draws of `dayLaw ν α`, concatenated in
order.

**Formalization Note** The spillover limit policy is static (it never re-solves at a day boundary),
so the concatenated list is all it needs. -/
noncomputable def horizonLaw {N : ℕ} (ν : PMF (DC N → ℕ)) (α : DC N → unitInterval) :
    ℕ → PMF (List (DC N × Bool))
  | 0 => PMF.pure []
  | T + 1 => (horizonLaw ν α T).bind fun w => (dayLaw ν α).map fun w' => w ++ w'

end FulfillFlex


