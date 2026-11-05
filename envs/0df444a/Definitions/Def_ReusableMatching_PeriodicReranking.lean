-- Prove2me | Definitions.Def_ReusableMatching_PeriodicReranking
-- name    : ReusableMatching_PeriodicReranking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:24.246885+00:00
-- url     : https://prove2.me/theorems/447d7dfb-caf1-4322-a5a6-6bd310e9db20
-- title:
--   Periodic Reranking (Algorithm 1)
-- statement:
--   **Periodic Reranking (PR)** runs on an OBMRR instance with a parameter $\beta$ and a seed vector $Y$. At every arrival $t$, in the order $t=0,1,\dots,n-1$:
--
--   1. the available resources are those not matched to any arrival $s$ with $t-d<s<t$;
--   2. each resource $v$ has the **reduced price** $r_v\bigl(1-g(y_v^{k(t)})\bigr)$, computed with its seed in the period $k(t)$ of $t$;
--   3. if no available resource is adjacent to $t$, arrival $t$ stays unmatched; otherwise $t$ is matched to an available neighbour of largest reduced price (even when that price is $0$), ties going to the least resource in a fixed priority order.
--
--   Since the seeds change every $d$ arrivals, every resource has a fresh seed each time it returns after a match. For $d\ge n$ the algorithm is the Perturbed Greedy algorithm for non-reusable resources.
--
--   **Formalization Note** The algorithm is a recursion over the arrivals: arrival $t$ is decided from the decisions on the arrivals $0,\dots,t-1$. Ties are broken by the linear order of the resource type; the paper gives no tie rule, and since the resource type and its order are arbitrary, every fixed priority order is covered. The main declaration returns the resource matched to each arrival (or none).
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Algorithm 1, p.8; description p.7

import Mathlib
import Definitions.Def_ReusableMatching_OBMRRInstance
import Definitions.Def_ReusableMatching_period
import Definitions.Def_ReusableMatching_g
import Definitions.Def_ReusableMatching_seedMeasure

namespace ReusableMatching

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

/-- **The reduced price** `r_v (1 − g(y_v^{k(t)}))` of resource `v` at arrival `t`
(arXiv:2110.07084v2, p.7: "the algorithm evaluates reduced prices `r_i(1 − g(y_i))`"; Algorithm 1,
p.8), computed with the seed of `v` in the period `k(t)` that contains `t`. -/
noncomputable def reducedPrice (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (v : V)
    (t : Fin n) : ℝ :=
  I.r v * (1 - g β (Y (v, period I t)))

/-- **Availability** (arXiv:2110.07084v2, p.2): given the decisions `a s` for the arrivals `s < t`
(`a s = some v` when `s` was matched to `v`), resource `v` is available at arrival `t` when it was
not matched at any arrival `s` with `t − d < s < t`: "each resource `i` is available at time `j` if
and only if it had not been matched at some time `j′ ∈ [j − d + 1, j − 1]`". -/
def IsAvailable (I : OBMRRInstance V n) (a : ℕ → Option V) (v : V) (t : ℕ) : Prop :=
  ∀ s : ℕ, s < t → a s = some v → s + I.d ≤ t

/-- **The least maximizer** of `f` on a finite set `C` of resources (`none` when `C` is empty):
the smallest element, for the linear order of `V`, among those where `f` attains its maximum
over `C`. -/
noncomputable def leastArgmax (C : Finset V) (f : V → ℝ) : Option V := by
  classical
  exact if h : C.Nonempty then
    some ((C.filter (fun v => f v = C.sup' h f)).min' (by
      obtain ⟨v, hv, hvM⟩ := Finset.exists_mem_eq_sup' h f
      exact ⟨v, Finset.mem_filter.2 ⟨hv, hvM.symm⟩⟩))
  else none

/-- **The decision of Periodic Reranking at arrival `t`** (arXiv:2110.07084v2, Algorithm 1, p.8,
lines "for every new arrival `j` do … Match `j` to `i∗ = arg max_{i ∈ S, (i,j) ∈ E} r_i(1 − g(y_i))`"),
given the decisions `a` for the earlier arrivals: the least maximizer of the reduced price among the
available neighbours of `t`, or `none` (unmatched) when `t` has no available neighbour. -/
noncomputable def chooseResource (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n)
    (a : ℕ → Option V) (t : Fin n) : Option V := by
  classical
  exact leastArgmax (Finset.univ.filter (fun v => (v, t) ∈ I.E ∧ IsAvailable I a v t))
    (fun v => reducedPrice I β Y v t)

/-- **The run of Periodic Reranking on the first `t` arrivals**: `assignment I β Y t s` is the
resource matched to arrival `s` for `s < t` (`none` if `s` is unmatched), and `none` for `s ≥ t`.
Arrival `t` is decided from the decisions on the arrivals `0, …, t − 1` (`chooseResource`). -/
noncomputable def assignment (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) :
    ℕ → ℕ → Option V
  | 0 => fun _ => none
  | t + 1 =>
    Function.update (assignment I β Y t) t
      (if h : t < n then chooseResource I β Y (assignment I β Y t) ⟨t, h⟩ else none)

/-- **Periodic Reranking (PR)**, Algorithm 1 of Delong, Farhadi, Niazadeh, Sivan & Udwani,
*Online Bipartite Matching with Reusable Resources*, arXiv:2110.07084v2, p.8:

```
Inputs: Set of resources V, usage duration d, parameter β;
Let g(x) = e^{β(x−1)} and S = V;
Every d time units: Generate new i.i.d. ranks y_i ∼ U[0,1] ∀ i ∈ V;
for every new arrival j do
  Update set S by adding resources that returned since arrival j − 1;
  Match j to i∗ = arg max_{i ∈ S, (i,j) ∈ E} r_i(1 − g(y_i));
  S = S \ {i∗};
end
```

`PeriodicReranking I β Y t` is the resource matched to arrival `t` (or `none`) when PR runs on the
instance `I` with parameter `β` and seed vector `Y`.

**Formalization Note.**
* Arrivals are `0`-based; arrival `t` uses the seeds `Y (·, t / d + 1)` of its period (`period`),
  so fresh seeds are used every `d` arrivals, starting at the first arrival; period `0` is the
  dummy period of p.8.
* `S` is the set of available resources: a resource matched to arrival `s` is unavailable at the
  arrivals `s + 1, …, s + d − 1` and available again at `s + d` (`IsAvailable`).
* An arrival with no available neighbour is left unmatched. Otherwise it is matched to a maximizer
  of the reduced price, even when the maximum is `0`.
* Ties are broken by a fixed priority order on the resources: the least maximizer for the linear
  order of `V` (`leastArgmax`). The paper does not specify a tie rule; since `V` and its order are
  arbitrary, every fixed priority order is an instance. -/
noncomputable def PeriodicReranking (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n)
    (t : Fin n) : Option V :=
  assignment I β Y n t

end ReusableMatching


