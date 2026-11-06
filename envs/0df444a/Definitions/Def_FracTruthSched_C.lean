-- Prove2me | Definitions.Def_FracTruthSched_C
-- name    : FracTruthSched_C
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:57.031997+00:00
-- url     : https://prove2.me/theorems/ec080b32-7f74-49dc-b3e1-6cf7d5ecbd66
-- title:
--   Eligible integral optimum $C(t)$ of a graph input
-- statement:
--   For a graph input $t$ of $MC_\ell$, $C(t)$ is the **optimal integral makespan among eligible allocations**:
--   $$C(t)=\min_{\sigma\ \text{eligible}}\ \max_i\sum_{e:\ \sigma(e)=i}t_{ie},$$
--   where an integral allocation $\sigma$ is eligible if it sends every edge to one of its endpoints and every self-loop to its owner. $C$ is the benchmark in the load bound (7) of the padding lemma.
--
--   **Formalization Note.** Restricting to eligible allocations is essential: graph inputs are encoded with zeros at non-incident pairs, so the minimum over all allocations would be $0$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 3 and the paragraph after it, p.9; Definition 2, p.8

import Mathlib
import Definitions.Def_FracTruthSched_incident
import Definitions.Def_FracTruthSched_schedMakespan

set_option autoImplicit false

namespace FracTruthSched

/-- The **eligible integral optimum** `C(t)` of a graph input (Anastasiadis et al.,
arXiv:2611.06642v1, p.9: "Write C(t) for the optimal integral makespan of graph input t among
eligible allocations"): the minimum of `max_i Σ_{e : σ e = i} t_ie` over the integral allocations
`σ` that send every edge to one of its endpoints and every self-loop to its owner (Definition 2).

**Formalization Note.** The minimum is `Finset.inf'` over the eligible maps `σ`; the set is
nonempty (each edge to its smaller endpoint, each loop to its owner). Restricting to eligible `σ`
is essential: since a graph input is encoded with zeros at non-incident pairs, the minimum over all
`σ` would be `0` at every input. -/
noncomputable def C {n ℓ : ℕ} [NeZero n] (t : Fin n → CoreTask n ℓ → ℝ) : ℝ :=
  (Finset.univ.filter (fun σ : CoreTask n ℓ → Fin n => ∀ e, incident (σ e) e)).inf'
    (by
      refine ⟨fun e => Sum.elim (fun q => q.1.1.1) id e, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro e
      cases e <;> simp [incident])
    (fun σ => schedMakespan t σ)

end FracTruthSched


