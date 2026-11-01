-- Prove2me | Definitions.Def_WagerFairDiv_AllocationProperties
-- name    : WagerFairDiv_AllocationProperties
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:01.219253+00:00
-- url     : https://prove2.me/theorems/83c4af0f-f167-4f05-b66e-69633ff73c4e
-- title:
--   Proportionality, Pareto optimality and weak / strict incentive compatibility of allocation mechanisms (Definitions 1, 3, 4)
-- statement:
--   Let $\mathcal A$ be a mechanism on report profiles $\hat{\mathbf v}\in\Delta_m^n$ and positive weights $\mathbf e$, with $E=\sum_i e_i$.
--
--   1. **Proportional** (Definition 1, p.2): for all $\hat{\mathbf v}$, $\mathbf e$ and every agent $i$,
--   $$\hat v_i\big(\mathcal A_i(\hat{\mathbf v},\mathbf e)\big)\ \ge\ \frac{e_i}{E}.$$
--   Values are the **reported** ones.
--   2. **Pareto optimal** (Definition 3, p.3): for all $\hat{\mathbf v}$, $\mathbf e$ and every feasible alternative allocation $\{\mathbf a'_1,\dots,\mathbf a'_n\}$, if $\hat v_i(\mathbf a'_i)>\hat v_i(\mathcal A_i(\hat{\mathbf v},\mathbf e))$ for some $i$, then $\hat v_j(\mathbf a'_j)<\hat v_j(\mathcal A_j(\hat{\mathbf v},\mathbf e))$ for some $j$.
--   3. **Weakly incentive compatible** (Definition 4, p.3): for every agent $i$ with true values $\mathbf v_i\in\Delta_m$, all reports $\hat{\mathbf v}$ and weights $\mathbf e$,
--   $$v_i\big(\mathcal A_i((\mathbf v_i,\hat{\mathbf v}_{-i}),\mathbf e)\big)\ \ge\ v_i\big(\mathcal A_i(\hat{\mathbf v},\mathbf e)\big).$$
--   4. **Strictly incentive compatible** (Definition 4, p.3): weakly incentive compatible, and the inequality is strict whenever $\mathbf v_i\ne\hat{\mathbf v}_i$.
--
--   These are the fair-division properties that Theorems 1–3 transfer to wagering mechanisms.
--
--   **Formalization Note** The alternatives in Pareto optimality range over **feasible** allocations (§2.1, p.2). The profile $(\mathbf v_i,\hat{\mathbf v}_{-i})$ is `Function.update v̂ i vᵢ`. Strict IC is encoded as weak IC together with strictness on every misreport; at $\mathbf v_i=\hat{\mathbf v}_i$ the two sides coincide, so this adds no condition.
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Definition 1 (proportional), p.2; Definition 3 (Pareto optimal), p.3; Definition 4 (weakly / strictly incentive compatible), p.3; feasible allocations, §2.1, p.2. PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model

namespace WagerFairDiv

variable {n m : ℕ}

/-- **Proportionality** (Definition 1, p.2): for all `v̂`, `e` and every agent `i`,
`v̂ᵢ(Aᵢ(v̂, e)) ≥ eᵢ / E`, the agent's reported value of her bundle is at least her weight
share. Values are the **reported** ones on both sides. -/
def Proportional (A : Mech n m) : Prop :=
  ∀ (v : Profile n m) (e : PosVec n) (i : Fin n), e.1 i / e.total ≤ val (v i).1 (A v e i)

/-- **Pareto optimality** (Definition 3, p.3): for all `v̂`, `e` and every alternative allocation
`a'`, if `v̂ᵢ(a'ᵢ) > v̂ᵢ(Aᵢ(v̂, e))` for some `i`, then `v̂ⱼ(a'ⱼ) < v̂ⱼ(Aⱼ(v̂, e))` for some `j`.

**Formalization Note.** The alternative allocations range over the **feasible** allocations of
§2.1, p.2 (`IsFeasibleAlloc`). -/
def ParetoOptimal (A : Mech n m) : Prop :=
  ∀ (v : Profile n m) (e : PosVec n) (a' : Fin n → Fin m → ℝ), IsFeasibleAlloc a' →
    (∃ i, val (v i).1 (A v e i) < val (v i).1 (a' i)) →
    ∃ j, val (v j).1 (a' j) < val (v j).1 (A v e j)

/-- **Weak incentive compatibility** of an allocation mechanism (Definition 4, p.3): for every
agent `i` with (true) values `vᵢ`, all reports `v̂` and weights `e`,
`vᵢ(Aᵢ((vᵢ, v̂₋ᵢ), e)) ≥ vᵢ(Aᵢ(v̂, e))`.

**Formalization Note.** The profile `(vᵢ, v̂₋ᵢ)` is `Function.update v̂ i vᵢ`. Both sides are
evaluated with the true values `vᵢ`. -/
def AllocWeakIC (A : Mech n m) : Prop :=
  ∀ (i : Fin n) (vi : stdSimplex ℝ (Fin m)) (v : Profile n m) (e : PosVec n),
    val vi.1 (A v e i) ≤ val vi.1 (A (Function.update v i vi) e i)

/-- **Strict incentive compatibility** of an allocation mechanism (Definition 4, p.3): the
inequality of weak incentive compatibility holds, and it is strict whenever `vᵢ ≠ v̂ᵢ`.

**Formalization Note.** Encoded as weak IC together with strictness on every misreport. When
`vᵢ = v̂ᵢ` the two sides coincide, so the first conjunct adds nothing beyond the second. -/
def AllocStrictIC (A : Mech n m) : Prop :=
  AllocWeakIC A ∧
    ∀ (i : Fin n) (vi : stdSimplex ℝ (Fin m)) (v : Profile n m) (e : PosVec n), vi ≠ v i →
      val vi.1 (A v e i) < val vi.1 (A (Function.update v i vi) e i)

end WagerFairDiv


