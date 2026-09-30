-- Prove2me | Definitions.Def_TierneyMH_Shared_OffDiagDominates
-- name    : TierneyMH_Shared_OffDiagDominates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T12:15:27.869388+00:00
-- url     : https://prove2.me/theorems/a0b5b150-3a17-4b66-b7ed-e04d880fdf8d
-- title:
--   Off-diagonal domination $P_1 \succeq P_2$ of transition kernels
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space, $\pi$ a measure on $E$, and $P_1, P_2$ transition kernels on $E$. Following Peskun (1973), $P_1$ **dominates $P_2$ off the diagonal**, written $P_1 \succeq P_2$, if for $\pi$-almost every $x \in E$,
--
--   $$
--   P_1\bigl(x, A \setminus \{x\}\bigr) \;\ge\; P_2\bigl(x, A \setminus \{x\}\bigr) \qquad \text{for all } A \in \mathcal E .
--   $$
--
--   The exceptional $\pi$-null set of points $x$ is fixed once, independently of $A$. Informally, from almost every state the kernel $P_1$ moves to every region other than the current point at least as readily as $P_2$ does; the two kernels may differ only in how much mass they leave on staying put.
--
--   This partial order is the hypothesis of the Peskun–Tierney comparison theorem: it orders the lag-one autocorrelations (Lemma 3) and, for reversible kernels, the asymptotic variances of ergodic averages (Theorem 4).
--
--   **Formalization Note** In the paper the order is defined for kernels "with invariant distribution $\pi$"; that standing premise is not part of the predicate, and each theorem using it states invariance or reversibility separately. The arguments are ordered $(\pi, P_1, P_2)$ with $P_1$ the dominating kernel. The set $A \setminus \{x\}$ is an event when singletons are measurable, which the theorems using it assume.
--
--   It is shared by two missions of this series and reviewed once for both: `02-peskun-ordering` (§3, p. 4; the hypothesis of Lemma 3 and Theorem 4, pp. 5–6) and `03-mixture-proposals` (§3, p. 4; the maximality of $\alpha_{MH}$ with respect to off-diagonal domination, §3, p. 7, and the conclusion of Proposition 5, p. 7).
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 4, §3 (definition of off-diagonal domination)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Shared

/-- **Off-diagonal domination** (Peskun 1973; Tierney 1998, §3, p. 4). For transition kernels
`P₁ P₂` on `E` and a measure `π`, `OffDiagDominates π P₁ P₂` (the paper's `P₁ ⪰ P₂`) holds when
for `π`-almost every `x ∈ E`, `P₁(x, A \ {x}) ≥ P₂(x, A \ {x})` for **every** measurable `A`.
The quantifier order is the paper's: the null set of exceptional `x` does not depend on `A`.

The paper's standing premise "`P₁` and `P₂` have invariant distribution `π`" is not part of
this predicate; every theorem using it states the invariance or reversibility hypotheses
separately. The set `A \ {x}` is measurable when singletons are measurable, which the theorems
using it assume (`MeasurableSingletonClass E`). -/
def OffDiagDominates {E : Type*} [MeasurableSpace E] (π : Measure E) (P₁ P₂ : Kernel E E) :
    Prop :=
  ∀ᵐ x ∂π, ∀ A : Set E, MeasurableSet A → P₂ x (A \ {x}) ≤ P₁ x (A \ {x})

end TierneyMH.Shared


