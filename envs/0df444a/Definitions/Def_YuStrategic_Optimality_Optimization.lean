-- Prove2me | Definitions.Def_YuStrategic_Optimality_Optimization
-- name    : YuStrategic_Optimality_Optimization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:26:03.436638+00:00
-- url     : https://prove2.me/theorems/7246fb8d-991a-4abb-b1f4-47369e997dcd
-- title:
--   Optimal value $\phi^*$, attainment set $E^*$, and everywhere $\epsilon$-optimality (3.3)–(3.4)
-- statement:
--   Let $D\subseteq\mathbb X\times\mathcal P(\Omega)$ with sections $D(x)=\{p\mid(x,p)\in D\}$, and $\phi:\mathbb X\times\mathcal P(\Omega)\to\bar{\mathbb R}$. Define
--   $$\phi^*(x)=\inf_{p\in D(x)}\phi(x,p),\qquad E^*=\Big\{x\in\mathbb X\ \Big|\ \operatorname*{arg\,min}_{p\in D(x)}\phi(x,p)\ne\varnothing\Big\}.$$
--   For $\epsilon>0$, a policy $\pi$ is **$\epsilon$-optimal everywhere** (for $\phi$, an optimal-value function $\phi^*$ and an attainment set $E^*$) if for every $x\in\mathbb X$ the strategic measure $\rho_x[\pi]$ satisfies
--   $$\phi(x,\rho_x[\pi])=\phi^*(x)\quad (x\in E^*),\qquad \phi(x,\rho_x[\pi])\le\begin{cases}\phi^*(x)+\epsilon&\text{if }\phi^*(x)>-\infty,\\ -1/\epsilon&\text{if }\phi^*(x)=-\infty,\end{cases}\quad (x\notin E^*).$$
--   With $D=\tilde{\mathcal S}_\star$ these are (3.3)–(3.4) of Theorem 3.3.
--
--   **Formalization Note.** The infimum is taken in $[-\infty,+\infty]$ (`EReal`); on an empty section it is $+\infty$ (the sections used in the mission are nonempty). The $\epsilon$-optimality predicate also requires $\rho_x[\pi]$ to exist, and quantifies over every $P$ with `IsStrategicMeasure M π δₓ P` (there is exactly one).
-- source:
--   Yu, arXiv:2206.06492v3, Theorem 3.3, pp. 8–9: φ* in (i), E* and (3.3)–(3.4) in (ii)

import Mathlib
import Definitions.Def_YuStrategic_Optimality_StrategicSets

namespace YuStrategic.Optimality

open MeasureTheory ProbabilityTheory

variable {X A : Type} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace A] [MeasurableSpace A]

/-- The optimal value `φ*(x) := inf_{p ∈ D(x)} φ(x, p)`, `x ∈ X`, of the partial minimization of
`φ` over the `x`-sections `D(x) = {p | (x, p) ∈ D}` of `D ⊆ X × P(Ω)` (Yu, arXiv:2206.06492v3,
Theorem 3.3(i), p. 8, with `D = S̃⋆`; Theorem 3.3(iii), p. 9, with `D = S̃′⋆`). The infimum is
taken in `R̄ = [−∞, +∞]`; on an empty section it is `+∞`. -/
noncomputable def phiStar (D : Set (X × ProbabilityMeasure (Path X A)))
    (φ : X × ProbabilityMeasure (Path X A) → EReal) (x : X) : EReal :=
  ⨅ (P : ProbabilityMeasure (Path X A)) (_ : (x, P) ∈ D), φ (x, P)

/-- The set of states at which the infimum `φ*(x)` over `D(x)` is attained,
`{x ∈ X | arg min_{p ∈ D(x)} φ(x, p) ≠ ∅}` (Theorem 3.3(ii), (3.3), p. 9: `E*` for `D = S̃⋆`). -/
def argminSet (D : Set (X × ProbabilityMeasure (Path X A)))
    (φ : X × ProbabilityMeasure (Path X A) → EReal) : Set X :=
  {x | ∃ P, (x, P) ∈ D ∧ φ (x, P) = phiStar D φ x}

/-- The policy `π` satisfies (3.3)–(3.4) of Theorem 3.3(ii) (p. 9) at every initial state, for the
optimal value `φstar`, the attainment set `Estar` and `ε > 0`: for every `x ∈ X` the strategic
measure `ρₓ[π]` exists, and
1. `φ(x, ρₓ[π]) = φstar(x)` if `x ∈ Estar` (3.3);
2. `φ(x, ρₓ[π]) ≤ φstar(x) + ε` if `x ∉ Estar` and `φstar(x) > −∞` (3.4);
3. `φ(x, ρₓ[π]) ≤ −1/ε` if `x ∉ Estar` and `φstar(x) = −∞` (3.4).

**Formalization Note.** `ρₓ[π]` is any `P` with `IsStrategicMeasure M π δₓ P`; such a `P` is
required to exist, and it is unique by the milestone `strategicMeasure_existsUnique`. -/
def IsEpsOptimalEverywhere (M : Model X A) (φ : X × ProbabilityMeasure (Path X A) → EReal)
    (φstar : X → EReal) (Estar : Set X) (ε : ℝ) (π : Policy M) : Prop :=
  ∀ x : X, (∃ P, IsStrategicMeasure M π (diracPM x) P) ∧
    ∀ P, IsStrategicMeasure M π (diracPM x) P →
      (x ∈ Estar → φ (x, P) = φstar x) ∧
      (x ∉ Estar → φstar x ≠ ⊥ → φ (x, P) ≤ φstar x + (ε : EReal)) ∧
      (x ∉ Estar → φstar x = ⊥ → φ (x, P) ≤ ((-1 / ε : ℝ) : EReal))

end YuStrategic.Optimality


