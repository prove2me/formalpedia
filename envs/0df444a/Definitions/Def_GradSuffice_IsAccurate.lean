-- Prove2me | Definitions.Def_GradSuffice_IsAccurate
-- name    : GradSuffice_IsAccurate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:24.933536+00:00
-- url     : https://prove2.me/theorems/d750a7c0-bbdb-4772-81df-40f54c7a9004
-- title:
--   $\varepsilon$-accurate randomized first-order algorithm
-- statement:
--   Let $(\Omega,\mu)$ be a probability space (the internal randomness) and let $A=(A_\omega)_{\omega\in\Omega}$ be a family of deterministic first-order algorithms with $T$ queries on $W$. The randomized algorithm $A$ is **$\varepsilon$-accurate** if for every objective $(U,f)$ on $W$ and every valid oracle $g$, the last query $w_T(\omega)$ of the run of $A_\omega$ satisfies
--   $$\mu\Big\{\omega:\ f(w_T(\omega))-\inf_{w\in W}f(w)\le\varepsilon\Big\}\ \ge\ \frac12 .$$
--
--   **Formalization Note** The success set is required to be measurable, which is what makes the probability defined. $\inf_{w\in W}f(w)$ is `sInf (f '' W)`; for a bounded domain and a Lipschitz objective this set of reals is bounded below. An algorithm with fewer than $T$ queries is padded by repeating its last query.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.4

import Mathlib
import Definitions.Def_GradSuffice_IsValidOracle
import Definitions.Def_GradSuffice_DetAlg_lastQuery

namespace GradSuffice

/-- **ε-accurate randomized first-order algorithm.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.4: "A first-order ε-accurate
optimization algorithm with iteration complexity `T(ε)` is a possibly randomized algorithm that, for
every convex 1-Lipschitz objective `f` and every valid first-order oracle, makes at most `T(ε)`
queries and outputs `w_T` such that `Pr[f(w_T) − inf_{w∈W} f(w) ≤ ε] ≥ 1/2`. The probability is
over the algorithm's internal randomness."

**Formalization Note.** The internal randomness is a probability space `(Ω, μ)`; seed `ω` runs the
deterministic algorithm `A ω`. "`Pr[…]`" is read as: the success set is measurable and has
`μ`-measure at least `1/2`. `inf_{w∈W} f(w)` is `sInf (f '' W)`. An algorithm with fewer queries is
padded by repeating its last query, so exactly `T` queries lose nothing. -/
def IsAccurate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) (ε : ℝ) {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A : Ω → DetAlg X W T) : Prop :=
  ∀ (F : Objective X W) (g : X → StrongDual ℝ X), IsValidOracle F g →
    MeasurableSet {ω | F.f ((A ω).lastQuery F.f g) - sInf (F.f '' W) ≤ ε} ∧
      (2⁻¹ : ENNReal) ≤ μ {ω | F.f ((A ω).lastQuery F.f g) - sInf (F.f '' W) ≤ ε}

end GradSuffice


