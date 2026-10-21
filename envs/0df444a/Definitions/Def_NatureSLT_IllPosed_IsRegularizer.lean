-- Prove2me | Definitions.Def_NatureSLT_IllPosed_IsRegularizer
-- name    : NatureSLT_IllPosed_IsRegularizer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:13.671143+00:00
-- url     : https://prove2.me/theorems/51214733-4443-48d0-870b-b6b514ae6ba7
-- title:
--   Regularization functional $\Omega$: lower semicontinuous, nonnegative, with compact sets $\{\Omega \le c\}$
-- statement:
--   Let $E_1$ be a topological space (in this chapter, the metric space of candidate solutions $f$). A **regularization functional** in the sense of §7.5 is a map
--
--   $$\Omega : E_1 \to [0, \infty]$$
--
--   that is lower semicontinuous and such that for every real $c > 0$ the sublevel set
--
--   $$\{\, g \in E_1 : \Omega(g) \le c \,\}$$
--
--   is compact. Its **domain** $\mathcal F = \{ g : \Omega(g) < \infty \}$ is the set of functions on which the book defines $\Omega$ ("the domain of solution of the equations").
--
--   This is the standing hypothesis on $\Omega$ under which Tikhonov's method is analyzed in Theorems 7.1, 7.3 and 7.5: compactness of the sublevel sets is what turns a bound on $\Omega$ along a family of approximate solutions into convergence.
--
--   **Formalization Note** The book's "positive" is read as nonnegative and is built into the codomain $[0,\infty]$; the value $\infty$ encodes "outside the domain $\mathcal F$". "Semicontinuous" is read as lower semicontinuous. The three further properties listed on p. 235 (convexity, $\Omega(0)=0$, strict monotonicity of $\gamma \mapsto \Omega(\gamma f)$), which the book imposes only "to impose uniqueness of the solution" and which as printed contradict each other at $f = 0$, are not part of the definition.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 235, Section 7.5

import Mathlib

namespace NatureSLT.IllPosed

open scoped ENNReal

/-- The regularization functional of §7.5 (Vapnik, *The Nature of Statistical Learning Theory*,
2nd ed., p. 235): "a semicontinuous, positive functional for which `Ω(f) ≤ c`, `c > 0`, is a
compactum (in the space of functions `f`). It is defined on the set of functions `f ∈ 𝓕`, the
domain of solution of the equations."

`Ω` takes values in `[0, ∞]`: positivity (nonnegativity) is built into the codomain, and the
domain `𝓕` is `{g | Ω g ≠ ⊤}`. "Semicontinuous" is lower semicontinuity. The compactum condition
is required for every real `c > 0`. Properties 1–3 of p. 235 (convexity, `Ω(0) = 0`, strict
monotonicity of `γ ↦ Ω(γf)`), imposed there only "to impose uniqueness", are not part of this
definition. -/
def IsRegularizer {E₁ : Type*} [TopologicalSpace E₁] (Ω : E₁ → ℝ≥0∞) : Prop :=
  LowerSemicontinuous Ω ∧ ∀ c : ℝ, 0 < c → IsCompact {g : E₁ | Ω g ≤ ENNReal.ofReal c}

end NatureSLT.IllPosed


