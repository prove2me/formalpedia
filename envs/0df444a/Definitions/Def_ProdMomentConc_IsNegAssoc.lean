-- Prove2me | Definitions.Def_ProdMomentConc_IsNegAssoc
-- name    : ProdMomentConc_IsNegAssoc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:17.586513+00:00
-- url     : https://prove2.me/theorems/46faeb12-8078-4415-867b-e05f7c1b5727
-- title:
--   Negative association (Definition 2.10)
-- statement:
--   A family of real random variables $(Z_i)_{i \in \iota}$ is **negatively associated** if for all disjoint finite index sets $I, J \subseteq \iota$ and every pair of functions $f : \mathbb R^I \to \mathbb R$, $g : \mathbb R^J \to \mathbb R$ that are both coordinatewise non-decreasing or both coordinatewise non-increasing,
--
--   $$
--   \mathbb E\big[f\big((Z_i)_{i\in I}\big)\, g\big((Z_j)_{j\in J}\big)\big] \le \mathbb E\big[f\big((Z_i)_{i\in I}\big)\big]\,\mathbb E\big[g\big((Z_j)_{j\in J}\big)\big].
--   $$
--
--   Negative association lets products of increasing functions of disjoint blocks be bounded by products of expectations, as for independent variables. In this mission it is used for the indicators of a uniformly random $k$-subset and for monotone functions of disjoint blocks of them.
--
--   **Formalization Note** No boundedness or measurability is imposed on $f$ and $g$. The inequality is required whenever the three expectations exist, i.e. whenever $f(Z_I)$, $g(Z_J)$ and their product are integrable; this guard excludes only cases where an expectation is undefined (Lean's Bochner integral would return $0$ there). For bounded families on a finite sample space every expectation exists.
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Definition 2.10, p.11 (PDF p.11)

import Mathlib

open MeasureTheory

namespace ProdMomentConc

/-- **Negative association** (Definition 2.10).
Saks, Srinivasan, Valieva, arXiv:2608.04125 (held version, sha256 5218e9d0…), Definition 2.10,
p.11: "A collection of random variables X1, . . . , Xm is said to be negatively associated if for any
I, J ⊂ [m], I ∩ J = ∅ and any pair of non-decreasing (or non-increasing) functions f : R^I → R,
g : R^J → R, E[f((Xi)i∈I) g((Xj)j∈J)] ≤ E[f((Xi)i∈I)] E[g((Xj)j∈J)]."

A family `Z : ι → Ω → ℝ` is negatively associated under `μ` if for all disjoint finite index sets
`I, J` and all `f : ℝ^I → ℝ`, `g : ℝ^J → ℝ` that are both coordinatewise non-decreasing or both
coordinatewise non-increasing, `E[f(Z_I) g(Z_J)] ≤ E[f(Z_I)] E[g(Z_J)]`.

**Formalization Note.** No boundedness or measurability is imposed on `f, g`. The inequality is
required whenever the three expectations exist, i.e. for every such pair for which `f(Z_I)`,
`g(Z_J)` and `f(Z_I) g(Z_J)` are integrable; the paper writes no integrability condition, and this
guard only excludes the cases where an expectation is undefined (Lean's Bochner integral would
return `0` there). For `[0, 1]`-valued families on a finite sample space every such expectation
exists. -/
def IsNegAssoc {Ω ι : Type*} [MeasurableSpace Ω] (Z : ι → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ (I J : Finset ι), Disjoint I J →
    ∀ (f : (I → ℝ) → ℝ) (g : (J → ℝ) → ℝ),
      ((Monotone f ∧ Monotone g) ∨ (Antitone f ∧ Antitone g)) →
      Integrable (fun ω => f (fun i => Z i ω)) μ →
      Integrable (fun ω => g (fun j => Z j ω)) μ →
      Integrable (fun ω => f (fun i => Z i ω) * g (fun j => Z j ω)) μ →
      ∫ ω, f (fun i => Z i ω) * g (fun j => Z j ω) ∂μ ≤
        (∫ ω, f (fun i => Z i ω) ∂μ) * ∫ ω, g (fun j => Z j ω) ∂μ

end ProdMomentConc


