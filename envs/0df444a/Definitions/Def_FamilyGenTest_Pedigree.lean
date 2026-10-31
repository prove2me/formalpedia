-- Prove2me | Definitions.Def_FamilyGenTest_Pedigree
-- name    : FamilyGenTest_Pedigree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:08.050702+00:00
-- url     : https://prove2.me/theorems/9f980667-462f-4009-b748-3e0fd0f45911
-- title:
--   Pedigree, Table 1 and the Mendelian product (5)
-- statement:
--   A **pedigree** on $\mathcal I$ says, for each person, whether they are a founder or a nonfounder with father $\mathrm{fa}(i)$ and mother $\mathrm{mo}(i)$ (the paper's ♂ᵢ and ♀ᵢ), with an order that puts parents before children. **Table 1** gives $\mathbb P(G_i=g_i\mid g_{\mathrm{fa}(i)},g_{\mathrm{mo}(i)})$, the law under which each parent independently passes a mutation with probability half its status. With founder priors $\mathbb P(G_i=g_i)$, $i\in\mathcal F$, the **Mendelian product** is
--   $$
--   \mathbb P(G=g)=\prod_{i\in\mathcal F}\mathbb P(G_i=g_i)\prod_{i\in\mathcal I\setminus\mathcal F}\mathbb P(G_i=g_i\mid g_{\mathrm{fa}(i)},g_{\mathrm{mo}(i)}).
--   $$
--
--   This is the prior of the paper's Bayesian network.
--
--   **Formalization Note** The two products are one product over $\mathcal I$ with a case on `parents i`. The `rank` function encodes acyclicity. The father and the mother are not required to be distinct, since nothing here uses it.
-- source:
--   Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694 (Jan 24 2023), §3.1, (5), p.11; Table 1, p.12

import Mathlib
import Definitions.Def_FamilyGenTest_risk

namespace FamilyGenTest

/-- A family pedigree (Adelman & Wang, Optimal Genetic Testing of Families, SSRN 4624694
(Jan 24 2023), §3.1, p.11): `parents i = none` for a founder, and
`parents i = some (♂ᵢ, ♀ᵢ)`, father and mother, for a nonfounder.

**Formalization Note** `rank` is an order with parents before children, which says that the
Bayesian network of Figure 2 is acyclic. -/
structure Pedigree (I : Type*) where
  parents : I → Option (I × I)
  rank : I → ℕ
  rank_lt : ∀ i f m, parents i = some (f, m) → rank f < rank i ∧ rank m < rank i

/-- Table 1 (Adelman & Wang, SSRN 4624694, p.12): `table1 f m g = ℙ(Gᵢ = g | g♂ᵢ = f, g♀ᵢ = m)`. -/
noncomputable def table1 : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![1, 0, 0], ![1/2, 1/2, 0], ![0, 1, 0]],
    ![![1/2, 1/2, 0], ![1/4, 1/2, 1/4], ![0, 1/2, 1/2]],
    ![![0, 1, 0], ![0, 1/2, 1/2], ![0, 0, 1]]]

variable {I : Type*} [Fintype I]

/-- The Mendelian product (5) (Adelman & Wang, SSRN 4624694, p.11), with founder priors `p`:
`∏_{i ∈ F} p i gᵢ · ∏_{i ∈ I \ F} ℙ(Gᵢ = gᵢ | g♂ᵢ, g♀ᵢ)`.

**Formalization Note** The two products of (5) are written as one product over `I` with a case on
`parents i`. -/
noncomputable def mendelian (P : Pedigree I) (p : I → Fin 3 → ℝ) (g : I → Fin 3) : ℝ :=
  ∏ i, match P.parents i with
    | none => p i (g i)
    | some (f, m) => table1 (g f) (g m) (g i)

end FamilyGenTest


