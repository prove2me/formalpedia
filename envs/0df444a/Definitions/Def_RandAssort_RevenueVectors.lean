-- Prove2me | Definitions.Def_RandAssort_RevenueVectors
-- name    : RandAssort_RevenueVectors
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:31:09.456923+00:00
-- url     : https://prove2.me/theorems/b1a4414f-5477-4d17-9016-7874da6c9d54
-- title:
--   The set $\mathcal R$ of expected revenue vectors $(R(S,u))_{S\in\mathcal S}$, $u\in\mathcal U$
-- statement:
--   For a robust assortment instance $(\mathcal N,\mathcal S,\mathfrak C,\mathcal U,r)$, the set of expected revenue vectors is
--   $$
--   \mathcal R=\bigl\{R\in\mathbb R^{|\mathcal S|}:\ [R_S=R(S,u)\ \forall S\in\mathcal S]\ \text{for some } u\in\mathcal U\bigr\}.
--   $$
--   It contains one vector for each uncertainty realization $u\in\mathcal U$, listing the expected revenue of every admissible assortment.
--
--   This set and its convex hull $\operatorname{conv}\mathcal R$ are the objects through which the proof of Theorem 1 links randomized assortments to distributions on $\mathcal U$. The proof's minimax argument is the bilinear game $p^\top R$ over $\Delta(\mathcal S)\times\operatorname{conv}\mathcal R$.
--
--   **Formalization Note** $\mathbb R^{|\mathcal S|}$ is the space of real functions on the members of $\mathcal S$, and $\mathcal R$ is the range of $u\mapsto(R(S,u))_{S\in\mathcal S}$ over $u\in\mathcal U$. The values $R^\star_{\mathrm{det}}$ and $R^\star_{\mathrm{rand}}$ of `RandAssort.Model` do not depend on this definition.
-- source:
--   Wang–Peura–Wiesemann, Randomized Assortment Optimization, Oper. Res. (2024), doi:10.1287/opre.2022.0129, proof of Theorem 1, e-companion p.ec8

import Mathlib
import Definitions.Def_RandAssort_Model

namespace RandAssort

variable {n : ℕ} {E : Type*}

/-- The set of expected revenue vectors
`ℛ = {R ∈ ℝ^{|𝒮|} : [R_S = R(S, u) ∀ S ∈ 𝒮] for some u ∈ 𝒰}`, proof of Theorem 1, e-companion
p.ec8 of Z. Wang, H. Peura, W. Wiesemann, *Randomized Assortment Optimization*, Operations
Research (2024), doi:10.1287/opre.2022.0129: for each realization `u ∈ 𝒰`, the vector of expected
revenues of all admissible assortments.

**Formalization Note** `ℝ^{|𝒮|}` is the space of functions on the members of `𝒮`, and `ℛ` is the
range of `u ↦ (R(S, u))_{S ∈ 𝒮}` over `u ∈ 𝒰`. This set is used only in the steps of the proof of
Theorem 1; the values `R⋆_det(𝒰)` and `R⋆_rand(𝒰)` are not defined through it. -/
def Instance.revSet (I : Instance n E) : Set (I.S → ℝ) :=
  Set.range fun u : I.U => fun S : I.S => I.R S u

end RandAssort


