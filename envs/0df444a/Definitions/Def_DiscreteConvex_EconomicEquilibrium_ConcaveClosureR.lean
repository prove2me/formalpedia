-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_ConcaveClosureR
-- name    : DiscreteConvex_EconomicEquilibrium_ConcaveClosureR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:50:07.534528+00:00
-- url     : https://prove2.me/theorems/7e19fefb-d937-45cb-a2b2-d2956847fd2c
-- title:
--   Concave closure of a utility-type function
-- statement:
--   The concave closure $\hat U : \mathbb R^K \to \mathbb R \cup \{\pm\infty\}$ of $U : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$, dual to the convex closure of Eq. (3.56):
--   $$\hat U(x) = \inf_{p \in \mathbb R^K,\ \alpha \in \mathbb R} \{\langle p,x\rangle + \alpha : \langle p,y\rangle + \alpha \ge U(y)\ \forall y \in \mathbb Z^K\}.$$
--   Used to build the continuous demand correspondence $\hat D_h$ of the derived continuous economy (Eq. (11.31), p.337).
--
--   **Formalization Note.** Represented in `EReal` (`= WithBot (WithTop ℝ)`), into which $U$'s codomain `WithBot ℝ` embeds via chunk 04's `ToERealOfBot`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56), dualized; see p.331, p.337.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56), dualized; see p.331, p.337

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_ToERealOfBot

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.56), dualized (the concave-closure
counterpart used implicitly at p.331, "the concave closure Û of U", and p.337 for `Ûh`): the
concave closure of a utility-type function, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexSets

/-- The concave closure `Û : Rᴷ → R ∪ {±∞}` of `U : Zᴷ → R ∪ {−∞}`, dual to the convex closure of
Eq. (3.56): `Û(x) = inf_{p ∈ Rᴷ, α ∈ R} \{⟨p,x⟩ + α : ⟨p,y⟩ + α ≥ U(y) ∀y ∈ Zᴷ\}`. Represented in
`EReal` (`= WithBot (WithTop ℝ)`), into which `U`'s codomain `WithBot ℝ` embeds via
`ToERealOfBot`. -/
noncomputable def ConcaveClosureR {K : Type*} [Fintype K] (U : (K → ℤ) → WithBot ℝ) (x : K → ℝ) :
    EReal :=
  sInf {v : EReal | ∃ (p : K → ℝ) (α : ℝ),
    (∀ y : K → ℤ, ToERealOfBot (U y) ≤ ((α + ∑ k, p k * (y k : ℝ) : ℝ) : EReal)) ∧
    v = ((α + ∑ k, p k * x k : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibrium


