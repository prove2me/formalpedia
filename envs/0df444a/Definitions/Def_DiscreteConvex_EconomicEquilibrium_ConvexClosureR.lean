-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_ConvexClosureR
-- name    : DiscreteConvex_EconomicEquilibrium_ConvexClosureR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:50:21.46463+00:00
-- url     : https://prove2.me/theorems/be15ac22-f39c-4d94-85d1-340a4b1440cb
-- title:
--   Convex closure of a cost-type function (Eq. 3.56)
-- statement:
--   The convex closure $\hat C : \mathbb R^K \to \mathbb R \cup \{\pm\infty\}$ of $C : \mathbb Z^K \to \mathbb R \cup \{+\infty\}$ (Eq. (3.56)):
--   $$\hat C(x) = \sup_{p \in \mathbb R^K,\ \alpha \in \mathbb R} \{\langle p,x\rangle + \alpha : \langle p,y\rangle + \alpha \le C(y)\ \forall y \in \mathbb Z^K\}.$$
--   Used to build the continuous supply correspondence $\hat S_l$ of the derived continuous economy (Eq. (11.32), p.337).
--
--   **Formalization Note.** A local copy of `DiscreteConvex.IntegralConvexity.ConvexClosure`, generalized from a `Fin n` ground set to this chapter's general `Fintype` ground set $K$. Represented in `EReal`, into which $C$'s codomain `WithTop ℝ` embeds via chunk 04's `ToEReal`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_ToEReal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.56) (used for `Ĉl`, p.337): the
convex closure of a cost-type function, in `DiscreteConvex.EconomicEquilibrium` (a local copy of
`DiscreteConvex.IntegralConvexity.ConvexClosure`, generalized from `Fin n` to a general `Fintype`
ground set `K` to match this chapter's `Zᴷ`).
-/

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexSets

/-- The convex closure `Ĉ : Rᴷ → R ∪ {±∞}` of `C : Zᴷ → R ∪ {+∞}` (Eq. (3.56)):
`Ĉ(x) = sup_{p ∈ Rᴷ, α ∈ R} \{⟨p,x⟩ + α : ⟨p,y⟩ + α ≤ C(y) ∀y ∈ Zᴷ\}`. Represented in `EReal`
(`= WithBot (WithTop ℝ)`), into which `C`'s codomain `WithTop ℝ` embeds via `ToEReal`. -/
noncomputable def ConvexClosureR {K : Type*} [Fintype K] (C : (K → ℤ) → WithTop ℝ) (x : K → ℝ) :
    EReal :=
  sSup {v : EReal | ∃ (p : K → ℝ) (α : ℝ),
    (∀ y : K → ℤ, ((α + ∑ k, p k * (y k : ℝ) : ℝ) : EReal) ≤ ToEReal (C y)) ∧
    v = ((α + ∑ k, p k * x k : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibrium


