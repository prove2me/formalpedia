-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel
-- name    : DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:12:54.449081+00:00
-- url     : https://prove2.me/theorems/2108b177-55e5-46bd-9655-375c0894d0af
-- title:
--   Lagrangian kernel of a perturbation function (Eq. 8.58)
-- statement:
--   The **Lagrangian function** $K(x,y) = \inf\{F(x,u) + \langle u,y\rangle : u \in \mathbb Z^U\}$ associated with a perturbation $F : \mathbb Z^V \times \mathbb Z^U \to \mathbb Z \cup \{+\infty\}$ of a primal problem. Lands in `EReal` since the infimum need not be finite.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.58).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.236, Eq. (8.58)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.236, Eq. (8.58): the Lagrangian kernel of a
perturbation function, in `DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- The **Lagrangian function** `K(x,y) = inf\{F(x,u) + ⟨u,y⟩ : u ∈ Z^U\}` (Eq. (8.58))
associated with a perturbation `F : Zⱽ × Z^U → Z ∪ {+∞}` of a primal problem. Landing in
`EReal` since the infimum need not be finite. -/
noncomputable def LagrangianKernel {V U : Type*} [Fintype U]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) (x : V → ℤ) (y : U → ℤ) : EReal :=
  sInf {v : EReal | ∃ u : U → ℤ,
    v = ToEReal (F x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDuality.Lagrange


