-- Prove2me | Definitions.Def_ChowFormsCH_Supplement_IsApproxSat
-- name    : ChowFormsCH_Supplement_IsApproxSat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:19:49.529041+00:00
-- url     : https://prove2.me/theorems/66f3adf8-b153-4673-baa6-06f635961ce5
-- title:
--   Approximate polynomial satisfiability over an arbitrary field
-- statement:
--   Let $F$ be a field with algebraic closure $\overline{F}$. Polynomials $f_1, \dots, f_m \in F[x_1, \dots, x_n]$ are **approximately satisfiable** if the Zariski closure of the image of the map
--   $$\phi_f : \overline{F}^{\,n} \to \overline{F}^{\,m}, \qquad \phi_f(a) = (f_1(a), \dots, f_m(a)),$$
--   contains the point $(0, \dots, 0)$ (Definition 1.7).
--
--   Satisfiable systems are approximately satisfiable. The converse fails, for example for $x y - 1$ and $x$. The published `APSCounting893.Main.PolynomialAPS` has the same meaning for presented fields. This version applies to any field and is used for the rational function fields of Theorem 5.6.
--
--   **Formalization Note** The Zariski closure is `RSCapacity.zClosure`, the zero locus of the vanishing ideal.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Definition 1.7, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry

set_option autoImplicit false

namespace ChowFormsCH.Supplement

/-- **Approximate polynomial satisfiability** over a field `F` (Andrews–Garg–Oliveira–Schost,
*Some algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version,
sha256 75e796c6…, Definition 1.7, p.5): polynomials `f₁, …, f_m ∈ F[x₁, …, xₙ]` are approximately
satisfiable if the closure of the image of `ϕ_f : Āⁿ → Ā^m`, `ϕ_f(a) = (f₁(a), …, f_m(a))`, contains
`(0, …, 0)`, where `Ā` is affine space over the algebraic closure `F̄` of `F`.

**Formalization Note** The closure is the Zariski closure in `F̄^m` (`RSCapacity.zClosure`, the zero
locus of the vanishing ideal), and the map is evaluated on all of `F̄ⁿ`. This is the semantics of the
published `APSCounting893.Main.PolynomialAPS`, stated for an arbitrary field so that it applies to
rational function fields. -/
def IsApproxSat (F : Type*) [Field F] {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) F) : Prop :=
  (0 : Fin m → AlgebraicClosure F) ∈ RSCapacity.zClosure
    (Set.range (fun x : Fin n → AlgebraicClosure F =>
      fun i => MvPolynomial.eval₂ (algebraMap F (AlgebraicClosure F)) x (f i)))

end ChowFormsCH.Supplement


