-- Prove2me | Definitions.Def_SemAC02_Supplement_clauseAx
-- name    : SemAC02_Supplement_clauseAx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:41:09.899278+00:00
-- url     : https://prove2.me/theorems/6e7124a2-0920-4c05-85ee-eb7ad39d2e93
-- title:
--   Clause polynomials ⟦C⟧ over a field and the polynomial encoding F_φ
-- statement:
--   Over a field $\mathbb F$, the literal $x_i$ is identified with the polynomial $1-x_i$ and $\neg x_i$ with $x_i$; each vanishes exactly when the literal is true. The **clause polynomial** of $C=\bigvee_{i\in P}x_i\vee\bigvee_{i\in N}\neg x_i$ is
--
--   $$
--   [\![C]\!]=\prod_{i\in P}(1-x_i)\prod_{i\in N}x_i,
--   $$
--
--   the indicator of the assignments falsifying $C$; the empty clause has $[\![\emptyset]\!]=1$. The **polynomial encoding** of a CNF $\varphi$ is $F_\varphi=\{[\![C]\!]:C\in\varphi\}$.
--
--   This is the axiom set of every refutation of a CNF in the paper.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.1, p.14 (PDF p.16); §2.3, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_ACirc

namespace SemAC02.Supplement

open MvPolynomial LiftSAParity

/-- The truth-value polynomial of a literal over a field `F` (Alekseev–Gryaznov–Itsykson–Pitassi–
Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), §2.1, p.14): `1 − x` for the positive literal `x` and `x` for the negative literal
`¬x`. It vanishes exactly when the literal is true. -/
noncomputable def litPolyF {F V : Type} [CommRing F] (l : V × Bool) : MvPolynomial V F :=
  if l.2 then 1 - X l.1 else X l.1

/-- The **clause polynomial** `⟦C⟧ = ∏_{i∈P} (1 − x_i) ∏_{i∈N} x_i` of a clause
`C = ⋁_{i∈P} x_i ∨ ⋁_{i∈N} ¬x_i` over `F` (p.14): the indicator of the assignments falsifying
`C`. The empty clause has `⟦∅⟧ = 1`. -/
noncomputable def clausePolyF {F V : Type} [CommRing F] (C : Clause V) : MvPolynomial V F :=
  ∏ l ∈ C, litPolyF l

/-- The **polynomial encoding** `F_φ = {⟦C⟧ : C ∈ φ}` of a set of clauses (p.18), as axioms in
`B_V(F)`. -/
noncomputable def clauseAx {F V : Type} [CommRing F] (S : Set (Clause V)) :
    Set ((V → Bool) → F) :=
  {f | ∃ C ∈ S, f = polyFn (clausePolyF C)}

end SemAC02.Supplement


