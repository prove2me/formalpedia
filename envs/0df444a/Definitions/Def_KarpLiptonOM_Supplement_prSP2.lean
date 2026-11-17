-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_prSP2
-- name    : KarpLiptonOM_Supplement_prSP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:40:03.805185+00:00
-- url     : https://prove2.me/theorems/e05d9264-30c6-41a9-a2ee-380df34cdaf7
-- title:
--   $\mathrm{prS}^{\mathrm P}_2$: promise symmetric alternation (Definition A.2.2)
-- statement:
--   A promise problem $\Pi=(\Pi_{\mathrm{YES}},\Pi_{\mathrm{NO}})$ is in $\mathrm{prS}^{\mathrm P}_2$ if there are polynomials $a,b$ and a polynomial-time predicate $V$ such that for every $x$,
--
--   $$
--   x\in\Pi_{\mathrm{YES}}\Rightarrow\exists y\in\{0,1\}^{a(|x|)}\,\forall z\in\{0,1\}^{b(|x|)}\;V(x,y,z)=1,\qquad
--   x\in\Pi_{\mathrm{NO}}\Rightarrow\exists z\in\{0,1\}^{b(|x|)}\,\forall y\in\{0,1\}^{a(|x|)}\;V(x,y,z)=0.
--   $$
--
--   Such $y$ and $z$ are **irrefutable certificates**. Inputs outside the promise are unconstrained.
--
--   This is the symmetric-alternation class of Canetti and of Russell–Sundaram in its promise form. The input-oblivious class $\mathrm O^{\mathrm P}_2$ of the base mission adds certificates depending only on $|x|$.
--
--   **Formalization Note** The shape is that of the published `KarpLiptonOM.OP2` without its oblivious clause.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.2, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_KarpLiptonOM_PolyPred3

namespace KarpLiptonOM.Supplement

/-- `Π ∈ prS₂^P` (Definition A.2.2, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.21, [Can96, RS98]): there are polynomials `a, b` and a
polynomial-time predicate `V` such that for every `x`,
`x ∈ Π_YES ⇒ ∃y ∈ {0,1}^{a(|x|)} ∀z ∈ {0,1}^{b(|x|)} V(x, y, z) = 1` and
`x ∈ Π_NO ⇒ ∃z ∈ {0,1}^{b(|x|)} ∀y ∈ {0,1}^{a(|x|)} V(x, y, z) = 0`
(such `y`, `z` are irrefutable certificates).

**Formalization Note** The shape is that of the published `KarpLiptonOM.OP2` without its oblivious
clause, for promise problems; lengths are `Polynomial ℕ` evaluations (nondecreasing; `≥ 1` is not
imposed, which changes no class, as in `OP2`). -/
def prSP2 : Set PromiseProblem :=
  {PP | ∃ (a b : Polynomial ℕ) (V : List Bool → List Bool → List Bool → Prop), PolyPred3 V ∧
    ∀ x : List Bool,
      (x ∈ PP.yes → ∃ y : List Bool, y.length = a.eval x.length ∧
        ∀ z : List Bool, z.length = b.eval x.length → V x y z) ∧
      (x ∈ PP.no → ∃ z : List Bool, z.length = b.eval x.length ∧
        ∀ y : List Bool, y.length = a.eval x.length → ¬ V x y z)}

end KarpLiptonOM.Supplement


