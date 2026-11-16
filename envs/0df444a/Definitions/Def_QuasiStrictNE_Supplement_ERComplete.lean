-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_ERComplete
-- name    : QuasiStrictNE_Supplement_ERComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:44:07.430166+00:00
-- url     : https://prove2.me/theorems/b91192f9-f1e3-4611-9c0a-4a98d43fba56
-- title:
--   $\exists\mathbb R$-completeness of a decision problem
-- statement:
--   The **existential theory of the reals** (ETR) is the set of true sentences $\exists x_1,\dots,x_n \in \mathbb R : \varphi(x_1,\dots,x_n)$, where $\varphi$ is a quantifier-free formula built from polynomial equalities and inequalities. The class $\exists\mathbb R$ consists of the decision problems that reduce to ETR in polynomial time. A language $L$ of binary strings is **$\exists\mathbb R$-complete** if
--
--   1. $L \in \exists\mathbb R$: there is a polynomial-time computable map $f$ with $w \in L \iff f(w) \in \mathrm{ETR}$ for every $w$; and
--   2. $L$ is $\exists\mathbb R$-hard: there is a polynomial-time computable map $g$ with $w \in \mathrm{ETR} \iff g(w) \in L$ for every $w$.
--
--   Theorem 2 is stated with this notion.
--
--   **Formalization Note** Reductions are the public `CookPvsNP.PolyReducible`: polynomial-time computable maps between bit strings, with Turing machines as in Cook's Clay description. ETR is the public `ETRLanguage`. Its terms are built from $0$, $1$, variables, $+$ and $\times$, its atoms are $=$ and $<$, its connectives are $\neg$, $\wedge$, $\vee$, and it has a fixed binary code. The paper allows polynomials with rational coefficients. These can be expressed through existential variables fixed by polynomial-size equations, so the two versions of ETR reduce to each other in polynomial time and define the same class $\exists\mathbb R$.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §2, p.9 (the class ∃R and ETR)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ApproxPolySatCH_Main_Supplement_ExistentialReals

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **∃R-completeness of a binary language** (Hansen & Nie, *On Existence and Computational Complexity
of Quasi-strict Equilibria*, arXiv:2611.06350, §2, p.9: "The complexity class used in our result about
multiplayer games is the class ∃R. Its canonical complete problem, the existential theory of the
reals (ETR), asks whether a sentence of the form ∃x1, . . . , xn ∈ R : φ(x1, . . . , xn) is true").

`ERComplete L` holds iff `L ∈ ∃R` — `L` is polynomial-time many-one reducible to ETR — and `L` is
∃R-hard — ETR is polynomial-time many-one reducible to `L`.

**Formalization Note** Reductions are the public `CookPvsNP.PolyReducible` (polynomial-time
computable maps on bit strings, Turing machines as in Cook's Clay description). ETR is the public
`ApproxPolySatCH.Main.Supplement.ETRLanguage`: true sentences `∃x ∈ ℝⁿ, φ(x)` with `φ` a Boolean
combination (¬, ∧, ∨) of equalities and strict inequalities between terms built from `0`, `1`,
variables, `+`, `×`, in a fixed self-delimiting binary code. The paper's rational coefficients are
expressible there by existential variables pinned by polynomial-size equations, so both versions of
ETR are polynomial-time interreducible and define the same class ∃R. -/
def ERComplete (L : Set (List Bool)) : Prop :=
  CookPvsNP.PolyReducible L ApproxPolySatCH.Main.Supplement.ETRLanguage ∧
    CookPvsNP.PolyReducible ApproxPolySatCH.Main.Supplement.ETRLanguage L

end QuasiStrictNE.Supplement


