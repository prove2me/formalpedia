-- Prove2me | Definitions.Def_PhyloCSP_pPred
-- name    : PhyloCSP_pPred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:25:49.627556+00:00
-- url     : https://prove2.me/theorems/0ea03d2a-eaa3-40c2-8521-9ddb2590c813
-- title:
--   The guarantees $p(\varphi,F)$ and $p(\Pi,F)$ of eq. (1)
-- statement:
--   Let $\varphi$ have arity $k$, let $\varphi'$ be its canonical relaxation and $A=\{x_1,\dots,x_k\}$. For a tree transformation $F$,
--   $$
--   p(\varphi,F)=\inf_{\substack{T:\ A\subseteq T_L\\ T\restriction A\in \mathrm{Sat}(\varphi')}}\ \Pr\bigl(F[T]{\restriction}A\in\mathrm{Sat}(\varphi)\bigr),\qquad p(\Pi,F)=\min_{\varphi\in\Pi}p(\varphi,F).
--   $$
--
--   The infimum runs over all finite trees $T$ and all ways of placing the distinct variables $x_1,\dots,x_k$ among the leaves of $T$ such that the induced pattern satisfies $\varphi'$. Proposition 1.7 of the paper shows that the rounding algorithm with transformation $F$ satisfies at least a $p(\Pi,F)$ fraction of the constraints of any completely satisfiable instance, in expectation.
--
--   **Formalization Note** Values lie in $[0,\infty]$; probabilities are at most $1$, and the empty infimum is $\infty$ (this happens only when $\mathrm{Sat}(\varphi')=\emptyset$, i.e. for an always-false predicate of arity at least $2$). "$A\subseteq T_L$" is an injection of the variables into the leaves.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), eq. (1), p.5 (PDF p.7)

import Mathlib
import Definitions.Def_PhyloCSP_TreeTransformation
import Definitions.Def_PhyloCSP_canonRelax
import Definitions.Def_PhyloCSP_ConstraintLanguage

set_option autoImplicit false

open scoped ENNReal

namespace PhyloCSP

/-- **The guarantee `p(φ, F)` of a tree transformation, eq. (1).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), eq. (1), p.5 (PDF p.7): "Let φ ∈ Π have arity k, let φ′ be its
canonical relaxation, and let A = {x1, . . . , xk}. For a tree transformation F, define
p(φ, F) = inf_{T : A ⊆ T_L, T↾A ∈ Sat(φ′)} Pr(F[T]↾A ∈ Sat(φ))".

The infimum is over every finite leaf set `S`, every tree `T` on `S` and every placement
`x : Fin k ↪ ↥S` of the distinct variables among its leaves such that the pattern of `x` in `T`
satisfies the canonical relaxation `φ′`; the quantity is the probability that the pattern of `x`
in the output `F[T]` satisfies `φ`.

**Formalization Note.** Values are in `ℝ≥0∞`; probabilities are at most `1`, and the empty
infimum is `⊤` (only when `Sat(φ′) = ∅`, i.e. for the always-false predicate). "A ⊆ T_L" is an
injection of the variables into the leaves (relabeling equivariance makes the choice of labels
irrelevant). -/
noncomputable def pPred (F : TreeTransformation) {k : ℕ} (φ : Predicate k) : ℝ≥0∞ :=
  ⨅ (S : Finset ℕ) (T : Pattern ↥S) (x : Fin k ↪ ↥S) (_ : T.comap x ∈ canonRelax φ),
    (F.law S T).toOuterMeasure {Q | Q.comap x ∈ φ}

/-- `p(Π, F) = min_{φ ∈ Π} p(φ, F)` (eq. (1), p.5). -/
noncomputable def pLang (F : TreeTransformation) (L : ConstraintLanguage) : ℝ≥0∞ :=
  ⨅ i, pPred F (L.sat i)

end PhyloCSP


