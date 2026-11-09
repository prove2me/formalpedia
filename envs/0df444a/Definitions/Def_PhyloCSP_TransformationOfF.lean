-- Prove2me | Definitions.Def_PhyloCSP_TransformationOfF
-- name    : PhyloCSP_TransformationOfF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:26:55.667308+00:00
-- url     : https://prove2.me/theorems/5f65df6b-7ad9-4dd6-a22a-21e02f65e987
-- title:
--   Transformations of the Fraïssé limit and their guarantees $p(\varphi,D)$
-- statement:
--   A **transformation of $\mathcal F$** is a probability distribution of a random ternary relation $D$ on $Z$ such that every realization $(Z,D)$ is a binary tree structure (Definition 7.6). For a predicate $\varphi$ of arity $k$ with canonical relaxation $\varphi'$,
--   $$
--   p(\varphi,D)=\inf_{\substack{x_1,\dots,x_k\in Z\ \text{distinct}\\ C\models\varphi'(x_1,\dots,x_k)}}\Pr\bigl(D\models\varphi(x_1,\dots,x_k)\bigr),\qquad p(\Pi,D)=\min_{\varphi\in\Pi}p(\varphi,D),
--   $$
--   where $C$ is the relation of the concrete Fraïssé limit. Automorphisms act by $(gD)(a;b,c)=D(g^{-1}a;g^{-1}b,g^{-1}c)$, and the distribution of $D$ is **$\mathrm{Aut}(\mathcal F)$-invariant** if $gD$ has the same distribution as $D$ for every $g\in\mathrm{Aut}(\mathcal F)$.
--
--   **Formalization Note** The law is a probability measure on the product space $\{0,1\}^{Z^3}$; "every realization" is read as "almost every realization", which describes the same laws on the closed set $\mathcal H$ of tree relations. Guarantees take values in $[0,\infty]$, with empty infimum $\infty$.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 7.6, p.20 (PDF p.22); p.21 (PDF p.23)

import Mathlib
import Definitions.Def_PhyloCSP_AutF
import Definitions.Def_PhyloCSP_canonRelax
import Definitions.Def_PhyloCSP_ConstraintLanguage

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PhyloCSP

/-- **Transformations of the Fraïssé limit (Definition 7.6) and their guarantees.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 7.6, p.20 (PDF p.22): "A transformation of F is a
probability distribution on ternary relations D on Z such that, for every realization of D, (Z, D)
is a binary tree structure."

**Formalization Note.** A law is a probability measure on `Z → Z → Z → Bool` with the product
σ-algebra. "For every realization" is read as "almost every realization": a law on the closed set
`H` of tree relations (p.21) is the same as a law on all relations giving `H` full measure. -/
def IsTransformationOfF (μ : Measure (Z → Z → Z → Bool)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ᵐ D ∂μ, IsTreeRel D

/-- `R ⊨ φ(x₁, …, x_k)`: the pattern of the distinct leaves `x` in the relation `R` belongs to
`Sat(φ)`. -/
def relSat {k : ℕ} (R : Z → Z → Z → Bool) (x : Fin k ↪ Z) (φ : Predicate k) : Prop :=
  ∃ P ∈ φ, ∀ a b c, P.1 a b c = R (x a) (x b) (x c)

/-- `p(φ, D)` of Definition 7.6, p.20: "p(φ, D) = inf_{x1,...,xk ∈ Z distinct, C ⊨ φ′(x1,...,xk)}
Pr(D ⊨ φ(x1, . . . , xk))" with `C = fraisseRel` and `φ′` the canonical relaxation. Values in
`ℝ≥0∞` (empty infimum `⊤`). -/
noncomputable def pPredF (μ : Measure (Z → Z → Z → Bool)) {k : ℕ} (φ : Predicate k) : ℝ≥0∞ :=
  ⨅ (x : Fin k ↪ Z) (_ : relSat fraisseRel x (canonRelax φ)), μ {D | relSat D x φ}

/-- `p(Π, D) = min_{φ ∈ Π} p(φ, D)`. -/
noncomputable def pLangF (μ : Measure (Z → Z → Z → Bool)) (L : ConstraintLanguage) : ℝ≥0∞ :=
  ⨅ i, pPredF μ (L.sat i)

/-- The action of a permutation on relations, p.21 (PDF p.23): "(gD)(a; b, c) =
D(g⁻¹a; g⁻¹b, g⁻¹c)". -/
def actRel (g : Equiv.Perm Z) (D : Z → Z → Z → Bool) : Z → Z → Z → Bool :=
  fun a b c => D (g⁻¹ a) (g⁻¹ b) (g⁻¹ c)

/-- p.21: "The distribution of D is invariant under Aut(F) if gD has the same distribution as D
for every g ∈ Aut(F)." -/
def IsAutInvariant (μ : Measure (Z → Z → Z → Bool)) : Prop :=
  ∀ g ∈ AutF, μ.map (actRel g) = μ

end PhyloCSP


