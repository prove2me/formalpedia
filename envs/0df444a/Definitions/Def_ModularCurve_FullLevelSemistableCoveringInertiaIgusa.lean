-- Prove2me | Definitions.Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa
-- name    : ModularCurve_FullLevelSemistableCoveringInertiaIgusa
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/e554232e-4010-5d00-8abb-26c4875c7c97
-- title:
--   Inertia stability of the Igusa chart at infinity
-- statement:
--   Fix a prime $q$, an integer $M' \neq 0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ and a finite set $W$ of places of the modular function field $\mathrm{modularFunctionFieldC}$ over the residue field of $A$. For a semistable covering $\mathcal{C}$ of type `SemistableCovering q M' A W` — whose data include, for each point $\ell$ of $\mathbb{P}^1(\mathbb{F}_q)$, an Igusa component chart $\mathcal{C}.\mathrm{CIg}\,\ell$ on the field `fieldBar q M'` with residue field $\mathcal{C}.\mathrm{FIg}\,\ell$ over $\mathrm{ResidueField}\,A$, consisting of a valuation subring `integers` with surjective `residue` map, a set `dom` of places of `fieldBar q M'` and a reduction map `placeMap` on those places — this module defines the predicate `InertiaIgusaInftyClause` on $\mathcal{C}$.
--
--   The predicate quantifies over all $\tau$ in `A.inertiaSubgroupIn ℚ`, the inertia subgroup of $A$ inside $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, with no restriction on the tame character of $\tau$, and lets $g$ be the semilinear automorphism [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](../def/ModularCurve_ArithmeticGalois.html#L54), which acts on `fieldBar q M'` coefficientwise through $\tau$. For the chart at the point `lineInfty q` $= [1:0]$ of $\mathbb{P}^1(\mathbb{F}_q)$ it asserts four things: the valuation subring `integers` of that chart is $g$-stable, in the sense that $f$ lies in it if and only if $g \cdot f$ does; a place $P$ lies in `dom` if and only if $g \cdot P$ does; `InducesOnChart (𝒞.CIg (lineInfty q)) g (RingEquiv.refl _)` holds, i.e. the stability of `integers` is witnessed and the induced automorphism of $\mathcal{C}.\mathrm{FIg}(\infty)$ is the identity, so residues are unchanged, $\overline{g \cdot f} = \overline{f}$; and the reduction map is $g$-invariant on its domain, $\mathrm{placeMap}(g \cdot P) = \mathrm{placeMap}(P)$ for $P \in \mathrm{dom}$. The first clause duplicates the stability witness contained in `InducesOnChart`.
--
--   This is the analogue, for all of inertia and for the single Igusa chart at $\infty$ with trivial induced map on the residue field, of the inertia clause in the naturality package (which allows a nontrivial induced automorphism and concerns the supersingular charts) and of `InertiaClause` (which treats all Igusa charts but only inertia elements of tame character $1$).
--
--   **Relation to Mathlib.** Mathlib has no notion of component charts, annuli or semistable coverings of a function field along a valuation subring; these, together with `InducesOnChart`, are the project's own. The inertia subgroup used here is obtained from Mathlib's `ValuationSubring.inertiaSubgroup` and `decompositionSubgroup` by pushing forward along the inclusion of the decomposition subgroup.
--
--   **Where it is used.** Clauses of this kind pin down the action of inertia at $q$ on the semistable reduction of the modular curve of level $\Gamma_H(q^2M')$, in particular on its Igusa components and their reductions of places; they serve as the starting point for determining how a general inertia element permutes the Igusa charts, and hence feed the computation of the Galois action needed in the level-lowering step at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelSemistableCoveringInertiaIgusa.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

namespace SemistableCovering

def InertiaIgusaInftyClause (𝒞 : SemistableCovering q M' A W) : Prop :=
  ∀ τ ∈ A.inertiaSubgroupIn ℚ,
    let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
    (∀ f : fieldBar q M', f ∈ (𝒞.CIg (lineInfty q)).integers ↔ g • f ∈ (𝒞.CIg (lineInfty q)).integers) ∧
      (∀ P, P ∈ (𝒞.CIg (lineInfty q)).dom ↔ g • P ∈ (𝒞.CIg (lineInfty q)).dom) ∧
      InducesOnChart (𝒞.CIg (lineInfty q)) g (RingEquiv.refl _) ∧
      (∀ P ∈ (𝒞.CIg (lineInfty q)).dom, (𝒞.CIg (lineInfty q)).placeMap (g • P) = (𝒞.CIg (lineInfty q)).placeMap P)

end SemistableCovering

end ModularCurve.FullLevel

end


