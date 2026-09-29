-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronAtPDataOrdV22
-- name    : ModularCurve_JZeroNeronAtPDataOrdV22
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/9eecf113-82ac-59ff-aa4a-5b26be35c1c4
-- title:
--   At-q Néron datum for J0​(Nq), ordinary version 2.2
-- statement:
--   Fix $N \ge 1$, a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb Q}$ whose maximal ideal contains $q$ (the predicate [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16), i.e. $q$ is a non-unit of $A$); write $J = J_0(Nq)$ for the project's Jacobian `JZero (N * q)` and $\mathbb T =$ `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$, acting on $J$ through `heckeModuleBar`. The structure `JZeroNeronAtPDataOrdV22` extends `JZeroNeronAtPDataOrdCore` by a single further field. The inherited data consist of the three-step filtration $\mathrm{toric}(m) \le \mathrm{fin}(m) \le \mathrm{finPart}(m) \le J[m]$ with its compatibilities under divisibility, its Hecke- and decomposition-stability, the inertia laws on the toric part, the component-group module $\Phi$ with its specialisation maps and Eisenstein relations, the abelian quotient maps to $J_0(N)^2$, the Raynaud prolongation clause, the cardinality pins $\#\mathrm{toric}(m) = m^{\mathrm{toricRank}}$ and $\#\mathrm{fin}(m) = m^{\mathrm{toricRank}+2\,\mathrm{abelianRank}}$, the two lower-level detection clauses, and the monodromy inclusion $\sigma x - x \in \mathrm{fin}(m)$ for every $m \ne 0$, every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$ and every $x \in J[m]$.
--
--   The new field `toric_card_heckeTorsion_le` asserts a bound on the toric $\mathfrak m$-torsion. It is required only under the following guards: $q \ne 2$; the Hecke inputs `HeckeInputsAll (N * q)` and the commutation hypothesis `HeckeOperatorsCommuteBar (N * q)`; and, for a maximal ideal $\mathfrak m \subseteq \mathbb T$ which is not eventually Eisenstein (there is no finite set $S$ of primes with $T_\ell - (\ell+1) \in \mathfrak m$ for all $\ell \notin S$), with $q \in \mathfrak m$, with $\mathbb T/\mathfrak m$ finite, and with $\dim_{\mathbb T/\mathfrak m} J[\mathfrak m] = 2$, where $J[\mathfrak m] = \{x \in J : t x = 0 \ \forall t \in \mathfrak m\}$. Under these hypotheses the conclusion is
--   $$\#\bigl(\mathrm{toric}(q) \cap J[\mathfrak m]\bigr) \le \#(\mathbb T/\mathfrak m),$$
--   the intersection being taken inside the additive group $J$. Thus the multiplicity-one hypothesis on $J[\mathfrak m]$ is built into the clause rather than derived. The predicate `HasJZeroNeronAtPDataOrdV22 N q hqN` says that such a datum exists for every valuation subring of $\overline{\mathbb Q}$ lying over $q$.
--
--   **Relation to Mathlib.** Mathlib has no Néron model, component group or character-group theory for modular Jacobians; the filtration, the component-group module and the toric multiplicity bound are the project's own axiomatisation, carried as fields of a structure. The ambient notions used are Mathlib's: `ValuationSubring` with its decomposition and inertia subgroups, `Submodule.torsionBySet` (here `heckeTorsion`), `MvPolynomial` (here `HeckeAlg`), and Hopf-algebra and flatness classes in the inherited Raynaud clause.
--
--   **Where it is used.** Data of this shape package the local analysis at $q$ of $J_0(Nq)$ used in Mazur's principle, the level-lowering step that removes a prime $q$ of multiplicative reduction from the level of the modular form attached to a Frey curve. The toric multiplicity bound under the non-Eisenstein and multiplicity-one guards is what forces the $\mathfrak m$-torsion to avoid the toric part, and hence produces a form of lower level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronAtPDataOrdV22.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataOrdCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataOrdV22 (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronAtPDataOrdCore N q hqN A hA where

  toric_card_heckeTorsion_le : q ≠ 2 → HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 → ((q : ℕ) : HeckeAlg) ∈ 𝔪 →
      Finite (HeckeAlg ⧸ 𝔪) →
      (letI := heckeModuleBar (N * q); Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero (N * q)) 𝔪) = 2) →
      Nat.card ↥(toric q ⊓ (letI := heckeModuleBar (N * q);
          (heckeTorsion (JZero (N * q)) 𝔪).toAddSubgroup)) ≤ Nat.card (HeckeAlg ⧸ 𝔪)

def HasJZeroNeronAtPDataOrdV22 (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataOrdV22 N q hqN A hA)

end ModularCurve

end


