-- Prove2me | Definitions.Def_QBFBackdoor_dual
-- name    : QBFBackdoor_dual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:09.18448+00:00
-- url     : https://prove2.me/theorems/3e5bf2ff-6b79-4b72-8f85-8972853ed406
-- title:
--   The de Morgan dual $\bar\Phi$ of a CNF QBF
-- statement:
--   Let $\Phi=Q.(C_1\wedge\cdots\wedge C_m)$ be a CNF QBF. Its **dual** is the disjunctive formula
--
--   $$
--   \bar\Phi=\bar Q.(\bar C_1\vee\cdots\vee\bar C_m),
--   $$
--
--   where $\bar Q$ replaces every $\forall$ of $Q$ by $\exists$ and vice versa, and $\bar C_i$ is the conjunction of the negations of the literals of $C_i$. For example, $C_i=(x\vee y\vee\neg z)$ gives $\bar C_i=(\neg x)\wedge(\neg y)\wedge(z)$. Each $\bar C_i$ is a conjunction of unit atoms, so $\bar\Phi$ is a disjunctive QBF over $\Gamma_{\mathrm{AFF}}$ with $m$ disjuncts.
--
--   This is the construction behind the PSPACE-completeness of Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ (Lemma 5.4).
--
--   **Formalization Note** It is defined for clauses of every width. The atoms of $\bar C_i$ are listed in the order of `Finset.toList`, which does not affect truth.
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 5.4, p.23

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_QSAT
import Definitions.Def_QBFBackdoor_DQBF

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved

/-- **The de Morgan dual `Φ̄` of a CNF QBF.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan,
Rychlicki, *Backdoors for Quantified Boolean Formulas*, arXiv:2604.15927 (held version, sha256
3ea1662e…), proof of Lemma 5.4, p.23: "Let Φ = Q.(C1 ∧ . . . ∧ Cm) be a quantified 3-CNF formula
and define Φ̄ = Q̄.(C̄1 ∨ . . . ∨ C̄m), where Q̄ is the prefix obtained from Q by replacing every ∀
with ∃ and vice versa, while C̄i is the negation of Ci, e.g., if Ci = (x ∨ y ∨ ¬z), then
C̄i = (¬x) ∧ (¬y) ∧ (z)."

The prefix bits are flipped, and disjunct `i` is the conjunction of the unit atoms `(x_v) = ¬b`,
one for each literal `(v, b)` of clause `i`.

**Formalization Note** The construction applies to clauses of any width. The literals of a clause
are listed in the order of `Finset.toList`; the order of the atoms of a conjunction does not affect
its truth. -/
noncomputable def dual {n m : ℕ} (φ : QBF n m) : DQBF n where
  q := fun j => !φ.q j
  disj := List.ofFn (fun i => (φ.clause i).toList.map (fun l => GAtom.unit l.1 (!l.2)))

end QBFBackdoor


