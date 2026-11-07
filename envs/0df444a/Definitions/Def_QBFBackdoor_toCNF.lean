-- Prove2me | Definitions.Def_QBFBackdoor_toCNF
-- name    : QBFBackdoor_toCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:58.031398+00:00
-- url     : https://prove2.me/theorems/a026c13f-997c-43bc-89b6-82490fbedfda
-- title:
--   The CNF form of a $\Gamma_{\mathrm{AFF}}$ formula
-- statement:
--   Every $\Gamma_{\mathrm{AFF}}$ atom is replaced by clauses:
--
--   $$
--   (x=y)\ \mapsto\ (x\vee\neg y)\wedge(\neg x\vee y),\qquad (x)\mapsto (x),\qquad (\neg x)\mapsto(\neg x),
--   $$
--
--   and a $\Gamma_{\mathrm{AFF}}$ formula $\phi$ is mapped to the conjunction of the clauses of its atoms. Every clause produced has at most two literals and at most one positive literal.
--
--   This conversion transfers the hardness of 4-Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ to the CNF classes 2-CNF and HORN in the proof of Theorem 5.9.
--
--   **Formalization Note** Clauses are sets of literals; `GAtom.toClauses` converts one atom and `toCNF` a list of atoms.
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Theorem 5.9, p.26

import Mathlib
import Definitions.Def_QBFBackdoor_DQBF

namespace QBFBackdoor

/-- **The clauses of a `Γ_AFF` atom.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki,
*Backdoors for Quantified Boolean Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…),
proof of Theorem 5.9, p.26: "replace every atom of the form (x = y) with a conjunction of clauses
(x∨¬y)∧(¬x∨y), and unit atoms with equivalent unit clauses."

A clause is a set of literals, `(v, true)` = `x_v`, `(v, false)` = `¬x_v`. The unit atom
`(x) = b` becomes the unit clause `{(x, b)}`. -/
def GAtom.toClauses {n : ℕ} : GAtom n → List (Finset (Fin n × Bool))
  | .unit x b => [{(x, b)}]
  | .eq x y => [{(x, true), (y, false)}, {(x, false), (y, true)}]

/-- The CNF obtained from a `Γ_AFF` formula by converting every atom (proof of Theorem 5.9,
p.26). -/
def toCNF {n : ℕ} (ϕ : List (GAtom n)) : List (Finset (Fin n × Bool)) :=
  ϕ.flatMap GAtom.toClauses

end QBFBackdoor


