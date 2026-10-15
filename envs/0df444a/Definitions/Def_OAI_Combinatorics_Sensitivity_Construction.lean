-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
-- name    : OAI_Combinatorics_Sensitivity_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:43:30.161114+00:00
-- url     : https://prove2.me/theorems/61f21e09-0fb3-42f0-ab76-c751eda78e56
-- title:
--   The constructed witness function: iterated row clauses, an OR of copies, and reindexing
-- statement:
--   Fix natural numbers $d$, $M$ and $r$, a regular tournament $T$ with parameter $M$ (a tournament on $k = 2M^2 + 1$ vertices in which every vertex has out-degree $M^2$), and a good labeling $\lambda$ of $T$ with $r$ labels. Write $[n] = \{0, 1, \dots, n-1\}$, identify Boolean values with $\{0,1\}$, and let $G_0, \dots, G_d$ be the initial family on $\{0,1\}^{[M] \times [d+2]}$, where $G_q$ accepts exactly the inputs within Hamming distance $d - q$ of one of the $M$ row indicators.
--
--   1. **Base.** The base of the construction assigns the initial family $(G_0, \dots, G_d)$ to the index count $d + 1$, and the constantly false family to every other index count.
--
--   2. **Coordinates.** The level-$n$ coordinate set is the tower coordinate set over $[M] \times [d+2]$ with $k$ rows and $r$ columns: $X_0 = [M] \times [d+2]$ and $X_{n+1} = ([k] \times [r]) \times X_n$.
--
--   3. **Terminal predicate.** $P_{T,\lambda} : \{0,1\}^{X_d} \to \{0,1\}$ is the single member of the tower family $F^{(d,1)}$, the family obtained from the initial family by $d$ levels of the row-clause construction over $(T, \lambda)$. Each level consumes one index, so the $d+1$ initial predicates leave exactly one predicate after $d$ levels.
--
--   4. **Final Boolean function.** $Q_{T,\lambda} = \mathrm{OR}_M \circ P_{T,\lambda}$ is the OR of $M$ disjoint copies of the terminal predicate, a Boolean function on $\{0,1\}^{[M] \times X_d}$.
--
--   5. **Dimension.** The number of variables is
--   $$
--   N(d, M, r) = (d+2)\, M^2 \, \big((2M^2+1)\, r\big)^d ,
--   $$
--   and the file proves $|[M] \times X_d| = N(d,M,r)$.
--
--   6. **Witness function.** $f_{T,\lambda} : \{0,1\}^{[N(d,M,r)]} \to \{0,1\}$ is $Q_{T,\lambda}$ reindexed along a fixed bijection $e : [M] \times X_d \to [N(d,M,r)]$, that is, $f_{T,\lambda}(x) = Q_{T,\lambda}(x \circ e)$.
--
--   This is the explicit Boolean function behind the quantitative separation of block sensitivity from sensitivity. Under the hypotheses $M > 0$, $r > 0$ and the parameter budget $\frac{\max(r,16)}{M}\, 3^{d+1} \le 2$, separate results show that $f_{T,\lambda}$ vanishes at the all-zero input, has sensitivity at most $2(d+2)M^{d+1}$, and has block sensitivity at least $M^2 (2M^2+1)^d$ at the all-zero input.
--
--   **Formalization Note** The definitions are `constructionBase d M` (which is `baseExtension (d + 1) (initialFamily d M)`), the abbreviation `ConstructionCoordinates d M r n` for `TowerCoordinates (2 * M ^ 2 + 1) r (Fin M × Fin (d + 2)) n`, `terminalPredicate d T A` (the member of index $0$ of `towerFamily T.toTournament A.label (constructionBase d M) d 1`, which starts from the base at index count $1 + d = d + 1$), `finalBoolean d T A` (which is `orCopies (K := Fin M)` applied to the terminal predicate), `constructionDimension d M r`, the cardinality lemma `final_coordinates_card`, and `finalWitness d T A`. The bijection is `Fintype.equivFinOfCardEq (final_coordinates_card d M r)`, a noncanonical classical choice.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Construction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Construction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex

namespace OAI

/-! The initial family, recursively constructed predicates, and final OR. -/

noncomputable section
open scoped Classical

namespace Paper320

def constructionBase (d M : ℕ) := baseExtension (d + 1) (initialFamily d M)

abbrev ConstructionCoordinates (d M r n : ℕ) :=
  TowerCoordinates (2 * M ^ 2 + 1) r (Fin M × Fin (d + 2)) n

def terminalPredicate {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (ConstructionCoordinates d M r d → Bool) → Bool :=
  towerFamily T.toTournament A.label (constructionBase d M) d 1 0

def finalBoolean {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (Fin M × ConstructionCoordinates d M r d → Bool) → Bool :=
  orCopies (K := Fin M) (terminalPredicate d T A)

def constructionDimension (d M r : ℕ) : ℕ :=
  (d + 2) * M ^ 2 * ((2 * M ^ 2 + 1) * r) ^ d

theorem final_coordinates_card (d M r : ℕ) :
    Fintype.card (Fin M × ConstructionCoordinates d M r d) = constructionDimension d M r := by
  rw [Fintype.card_prod, tower_coordinates_card]
  simp only [Fintype.card_prod, Fintype.card_fin, constructionDimension]
  ring

def finalWitness {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (Fin (constructionDimension d M r) → Bool) → Bool :=
  reindex (Fintype.equivFinOfCardEq (final_coordinates_card d M r)) (finalBoolean d T A)

end Paper320

end

end OAI


