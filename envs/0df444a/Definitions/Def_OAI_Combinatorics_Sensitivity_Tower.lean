-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
-- name    : OAI_Combinatorics_Sensitivity_Tower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:32:22.395883+00:00
-- url     : https://prove2.me/theorems/589f9711-918f-4d1b-ad77-ca9a01346822
-- title:
--   Iterated row-clause construction: tower coordinates, families, and lifted blocks
-- statement:
--   Fix a tournament $T$ on $[k] = \{0, \dots, k-1\}$ and a labeling $\lambda : [k] \times [k] \to [r]$, and let $\mathcal{R}$ denote one level of the row-clause construction, which turns a family of $h+1$ predicates on $\{0,1\}^X$ into a family of $h$ predicates on $\{0,1\}^{([k] \times [r]) \times X}$.
--
--   1. **Tower coordinates.** From a coordinate set $I$ define $X_0 = I$ and $X_{n+1} = ([k] \times [r]) \times X_n$. If $I$ is finite, so is every $X_n$, and
--   $$
--   |X_n| = (kr)^n \, |I| .
--   $$
--
--   2. **Block index sets.** From an index set $K$ define $K_0 = K$ and $K_{n+1} = [k] \times K_n$.
--
--   3. **Tower family.** Given a base that assigns to every $h \in \mathbb{N}$ a family $\mathrm{base}(h)$ of $h$ predicates on $\{0,1\}^I$, define families $F^{(n,h)}$ of $h$ predicates on $\{0,1\}^{X_n}$ by
--   $$
--   F^{(0,h)} = \mathrm{base}(h), \qquad F^{(n+1,h)} = \mathcal{R}\big(F^{(n,h+1)}\big).
--   $$
--   Each level consumes one index, so $F^{(n,h)}$ is built from $\mathrm{base}(h+n)$.
--
--   4. **Tower blocks.** Given blocks $(B_b)_{b \in K}$, finite subsets of $I$, define blocks of $X_n$ indexed by $K_n$:
--   $$
--   B^{(0)}_b = B_b, \qquad B^{(n+1)}_{(i,b)} = \mathrm{lift}_i\big(B^{(n)}_b\big),
--   $$
--   where $\mathrm{lift}_i$ places a copy of a block in every column of row $i$.
--
--   5. **Base extension.** A single family $G$ of $D$ predicates is turned into a base by setting $\mathrm{base}(D) = G$ and letting $\mathrm{base}(h)$ consist of constantly false predicates for $h \ne D$.
--
--   These objects describe the $n$-fold iteration of the construction: starting from the initial Hamming-ball family of $d+1$ predicates, the tower family after $d$ levels contains the terminal predicate, and the tower blocks are its pairwise disjoint sensitive blocks at the all-zero input.
--
--   **Formalization Note** The types `TowerCoordinates k r I n` and `TowerBlockIndex k K n` are defined by recursion on `n`, with `Fintype` instances `towerCoordinatesFintype` and `towerBlockIndexFintype`; the cardinality formula is `tower_coordinates_card`. The tower family `towerFamily T label base n h` and the blocks `towerBlocks` are defined by recursion on `n`. `baseExtension` casts the index along the equation $h = D$, and `baseExtension_same` records that it returns $G$ at $h = D$; the constant-false values for $h \ne D$ are placeholders not used in the construction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Tower.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Tower.lean by skeleton subtraction
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

namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

def TowerCoordinates (k r : ℕ) (I : Type) : ℕ → Type
  | 0 => I
  | n + 1 => (Fin k × Fin r) × TowerCoordinates k r I n

instance towerCoordinatesFintype (k r : ℕ) (I : Type) [Fintype I] :
    (n : ℕ) → Fintype (TowerCoordinates k r I n)
  | 0 => inferInstanceAs (Fintype I)
  | n + 1 => by
    letI := towerCoordinatesFintype k r I n
    exact inferInstanceAs (Fintype ((Fin k × Fin r) × TowerCoordinates k r I n))

def TowerBlockIndex (k : ℕ) (K : Type) : ℕ → Type
  | 0 => K
  | n + 1 => Fin k × TowerBlockIndex k K n

instance towerBlockIndexFintype (k : ℕ) (K : Type) [Fintype K] :
    (n : ℕ) → Fintype (TowerBlockIndex k K n)
  | 0 => inferInstanceAs (Fintype K)
  | n + 1 => by
    letI := towerBlockIndexFintype k K n
    exact inferInstanceAs (Fintype (Fin k × TowerBlockIndex k K n))

def towerFamily {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool) :
    (n h : ℕ) → Fin h → (TowerCoordinates k r I n → Bool) → Bool
  | 0, h => base h
  | n + 1, h => recursiveFamily T label (towerFamily T label base n (h + 1))

def towerBlocks {k r : ℕ} {I K : Type} (blocks : K → Finset I) :
    (n : ℕ) → TowerBlockIndex k K n → Finset (TowerCoordinates k r I n)
  | 0, b => blocks b
  | n + 1, b => rowLift b.1 (towerBlocks blocks n b.2)

/-- Extend a prescribed initial family to unused index counts without adding assumptions. -/
def baseExtension {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool)
    (h : ℕ) (q : Fin h) (x : I → Bool) : Bool :=
  if he : h = D then F (Fin.cast he q) x else false

@[simp] theorem baseExtension_same {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool) :
    baseExtension D F D = F := by
  funext q x
  simp [baseExtension]

theorem tower_coordinates_card {k r : ℕ} {I : Type} [Fintype I] (n : ℕ) :
    Fintype.card (TowerCoordinates k r I n) = (k * r) ^ n * Fintype.card I := by
  induction n with
  | zero =>
    change Fintype.card I = (k * r) ^ 0 * Fintype.card I
    simp
  | succ n ih =>
    change Fintype.card ((Fin k × Fin r) × TowerCoordinates k r I n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

end Paper320

end

end OAI


