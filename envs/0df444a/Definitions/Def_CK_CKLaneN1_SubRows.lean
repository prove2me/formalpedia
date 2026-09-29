-- Prove2me | Definitions.Def_CK_CKLaneN1_SubRows
-- name    : CK_CKLaneN1_SubRows
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:52:31.867108+00:00
-- url     : https://prove2.me/theorems/20c09707-7829-4b8b-b7fe-58e908eb8a0e
-- title:
--   Courtade–Kumar proof module `CKLaneN1.SubRows` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.SubRows` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.SubRows` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.SubRows (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/SubRows.lean)

import Definitions.Def_CK_GeneralCK_BellmanAssembly

-- ===== source module CKLaneN1.SubRows =====
section

/-!
# Lane N1: binding sub-row propositions of the central mean square

Source: `CK_OPPOSITE_EXTENSION.zip` (sha256
3f4b121c784ae512aadf9b0fe829c154d43cc7012f7f5bcb77433b446f66392a), `PROOF.md` §4
("Exhaustive assembly of the main theorem"), and its dependency
`dependencies/CK_NO_SEPARATION_EXTENSION.zip` (sha256
e9cd4c2e81718635f8e9e7d4ed75b0b00748431039274b49d8f6e201014923cc), Theorems A/B.

`CentralSquareRow` is a verbatim copy of `CKRoute.CentralSquare`
(`~/ck_lanes_20260923/coord/routesrc/CKRoute/Manuscript.lean`), with a verbatim local copy of
`CKRoute.PsiActive`, so the coordinator binds it by `Iff.rfl`.

Every sub-row is stated for canonical laws (`a ≤ b`, `a + b ≤ 1`) with strict psi-activity,
exactly like the route rows. Notation of the archive, in canonical orientation:
`d = |a-b| = b - a`, `q = |1-a-b| = 1 - a - b`, `E = (e+f)/2 = meanEntropy`.

§4 table (opposite side `a ≤ 1/2 ≤ b`, both means in `[1/10, 9/10]`):

| Domain                                      | Sub-row            | Owner lane |
|---------------------------------------------|--------------------|------------|
| same side `b ≤ 1/2` (half-square)           | `SR_SameSideHalf`  | N1         |
| `d ≤ 1/50`                                  | `SR_DiagonalBand`  | N1         |
| `d ≥ 1/50`, `E ≥ 11/200`                    | `SR_Moderate`      | N1b        |
| `d ≥ 1/50`, `E ≤ 11/200`, `d ≤ 4E`          | `SR_SmallRatio`    | N1         |
| `d ≥ 1/50`, `E ≤ 11/200`, `4E ≤ d ≤ 8E`     | `SR_Transition`    | N1c        |
| `d ≥ 1/50`, `E ≤ 11/200`, `d ≥ 8E`          | `SR_LargeRatio`    | N4         |
|   … and `q ≥ 8E` (parent dominance (2))     | `SR_Parent8`       | N4         |
|   … and `q ≤ 8E` (eight-ratio theorem (3))  | `SR_EightRatio`    | N4         |

All interfaces overlap at equality (closed inequalities), as in the archive.
Nothing here asserts that any row holds.
-/

namespace CKLaneN1

open GeneralCK

/-- Strict psi-activity at the parent (verbatim copy of `CKRoute.PsiActive`). -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- Central mean square `a,b ∈ [1/10,9/10]` (CK_OPPOSITE_EXTENSION.zip, sha256
3f4b121c784ae512aadf9b0fe829c154d43cc7012f7f5bcb77433b446f66392a). Canonical form.
(Verbatim copy of `CKRoute.CentralSquare`.) -/
def CentralSquareRow : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → PsiActive μ → μ.gap ≤ μ.cost

/-- Same-side half-square `[1/10,1/2]^2`, canonical
(CK_NO_SEPARATION_EXTENSION Theorem B, lower half-square). -/
def SR_SameSideHalf : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 → PsiActive μ → μ.gap ≤ μ.cost

/-- §4 row `d ≤ 1/50`: the full-entropy central diagonal band
(CK_NO_SEPARATION_EXTENSION Theorem A), on the opposite central part. -/
def SR_DiagonalBand : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    μ.b - μ.a ≤ 1 / 50 → PsiActive μ → μ.gap ≤ μ.cost

/-- §4 row `d ≥ 1/50, E ≥ 11/200`: moderate-entropy theorem (5)
(`opposite_cover/PROOF.md`, 4,730 leaves). -/
def SR_Moderate : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → 11 / 200 ≤ μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-- §4 row `d ≥ 1/50, E ≤ 11/200, d ≤ 4E`: central small-ratio theorem and tail
(CK_SMALL_RATIO_EXTENSION Theorem 4, 611 leaves + 11 tail comparisons). -/
def SR_SmallRatio : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 → μ.b - μ.a ≤ 4 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- §4 row `d ≥ 1/50, E ≤ 11/200, 4E ≤ d ≤ 8E`: transition theorem (4)
(`transition/PROOF.md`, 2,425 leaves). -/
def SR_Transition : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    4 * μ.meanEntropy ≤ μ.b - μ.a → μ.b - μ.a ≤ 8 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- §4 row `d ≥ 1/50, E ≤ 11/200, d ≥ 8E, q ≥ 8E`: parent dominance (2)
(`audit/PARENT8_PROOF.md`, 332 leaves + analytic tail); vacuous in-row. -/
def SR_Parent8 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a → 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Law-level parent-dominance form of the `SR_Parent8` domain (psi not strictly active). -/
def SR_Parent8Dominance : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a → 8 * μ.meanEntropy ≤ 1 - μ.a - μ.b →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy

/-- §4 row `d ≥ 1/50, E ≤ 11/200, d ≥ 8E, q ≤ 8E`: eight-ratio theorem (3)
(`analytic/EIGHT_RATIO_PROOF.md`, 50 leaves + analytic tail). -/
def SR_EightRatio : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a → 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Union of the last two §4 rows (`d ≥ 1/50, E ≤ 11/200, d ≥ 8E`): parent8 ∪ eight-ratio. -/
def SR_LargeRatio : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → 1 / 2 ≤ μ.b → μ.b ≤ 9 / 10 →
    1 / 50 ≤ μ.b - μ.a → μ.meanEntropy ≤ 11 / 200 →
    8 * μ.meanEntropy ≤ μ.b - μ.a →
    PsiActive μ → μ.gap ≤ μ.cost

/-- The six sub-rows consumed by the §4 assembly adapter `centralSquare_of_subrows`. -/
structure SubRows : Prop where
  sameSideHalf : SR_SameSideHalf
  diagonalBand : SR_DiagonalBand
  moderate : SR_Moderate
  smallRatio : SR_SmallRatio
  transition : SR_Transition
  largeRatio : SR_LargeRatio

end CKLaneN1

end


