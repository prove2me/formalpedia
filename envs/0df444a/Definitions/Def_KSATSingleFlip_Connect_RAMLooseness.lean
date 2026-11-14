-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_RAMLooseness
-- name    : KSATSingleFlip_Connect_RAMLooseness
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:00:15.987066+00:00
-- url     : https://prove2.me/theorems/b08ddbd6-db03-41f1-b251-5f57d894059a
-- title:
--   Constructive looseness and local routing in a word-RAM model
-- statement:
--   This predicate expresses the algorithmic low-density conclusions of Theorem 1.3 in the explicitly defined candidate word-RAM model. A common set of at least $1-1/n$ solution mass must support every variable-reversal request with a satisfying compact flip list in at most $c_k n$ steps, and every nearby satisfying target with a satisfying compact flip list in at most $d_k n^2$ steps. The outputs obey the stated logarithmic and linear path-length bounds. The requirement applies to every sparse ordering of the same proper-clause formula. This is a model-specific formalization; it does not assert the programs exist.
-- source:
--   Formalization of Theorem 1.3(a,b), Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed p. 4 (PDF p. 6), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf. The paper does not specify this particular RAM instruction set.

import Definitions.Def_KSATSingleFlip_Connect_WordRAM
import Definitions.Def_KSATSingleFlip_Connect_LoosenessRigidity

noncomputable section
open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- The constructive low-density geometry in a particular deterministic
word-RAM model. Both programs and budgets are independent of the input formula.
Every sparse ordering of each proper clause must be handled. -/
def HasRAMLooseLocalGeometry {n k m : ℕ} (F : Formula n k m)
    (flipProgram routeProgram : WordRAMProgram) (flipCost routeCost : ℕ)
    (radius pathConstant : ℝ) : Prop :=
  0 < numSols (ofFormula F) ∧
  ∃ S ⊆ sols (ofFormula F),
    (1 - 1 / (n : ℝ)) * numSols (ofFormula F) ≤ (S.card : ℝ) ∧
    ∀ x ∈ S,
      (∀ v : Fin n, ∀ G : SparseFormula n k m,
        sparseFormulaSemantics G = ofFormula F →
        ∃ p : FlipListPath n,
          wordRAMFlipResult flipProgram (flipCost * n) G x v = some p ∧
          p.Satisfies (ofFormula F) ∧ p.terminal v ≠ x v ∧
          (p.flips.length : ℝ) ≤ 32 * (Real.log k)^5 * Real.log n) ∧
      (∀ y ∈ sols (ofFormula F), (hamming x y : ℝ) ≤ radius * n →
        ∀ G : SparseFormula n k m, sparseFormulaSemantics G = ofFormula F →
        ∃ p : FlipListPath n,
          wordRAMRouteResult routeProgram (routeCost * n * n) G x y = some p ∧
          p.Satisfies (ofFormula F) ∧ p.terminal = y ∧
          (p.flips.length : ℝ) ≤ pathConstant * n)

end KSATSingleFlip.Connect


