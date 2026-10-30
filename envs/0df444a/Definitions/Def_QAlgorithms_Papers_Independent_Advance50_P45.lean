-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P45
-- name    : QAlgorithms_Papers_Independent_Advance50_P45
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:17:45.826787+00:00
-- url     : https://prove2.me/theorems/9ea72a25-9bea-4ee6-8cb0-756b587db63b
-- title:
--   Definitions for Optimal uniform continuity bound for conditional entropy of classical--quantum states
-- statement:
--   The objects the formalized statements of *Optimal uniform continuity bound for conditional entropy of classical--quantum states* (arXiv:1909.01755) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CQState`: PDF pp.2,5, Eqs.(5),(31): a normalized CQ ensemble in a fixed classical basis X, with a normalized density matrix at EVERY label, even of zero mass. For countable X this represents the direct sum of the weighted B blocks. PMF normalization excludes an empty label space.
--   - `cqCoordinates`: PDF pp.2,5, Eqs.(5),(31): all coordinates of the CQ operator; blocks at different labels are orthogonal. For finite X this is its full density matrix; for countable X it is the kernel of the trace-class direct sum. The accepted cqBlock finite-mixture definition is specialized to a singleton mixing index, so its block is exactly the probability mass times the branch density.
--   - `cqConditionalEntropy`: PDF pp.2,5, Eqs.(4),(29): average branch von Neumann entropy in bits. This sum is absolutely convergent: each normalized finite B branch has entropy between 0 and log₂(card B), and the real PMF masses sum to one. No hypothesis on the Shannon entropy of the classical labels is required.
--   - `finiteCQDistance`: PDF p.2, Eq.(6): half the Schatten trace norm of the difference of the full finite CQ matrices, retaining the SAME classical coordinates.
--   - `countableCQDistance`: PDF p.5, Eq.(32): half the trace norm of the countable direct-sum operator difference. Orthogonal blocks give the SUM of their trace norms. The sum converges since each term is at most r(x)+s(x), whose sum is 2. It is not the trace norm of the averaged B matrices.
--   - `swapFactors`: PDF p.5, Eq.(28): exchange A and B product coordinates, including both row and column coordinates, to use the accepted convex roof's traceRight.
--   - `formationEntropy`: PDF p.5, Eq.(28): entanglement of formation, the infimum of the average B-marginal entropy over ALL normalized finite pure-state decompositions with the prescribed barycenter. Ensemble lengths are unrestricted. Coordinate swap maps these decompositions bijectively to the accepted convex roof's domain.
-- source:
--   Optimal uniform continuity bound for conditional entropy of classical--quantum states, arXiv:1909.01755v2, https://arxiv.org/abs/1909.01755v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
Wilde, arXiv:1909.01755v2: Proposition 1 and Corollaries 2–3.
Entropies are in bits. All local definitions have complete bodies; only the
three source results have sorry proofs. Compilation awaits the batch handoff.
The accepted Gap48.P22 import supplies the unrestricted finite pure-ensemble
convex roof; swapping coordinates aligns its marginal with Eq.(28).
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (cqBlock)

/-- PDF pp.2,5, Eqs.(5),(31): a normalized CQ ensemble in a fixed classical
basis X, with a normalized density matrix at EVERY label, even of zero mass.
For countable X this represents the direct sum of the weighted B blocks.
PMF normalization excludes an empty label space. -/
structure CQState (X B : Type*) [Fintype B] where
  probability : PMF X
  branch : X → Matrix B B ℂ
  normalized : ∀ x, IsDensityMatrix (branch x)

/-- PDF pp.2,5, Eqs.(5),(31): all coordinates of the CQ operator; blocks at
different labels are orthogonal. For finite X this is its full density matrix;
for countable X it is the kernel of the trace-class direct sum. The accepted
cqBlock finite-mixture definition is specialized to a singleton mixing index,
so its block is exactly the probability mass times the branch density. -/
def cqCoordinates {X B : Type*} [Fintype B] (R : CQState X B) :
    Matrix (X × B) (X × B) ℂ :=
  fun i j => if i.1 = j.1 then
    (cqBlock (fun _ : Unit => R.branch i.1)
      (fun _ : X × Unit => (R.probability i.1).toReal) i.1) i.2 j.2
    else 0

/-- PDF pp.2,5, Eqs.(4),(29): average branch von Neumann entropy in bits.
This sum is absolutely convergent: each normalized finite B branch has entropy
between 0 and log₂(card B), and the real PMF masses sum to one. No hypothesis
on the Shannon entropy of the classical labels is required. -/
def cqConditionalEntropy {X B : Type*} [Fintype B] [DecidableEq B]
    (R : CQState X B) : ℝ :=
  ∑' x, (R.probability x).toReal * vnEntropy (R.branch x)

/-- PDF p.2, Eq.(6): half the Schatten trace norm of the difference of the
full finite CQ matrices, retaining the SAME classical coordinates. -/
def finiteCQDistance {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B]
    (R S : CQState X B) : ℝ :=
  traceNorm (cqCoordinates R - cqCoordinates S) / 2

/-- PDF p.5, Eq.(32): half the trace norm of the countable direct-sum
operator difference. Orthogonal blocks give the SUM of their trace norms.
The sum converges since each term is at most r(x)+s(x), whose sum is 2.
It is not the trace norm of the averaged B matrices. -/
def countableCQDistance {X B : Type*} [Fintype B] [DecidableEq B]
    (R S : CQState X B) : ℝ :=
  (∑' x, traceNorm
    (cqBlock (fun _ : Unit => R.branch x)
      (fun _ : X × Unit => (R.probability x).toReal) x -
     cqBlock (fun _ : Unit => S.branch x)
      (fun _ : X × Unit => (S.probability x).toReal) x)) / 2

/-- PDF p.5, Eq.(28): exchange A and B product coordinates, including both
row and column coordinates, to use the accepted convex roof's traceRight. -/
def swapFactors {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (B × A) (B × A) ℂ :=
  fun i j => rho (i.2, i.1) (j.2, j.1)

/-- PDF p.5, Eq.(28): entanglement of formation, the infimum of the average
B-marginal entropy over ALL normalized finite pure-state decompositions with
the prescribed barycenter. Ensemble lengths are unrestricted. Coordinate swap
maps these decompositions bijectively to the accepted convex roof's domain. -/
def formationEntropy {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Gap48.P22.formationEntanglement (swapFactors rho)

/-- Different classical labels have zero matrix entries (Eqs.(5),(31)). -/
example {X B : Type*} [Fintype B] (R : CQState X B)
    (x y : X) (b c : B) (h : x ≠ y) : cqCoordinates R (x,b) (y,c) = 0 := by
  simp [cqCoordinates, h]

/-- One certain label gives exactly its branch entropy (Eq.(29)). -/
example {B : Type*} [Fintype B] [DecidableEq B]
    (rho : Matrix B B ℂ) (h : IsDensityMatrix rho) :
    cqConditionalEntropy (⟨PMF.pure (), fun _ => rho, fun _ => h⟩ : CQState Unit B) =
      vnEntropy rho := by
  simp [cqConditionalEntropy]

/-- The finite distance of identical CQ states is zero (Eq.(6)). -/
example {X B : Type*} [Fintype X] [Fintype B] [DecidableEq B]
    (R : CQState X B) : finiteCQDistance R R = 0 := by
  simp [finiteCQDistance, traceNorm, cfc_zero]

/-- The countable distance of identical CQ states is zero (Eq.(32)). -/
example {X B : Type*} [Fintype B] [DecidableEq B]
    (R : CQState X B) : countableCQDistance R R = 0 := by
  simp [countableCQDistance, traceNorm, cfc_zero]

/-- Swapping makes the accepted roof's marginal exactly the source B marginal,
for EVERY operator, and hence for every member of every decomposition. -/
example {A B : Type*} [Fintype A]
    (rho : Matrix (A × B) (A × B) ℂ) :
    traceRight (swapFactors rho) = traceLeft rho := by
  rfl

/-- Product-coordinate swapping is an involution, so ensemble transport is
bijective, with no restriction on ensemble cardinality or barycenter. -/
example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    swapFactors (swapFactors rho) = rho := by
  rfl

/-- For a qubit the logarithmic term vanishes (Eq.(4)). -/
example (epsilon : ℝ) :
    epsilon * Real.logb 2 ((2 : ℝ) - 1) + binEntropy2 epsilon = binEntropy2 epsilon := by
  norm_num

end QAlgorithms.Papers.Independent.Advance50.P45


