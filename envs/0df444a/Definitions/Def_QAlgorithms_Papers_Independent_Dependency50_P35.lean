-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
-- name    : QAlgorithms_Papers_Independent_Dependency50_P35
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:50:33.016649+00:00
-- url     : https://prove2.me/theorems/84fde4b4-84bf-4037-af98-218a37f6262b
-- title:
--   Definitions for On quantum Renyi entropies: a new generalization and some properties
-- statement:
--   The objects the formalized statements of *On quantum Renyi entropies: a new generalization and some properties* (arXiv:1306.3142) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tr`: PDF p.3: real trace on Hermitian matrices.
--   - `Substate`: PDF p.3: the set S excludes zero and permits subnormalization.
--   - `Density`: PDF p.26, footnote 46: normalized positive operators.
--   - `Dominates`: PDF p.4: sigma dominates rho iff ker sigma is contained in ker rho.
--   - `Domain`: PDF pp.4–5: the finite real-valued axiomatic domain.
--   - `spectralPower`: PDF pp.3,21: spectral powers, with generalized inverse for negative exponents. The zero exponent is the identity even on the kernel.
--   - `lnOp`: PDF pp.3,18–20: natural operator logarithm, zero on the kernel.
--   - `logOp`: PDF p.3: base-two operator logarithm.
--   - `elog`: Scalar log with its extended zero limit, not Real.log's totalized value.
--   - `elogNN`: Extended scalar logarithm also retaining a positive-infinite trace objective.
--   - `sandwich`: PDF p.7, Definition 2: the unnormalized sandwiched trace.
--   - `rawTrace`: PDF p.7: trace before the scalar logarithm.
--   - `divergence`: PDF p.7: Definition 2, including orthogonality and support failure. Outside the source's positive orders other than one, no interpretation is asserted.
--   - `relative`: PDF p.6, Definition 1: trace-normalized relative entropy in bits.
--   - `maxRelative`: PDF p.8, Definition 3: EReal infimum, so an empty feasible set yields +infinity.
--   - `petz`: PDF pp.4,10: Petz divergence, continuously extended at order one.
--   - `renyiEntropy`: PDF pp.3–4: unconditional Renyi entropy, with the von Neumann value at one.
--   - `supportId`: PDF p.10: identity on the support, embedded in the ambient space.
--   - `supportRank`: PDF pp.10–12: support dimension, not ambient dimension.
--   - `supportMixed`: PDF p.10: maximally mixed state on supp rho.
--   - `conditionalRenyi`: PDF p.11, Definition 4: supremum over precisely S_B, including subnormalized states.
--   - `leftMarginal`: Partial trace over the second register.
--   - `rightMarginal`: Partial trace over the first register.
--   - `marginalAB`: The AB marginal of the fixed tensor ordering A,(B,C).
--   - `marginalAC`: The AC marginal of the same tripartite operator.
--   - `reorderACB`: Reordering the same tripartite operator as (AC),B; no independent state is introduced.
--   - `cq`: PDF p.12: direct sum of weighted states with classical second register.
--   - `cqConditional`: PDF p.12: weighted conditional states, tensor-ordered as A,(B,Y).
--   - `blockTerm`: PDF p.12: evaluate a block before taking its logarithm; avoids 0 times infinity. For a>1 a positive numerator block with zero reference or support failure gives infinity. For a<1 a zero reference or orthogonal block contributes zero.
--   - `exponential`: PDF pp.9,22: exp((a-1)D), preserving infinity. At a=1 the raw trace extension is tr rho, hence one on density matrices, even at support mismatch.
--   - `NormalizedJointConvex`: PDF p.26, footnote 46: joint convexity on normalized pairs.
--   - `auxiliaryRenyi`: PDF p.15, Definition 5: auxiliary quantity with the printed composed-support guards.
--   - `columnProjector`: PDF p.17: rank-one projector for column k of an orthonormal eigenbasis U.
--   - `pinch`: PDF p.17: rank-one pinching, including choices within repeated eigenspaces.
--   - `concaveTensor`: PDF p.21, Lemma 16: tensor-power operator map on a pair of matrices.
--   - `perspectiveTensor`: PDF p.22, Lemma 17: only the inner sandwich is raised to a.
--   - `POVM`: PDF p.14: finite POVM on A, without a projectivity assumption.
--   - `opNorm`: PDF p.14: the induced Hilbert-space operator norm. The supremum set is nonempty (zero vector) and bounded (a finite-dimensional linear map).
--   - `measurementOverlap`: PDF p.14: the source's UNSQUARED maximum overlap. The set is finite; POVMs on the nonzero input space imply nonempty outcome sets.
--   - `measured`: PDF p.14: cq measurement output; the square-root sandwich gives the same partial-trace blocks as the source's formula Tr_A[M_x rho].
--   - `DivergenceFamily`: PDF pp.4–6: one divergence functional across all finite types and dimensions. It is real-valued on Domain; off-domain values are not used in the axioms.
--   - `directSum`: PDF p.5: direct sum in the disjoint-union basis.
--   - `SixAxioms`: PDF pp.4–5: the complete six axioms, with a single continuous strictly monotonic real generator. The mean equation is written after applying g; strict monotonicity makes this equivalent to the inverse-g equation on its image.
--   - `GeneralMeanConvexity`: PDF pp.5–6: convexity/concavity on normalized arguments in D's domain.
--   - `FamilyDPI`: PDF pp.5–6: CPTPM inequality across arbitrary finite input/output dimensions, on the real-valued domain of the axiomatic D.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, https://arxiv.org/abs/1306.3142v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

/-! arXiv:1306.3142v4. PDF page numbers, logarithms in bits.
Theorem 2 and Lemma 19 are deferred in HARD.md because their printed domains admit
counterexamples. Proposition 15 is corrected using its derivation on PDF p.20.
The accepted matrix, Schatten and probability-distribution definitions and Mathlib
Kronecker product are reused. Remaining local names distinguish this paper's concepts
from unrelated frozen names; no frozen definition is changed. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.
open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)
open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.3: real trace on Hermitian matrices. -/
def tr {I : Type} [Fintype I] (X : Mat I) : ℝ := X.trace.re

/-- PDF p.3: the set S excludes zero and permits subnormalization. -/
def Substate {I : Type} [Fintype I] (X : Mat I) : Prop :=
  X.PosSemidef ∧ 0 < tr X ∧ tr X ≤ 1

/-- PDF p.26, footnote 46: normalized positive operators. -/
def Density {I : Type} [Fintype I] (X : Mat I) : Prop :=
  X.PosSemidef ∧ tr X = 1

/-- PDF p.4: sigma dominates rho iff ker sigma is contained in ker rho. -/
def Dominates {I : Type} [Fintype I] [DecidableEq I] (sigma rho : Mat I) : Prop :=
  LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin

/-- PDF pp.4–5: the finite real-valued axiomatic domain. -/
def Domain {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : Prop :=
  rho.PosSemidef ∧ sigma.PosSemidef ∧ rho ≠ 0 ∧ Dominates sigma rho

/-- PDF pp.3,21: spectral powers, with generalized inverse for negative exponents.
The zero exponent is the identity even on the kernel. -/
def spectralPower {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) (t : ℝ) : Mat I :=
  if t = 0 then 1 else cfc (fun x : ℝ => if x = 0 then 0 else x ^ t) X

/-- PDF pp.3,18–20: natural operator logarithm, zero on the kernel. -/
def lnOp {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) : Mat I :=
  cfc Real.log X

/-- PDF p.3: base-two operator logarithm. -/
def logOp {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) : Mat I :=
  ((1 / Real.log 2 : ℝ) : ℂ) • lnOp X

/-- Scalar log with its extended zero limit, not Real.log's totalized value. -/
def elog (x : ℝ) : EReal := if 0 < x then (Real.logb 2 x : EReal) else ⊥

/-- Extended scalar logarithm also retaining a positive-infinite trace objective. -/
def elogNN (x : ℝ≥0∞) : EReal :=
  if x = ⊤ then ⊤ else if x = 0 then ⊥ else (Real.logb 2 x.toReal : EReal)

/-- PDF p.7, Definition 2: the unnormalized sandwiched trace. -/
def sandwich {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : Mat I :=
  spectralPower sigma ((1 - a) / (2 * a)) * rho * spectralPower sigma ((1 - a) / (2 * a))

/-- PDF p.7: trace before the scalar logarithm. -/
def rawTrace {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : ℝ := tr (spectralPower (sandwich a rho sigma) a)

/-- PDF p.7: Definition 2, including orthogonality and support failure.
Outside the source's positive orders other than one, no interpretation is asserted. -/
def divergence {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : EReal :=
  if rho * sigma ≠ 0 ∧ (Dominates sigma rho ∨ a < 1) then
    ((1 / (a - 1) : ℝ) : EReal) * elog (rawTrace a rho sigma / tr rho)
  else ⊤

/-- PDF p.6, Definition 1: trace-normalized relative entropy in bits. -/
def relative {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : EReal :=
  if Dominates sigma rho then (tr (rho * (logOp rho - logOp sigma)) / tr rho : ℝ)
  else ⊤

/-- PDF p.8, Definition 3: EReal infimum, so an empty feasible set yields +infinity. -/
def maxRelative {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : EReal :=
  sInf {v : EReal | ∃ l : ℝ, v = (l : EReal) ∧
    ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - rho).PosSemidef}

/-- PDF pp.4,10: Petz divergence, continuously extended at order one. -/
def petz {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : EReal :=
  if a = 1 then relative rho sigma
  else if rho * sigma ≠ 0 ∧ (Dominates sigma rho ∨ a < 1) then
    ((1 / (a - 1) : ℝ) : EReal) *
      elog (tr (spectralPower rho a * spectralPower sigma (1 - a)) / tr rho)
  else ⊤

/-- PDF pp.3–4: unconditional Renyi entropy, with the von Neumann value at one. -/
def renyiEntropy {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (rho : Mat I) : ℝ :=
  if a = 1 then -tr (rho * logOp rho) / tr rho
  else Real.logb 2 (tr (spectralPower rho a) / tr rho) / (1 - a)

/-- PDF p.10: identity on the support, embedded in the ambient space. -/
def supportId {I : Type} [Fintype I] [DecidableEq I] (rho : Mat I) : Mat I :=
  cfc (fun x : ℝ => if x = 0 then 0 else 1) rho

/-- PDF pp.10–12: support dimension, not ambient dimension. -/
def supportRank {I : Type} [Fintype I] [DecidableEq I] (rho : Mat I) : ℕ :=
  Module.finrank ℂ (LinearMap.range rho.mulVecLin)

/-- PDF p.10: maximally mixed state on supp rho. -/
def supportMixed {I : Type} [Fintype I] [DecidableEq I] (rho : Mat I) : Mat I :=
  (((supportRank rho : ℝ)⁻¹ : ℝ) : ℂ) • supportId rho

/-- PDF p.11, Definition 4: supremum over precisely S_B, including subnormalized states. -/
def conditionalRenyi {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (a : ℝ) (rho : Mat (A × B)) : EReal :=
  sSup {v : EReal | ∃ sigma : Mat B, Substate sigma ∧
    v = -divergence a rho (Matrix.kronecker (1 : Mat A) sigma)}

/-- Partial trace over the second register. -/
def leftMarginal {A B : Type} [Fintype B] (rho : Mat (A × B)) : Mat A :=
  fun i j => ∑ b, rho (i,b) (j,b)

/-- Partial trace over the first register. -/
def rightMarginal {A B : Type} [Fintype A] (rho : Mat (A × B)) : Mat B :=
  fun i j => ∑ a, rho (a,i) (a,j)

/-- The AB marginal of the fixed tensor ordering A,(B,C). -/
def marginalAB {A B C : Type} [Fintype C] (rho : Mat (A × (B × C))) : Mat (A × B) :=
  fun i j => ∑ c, rho (i.1,(i.2,c)) (j.1,(j.2,c))

/-- The AC marginal of the same tripartite operator. -/
def marginalAC {A B C : Type} [Fintype B] (rho : Mat (A × (B × C))) : Mat (A × C) :=
  fun i j => ∑ b, rho (i.1,(b,i.2)) (j.1,(b,j.2))

/-- Reordering the same tripartite operator as (AC),B; no independent state is introduced. -/
def reorderACB {A B C : Type} (rho : Mat (A × (B × C))) : Mat ((A × C) × B) :=
  fun i j => rho (i.1.1,(i.2,i.1.2)) (j.1.1,(j.2,j.1.2))

/-- PDF p.12: direct sum of weighted states with classical second register. -/
def cq {A Y : Type} [DecidableEq Y] (p : Y → ℝ) (rho : Y → Mat A) : Mat (A × Y) :=
  fun i j => if i.2 = j.2 then (p i.2 : ℂ) * rho i.2 i.1 j.1 else 0

/-- PDF p.12: weighted conditional states, tensor-ordered as A,(B,Y). -/
def cqConditional {A B Y : Type} [DecidableEq Y]
    (p : Y → ℝ) (rho : Y → Mat (A × B)) : Mat (A × (B × Y)) :=
  fun i j => if i.2.2 = j.2.2 then
    (p i.2.2 : ℂ) * rho i.2.2 (i.1,i.2.1) (j.1,j.2.1) else 0

/-- PDF p.12: evaluate a block before taking its logarithm; avoids 0 times infinity.
For a>1 a positive numerator block with zero reference or support failure gives infinity.
For a<1 a zero reference or orthogonal block contributes zero. -/
def blockTerm {A : Type} [Fintype A] [DecidableEq A]
    (a p q : ℝ) (rho sigma : Mat A) : ℝ≥0∞ :=
  if p = 0 then 0 else
  if 1 < a ∧ (q = 0 ∨ ¬ Dominates sigma rho) then ⊤
  else ENNReal.ofReal (p ^ a * q ^ (1 - a) * rawTrace a rho sigma)

/-- PDF pp.9,22: exp((a-1)D), preserving infinity. At a=1 the raw trace
extension is tr rho, hence one on density matrices, even at support mismatch. -/
def exponential {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : EReal :=
  if a = 1 then (tr rho : EReal)
  else if 1 < a ∧ ¬ Dominates sigma rho then ⊤
  else (rawTrace a rho sigma / tr rho : ℝ)

/-- PDF p.26, footnote 46: joint convexity on normalized pairs. -/
def NormalizedJointConvex {I : Type} [Fintype I] [DecidableEq I]
    (f : Mat I → Mat I → EReal) : Prop :=
  ∀ X1 X2 Y1 Y2, Density X1 → Density X2 → Density Y1 → Density Y2 →
  ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
    f ((l : ℂ) • X1 + ((1-l : ℝ) : ℂ) • X2)
      ((l : ℂ) • Y1 + ((1-l : ℝ) : ℂ) • Y2) ≤
    (l : EReal) * f X1 Y1 + ((1-l : ℝ) : EReal) * f X2 Y2

/-- PDF p.15, Definition 5: auxiliary quantity with the printed composed-support guards. -/
def auxiliaryRenyi {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma tau : Mat I) : EReal :=
  let R := spectralPower rho (1/2 : ℝ)
  if 1 < a ∧ ¬ Dominates sigma (R * spectralPower tau ((a-1)/a) * R) then ⊤
  else if a < 1 ∧ ¬ Dominates tau (R * spectralPower sigma ((1-a)/a) * R) then ⊥
  else ((a / (a-1) : ℝ) : EReal) *
    elog (tr (R * spectralPower sigma ((1-a)/a) * R * spectralPower tau ((a-1)/a)))

/-- PDF p.17: rank-one projector for column k of an orthonormal eigenbasis U. -/
def columnProjector {I : Type} (U : Mat I) (k : I) : Mat I :=
  fun i j => U i k * conj (U j k)

/-- PDF p.17: rank-one pinching, including choices within repeated eigenspaces. -/
def pinch {I : Type} [Fintype I] (U rho : Mat I) : Mat I :=
  ∑ k, columnProjector U k * rho * columnProjector U k

/-- PDF p.21, Lemma 16: tensor-power operator map on a pair of matrices. -/
def concaveTensor {I : Type} [Fintype I] [DecidableEq I]
    (b : ℝ) (L R : Mat I) : Mat (I × I) :=
  Matrix.kronecker (spectralPower L b) (spectralPower R.transpose (1-b))

/-- PDF p.22, Lemma 17: only the inner sandwich is raised to a. -/
def perspectiveTensor {I : Type} [Fintype I] [DecidableEq I]
    (a b : ℝ) (L R : Mat I) : Mat (I × I) :=
  Matrix.kronecker (spectralPower R (b/2) * spectralPower (spectralPower R (-b/2) * L * spectralPower R (-b/2)) a *
    spectralPower R (b/2)) (spectralPower R.transpose ((1-a)*(1-b)))

/-- PDF p.14: finite POVM on A, without a projectivity assumption. -/
def POVM {A X : Type} [Fintype X] [DecidableEq A] (M : X → Mat A) : Prop :=
  (∀ x, (M x).PosSemidef) ∧ ∑ x, M x = 1

/-- PDF p.14: the induced Hilbert-space operator norm. The supremum set is
nonempty (zero vector) and bounded (a finite-dimensional linear map). -/
def opNorm {A : Type} [Fintype A] [DecidableEq A] (X : Mat A) : ℝ :=
  sSup {r : ℝ | ∃ v : EuclideanSpace ℂ A, ‖v‖ ≤ 1 ∧ r = ‖Matrix.toEuclideanLin X v‖}

/-- PDF p.14: the source's UNSQUARED maximum overlap. The set is finite;
POVMs on the nonzero input space imply nonempty outcome sets. -/
def measurementOverlap {A X Y : Type} [Fintype A] [Fintype X] [Fintype Y] [DecidableEq A]
    (M : X → Mat A) (N : Y → Mat A) : ℝ :=
  sSup {r : ℝ | ∃ x y, r = opNorm (spectralPower (M x) (1/2 : ℝ) * spectralPower (N y) (1/2 : ℝ))}

/-- PDF p.14: cq measurement output; the square-root sandwich gives the same
partial-trace blocks as the source's formula Tr_A[M_x rho]. -/
def measured {A D X : Type} [Fintype A] [Fintype D] [DecidableEq A]
    [DecidableEq D] [DecidableEq X] (M : X → Mat A) (rho : Mat (A × D)) : Mat (X × D) :=
  fun i j => if i.1 = j.1 then
    let K := Matrix.kronecker (spectralPower (M i.1) (1/2 : ℝ)) (1 : Mat D)
    ∑ a, (K * rho * K) (a,i.2) (a,j.2)
  else 0

/-- PDF pp.4–6: one divergence functional across all finite types and dimensions.
It is real-valued on Domain; off-domain values are not used in the axioms. -/
abbrev DivergenceFamily := ∀ (I : Type) [Fintype I] [DecidableEq I], Mat I → Mat I → ℝ

/-- PDF p.5: direct sum in the disjoint-union basis. -/
def directSum {I J : Type} (X : Mat I) (Y : Mat J) : Mat (I ⊕ J) :=
  fun i j => match i,j with
    | .inl i, .inl j => X i j
    | .inr i, .inr j => Y i j
    | _, _ => 0

/-- PDF pp.4–5: the complete six axioms, with a single continuous strictly
monotonic real generator. The mean equation is written after applying g; strict
monotonicity makes this equivalent to the inverse-g equation on its image. -/
def SixAxioms (D : DivergenceFamily) (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ (StrictMono g ∨ StrictAnti g) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I],
    ContinuousOn (fun p : Mat I × Mat I => D I p.1 p.2)
      {p | Domain p.1 p.2}) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ rho sigma : Mat I, ∀ U : Matrix J I ℂ,
    Domain rho sigma → Uᴴ * U = 1 → U * Uᴴ = 1 →
    D I rho sigma = D J (U * rho * Uᴴ) (U * sigma * Uᴴ)) ∧
  D (Fin 1) 1 ((1/2 : ℂ) • (1 : Mat (Fin 1))) = Real.logb 2 2 ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I], ∀ rho sigma : Mat I,
    Domain rho sigma →
      ((rho - sigma).PosSemidef → 0 ≤ D I rho sigma) ∧
      ((sigma - rho).PosSemidef → D I rho sigma ≤ 0)) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ rho sigma : Mat I, ∀ tau omega : Mat J,
    Domain rho sigma → Domain tau omega →
    D (I × J) (Matrix.kronecker rho tau) (Matrix.kronecker sigma omega) = D I rho sigma + D J tau omega) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ rho sigma : Mat I, ∀ tau omega : Mat J,
    Domain rho sigma → Domain tau omega → tr rho + tr tau ≤ 1 →
    tr sigma + tr omega ≤ 1 →
    g (D (I ⊕ J) (directSum rho tau) (directSum sigma omega)) =
      tr rho / (tr rho + tr tau) * g (D I rho sigma) +
      tr tau / (tr rho + tr tau) * g (D J tau omega))

/-- PDF pp.5–6: convexity/concavity on normalized arguments in D's domain. -/
def GeneralMeanConvexity (D : DivergenceFamily) (g : ℝ → ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], ∀ rho sigma tau omega : Mat I,
    Domain rho sigma → Domain tau omega →
    Density rho → Density sigma → Density tau → Density omega →
    ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
    let lhs := g (D I ((l : ℂ) • rho + ((1-l : ℝ) : ℂ) • tau)
      ((l : ℂ) • sigma + ((1-l : ℝ) : ℂ) • omega))
    let rhs := l * g (D I rho sigma) + (1-l) * g (D I tau omega)
    (StrictMono g → lhs ≤ rhs) ∧ (StrictAnti g → rhs ≤ lhs)

/-- PDF pp.5–6: CPTPM inequality across arbitrary finite input/output dimensions,
on the real-valued domain of the axiomatic D. -/
def FamilyDPI (D : DivergenceFamily) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ E : Superop I J, IsChannel E → ∀ rho sigma : Mat I, Domain rho sigma →
      D J (E rho) (E sigma) ≤ D I rho sigma

/-! Sanity examples for every local definition. These are definition checks, not
proofs of any paper result. They pin scalar, kernel, block, and reindexing conventions. -/

example : Mat (Fin 1) = Matrix (Fin 1) (Fin 1) ℂ := rfl

example : tr (0 : Mat (Fin 1)) = 0 := by simp [tr]

example : ¬ Substate (0 : Mat (Fin 1)) := by simp [Substate, tr]

example : ¬ Density (0 : Mat (Fin 1)) := by simp [Density, tr]

example {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) : Dominates X X := le_rfl

example {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) (h : Domain X X) : X ≠ 0 := h.2.2.1

example {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) : spectralPower X 0 = 1 := by simp [spectralPower]

example {I : Type} [Fintype I] [DecidableEq I] : lnOp (0 : Mat I) = 0 := by simp [lnOp, cfc_zero]

example {I : Type} [Fintype I] [DecidableEq I] : logOp (0 : Mat I) = 0 := by simp [logOp, lnOp, cfc_zero]

example : elog 0 = ⊥ := by simp [elog]

example : elogNN 0 = ⊥ ∧ elogNN ⊤ = ⊤ := by simp [elogNN]

example {I : Type} [Fintype I] [DecidableEq I] (X Y : Mat I) : sandwich 1 X Y = X := by
  simp [sandwich, spectralPower]

example {I : Type} [Fintype I] [DecidableEq I] (X Y : Mat I) :
    rawTrace 1 X Y = tr (spectralPower (sandwich 1 X Y) 1) := rfl

example {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (X : Mat I) : divergence a X 0 = ⊤ := by
  simp [divergence]

example {I : Type} [Fintype I] [DecidableEq I] (X Y : Mat I) (h : ¬ Dominates Y X) :
    relative X Y = ⊤ := by simp [relative, h]

example {I : Type} [Fintype I] [DecidableEq I] (X Y : Mat I)
    (h : ∀ l : ℝ, ¬ ((((2 : ℝ) ^ l : ℝ) : ℂ) • Y - X).PosSemidef) :
    maxRelative X Y = ⊤ := by
  have hempty : {v : EReal | ∃ l : ℝ, v = (l : EReal) ∧
      ((((2 : ℝ) ^ l : ℝ) : ℂ) • Y - X).PosSemidef} = ∅ := by
    ext v
    constructor
    · intro hv
      obtain ⟨l, _, hpos⟩ := hv
      exact (h l hpos).elim
    · intro hv
      exact hv.elim
  rw [maxRelative, hempty, sInf_empty]

example {I : Type} [Fintype I] [DecidableEq I] (X Y : Mat I) : petz 1 X Y = relative X Y := by
  simp [petz]

example {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) :
    renyiEntropy 1 X = -tr (X * logOp X) / tr X := by simp [renyiEntropy]

example {I : Type} [Fintype I] [DecidableEq I] : supportId (0 : Mat I) = 0 := by
  simp [supportId, cfc_zero]

example {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) :
    supportRank X = Module.finrank ℂ (LinearMap.range X.mulVecLin) := rfl

example {I : Type} [Fintype I] [DecidableEq I] : supportMixed (0 : Mat I) = 0 := by
  simp [supportMixed, supportId, cfc_zero]

example {I J : Type} (X : Mat I) (Y : Mat J) (i j : I) (k l : J) :
    Matrix.kronecker X Y (i,k) (j,l) = X i j * Y k l := rfl

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (a : ℝ) (rho : Mat (A × B)) : conditionalRenyi a rho =
    sSup {v : EReal | ∃ sigma : Mat B, Substate sigma ∧
      v = -divergence a rho (Matrix.kronecker (1 : Mat A) sigma)} := rfl

example {A : Type} (rho : Mat (A × Fin 1)) (i j : A) :
    leftMarginal rho i j = rho (i,0) (j,0) := by simp [leftMarginal]

example {B : Type} (rho : Mat (Fin 1 × B)) (i j : B) :
    rightMarginal rho i j = rho (0,i) (0,j) := by simp [rightMarginal]

example {A B : Type} (rho : Mat (A × (B × Fin 1))) (i j : A × B) :
    marginalAB rho i j = rho (i.1,(i.2,0)) (j.1,(j.2,0)) := by simp [marginalAB]

example {A C : Type} (rho : Mat (A × (Fin 1 × C))) (i j : A × C) :
    marginalAC rho i j = rho (i.1,(0,i.2)) (j.1,(0,j.2)) := by simp [marginalAC]

example {A B C : Type} (rho : Mat (A × (B × C))) (a a2 : A) (b b2 : B) (c c2 : C) :
    reorderACB rho ((a,c),b) ((a2,c2),b2) = rho (a,(b,c)) (a2,(b2,c2)) := rfl

example : Distribution (Fin 1) := ⟨fun _ => (1 : ℝ), by simp⟩

example {A Y : Type} [DecidableEq Y] (rho : Y → Mat A) : cq (fun _ => 0) rho = 0 := by
  ext i j
  simp [cq]

example {A B Y : Type} [DecidableEq Y] (rho : Y → Mat (A × B)) :
    cqConditional (fun _ => 0) rho = 0 := by
  ext i j
  simp [cqConditional]

example {A : Type} [Fintype A] [DecidableEq A] (a q : ℝ) (X Y : Mat A) :
    blockTerm a 0 q X Y = 0 := by simp [blockTerm]

example {I : Type} [Fintype I] [DecidableEq I] (X Y : Mat I) : exponential 1 X Y = (tr X : EReal) := by
  simp [exponential]

example {I : Type} [Fintype I] [DecidableEq I] :
    NormalizedJointConvex (I := I) (fun _ _ => (0 : EReal)) := by simp [NormalizedJointConvex]

-- The accepted Schatten expression is the eigenvalue power sum. For PSD X and
-- p>0 this is (Tr X^p)^(1/p), including zero eigenvalues and an empty index type.
example {I : Type} [Fintype I] [DecidableEq I] (p : ℝ) (X : Mat I) :
    schatten p X = (∑ j, (QAlgorithms.Papers.Independent.Information100.P63.eigen X j) ^ p) ^ (1 / p) := rfl

example {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (rho sigma tau : Mat I)
    (h : 1 < a ∧ ¬ Dominates sigma (spectralPower rho (1/2 : ℝ) * spectralPower tau ((a-1)/a) * spectralPower rho (1/2 : ℝ))) :
    auxiliaryRenyi a rho sigma tau = ⊤ := by
  dsimp only [auxiliaryRenyi]
  exact if_pos h

example {I : Type} (U : Mat I) (k i j : I) :
    columnProjector U k i j = U i k * conj (U j k) := rfl

example {I : Type} [Fintype I] (U : Mat I) : pinch U 0 = 0 := by simp [pinch]

example {I : Type} [Fintype I] [DecidableEq I] (L R : Mat I) :
    concaveTensor 0 L R = Matrix.kronecker (1 : Mat I) (spectralPower R.transpose 1) := by
  simp [concaveTensor, spectralPower]

example {I : Type} [Fintype I] [DecidableEq I] (L R : Mat I) :
    perspectiveTensor 1 0 L R = Matrix.kronecker (spectralPower L 1) (1 : Mat I) := by
  simp [perspectiveTensor, spectralPower]

example {A X : Type} [Fintype X] [DecidableEq A] (M : X → Mat A) (h : POVM M) :
    ∑ x, M x = 1 := h.2

example {A : Type} [Fintype A] [DecidableEq A] (M : Mat A) :
    opNorm M = sSup {r : ℝ | ∃ v : EuclideanSpace ℂ A, ‖v‖ ≤ 1 ∧ r = ‖Matrix.toEuclideanLin M v‖} := rfl

example {A X Y : Type} [Fintype A] [Fintype X] [Fintype Y] [DecidableEq A] (M : X → Mat A) (N : Y → Mat A) :
    measurementOverlap M N = sSup {r : ℝ | ∃ x y, r = opNorm (spectralPower (M x) (1/2 : ℝ) * spectralPower (N y) (1/2 : ℝ))} := rfl

example {A D X : Type} [Fintype A] [Fintype D] [DecidableEq A] [DecidableEq D] [DecidableEq X]
    (M : X → Mat A) (rho : Mat (A × D)) (x y : X) (d e : D) (h : x ≠ y) :
    measured M rho (x,d) (y,e) = 0 := by simp [measured, h]

example : DivergenceFamily := fun _ _ _ _ _ => 0

example {I J : Type} (X : Mat I) (Y : Mat J) (i : I) (j : J) :
    directSum X Y (.inl i) (.inr j) = 0 := rfl

example (D : DivergenceFamily) (g : ℝ → ℝ) (h : SixAxioms D g) :
    D (Fin 1) 1 ((1/2 : ℂ) • (1 : Mat (Fin 1))) = Real.logb 2 2 := h.2.2.2.2.1

example : GeneralMeanConvexity (fun _ _ _ _ _ => 0) id := by
  simp [GeneralMeanConvexity]

example : FamilyDPI (fun _ _ _ _ _ => 0) := by
  intro I J _ _ _ _ E hE rho sigma h
  exact le_rfl

/-- Nonzero scalar-state sanity: S is inhabited and contains a normalized state. -/
example : Substate (1 : Mat (Fin 1)) := by
  refine ⟨Matrix.PosSemidef.one, ?_, ?_⟩ <;> norm_num [tr, Matrix.trace]

/-- Spectral powers preserve the scalar identity for every real exponent. -/
example {I : Type} [Fintype I] [DecidableEq I] (t : ℝ) : spectralPower (1 : Mat I) t = 1 := by
  simp [spectralPower, cfc_one]

/-- A normalized scalar compared with itself has zero divergence at every admissible order. -/
example (a : ℝ) : divergence a (1 : Mat (Fin 1)) 1 = 0 := by
  simp [divergence, Dominates, rawTrace, sandwich, spectralPower, cfc_one, tr, Matrix.trace, elog]

end QAlgorithms.Papers.Independent.Dependency50.P35


