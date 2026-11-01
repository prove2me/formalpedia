-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P05
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P05
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T03:55:40.914202+00:00
-- url     : https://prove2.me/theorems/9861cf16-db94-4b8a-9ae9-5748dbcf5e62
-- title:
--   Definitions for A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory
-- statement:
--   The objects the formalized statements of *A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory* (arXiv:quant-ph/0208139) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DensityOutputChannel`: PDF p.1, (1): a classical-input channel with normalized PSD output matrices.
--   - `channelAverage`: PDF p.2, (4): the average output operator, constructed from the channel and law.
--   - `outputEntropyNats`: PDF p.2, (4): entropy in nats; zero eigenvalues contribute 0 log 0 = 0.
--   - `channelInformationNats`: PDF p.2, (4): Holevo mutual information for the given input law, in nats.
--   - `DistinctWordCode`: PDF pp.1–2: a nonempty codebook of distinct words and a sub-POVM decoder. The remaining effect 1 - sum decoder is the failure outcome.
--   - `uniformMessageError`: PDF p.1, (2): error averaged over the uniformly distributed messages, computed on the original output states, without pinching.
--   - `pinchedWord`: PDF pp.3–5: pinching onto full distinct-eigenvalue eigenspaces of sigma^n.
--   - `pinchedLowerTail`: PDF pp.4–5, (16),(21): iid pinched lower tail. The complement of the STRICT positive projector includes the zero eigenspace; BOTH rho occurrences in the trace/projection are pinched.
--   - `goodMass`: PDF p.4, (17): one-shot mass of the strictly positive pinched likelihood test.
--   - `matrixOfHS`: PDF p.8, (42): reshaping Hilbert–Schmidt coordinates into a matrix. The Euclidean inner product on these coordinates is Tr(A* B).
--   - `commutantHS`: PDF pp.7–8, (40)–(41): commutant of the generated unital *-algebra. For an arbitrary C it requires commuting with C AND C*, not just C. Reshaping equips this subspace with the Hilbert–Schmidt inner product.
--   - `algebraPinch`: PDF p.8, (41): Hilbert–Schmidt orthogonal projection onto the commutant. This supplies the literal arbitrary-reference domain of Lemma 3. For Hermitian references it is the spectral pinching (43), preserving degenerate eigenspaces.
-- source:
--   A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory, arXiv:quant-ph/0208139v1, https://arxiv.org/abs/quant-ph/0208139v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

/-! Ogawa–Nagaoka, arXiv:quant-ph/0208139v1. Natural logarithms.
Only accepted frozen modules are imported. Paper-local operational definitions
adapt the accepted finite laws, averages and ordered iid products to (1)–(4),
(16)–(21), and the general projection (41). Distinct local names preserve the
cq word-code model and natural-log information rather than unrelated frozen
objects sharing old short names; see ASSESSMENT.json.
Lemma 4 is deferred because its negative powers are unpinned for singular states.
Compilation is pending the batch mechanical handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P05

open scoped Matrix ComplexConjugate ComplexOrder BigOperators
open Filter Topology QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr pinch typeI accept)
open QAlgorithms.Papers.Independent.Claimed50.P45 (pinchedTest)
open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)
open QAlgorithms.Papers.Independent.Information100.P27 (average)
open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)
open QAlgorithms.Papers.Independent.Dependency50.P35 (directSum)
open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X I : Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

/-- PDF p.1, (1): a classical-input channel with normalized PSD output matrices. -/
structure DensityOutputChannel (X I : Type) [Fintype I] where
  state : X → Mat I
  normalized : ∀ x, IsDensityMatrix (state x)

/-- PDF p.2, (4): the average output operator, constructed from the channel and law. -/
def channelAverage (W : DensityOutputChannel X I) (p : Distribution X) : Mat I :=
  average p.val W.state

/-- PDF p.2, (4): entropy in nats; zero eigenvalues contribute 0 log 0 = 0. -/
def outputEntropyNats (rho : Mat I) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.log x) rho).trace.re

/-- PDF p.2, (4): Holevo mutual information for the given input law, in nats. -/
def channelInformationNats (W : DensityOutputChannel X I) (p : Distribution X) : ℝ :=
  outputEntropyNats (channelAverage W p) - ∑ x, p.val x * outputEntropyNats (W.state x)

/-- PDF pp.1–2: a nonempty codebook of distinct words and a sub-POVM decoder.
The remaining effect 1 - sum decoder is the failure outcome. -/
structure DistinctWordCode (A J : Type) [Fintype J] [DecidableEq J] where
  size : ℕ
  positive_size : 0 < size
  word : Fin size → A
  distinct : Function.Injective word
  decoder : Fin size → Mat J
  positive_decoder : ∀ k, (decoder k).PosSemidef
  failure_positive : (1 - ∑ k, decoder k).PosSemidef

/-- PDF p.1, (2): error averaged over the uniformly distributed messages,
computed on the original output states, without pinching. -/
def uniformMessageError {A J : Type} [Fintype J] [DecidableEq J]
    (rho : A → Mat J) (C : DistinctWordCode A J) : ℝ :=
  (C.size : ℝ)⁻¹ * ∑ k, (1 - tr (rho (C.word k) * C.decoder k))

/-- PDF pp.3–5: pinching onto full distinct-eigenvalue eigenspaces of sigma^n. -/
def pinchedWord (W : DensityOutputChannel X I) (p : Distribution X) (n : ℕ)
    (u : Fin n → X) : Mat (Fin n → I) :=
  pinch (copies n (channelAverage W p)) (wordOutput W.state u)

/-- PDF pp.4–5, (16),(21): iid pinched lower tail. The complement of the
STRICT positive projector includes the zero eigenspace; BOTH rho occurrences
in the trace/projection are pinched. -/
def pinchedLowerTail (W : DensityOutputChannel X I) (p : Distribution X) (n : ℕ) (a : ℝ) : ℝ :=
  ∑ u : Fin n → X, wordProb p.val n u *
    tr (pinchedWord W p n u *
      (1 - positiveProjection (pinchedWord W p n u -
        (Real.exp ((n : ℝ) * a) : ℂ) • copies n (channelAverage W p))))

/-- PDF p.4, (17): one-shot mass of the strictly positive pinched likelihood test. -/
def goodMass (W : DensityOutputChannel X I) (p : Distribution X) (c : ℝ) : ℝ :=
  ∑ x, p.val x *
    tr (pinch (channelAverage W p) (W.state x) *
      positiveProjection (pinch (channelAverage W p) (W.state x) -
        (c : ℂ) • channelAverage W p))

/-- PDF p.8, (42): reshaping Hilbert–Schmidt coordinates into a matrix.
The Euclidean inner product on these coordinates is Tr(A* B). -/
def matrixOfHS : EuclideanSpace ℂ (I × I) →ₗ[ℂ] Mat I where
  toFun v := Matrix.of fun i j => v (i, j)
  map_add' v w := by ext i j; rfl
  map_smul' c v := by ext i j; rfl

/-- PDF pp.7–8, (40)–(41): commutant of the generated unital *-algebra.
For an arbitrary C it requires commuting with C AND C*, not just C.
Reshaping equips this subspace with the Hilbert–Schmidt inner product. -/
def commutantHS (C : Mat I) : Submodule ℂ (EuclideanSpace ℂ (I × I)) :=
  (Subalgebra.centralizer ℂ ({C, Cᴴ} : Set (Mat I))).toSubmodule.comap matrixOfHS

/-- PDF p.8, (41): Hilbert–Schmidt orthogonal projection onto the commutant.
This supplies the literal arbitrary-reference domain of Lemma 3. For Hermitian
references it is the spectral pinching (43), preserving degenerate eigenspaces. -/
def algebraPinch (C A : Mat I) : Mat I :=
  matrixOfHS ((commutantHS C).starProjection
    (WithLp.toLp 2 (fun ij : I × I => A ij.1 ij.2)))

/-- Sanity: every law, including laws with zero weights, has total mass one. -/
example (p : Distribution X) : ∑ x, p.val x = 1 := p.property.2

/-- Sanity: the channel carries normalization rather than an unnormalized state. -/
example (W : DensityOutputChannel X I) (x : X) : (W.state x).trace = 1 :=
  (W.normalized x).2

/-- Sanity: the empty product is 1, but all rates below use positive lengths. -/
example (p : Distribution X) (u : Fin 0 → X) : wordProb p.val 0 u = 1 := by
  simp [wordProb]

/-- Sanity: at a fixed one-use word the output is exactly its single factor. -/
example (W : DensityOutputChannel X I) (u : Fin 1 → X) (i j : Fin 1 → I) :
    wordOutput W.state u i j = W.state (u 0) (i 0) (j 0) := by
  simp [wordOutput]

/-- Sanity: the zero density candidate has zero entropy in the total definition. -/
example : outputEntropyNats (0 : Mat I) = 0 := by
  simp [outputEntropyNats, cfc_zero]

/-- Sanity: the general pinching maps the zero operator to zero for EVERY reference. -/
example (C : Mat I) : algebraPinch C 0 = 0 := by
  change matrixOfHS ((commutantHS C).starProjection
    (0 : EuclideanSpace ℂ (I × I))) = 0
  rw [map_zero, map_zero]

/-- Sanity: a direct sum has zero off-diagonal blocks. -/
example (A B : Mat I) (i j : I) : directSum A B (Sum.inl i) (Sum.inr j) = 0 := by
  rfl

end QAlgorithms.Papers.Independent.Intakethird100.P05


