-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P61
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:04:07.369991+00:00
-- url     : https://prove2.me/theorems/12a403fc-9305-486c-8699-400a6cb6536f
-- title:
--   Definitions for On the communication cost of entanglement transformations
-- statement:
--   The objects the formalized statements of *On the communication cost of entanglement transformations* (arXiv:quant-ph/0204092) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteMin`: PDF p.3: finite minimum; the empty-set default is unused on valid smoothing inputs.
--   - `finiteMax`: PDF pp.2--3: finite maximum; empty support has value zero.
--   - `spectralSupport`: PDF p.2: support of the positive spectrum, counted with multiplicity.
--   - `largestWeight`: PDF p.2: largest eigenvalue of a positive matrix.
--   - `entropyZero`: PDF p.2: S_0, also for subnormalized positive matrices.
--   - `entropyOne`: PDF p.2: von Neumann entropy in bits; zero weights contribute zero.
--   - `spread`: PDF p.2, (1): spectral spread; no trace renormalization.
--   - `Flat`: PDF p.2: flatness only on positive support, including rank one.
--   - `spectralRetentions`: PDF p.3, (6)--(8): retained spectral subsets with mass at least 1-epsilon. Zero eigenvalues may be removed without changing any of these minima.
--   - `smoothZero`: PDF p.3, (6): smoothed support entropy.
--   - `smoothInfinity`: PDF p.3, (7): smoothed largest-weight entropy.
--   - `smoothSpread`: PDF p.3, (8): joint minimum, rather than a difference of separate minima.
--   - `RenyiOrder`: PDF pp.2,5: nonnegative Renyi orders with a separate infinity endpoint.
--   - `spectralRenyi`: PDF p.2: entropy of a retained positive spectrum. Orders 0,1,infinity are handled separately; zero weights are excluded before exponentiation. The order-one branch is used only on the full normalized spectrum; no continuous order-one extension is claimed for a retained subnormalized spectrum.
--   - `upperRenyiFactor`: PDF p.5, Remark 12: beta/(beta-1) has limiting value one at infinity.
--   - `eigenvalueRenyiEntropy`: PDF p.2: Renyi entropy with the source's endpoint conventions.
--   - `renyiGap`: PDF p.3, Remark 2: Renyi gap.
--   - `smoothRenyiGap`: PDF p.5, Remark 12: joint smoothing of the Renyi gap.
--   - `BipartiteMatrix`: PDF p.2: concrete finite bipartite matrices.
--   - `aliceApply`: PDF p.2: Alice's Kraus operation tensored with Bob's identity, retaining off-diagonal blocks.
--   - `bobApply`: PDF p.2: Bob's local Kraus operation tensored with Alice's identity.
--   - `transferAB`: PDF p.2: an m-dimensional subsystem moves from Alice to Bob by reassociation.
--   - `transferBA`: PDF p.2: an m-dimensional subsystem moves from Bob to Alice.
--   - `QuantumExecution`: PDF p.2 and Fig.1: finite deterministic executions. Local CPTP operations include arbitrary pure ancillary preparation and disposal. Transfers have positive integer dimensions and their costs are summed. No postselection or unconstrained joint-channel constructor is present.
--   - `ClassicalExecution`: PDF p.5, Corollary 10: finite adaptive LOCC trees. Each communicated instrument outcome is available to both parties. Branch states are unnormalized and all final branches are summed. C bounds worst-case total log-alphabet cost; this includes every fixed-length binary-message protocol in the source.
--   - `pack`: PDF pp.1--2: separate local basis identifications with finite index sets.
--   - `Quantum`: PDF p.2: operational quantum communication relation.
--   - `Classical`: PDF p.5: operational classical communication relation.
--   - `aliceDensity`: PDF pp.1--2: Alice's reduced density; the second tensor factor is traced out.
--   - `QuantumPrepares`: PDF p.5: fidelity is tested on the unconditional, possibly mixed, output.
--   - `ClassicalPrepares`: PDF p.5: classical-only preparation, summing every branch.
--   - `tensorPureStates`: PDF p.5: bipartite tensor with all Alice factors before all Bob factors.
--   - `pureStateCopies`: PDF pp.6--7: n copies with bipartite ownership spectralRetentions; the empty product is one.
--   - `bellRank`: PDF pp.1--2: normalized maximally entangled rank-r state when r>0.
--   - `eprPairs`: PDF p.5: k EPR pairs, including k=0.
--   - `smoothingError`: PDF p.5: the eighth root of 4 epsilon.
--   - `binaryState`: PDF p.3: binary Schmidt-diagonal state, with complex amplitudes.
--   - `harmonicSum`: PDF p.7: the ordinary harmonic sum, with indices starting at one.
--   - `harmonicState`: PDF p.7: normalized harmonic embezzling vector for n>0. At n=0 its Hilbert space is empty, and no normalized-state assertion is used.
--   - `harmonicTailCuts`: PDF p.8, (21): feasible integer tail cutoffs, restricted to 1<=k<=n.
--   - `harmonicHeadCuts`: PDF p.8, (22): feasible integer head cutoffs; the upper limit is k-1, inclusive.
--   - `applyLocalMaps`: PDF p.6, (20): action of separate local linear maps on a bipartite vector. Isometricity is required explicitly in the residual-family theorem.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, https://arxiv.org/abs/quant-ph/0204092v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

/-! Hayden--Winter, quant-ph/0204092v3. Page citations are PDF pages.
Exact matching primitives are imported from the pinned accepted library.
All new definitions are local to this paper. Subnormalized spectral truncations
are never renormalized. Protocol costs count physical message dimensions. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)
open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)
open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)
open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.3: finite minimum; the empty-set default is unused on valid smoothing inputs. -/
def finiteMin {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h f else 0

/-- PDF pp.2--3: finite maximum; empty support has value zero. -/
def finiteMax {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℝ) : ℝ :=
  if h : s.Nonempty then s.sup' h f else 0

section Spectral

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.2: support of the positive spectrum, counted with multiplicity. -/
def spectralSupport (rho : Matrix I I ℂ) : Finset (Fin (Fintype.card I)) :=
  Finset.univ.filter fun i => 0 < ascEigenvalues rho i

/-- PDF p.2: largest eigenvalue of a positive matrix. -/
def largestWeight (rho : Matrix I I ℂ) : ℝ :=
  finiteMax (spectralSupport rho) (ascEigenvalues rho)

/-- PDF p.2: S_0, also for subnormalized positive matrices. -/
def entropyZero (rho : Matrix I I ℂ) : ℝ := logTwo (supportRank rho)

/-- PDF p.2: von Neumann entropy in bits; zero weights contribute zero. -/
def entropyOne (rho : Matrix I I ℂ) : ℝ :=
  -∑ i, ascEigenvalues rho i * logTwo (ascEigenvalues rho i)

/-- PDF p.2, (1): spectral spread; no trace renormalization. -/
def spread (rho : Matrix I I ℂ) : ℝ := entropyZero rho - entropyInfinity rho

/-- PDF p.2: flatness only on positive support, including rank one. -/
def Flat (rho : Matrix I I ℂ) : Prop :=
  ∀ i ∈ spectralSupport rho, ∀ j ∈ spectralSupport rho,
    ascEigenvalues rho i = ascEigenvalues rho j

/-- PDF p.3, (6)--(8): retained spectral subsets with mass at least 1-epsilon.
Zero eigenvalues may be removed without changing any of these minima. -/
def spectralRetentions (rho : Matrix I I ℂ) (epsilon : ℝ) : Finset (Finset (Fin (Fintype.card I))) :=
  (spectralSupport rho).powerset.filter fun s => 1 - epsilon ≤ ∑ i ∈ s, ascEigenvalues rho i

/-- PDF p.3, (6): smoothed support entropy. -/
def smoothZero (rho : Matrix I I ℂ) (epsilon : ℝ) : ℝ :=
  logTwo (finiteMin (spectralRetentions rho epsilon) fun s => (s.card : ℝ))

/-- PDF p.3, (7): smoothed largest-weight entropy. -/
def smoothInfinity (rho : Matrix I I ℂ) (epsilon : ℝ) : ℝ :=
  -logTwo (finiteMin (spectralRetentions rho epsilon) fun s => finiteMax s (ascEigenvalues rho))

/-- PDF p.3, (8): joint minimum, rather than a difference of separate minima. -/
def smoothSpread (rho : Matrix I I ℂ) (epsilon : ℝ) : ℝ :=
  logTwo (finiteMin (spectralRetentions rho epsilon) fun s =>
    (s.card : ℝ) * finiteMax s (ascEigenvalues rho))

end Spectral

/-- PDF pp.2,5: nonnegative Renyi orders with a separate infinity endpoint. -/
abbrev RenyiOrder := WithTop NNReal

/-- PDF p.2: entropy of a retained positive spectrum. Orders 0,1,infinity are
handled separately; zero weights are excluded before exponentiation. The order-one
branch is used only on the full normalized spectrum; no continuous order-one
extension is claimed for a retained subnormalized spectrum. -/
def spectralRenyi {n : ℕ} (r : Fin n → ℝ) (s : Finset (Fin n)) (alpha : RenyiOrder) : ℝ :=
  if alpha = ⊤ then -logTwo (finiteMax s r)
  else let a : ℝ := (alpha.untopD 0 : NNReal)
       if a = 0 then logTwo s.card
       else if a = 1 then -∑ i ∈ s, r i * logTwo (r i)
       else logTwo (∑ i ∈ s, (r i) ^ a) / (1 - a)

/-- PDF p.5, Remark 12: beta/(beta-1) has limiting value one at infinity. -/
def upperRenyiFactor (beta : RenyiOrder) : ℝ :=
  if beta = ⊤ then 1 else
    let b : ℝ := (beta.untopD 0 : NNReal)
    b / (b - 1)

section SpectralResults

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.2: Renyi entropy with the source's endpoint conventions. -/
def eigenvalueRenyiEntropy (rho : Matrix I I ℂ) (alpha : RenyiOrder) : ℝ :=
  spectralRenyi (ascEigenvalues rho) (spectralSupport rho) alpha

/-- PDF p.3, Remark 2: Renyi gap. -/
def renyiGap (rho : Matrix I I ℂ) (alpha beta : RenyiOrder) : ℝ :=
  eigenvalueRenyiEntropy rho alpha - eigenvalueRenyiEntropy rho beta

/-- PDF p.5, Remark 12: joint smoothing of the Renyi gap. -/
def smoothRenyiGap (rho : Matrix I I ℂ) (alpha beta : RenyiOrder) (epsilon : ℝ) : ℝ :=
  finiteMin (spectralRetentions rho epsilon) fun s =>
    spectralRenyi (ascEigenvalues rho) s alpha - spectralRenyi (ascEigenvalues rho) s beta

end SpectralResults

/-- PDF p.2: concrete finite bipartite matrices. -/
abbrev BipartiteMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

/-- PDF p.2: Alice's Kraus operation tensored with Bob's identity, retaining off-diagonal blocks. -/
def aliceApply {a b c k : ℕ} (K : Fin k → Matrix (Fin c) (Fin a) ℂ)
    (rho : BipartiteMatrix a b) : BipartiteMatrix c b :=
  krausApply (fun j => Matrix.kronecker (K j) (1 : Matrix (Fin b) (Fin b) ℂ)) rho

/-- PDF p.2: Bob's local Kraus operation tensored with Alice's identity. -/
def bobApply {a b d k : ℕ} (K : Fin k → Matrix (Fin d) (Fin b) ℂ)
    (rho : BipartiteMatrix a b) : BipartiteMatrix a d :=
  krausApply (fun j => Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) (K j)) rho

/-- PDF p.2: an m-dimensional subsystem moves from Alice to Bob by reassociation. -/
def transferAB {a b m : ℕ} (rho : BipartiteMatrix (a * m) b) : BipartiteMatrix a (m * b) :=
  fun p q => rho
    (finProdFinEquiv (p.1, (finProdFinEquiv.symm p.2).1), (finProdFinEquiv.symm p.2).2)
    (finProdFinEquiv (q.1, (finProdFinEquiv.symm q.2).1), (finProdFinEquiv.symm q.2).2)

/-- PDF p.2: an m-dimensional subsystem moves from Bob to Alice. -/
def transferBA {a b m : ℕ} (rho : BipartiteMatrix a (m * b)) : BipartiteMatrix (a * m) b :=
  fun p q => rho
    ((finProdFinEquiv.symm p.1).1, finProdFinEquiv ((finProdFinEquiv.symm p.1).2, p.2))
    ((finProdFinEquiv.symm q.1).1, finProdFinEquiv ((finProdFinEquiv.symm q.1).2, q.2))

/-- PDF p.2 and Fig.1: finite deterministic executions. Local CPTP operations
include arbitrary pure ancillary preparation and disposal. Transfers have positive
integer dimensions and their costs are summed. No postselection or unconstrained
joint-channel constructor is present. -/
inductive QuantumExecution : {a b c d : ℕ} → BipartiteMatrix a b → BipartiteMatrix c d → ℝ → Prop
  | identity {a b} (rho : BipartiteMatrix a b) : QuantumExecution rho rho 0
  | alice {a b c k} (rho : BipartiteMatrix a b) (K : Fin k → Matrix (Fin c) (Fin a) ℂ)
      (hK : IsKrausFamily K) : QuantumExecution rho (aliceApply K rho) 0
  | bob {a b d k} (rho : BipartiteMatrix a b) (K : Fin k → Matrix (Fin d) (Fin b) ℂ)
      (hK : IsKrausFamily K) : QuantumExecution rho (bobApply K rho) 0
  | sendAB {a b m} (rho : BipartiteMatrix (a * m) b) (hm : 0 < m) :
      QuantumExecution rho (transferAB rho) (logTwo m)
  | sendBA {a b m} (rho : BipartiteMatrix a (m * b)) (hm : 0 < m) :
      QuantumExecution rho (transferBA rho) (logTwo m)
  | compose {a b c d e f} {rho : BipartiteMatrix a b} {sigma : BipartiteMatrix c d}
      {tau : BipartiteMatrix e f} {C D : ℝ} :
      QuantumExecution rho sigma C → QuantumExecution sigma tau D → QuantumExecution rho tau (C + D)

/-- PDF p.5, Corollary 10: finite adaptive LOCC trees. Each communicated
instrument outcome is available to both parties. Branch states are unnormalized
and all final branches are summed. C bounds worst-case total log-alphabet cost;
this includes every fixed-length binary-message protocol in the source. -/
inductive ClassicalExecution : {a b c d : ℕ} → BipartiteMatrix a b → BipartiteMatrix c d → ℝ → Prop
  | identity {a b} (rho : BipartiteMatrix a b) : ClassicalExecution rho rho 0
  | alice {a b c k} (rho : BipartiteMatrix a b) (K : Fin k → Matrix (Fin c) (Fin a) ℂ)
      (hK : IsKrausFamily K) : ClassicalExecution rho (aliceApply K rho) 0
  | bob {a b d k} (rho : BipartiteMatrix a b) (K : Fin k → Matrix (Fin d) (Fin b) ℂ)
      (hK : IsKrausFamily K) : ClassicalExecution rho (bobApply K rho) 0
  | aliceMessage {a b c d e k m} (rho : BipartiteMatrix a b)
      (K : Fin m → Fin k → Matrix (Fin c) (Fin a) ℂ) (hm : 0 < m)
      (hK : (∑ j, ∑ l, (K j l)ᴴ * K j l) = 1)
      (sigma : Fin m → BipartiteMatrix d e) (cost : Fin m → ℝ) (budget : ℝ)
      (hbudget : ∀ j, cost j ≤ budget)
      (next : ∀ j, ClassicalExecution (aliceApply (K j) rho) (sigma j) (cost j)) :
      ClassicalExecution rho (∑ j, sigma j) (logTwo m + budget)
  | bobMessage {a b c d e k m} (rho : BipartiteMatrix a b)
      (K : Fin m → Fin k → Matrix (Fin c) (Fin b) ℂ) (hm : 0 < m)
      (hK : (∑ j, ∑ l, (K j l)ᴴ * K j l) = 1)
      (sigma : Fin m → BipartiteMatrix d e) (cost : Fin m → ℝ) (budget : ℝ)
      (hbudget : ∀ j, cost j ≤ budget)
      (next : ∀ j, ClassicalExecution (bobApply (K j) rho) (sigma j) (cost j)) :
      ClassicalExecution rho (∑ j, sigma j) (logTwo m + budget)
  | compose {a b c d e f} {rho : BipartiteMatrix a b} {sigma : BipartiteMatrix c d}
      {tau : BipartiteMatrix e f} {C D : ℝ} :
      ClassicalExecution rho sigma C → ClassicalExecution sigma tau D → ClassicalExecution rho tau (C + D)

section Operational

variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- PDF pp.1--2: separate local basis identifications with finite index sets. -/
def pack (rho : Matrix (A × B) (A × B) ℂ) : BipartiteMatrix (Fintype.card A) (Fintype.card B) :=
  fun p q => rho ((Fintype.equivFin A).symm p.1, (Fintype.equivFin B).symm p.2)
    ((Fintype.equivFin A).symm q.1, (Fintype.equivFin B).symm q.2)

/-- PDF p.2: operational quantum communication relation. -/
def Quantum (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (C × D) (C × D) ℂ)
    (cost : ℝ) : Prop := QuantumExecution (pack rho) (pack sigma) cost

/-- PDF p.5: operational classical communication relation. -/
def Classical (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (C × D) (C × D) ℂ)
    (cost : ℝ) : Prop := ClassicalExecution (pack rho) (pack sigma) cost

/-- PDF pp.1--2: Alice's reduced density; the second tensor factor is traced out. -/
def aliceDensity (phi : EuclideanSpace ℂ (A × B)) : Matrix A A ℂ := traceRight (pureDensity phi)

/-- PDF p.5: fidelity is tested on the unconditional, possibly mixed, output. -/
def QuantumPrepares (phi : EuclideanSpace ℂ (A × B)) (psi : EuclideanSpace ℂ (C × D))
    (epsilon cost : ℝ) : Prop :=
  ∃ sigma : Matrix (C × D) (C × D) ℂ,
    Quantum (pureDensity phi) sigma cost ∧ fidelity sigma (pureDensity psi) ≥ 1 - epsilon

/-- PDF p.5: classical-only preparation, summing every branch. -/
def ClassicalPrepares (phi : EuclideanSpace ℂ (A × B)) (psi : EuclideanSpace ℂ (C × D))
    (epsilon cost : ℝ) : Prop :=
  ∃ sigma : Matrix (C × D) (C × D) ℂ,
    Classical (pureDensity phi) sigma cost ∧ fidelity sigma (pureDensity psi) ≥ 1 - epsilon

/-- PDF p.5: bipartite tensor with all Alice factors before all Bob factors. -/
def tensorPureStates (phi : EuclideanSpace ℂ (A × B)) (psi : EuclideanSpace ℂ (C × D)) :
    EuclideanSpace ℂ ((A × C) × (B × D)) :=
  WithLp.toLp 2 fun p => phi (p.1.1, p.2.1) * psi (p.1.2, p.2.2)

/-- PDF pp.6--7: n copies with bipartite ownership spectralRetentions; the empty product is one. -/
def pureStateCopies (psi : EuclideanSpace ℂ (A × B)) (n : ℕ) :
    EuclideanSpace ℂ ((Fin n → A) × (Fin n → B)) :=
  WithLp.toLp 2 fun p => ∏ j, psi (p.1 j, p.2 j)

/-- PDF pp.1--2: normalized maximally entangled rank-r state when r>0. -/
def bellRank (r : ℕ) : EuclideanSpace ℂ (Fin r × Fin r) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then ((Real.sqrt (r : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.5: k EPR pairs, including k=0. -/
def eprPairs (k : ℕ) : EuclideanSpace ℂ (Fin (2 ^ k) × Fin (2 ^ k)) := bellRank (2 ^ k)

/-- PDF p.5: the eighth root of 4 epsilon. -/
def smoothingError (epsilon : ℝ) : ℝ := (4 * epsilon) ^ (1 / 8 : ℝ)

end Operational

/-- PDF p.3: binary Schmidt-diagonal state, with complex amplitudes. -/
def binaryState (alpha beta : ℂ) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p => if p = (false,false) then alpha else if p = (true,true) then beta else 0

section Dilution

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end Dilution

/-- PDF p.7: the ordinary harmonic sum, with indices starting at one. -/
def harmonicSum (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n, (i : ℝ)⁻¹

/-- PDF p.7: normalized harmonic embezzling vector for n>0.
At n=0 its Hilbert space is empty, and no normalized-state assertion is used. -/
def harmonicState (n : ℕ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then
    (Real.sqrt (1 / (((p.1.val + 1 : ℕ) : ℝ) * harmonicSum n)) : ℂ) else 0

/-- PDF p.8, (21): feasible integer tail cutoffs, restricted to 1<=k<=n. -/
def harmonicTailCuts (n : ℕ) (delta : ℝ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k =>
    (∑ i ∈ Finset.Icc (k + 1) n, 1 / ((i : ℝ) * harmonicSum n)) ≤ delta

/-- PDF p.8, (22): feasible integer head cutoffs; the upper limit is k-1, inclusive. -/
def harmonicHeadCuts (n : ℕ) (delta : ℝ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k =>
    (∑ i ∈ Finset.Icc 1 (k - 1), 1 / ((i : ℝ) * harmonicSum n)) ≤ delta

/-- PDF p.6, (20): action of separate local linear maps on a bipartite vector.
Isometricity is required explicitly in the residual-family theorem. -/
def applyLocalMaps {A B C D : Type} [Fintype A] [Fintype B]
    (U : Matrix C A ℂ) (V : Matrix D B ℂ) (phi : EuclideanSpace ℂ (A × B)) :
    EuclideanSpace ℂ (C × D) :=
  WithLp.toLp 2 fun p => ∑ a, ∑ b, U p.1 a * V p.2 b * phi (a,b)

/-- Sanity examples for the paper-local substrate. These pin definitions rather
than prove the paper's theorem statements. -/

example : logTwo 1 = 0 := by simp [logTwo, Real.logb]

example {I : Type*} [DecidableEq I] (i : I) (f : I → ℝ) : finiteMin {i} f = f i := by
  simp [finiteMin]

example {I : Type*} [DecidableEq I] (i : I) (f : I → ℝ) : finiteMax {i} f = f i := by
  simp [finiteMax]

example {n : ℕ} (r : Fin n → ℝ) (s : Finset (Fin n)) :
    spectralRenyi r s (0 : RenyiOrder) = logTwo s.card := by simp [spectralRenyi]

example : upperRenyiFactor ⊤ = 1 := by simp [upperRenyiFactor]

example {a b : ℕ} (rho : BipartiteMatrix a b) : QuantumExecution rho rho 0 :=
  QuantumExecution.identity rho

example {a b : ℕ} (rho : BipartiteMatrix a b) : ClassicalExecution rho rho 0 :=
  ClassicalExecution.identity rho

example {a b m : ℕ} (rho : BipartiteMatrix (a * m) b) (hm : 0 < m) :
    QuantumExecution rho (transferAB rho) (logTwo m) := QuantumExecution.sendAB rho hm

example {A B : Type} [Fintype A] [Fintype B] (psi : EuclideanSpace ℂ (A × B))
    (p : (Fin 0 → A) × (Fin 0 → B)) : pureStateCopies psi 0 p = 1 := by simp [pureStateCopies]

example : eprPairs 0 (0,0) = 1 := by simp [eprPairs, bellRank]

example : harmonicSum 1 = 1 := by norm_num [harmonicSum]

example : harmonicState 1 (0,0) = 1 := by norm_num [harmonicState, harmonicSum]

example {A B C D : Type} [Fintype A] [Fintype B]
    (U : Matrix C A ℂ) (V : Matrix D B ℂ) (phi : EuclideanSpace ℂ (A × B)) (c : C) (d : D) :
    applyLocalMaps U V phi (c,d) = ∑ a, ∑ b, U c a * V d b * phi (a,b) := rfl

example (alpha beta : ℂ) : binaryState alpha beta (false,false) = alpha := by simp [binaryState]

example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    spread rho = entropyZero rho - entropyInfinity rho := rfl

example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) (e : ℝ) :
    smoothSpread rho e = logTwo (finiteMin (spectralRetentions rho e) fun s =>
      (s.card : ℝ) * finiteMax s (ascEigenvalues rho)) := rfl

example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (alpha beta : RenyiOrder) : renyiGap rho alpha beta = eigenvalueRenyiEntropy rho alpha - eigenvalueRenyiEntropy rho beta := rfl

example {a b c k : ℕ} (K : Fin k → Matrix (Fin c) (Fin a) ℂ) (rho : BipartiteMatrix a b) :
    aliceApply K rho = krausApply (fun j => Matrix.kronecker (K j)
      (1 : Matrix (Fin b) (Fin b) ℂ)) rho := rfl

example {a b d k : ℕ} (K : Fin k → Matrix (Fin d) (Fin b) ℂ) (rho : BipartiteMatrix a b) :
    bobApply K rho = krausApply (fun j => Matrix.kronecker
      (1 : Matrix (Fin a) (Fin a) ℂ) (K j)) rho := rfl

example {a b m : ℕ} (rho : BipartiteMatrix a (m * b)) (hm : 0 < m) :
    QuantumExecution rho (transferBA rho) (logTwo m) := QuantumExecution.sendBA rho hm

example {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : Quantum rho rho 0 := QuantumExecution.identity (pack rho)

example {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : Classical rho rho 0 := ClassicalExecution.identity (pack rho)

example {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (phi : EuclideanSpace ℂ (A × B)) (a a0 : A) :
    aliceDensity phi a a0 = ∑ b, phi (a,b) * conj (phi (a0,b)) := rfl

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    fidelity rho sigma = (rootFidelity rho sigma) ^ 2 := rfl

example : smoothingError 0 = 0 := by norm_num [smoothingError]

example : harmonicTailCuts 1 0 = {1} := by norm_num [harmonicTailCuts, harmonicSum]

example : harmonicHeadCuts 1 0 = {1} := by norm_num [harmonicHeadCuts, harmonicSum]

end QAlgorithms.Papers.Independent.Intakenext100.P61


