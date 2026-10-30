-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P19
-- name    : QAlgorithms_Papers_Independent_Extend50_P19
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:02:29.982803+00:00
-- url     : https://prove2.me/theorems/a0a42aa0-b064-4be2-8a20-4e0c563213fe
-- title:
--   Definitions for Optimality of the pretty good measurement for port-based teleportation
-- statement:
--   The objects the formalized statements of *Optimality of the pretty good measurement for port-based teleportation* (arXiv:2008.11194) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DiscriminationIndex`: Alice's N ports followed by the extra single system (PDF pp.6-7).
--   - `ResourceIndex`: Physical port resource coordinates A^N B^N (PDF p.5).
--   - `spectralInverse`: Generalized inverse of a finite Hermitian PSD operator, zero on its kernel (PDF p.3). Its use below always carries PSD, either explicitly or by construction.
--   - `spectralInverseSqrt`: Generalized inverse square root, with zero eigenvalues sent to zero (PDF p.7, (4.11)).
--   - `weylDim`: Actual Weyl dimension, from the accepted tensor Young image (PDF p.4).
--   - `spechtDim`: Actual Specht dimension, from the accepted regular Young ideal (PDF p.4).
--   - `AddsBox`: Addition of one box, retaining valid height-bounded partitions (PDF pp.3-4). This never includes the negative highest weights in footnote 3 on p.7.
--   - `liftAlice`: Tensor an Alice operator with identity on the extra system (PDF p.3).
--   - `portRho`: The normalized state Phi^+_{A_i B} tensor I/d^(N-1), in the original port order (PDF p.6, (4.2)). Its nonzero entries are 1/d^N.
--   - `portAverage`: The UNNORMALIZED ensemble sum (PDF p.7, (4.9)); labels have prior 1/N.
--   - `standardPGM`: The PGM from the original maximally entangled ensemble, completed to a full POVM by equally distributing the complementary support projection (PDF p.7, (4.11)-(4.12)). The added term contributes zero on every ensemble used here, including all the symmetric canonical resources of Section 5.
--   - `discriminationSuccess`: Uniform-prior mixed-state discrimination success (PDF p.5, (3.5)).
--   - `mixedAction`: Actual mixed action U^(tensor N) tensor conjugate(U) (PDF pp.6-8). Complex conjugation is in the computational basis, without a transpose.
--   - `mixedIsotypic`: The physical alpha-isotypic subspace for the mixed action: the span of images of ALL intertwiners from the actual polynomial Schur module of shape alpha (PDF pp.7-8, (4.8) and Q_alpha). This is independent of portAverage and of its claimed eigenvalues. Nonpolynomial sectors remain in the orthogonal complement, rather than being assigned an invalid partition.
--   - `mixedProjector`: Orthogonal projection onto the physical mixed-action isotypic subspace (PDF p.8). Both basis vectors use the conjugate-linear-first convention.
--   - `mixedBlock`: Joint physical U_d and S_N block (PDF p.7, (4.9)). P_mu is the accepted full isotypic projector, never a single tensor Young image.
--   - `portEigenvalue`: Eigenvalue in Lemma 3: N/d^N times m_mu d_alpha/(m_alpha d_mu) (PDF p.7, (4.10)).
--   - `portsVector`: The N independent normalized maximally entangled pairs, grouped A^N B^N (PDF pp.3,6, (2.1) and (4.1)).
--   - `standardResource`: The fixed independent maximally entangled resource (PDF p.6, (4.1)).
--   - `canonicalFilter`: O_c = sum_mu sqrt(c_mu) P_mu, computed from the actual full physical Schur projectors (PDF pp.13-14, (5.15) and (5.26)).
--   - `FeasibleWeights`: Nonnegative canonical weights and the exact trace normalization sum c_mu m_mu d_mu = d^N (PDF p.12, (5.9)). Zeros are permitted.
--   - `canonicalVector`: Canonical resource vector (O_c tensor I)|Phi^+>^(tensor N) (PDF p.11, (5.1)); feasible weights make it a unit vector.
--   - `canonicalResource`: Pure density operator of the canonical resource (PDF p.11, (5.1)).
--   - `canonicalEnsemble`: eta_i = (O_c tensor I) rho_i (O_c tensor I)^dagger (PDF pp.11-12, (5.2)); the PGM below is not recomputed from eta.
--   - `insertPort`: Insert the kept Bob port into its original position (PDF p.5, (3.1)).
--   - `resourceMarginal`: Trace out Bob's other N-1 ports and relabel B_i as the output B (PDF p.5, (3.4)); this applies to arbitrary mixed resource states.
--   - `pbtChannel`: Physical deterministic PBT channel, entrywise version of (3.1), PDF p.5. The Alice trace contracts E against sigma tensor phi; no correction is made on Bob's kept port. The POVM order is A^N A_0, with A_0 last.
--   - `pbtFidelity`: Entanglement fidelity of the actual channel (3.1), namely <Phi^+|(Lambda tensor id)(Phi^+)|Phi^+> (PDF p.5, (3.2)). The coordinate contraction is d^(-2) sum_{k,l} Lambda(|k><l|)_{k,l}. It is not defined using any representation-theoretic performance formula.
--   - `coefficientScore`: The coefficient numerator in (5.8), PDF p.12. The square is inside the sum over alpha. At c=1 this is the numerator in (4.13), PDF p.8.
-- source:
--   Optimality of the pretty good measurement for port-based teleportation, arXiv:2008.11194v2, https://arxiv.org/abs/2008.11194v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition

/-!
Statements from Felix Leditzky, arXiv:2008.11194v2 (2022).
Tensor words list ports in their original order; the extra single system is last.
All new constructions are local to this paper. No dual certificate, decomposition,
or symmetry reduction is an assumption of a headline theorem.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace QAlgorithms.Papers.Independent.Extend50.P19

attribute [local instance] Classical.propDecidable

/-- Alice's N ports followed by the extra single system (PDF pp.6-7). -/
abbrev DiscriminationIndex (d N : ℕ) := (Fin N → Fin d) × Fin d

/-- Physical port resource coordinates A^N B^N (PDF p.5). -/
abbrev ResourceIndex (d N : ℕ) := (Fin N → Fin d) × (Fin N → Fin d)

/-- Generalized inverse of a finite Hermitian PSD operator, zero on its kernel
(PDF p.3). Its use below always carries PSD, either explicitly or by construction. -/
def spectralInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => x⁻¹) X

/-- Generalized inverse square root, with zero eigenvalues sent to zero
(PDF p.7, (4.11)). -/
def spectralInverseSqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) X

/-- Actual Weyl dimension, from the accepted tensor Young image (PDF p.4). -/
def weylDim {d n : ℕ} (mu : Schur.Partition d n) : ℕ :=
  Module.finrank ℂ (Schur.schurModule mu)

/-- Actual Specht dimension, from the accepted regular Young ideal (PDF p.4). -/
def spechtDim {d n : ℕ} (mu : Schur.Partition d n) : ℕ :=
  Module.finrank ℂ (Schur.spechtSpace mu)

/-- Addition of one box, retaining valid height-bounded partitions (PDF pp.3-4).
This never includes the negative highest weights in footnote 3 on p.7. -/
def AddsBox {d m n : ℕ} (alpha : Schur.Partition d m)
    (mu : Schur.Partition d n) : Prop :=
  alpha.val.cells ⊆ mu.val.cells ∧ mu.val.card = alpha.val.card + 1

/-- Tensor an Alice operator with identity on the extra system (PDF p.3). -/
def liftAlice {d N : ℕ} (X : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  Matrix.kronecker X (1 : Matrix (Fin d) (Fin d) ℂ)

/-- The normalized state Phi^+_{A_i B} tensor I/d^(N-1), in the original
port order (PDF p.6, (4.2)). Its nonzero entries are 1/d^N. -/
def portRho (d N : ℕ) (i : Fin N) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  Matrix.of fun x y =>
    if x.1 i = x.2 ∧ y.1 i = y.2 ∧ (∀ j, j ≠ i → x.1 j = y.1 j)
    then ((d : ℂ)^N)⁻¹ else 0

/-- The UNNORMALIZED ensemble sum (PDF p.7, (4.9)); labels have prior 1/N. -/
def portAverage (d N : ℕ) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  ∑ i : Fin N, portRho d N i

/-- The PGM from the original maximally entangled ensemble, completed to a
full POVM by equally distributing the complementary support projection
(PDF p.7, (4.11)-(4.12)). The added term contributes zero on every ensemble
used here, including all the symmetric canonical resources of Section 5. -/
def standardPGM (d N : ℕ) (i : Fin N) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  let R := portAverage d N
  let S := spectralInverseSqrt R
  S * portRho d N i * S + (N : ℂ)⁻¹ • (1 - R * spectralInverse R)

/-- Uniform-prior mixed-state discrimination success (PDF p.5, (3.5)). -/
def discriminationSuccess {d N : ℕ}
    (rho E : Fin N → Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, effectProb (E i) (rho i)

/-- Actual mixed action U^(tensor N) tensor conjugate(U) (PDF pp.6-8).
Complex conjugation is in the computational basis, without a transpose. -/
def mixedAction (d N : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  Matrix.of fun x y => piKron N U x.1 y.1 * conj (U x.2 y.2)

/-- The physical alpha-isotypic subspace for the mixed action: the span of
images of ALL intertwiners from the actual polynomial Schur module of shape
alpha (PDF pp.7-8, (4.8) and Q_alpha). This is independent of portAverage
and of its claimed eigenvalues. Nonpolynomial sectors remain in the
orthogonal complement, rather than being assigned an invalid partition. -/
def mixedIsotypic {d N : ℕ} (alpha : Schur.Partition d (N-1)) :
    Submodule ℂ (EuclideanSpace ℂ (DiscriminationIndex d N)) :=
  Submodule.span ℂ {w | ∃ T : Schur.schurModule alpha →ₗ[ℂ]
      EuclideanSpace ℂ (DiscriminationIndex d N),
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) (v : Schur.schurModule alpha),
      T (Schur.polynomialRepresentation alpha (U : Matrix (Fin d) (Fin d) ℂ) v) =
        act (mixedAction d N (U : Matrix (Fin d) (Fin d) ℂ)) (T v)) ∧
    ∃ v, T v = w}

/-- Orthogonal projection onto the physical mixed-action isotypic subspace
(PDF p.8). Both basis vectors use the conjugate-linear-first convention. -/
def mixedProjector {d N : ℕ} (alpha : Schur.Partition d (N-1)) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  Matrix.of fun x y => inner ℂ (ket x) ((mixedIsotypic alpha).starProjection (ket y))

/-- Joint physical U_d and S_N block (PDF p.7, (4.9)). P_mu is the accepted
full isotypic projector, never a single tensor Young image. -/
def mixedBlock {d N : ℕ} (alpha : Schur.Partition d (N-1))
    (mu : Schur.Partition d N) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  liftAlice (Schur.isotypicProjector mu) * mixedProjector alpha

/-- Eigenvalue in Lemma 3: N/d^N times m_mu d_alpha/(m_alpha d_mu)
(PDF p.7, (4.10)). -/
def portEigenvalue {d N : ℕ} (alpha : Schur.Partition d (N-1))
    (mu : Schur.Partition d N) : ℝ :=
  (N : ℝ) / (d : ℝ)^N *
    (((weylDim mu : ℝ) * (spechtDim alpha : ℝ)) /
      ((weylDim alpha : ℝ) * (spechtDim mu : ℝ)))

/-- The N independent normalized maximally entangled pairs, grouped A^N B^N
(PDF pp.3,6, (2.1) and (4.1)). -/
def portsVector (d N : ℕ) : EuclideanSpace ℂ (ResourceIndex d N) :=
  WithLp.toLp 2 fun x =>
    if x.1 = x.2 then ((Real.sqrt ((d : ℝ)^N))⁻¹ : ℂ) else 0

/-- The fixed independent maximally entangled resource (PDF p.6, (4.1)). -/
def standardResource (d N : ℕ) : Matrix (ResourceIndex d N) (ResourceIndex d N) ℂ :=
  pureDensity (portsVector d N)

/-- O_c = sum_mu sqrt(c_mu) P_mu, computed from the actual full physical
Schur projectors (PDF pp.13-14, (5.15) and (5.26)). -/
def canonicalFilter {d N : ℕ} (c : Schur.Partition d N → ℝ) :
    Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ :=
  ∑ mu, (Real.sqrt (c mu) : ℂ) • Schur.isotypicProjector mu

/-- Nonnegative canonical weights and the exact trace normalization
sum c_mu m_mu d_mu = d^N (PDF p.12, (5.9)). Zeros are permitted. -/
def FeasibleWeights {d N : ℕ} (c : Schur.Partition d N → ℝ) : Prop :=
  (∀ mu, 0 ≤ c mu) ∧
    ∑ mu, c mu * (spechtDim mu : ℝ) * (weylDim mu : ℝ) = (d : ℝ)^N

/-- Canonical resource vector (O_c tensor I)|Phi^+>^(tensor N)
(PDF p.11, (5.1)); feasible weights make it a unit vector. -/
def canonicalVector {d N : ℕ} (c : Schur.Partition d N → ℝ) :
    EuclideanSpace ℂ (ResourceIndex d N) :=
  act (Matrix.kronecker (canonicalFilter c) (1 : Matrix ((Fin N → Fin d)) ((Fin N → Fin d)) ℂ))
    (portsVector d N)

/-- Pure density operator of the canonical resource (PDF p.11, (5.1)). -/
def canonicalResource {d N : ℕ} (c : Schur.Partition d N → ℝ) :
    Matrix (ResourceIndex d N) (ResourceIndex d N) ℂ :=
  pureDensity (canonicalVector c)

/-- eta_i = (O_c tensor I) rho_i (O_c tensor I)^dagger
(PDF pp.11-12, (5.2)); the PGM below is not recomputed from eta. -/
def canonicalEnsemble {d N : ℕ} (c : Schur.Partition d N → ℝ) (i : Fin N) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  liftAlice (canonicalFilter c) * portRho d N i * (liftAlice (canonicalFilter c))ᴴ

/-- Insert the kept Bob port into its original position (PDF p.5, (3.1)). -/
def insertPort {d N : ℕ} (i : Fin N) (b : Fin d)
    (rest : {j : Fin N // j ≠ i} → Fin d) : (Fin N → Fin d) :=
  fun j => if h : j = i then b else rest ⟨j, h⟩

/-- Trace out Bob's other N-1 ports and relabel B_i as the output B
(PDF p.5, (3.4)); this applies to arbitrary mixed resource states. -/
def resourceMarginal {d N : ℕ}
    (phi : Matrix (ResourceIndex d N) (ResourceIndex d N) ℂ) (i : Fin N) :
    Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ :=
  Matrix.of fun x y => ∑ rest : {j : Fin N // j ≠ i} → Fin d,
    phi (x.1, insertPort i x.2 rest) (y.1, insertPort i y.2 rest)

/-- Physical deterministic PBT channel, entrywise version of (3.1), PDF p.5.
The Alice trace contracts E against sigma tensor phi; no correction is made
on Bob's kept port. The POVM order is A^N A_0, with A_0 last. -/
def pbtChannel {d N : ℕ}
    (phi : Matrix (ResourceIndex d N) (ResourceIndex d N) ℂ)
    (E : Fin N → Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ)
    (sigma : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun b bprime => ∑ i : Fin N, ∑ a : (Fin N → Fin d), ∑ aprime : (Fin N → Fin d),
    ∑ t : Fin d, ∑ tprime : Fin d,
      E i (a,t) (aprime,tprime) * sigma tprime t *
        resourceMarginal phi i (aprime,b) (a,bprime)

/-- Entanglement fidelity of the actual channel (3.1), namely
<Phi^+|(Lambda tensor id)(Phi^+)|Phi^+> (PDF p.5, (3.2)).
The coordinate contraction is d^(-2) sum_{k,l} Lambda(|k><l|)_{k,l}.
It is not defined using any representation-theoretic performance formula. -/
def pbtFidelity {d N : ℕ}
    (phi : Matrix (ResourceIndex d N) (ResourceIndex d N) ℂ)
    (E : Fin N → Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ) : ℝ :=
  ((d : ℝ)^2)⁻¹ *
    (∑ k : Fin d, ∑ l : Fin d,
      pbtChannel phi E (Matrix.of fun x y => if x = k ∧ y = l then 1 else 0) k l).re

/-- The coefficient numerator in (5.8), PDF p.12. The square is inside the
sum over alpha. At c=1 this is the numerator in (4.13), PDF p.8. -/
def coefficientScore {d N : ℕ} (c : Schur.Partition d N → ℝ) : ℝ :=
  ∑ alpha : Schur.Partition d (N-1),
    (∑ mu : Schur.Partition d N,
      if AddsBox alpha mu then
        Real.sqrt (c mu * (spechtDim mu : ℝ) * (weylDim mu : ℝ)) else 0)^2

/-! Definitional sanity checks; these are not proofs of any source theorem. -/

/-- On a one-dimensional local system every port state has its unique entry 1. -/
example (N : ℕ) (i : Fin N) :
    portRho 1 N i ((fun _ => 0),0) ((fun _ => 0),0) = 1 := by
  simp [portRho]

/-- The empty tensor product has normalized scalar amplitude 1. -/
example (d : ℕ) (x : (Fin 0 → Fin d)) : portsVector d 0 (x,x) = 1 := by
  simp [portsVector]

/-- Tracing the identity on one local system gives its dimension. -/
example (d : ℕ) (x : (Fin 0 → Fin d)) :
    traceLeft ((1 : Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ).submatrix
      (fun p : Fin d × (Fin 0 → Fin d) => Fin.cons p.1 p.2)
      (fun p : Fin d × (Fin 0 → Fin d) => Fin.cons p.1 p.2)) x x = (d : ℂ) := by
  simp [traceLeft]

/-- The kept port is inserted in its original position. -/
example {d N : ℕ} (i : Fin N) (b : Fin d)
    (rest : {j : Fin N // j ≠ i} → Fin d) : insertPort i b rest i = b := by
  simp [insertPort]

/-- Zero input gives zero output in the actual channel formula. -/
example {d N : ℕ} (phi : Matrix (ResourceIndex d N) (ResourceIndex d N) ℂ)
    (E : Fin N → Matrix (DiscriminationIndex d N) (DiscriminationIndex d N) ℂ) :
    pbtChannel phi E 0 = 0 := by
  ext b bprime
  simp [pbtChannel]

/-- With no ordinary tensor factors, the mixed action is the conjugate action. -/
example (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (x y : (Fin 0 → Fin d)) (b bprime : Fin d) :
    mixedAction d 0 U (x,b) (y,bprime) = conj (U b bprime) := by
  simp [mixedAction, piKron]

/-- Zero coefficients give zero score; at d,N positive they are not feasible. -/
example (d N : ℕ) : coefficientScore (d := d) (N := N) (fun _ => 0) = 0 := by
  simp [coefficientScore]

end QAlgorithms.Papers.Independent.Extend50.P19


