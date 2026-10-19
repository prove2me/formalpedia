-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
-- name    : QAlgorithms_Papers_Independent_Information100_P53
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:51:52.089973+00:00
-- url     : https://prove2.me/theorems/58a755f4-0548-40eb-b751-3e298e59129d
-- title:
--   Definitions for A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding
-- statement:
--   The objects the formalized statements of *A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding* (arXiv:2610.06840) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsPrior`: PDF p.2, §II-B: a fixed prior distribution; zero probabilities are allowed.
--   - `SpectralData`: PDF pp.2,4: a decreasing spectrum with multiplicity and a complete orthonormal spectral basis. This packages the source's choice of spectral decomposition.
--   - `success`: PDF p.2, Born rule: average success of a specified decoding measurement.
--   - `fidelity`: PDF p.2: squared Uhlmann fidelity, using the accepted root-fidelity convention.
--   - `pairSum`: PDF pp.3–4: one term per unordered pair of distinct message labels.
--   - `fidelitySum`: PDF pp.3–4, Eqs.(4),(6): the full fixed-prior pairwise fidelity expression.
--   - `traceSum`: PDF p.4, Theorem 3: pairwise trace norms, with no factor one half.
--   - `IsTopSelection`: PDF p.4, Eq.(7), and p.5, Eqs.(10)–(11): any selection of the k largest weights, including every way of resolving ties.
--   - `spectralWeight`: PDF p.4: the weighted eigenvalue attached to a message/eigenvector index.
--   - `selectedProjector`: PDF p.4, sufficient equality condition in Theorem 4: the selected rank-one projectors for a particular message. This definition does not assert POVM completeness.
--   - `positiveProjector`: PDF p.2, §II-A: projection onto the strictly positive spectral subspace. The functions in these cfc definitions are continuous on every finite spectrum.
--   - `kernelProjector`: PDF p.2, §II-A: projection onto the kernel, including zero eigenvalues.
--   - `IsQuasiPerfect`: PDF p.2, Definition 1: the paper's unweighted, weak quasi-perfect-code condition. Both the positive and the kernel projectors enter the covering inequality.
--   - `qubitInput`: PDF p.3, Lemma 3: the first pure qubit input, with b constructed from a.
--   - `amplitudeDamping`: PDF p.3, §II-E: amplitude damping through the two printed Kraus operators.
--   - `productMatrix`: PDF pp.3–5: tensor product of symbol matrices, in the product computational basis. The single-use dimension is q, resolving §III-C's inconsistent tensor-power notation.
--   - `productVector`: PDF pp.4–5, Lemma 4: tensor product of the selected eigenvectors.
--   - `productWeight`: PDF p.5, Proposition 1: weighted product eigenvalues, one index per factor.
--   - `classicalSuccess`: PDF pp.4–5: correct classical decoding with fixed, possibly nonuniform priors uses a maximum weighted entry in each column (MAP decoding).
--   - `IsSymmetric`: PDF p.5, Definition 2: unitary equivalence of every pair of symbols.
--   - `blockEnsembleState`: PDF p.2, Eq.(1): the actual block-diagonal state diag(p_i rho_i), on the classical-message register tensored with the original Hilbert space.
--   - `binaryComparisonState`: PDF p.2, Eq.(1): the comparison state (I_M/M) tensor mu. The theorem uses M>0; the total extension at M=0 is never used.
--   - `binaryTypeIError`: PDF p.2, Eq.(2): optimal type-I error under the type-II constraint. Only effects 0 <= T <= I satisfying Tr(psi1 T) <= beta enter the infimum. The theorem uses density matrices and beta=1/M>0, making the range nonempty (the zero effect is feasible) and bounded in [0,1].
-- source:
--   A Spectrum-Based Converse for Quantum State Discrimination and Its Applications to Classical-Quantum Channel Coding, arXiv:2610.06840v1, https://arxiv.org/abs/2610.06840v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Channel

/-!
Statements from Havas–Lin–Rosnes, arXiv:2610.06840v1.
All page citations are PDF pages. New definitions are local to this paper.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P53

open scoped Matrix ComplexConjugate ComplexOrder
open Finset

/-- PDF p.2, §II-B: a fixed prior distribution; zero probabilities are allowed. -/
def IsPrior {M : ℕ} (p : Fin M → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- PDF pp.2,4: a decreasing spectrum with multiplicity and a complete orthonormal
spectral basis. This packages the source's choice of spectral decomposition. -/
structure SpectralData {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) where
  value : Fin N → ℝ
  basis : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))
  decreasing : Antitone value
  reconstruct : A = ∑ j, (value j : ℂ) • pureDensity (basis j)

/-- PDF p.2, Born rule: average success of a specified decoding measurement. -/
def success {M : ℕ} {Index : Type*} [Fintype Index]
    (p : Fin M → ℝ) (rho D : Fin M → Matrix Index Index ℂ) : ℝ :=
  ∑ i, p i * effectProb (D i) (rho i)

/-- PDF p.2: squared Uhlmann fidelity, using the accepted root-fidelity convention. -/
def fidelity {Index : Type*} [Fintype Index] [DecidableEq Index]
    (A B : Matrix Index Index ℂ) : ℝ := (rootFidelity A B) ^ 2

/-- PDF pp.3–4: one term per unordered pair of distinct message labels. -/
def pairSum {M : ℕ} (f : Fin M → Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j

/-- PDF pp.3–4, Eqs.(4),(6): the full fixed-prior pairwise fidelity expression. -/
def fidelitySum {M N : ℕ} (p : Fin M → ℝ)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  pairSum fun i j => Real.sqrt
    (p i ^ 2 + 2 * (1 - 2 * fidelity (rho i) (rho j)) * p i * p j + p j ^ 2)

/-- PDF p.4, Theorem 3: pairwise trace norms, with no factor one half. -/
def traceSum {M N : ℕ} (p : Fin M → ℝ)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  pairSum fun i j => traceNorm ((p i : ℂ) • rho i - (p j : ℂ) • rho j)

/-- PDF p.4, Eq.(7), and p.5, Eqs.(10)–(11): any selection of the k largest
weights, including every way of resolving ties. -/
def IsTopSelection {Label : Type*} [DecidableEq Label] (k : ℕ) (w : Label → ℝ)
    (I : Finset Label) : Prop :=
  I.card = k ∧ ∀ u ∈ I, ∀ v, v ∉ I → w v ≤ w u

/-- PDF p.4: the weighted eigenvalue attached to a message/eigenvector index. -/
def spectralWeight {M N : ℕ} {rho : Fin M → Matrix (Fin N) (Fin N) ℂ}
    (p : Fin M → ℝ) (s : ∀ i, SpectralData (rho i)) (z : Fin M × Fin N) : ℝ :=
  p z.1 * (s z.1).value z.2

/-- PDF p.4, sufficient equality condition in Theorem 4: the selected rank-one
projectors for a particular message. This definition does not assert POVM completeness. -/
def selectedProjector {M N : ℕ} {rho : Fin M → Matrix (Fin N) (Fin N) ℂ}
    (s : ∀ i, SpectralData (rho i)) (I : Finset (Fin M × Fin N)) (i : Fin M) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ I), pureDensity ((s i).basis j)

/-- PDF p.2, §II-A: projection onto the strictly positive spectral subspace.
The functions in these cfc definitions are continuous on every finite spectrum. -/
def positiveProjector {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) A

/-- PDF p.2, §II-A: projection onto the kernel, including zero eigenvalues. -/
def kernelProjector {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) A

/-- PDF p.2, Definition 1: the paper's unweighted, weak quasi-perfect-code condition.
Both the positive and the kernel projectors enter the covering inequality. -/
def IsQuasiPerfect {M N : ℕ} (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ (mu : Matrix (Fin N) (Fin N) ℂ) (t : ℝ), IsDensityMatrix mu ∧
    (∀ i j, i ≠ j →
      positiveProjector (rho i - (t : ℂ) • mu) *
        positiveProjector (rho j - (t : ℂ) • mu) = 0) ∧
    ((∑ i, (positiveProjector (rho i - (t : ℂ) • mu) +
      kernelProjector (rho i - (t : ℂ) • mu))) - 1).PosSemidef

/-- PDF p.3, Lemma 3: the first pure qubit input, with b constructed from a. -/
def qubitInput (a f : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), (Real.sqrt (a * (1 - a)) : ℂ) * Complex.exp ((f : ℂ) * Complex.I);
    (Real.sqrt (a * (1 - a)) : ℂ) * Complex.exp (-(f : ℂ) * Complex.I), (1 - a : ℝ)]

/-- PDF p.3, §II-E: amplitude damping through the two printed Kraus operators. -/
def amplitudeDamping (gamma : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let K0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, (Real.sqrt (1 - gamma) : ℂ)]
  let K1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, (Real.sqrt gamma : ℂ); 0, 0]
  K0 * A * K0ᴴ + K1 * A * K1ᴴ

/-- PDF pp.3–5: tensor product of symbol matrices, in the product computational basis.
The single-use dimension is q, resolving §III-C's inconsistent tensor-power notation. -/
def productMatrix {n q : ℕ} {F : Type*}
    (rho : F → Matrix (Fin q) (Fin q) ℂ) (x : Fin n → F) :
    Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ :=
  fun u v => ∏ l, rho (x l) (u l) (v l)

/-- PDF pp.4–5, Lemma 4: tensor product of the selected eigenvectors. -/
def productVector {n q : ℕ} {F : Type*}
    {rho : F → Matrix (Fin q) (Fin q) ℂ} (s : ∀ a, SpectralData (rho a))
    (x : Fin n → F) (j : Fin n → Fin q) : EuclideanSpace ℂ (Fin n → Fin q) :=
  WithLp.toLp 2 fun u => ∏ l, (s (x l)).basis (j l) (u l)

/-- PDF p.5, Proposition 1: weighted product eigenvalues, one index per factor. -/
def productWeight {n q M : ℕ} {F : Type*} (p : Fin M → ℝ)
    (a : F → Fin q → ℝ) (code : Fin M → Fin n → F)
    (z : Fin M × (Fin n → Fin q)) : ℝ :=
  p z.1 * ∏ l, a (code z.1 l) (z.2 l)

/-- PDF pp.4–5: correct classical decoding with fixed, possibly nonuniform priors
uses a maximum weighted entry in each column (MAP decoding). -/
def classicalSuccess {M N : ℕ} (p : Fin M → ℝ) (W : Fin M → Fin N → ℝ) : ℝ :=
  ∑ j, ⨆ i : Fin M, p i * W i j

/-- PDF p.5, Definition 2: unitary equivalence of every pair of symbols. -/
def IsSymmetric {q : ℕ} {F : Type*} (rho : F → Matrix (Fin q) (Fin q) ℂ) : Prop :=
  ∀ x y, ∃ U : Matrix.unitaryGroup (Fin q) ℂ,
    rho x = (U : Matrix (Fin q) (Fin q) ℂ) * rho y *
      (U : Matrix (Fin q) (Fin q) ℂ)ᴴ

/-- The one-message prior is normalized, and zero weights are not required to be positive. -/
example : IsPrior (fun _ : Fin 1 => (1 : ℝ)) := by
  norm_num [IsPrior]

/-- A singleton message family has no pair contributions. -/
example (f : Fin 1 → Fin 1 → ℝ) : pairSum f = 0 := by
  simp [pairSum, Finset.sum_filter]

/-- Selecting no weights is a valid top-zero selection. -/
example {Label : Type*} [DecidableEq Label] (w : Label → ℝ) : IsTopSelection 0 w ∅ := by
  simp [IsTopSelection]

/-- A zero-length tensor has its unique entry equal to one. -/
example {q : ℕ} {F : Type*} (rho : F → Matrix (Fin q) (Fin q) ℂ)
    (x : Fin 0 → F) (u v : Fin 0 → Fin q) : productMatrix rho x u v = 1 := by
  simp [productMatrix]

/-- PDF p.2, Eq.(1): the actual block-diagonal state diag(p_i rho_i),
on the classical-message register tensored with the original Hilbert space. -/
def blockEnsembleState {M N : ℕ} (p : Fin M → ℝ)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ :=
  fun u v => if u.1 = v.1 then (p u.1 : ℂ) * rho u.1 u.2 v.2 else 0

/-- PDF p.2, Eq.(1): the comparison state (I_M/M) tensor mu.
The theorem uses M>0; the total extension at M=0 is never used. -/
def binaryComparisonState {M N : ℕ} (mu : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ :=
  Matrix.kronecker (((1 / (M : ℝ) : ℝ) : ℂ) •
    (1 : Matrix (Fin M) (Fin M) ℂ)) mu

/-- PDF p.2, Eq.(2): optimal type-I error under the type-II constraint.
Only effects 0 <= T <= I satisfying Tr(psi1 T) <= beta enter the infimum.
The theorem uses density matrices and beta=1/M>0, making the range nonempty
(the zero effect is feasible) and bounded in [0,1]. -/
def binaryTypeIError {Index : Type*} [Fintype Index] [DecidableEq Index]
    (beta : ℝ) (psi0 psi1 : Matrix Index Index ℂ) : ℝ :=
  sInf {e : ℝ | ∃ T : Matrix Index Index ℂ,
    IsEffect T ∧ effectProb T psi1 ≤ beta ∧ e = 1 - effectProb T psi0}

/-- Each diagonal block is the corresponding weighted input state. -/
example {M N : ℕ} (p : Fin M → ℝ)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (i : Fin M) (a b : Fin N) :
    blockEnsembleState p rho (i, a) (i, b) = (p i : ℂ) * rho i a b := by
  simp [blockEnsembleState]

/-- Distinct message blocks have no coherence. -/
example {M N : ℕ} (p : Fin M → ℝ)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (i j : Fin M) (hij : i ≠ j)
    (a b : Fin N) : blockEnsembleState p rho (i, a) (j, b) = 0 := by
  simp [blockEnsembleState, hij]

/-- Every comparison-state diagonal block is mu/M. -/
example {M N : ℕ} (mu : Matrix (Fin N) (Fin N) ℂ) (i : Fin M) (a b : Fin N) :
    binaryComparisonState (M := M) mu (i, a) (i, b) =
      (((1 / (M : ℝ) : ℝ) : ℂ) * mu a b) := by
  simp [binaryComparisonState, Matrix.kronecker]

/-- The zero effect is a feasible binary test at every nonnegative threshold. -/
example {Index : Type*} [Fintype Index] [DecidableEq Index]
    (psi1 : Matrix Index Index ℂ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsEffect (0 : Matrix Index Index ℂ) ∧ effectProb 0 psi1 ≤ beta := by
  constructor
  · exact ⟨Matrix.PosSemidef.zero, by simpa using
      (Matrix.PosSemidef.one : (1 : Matrix Index Index ℂ).PosSemidef)⟩
  · simpa [effectProb] using hbeta

end QAlgorithms.Papers.Independent.Information100.P53


