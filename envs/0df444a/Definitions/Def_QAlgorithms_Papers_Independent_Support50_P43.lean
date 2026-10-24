-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43
-- name    : QAlgorithms_Papers_Independent_Support50_P43
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T22:29:38.700061+00:00
-- url     : https://prove2.me/theorems/13ddaf80-80d1-415c-99ab-98effa58b184
-- title:
--   Definitions for Multiparty Quantum Mutual Information: An alternative definition
-- statement:
--   The objects the formalized statements of *Multiparty Quantum Mutual Information: An alternative definition* (arXiv:1504.07176) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `restrictLabel`: Restrict a joint computational label to the selected registers (PDF p.3).
--   - `reducedDensity`: Partial trace via the accepted register marginal, with a trivial external register attached and then removed (PDF pp.1–3). Both retained indices remain independent.
--   - `marginalEntropyBits`: Entropy of the accepted marginal with its one-dimensional external factor (PDF pp.1,3,5). Attaching Unit does not change the marginal spectrum.
--   - `alternativeOn`: Alternative information of the individual parties in s (PDF pp.2–3,(10),(13)). For a singleton this is S(empty), hence zero on density inputs.
--   - `conventionalOn`: Conventional multipartite information, without a factor 1/2 (PDF p.1,(2)).
--   - `commonOn`: Common information: alternating sum over every nonempty subset exactly once (PDF p.3, below (13)).
--   - `IsProductAcross`: Density factors across a partition of the physical parties (PDF p.4, Theorem 5). This entrywise product is the tensor product after canonical regrouping.
--   - `cutProduct`: Product of the two marginals at the cut s|complement(s), indexed on the original joint basis, so no replica-space identification is used (PDF p.3,(13), middle line).
--   - `singletonProduct`: Tensor product of all single-party marginals on the original joint basis (PDF pp.1,3,(2),(13)).
--   - `HomBasis`: Homogeneous n-party computational basis (PDF p.5, Table I).
--   - `dickeQubitVector`: Reindex the accepted computational Dicke vector from Bool to Fin 2 (PDF p.5, Table I). The map sends 0 to false and 1 to true.
--   - `antisymmetric`: Three-qutrit antisymmetric vector, labels 1,2,3 renamed 0,1,2 (PDF pp.4–5). The three even permutations are positive.
--   - `cluster`: Four-qubit cluster vector with signs +,+,+,- (PDF p.5, Table I).
--   - `informationPair`: The pair (common information, alternative information), in bits (PDF p.5).
--   - `noisyQubits`: White-noise family from Figures 2(a,b) and 3, on three QUBITS (PDF pp.4–5); 0≤p≤1 and psi=GHZ3 or W3 in the statements.
--   - `partialTransposeA`: Partial transpose on A in the computational basis, keeping B,C fixed (PDF p.4).
--   - `logarithmicNegativity`: Logarithmic negativity E_N(A:BC), not (trace norm - 1)/2 (PDF p.4, Fig.2).
--   - `LocalBases`: Independent choice of one local orthonormal qubit basis at each party (PDF p.5, (16)–(18)).
--   - `measurementProjector`: Product rank-one outcome projector on measured parties s, identity elsewhere (PDF p.5). Outcomes have NO coordinates for unmeasured parties.
--   - `postMeasurement`: Nonselective local projective measurement (PDF p.5, below (18)).
--   - `discordScore`: Choice of information functional for the two panels of Figure 3 (PDF p.5).
--   - `discord`: Optimized information loss, with one joint optimization over independent local bases on s (PDF p.5,(16)–(18)). For density inputs the value set is nonempty, bounded, and compact, so sSup equals the printed maximum.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, https://arxiv.org/abs/1504.07176v2

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

/-!
arXiv:1504.07176v2, finite-dimensional statements, entropies in bits.
The source's tensor-power relative-entropy identities and unrestricted CP
monotonicity are deferred, not assumptions. Compilation is pending batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Restrict a joint computational label to the selected registers (PDF p.3). -/
def restrictLabel {n : ℕ} {D : Fin n → Type} (s : Finset (Fin n))
    (x : RegisterBasis D) : SubBasis D s := fun i => x i.val

/-- Partial trace via the accepted register marginal, with a trivial external register
attached and then removed (PDF pp.1–3). Both retained indices remain independent. -/
def reducedDensity {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) :
    Matrix (SubBasis D s) (SubBasis D s) ℂ :=
  fun a b => QAlgorithms.Papers.Independent.Claimed50.P33.registerMarginal
    (QAlgorithms.Papers.Independent.Claimed50.P33.trivialExtension rho) s (a, ()) (b, ())

/-- Entropy of the accepted marginal with its one-dimensional external factor
(PDF pp.1,3,5). Attaching Unit does not change the marginal spectrum. -/
def marginalEntropyBits {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) : ℝ :=
  QAlgorithms.Papers.Independent.Claimed50.P33.entropyAt
    (QAlgorithms.Papers.Independent.Claimed50.P33.trivialExtension rho) s

/-- Alternative information of the individual parties in s (PDF pp.2–3,(10),(13)).
For a singleton this is S(empty), hence zero on density inputs. -/
def alternativeOn {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) : ℝ :=
  (∑ i ∈ s, marginalEntropyBits rho (s.erase i)) - (s.card - 1 : ℕ) * marginalEntropyBits rho s

/-- Conventional multipartite information, without a factor 1/2 (PDF p.1,(2)). -/
def conventionalOn {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) : ℝ :=
  (∑ i ∈ s, marginalEntropyBits rho {i}) - marginalEntropyBits rho s

/-- Common information: alternating sum over every nonempty subset exactly once
(PDF p.3, below (13)). -/
def commonOn {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) : ℝ :=
  ∑ t ∈ s.powerset.filter (fun t => t.Nonempty),
    (-1 : ℝ) ^ (t.card + 1) * marginalEntropyBits rho t

/-- Density factors across a partition of the physical parties (PDF p.4, Theorem 5).
This entrywise product is the tensor product after canonical regrouping. -/
def IsProductAcross {n m : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (blocks : Fin m → Finset (Fin n)) : Prop :=
  ∀ a b, rho a b = ∏ j, reducedDensity rho (blocks j)
    (restrictLabel (blocks j) a) (restrictLabel (blocks j) b)

/-- Product of the two marginals at the cut s|complement(s), indexed on the original
joint basis, so no replica-space identification is used (PDF p.3,(13), middle line). -/
def cutProduct {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) :
    Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  fun a b => reducedDensity rho s (restrictLabel s a) (restrictLabel s b) *
    reducedDensity rho sᶜ (restrictLabel sᶜ a) (restrictLabel sᶜ b)

/-- Tensor product of all single-party marginals on the original joint basis
(PDF pp.1,3,(2),(13)). -/
def singletonProduct {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : Matrix (RegisterBasis D) (RegisterBasis D) ℂ :=
  fun a b => ∏ i, reducedDensity rho {i} (restrictLabel {i} a) (restrictLabel {i} b)

/-- Homogeneous n-party computational basis (PDF p.5, Table I). -/
abbrev HomBasis (n d : ℕ) := Fin n → Fin d

/-- Reindex the accepted computational Dicke vector from Bool to Fin 2
(PDF p.5, Table I). The map sends 0 to false and 1 to true. -/
def dickeQubitVector (n r : ℕ) : EuclideanSpace ℂ (HomBasis n 2) :=
  WithLp.toLp 2 fun x =>
    QAlgorithms.Papers.Independent.Information100.P22.dicke (I := Fin n) r
      (fun i => x i == 1)

/-- Three-qutrit antisymmetric vector, labels 1,2,3 renamed 0,1,2
(PDF pp.4–5). The three even permutations are positive. -/
def antisymmetric : EuclideanSpace ℂ (HomBasis 3 3) :=
  WithLp.toLp 2 fun x =>
    if x = ![0,1,2] ∨ x = ![1,2,0] ∨ x = ![2,0,1] then
      ((Real.sqrt 6)⁻¹ : ℂ)
    else if x = ![0,2,1] ∨ x = ![1,0,2] ∨ x = ![2,1,0] then
      -((Real.sqrt 6)⁻¹ : ℂ) else 0

/-- Four-qubit cluster vector with signs +,+,+,- (PDF p.5, Table I). -/
def cluster : EuclideanSpace ℂ (HomBasis 4 2) :=
  WithLp.toLp 2 fun x =>
    if x = ![0,0,0,0] ∨ x = ![0,0,1,1] ∨ x = ![1,1,0,0] then 1/2
    else if x = ![1,1,1,1] then -(1/2) else 0

/-- The pair (common information, alternative information), in bits (PDF p.5). -/
def informationPair {n d : ℕ} (psi : EuclideanSpace ℂ (HomBasis n d)) : ℝ × ℝ :=
  (commonOn (pureDensity psi) Finset.univ, alternativeOn (pureDensity psi) Finset.univ)

/-- White-noise family from Figures 2(a,b) and 3, on three QUBITS
(PDF pp.4–5); 0≤p≤1 and psi=GHZ3 or W3 in the statements. -/
def noisyQubits (psi : EuclideanSpace ℂ (HomBasis 3 2)) (p : ℝ) :
    Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ :=
  (p : ℂ) • pureDensity psi + (((1-p)/8 : ℝ) : ℂ) • 1

/-- Partial transpose on A in the computational basis, keeping B,C fixed (PDF p.4). -/
def partialTransposeA (rho : Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ) :
    Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ :=
  fun a b => rho (Function.update a 0 (b 0)) (Function.update b 0 (a 0))

/-- Logarithmic negativity E_N(A:BC), not (trace norm - 1)/2 (PDF p.4, Fig.2). -/
def logarithmicNegativity (rho : Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ) : ℝ :=
  Real.logb 2 (traceNorm (partialTransposeA rho))

/-- Independent choice of one local orthonormal qubit basis at each party
(PDF p.5, (16)–(18)). -/
abbrev LocalBases := Fin 3 → Matrix.unitaryGroup (Fin 2) ℂ

/-- Product rank-one outcome projector on measured parties s, identity elsewhere
(PDF p.5). Outcomes have NO coordinates for unmeasured parties. -/
def measurementProjector (U : LocalBases) (s : Finset (Fin 3))
    (z : SubBasis (fun _ : Fin 3 => Fin 2) s) :
    Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ :=
  fun a b => ∏ i, if hi : i ∈ s then
    (U i : Matrix (Fin 2) (Fin 2) ℂ) (a i) (z ⟨i,hi⟩) *
      conj ((U i : Matrix (Fin 2) (Fin 2) ℂ) (b i) (z ⟨i,hi⟩))
    else if a i = b i then 1 else 0

/-- Nonselective local projective measurement (PDF p.5, below (18)). -/
def postMeasurement (U : LocalBases) (s : Finset (Fin 3))
    (rho : Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ) :
    Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ :=
  ∑ z : SubBasis (fun _ : Fin 3 => Fin 2) s,
    measurementProjector U s z * rho * measurementProjector U s z

/-- Choice of information functional for the two panels of Figure 3 (PDF p.5). -/
def discordScore (alternative : Bool)
    (rho : Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ) : ℝ :=
  if alternative then alternativeOn rho Finset.univ else conventionalOn rho Finset.univ

/-- Optimized information loss, with one joint optimization over independent local
bases on s (PDF p.5,(16)–(18)). For density inputs the value set is nonempty,
bounded, and compact, so sSup equals the printed maximum. -/
def discord (alternative : Bool) (s : Finset (Fin 3))
    (rho : Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ) : ℝ :=
  discordScore alternative rho - sSup {v : ℝ | ∃ U : LocalBases,
    v = discordScore alternative (postMeasurement U s rho)}

/-! Small sanity checks for the constructed adapters. -/

example {n : ℕ} {D : Fin n → Type} (s : Finset (Fin n)) (x : RegisterBasis D)
    (i : {i : Fin n // i ∈ s}) : restrictLabel s x i = x i.val := rfl

example {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (s : Finset (Fin n)) : reducedDensity (0 : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) s = 0 := by
  ext a b
  simp [reducedDensity, QAlgorithms.Papers.Independent.Claimed50.P33.registerMarginal,
    QAlgorithms.Papers.Independent.Claimed50.P33.trivialExtension]

example {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) :
    marginalEntropyBits rho s = QAlgorithms.Papers.Independent.Claimed50.P33.entropyAt
      (QAlgorithms.Papers.Independent.Claimed50.P33.trivialExtension rho) s := rfl

example {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : alternativeOn rho ∅ = 0 := by
  simp [alternativeOn]

example {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : commonOn rho ∅ = 0 := by
  unfold commonOn
  apply Finset.sum_eq_zero
  intro t ht
  have hsubset : t ⊆ (∅ : Finset (Fin n)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp ht).2
  have hfalse : False := by simpa using hsubset hi
  exact hfalse.elim

example (x : HomBasis 3 2) : dickeQubitVector 3 1 x =
    QAlgorithms.Papers.Independent.Information100.P22.dicke (I := Fin 3) 1
      (fun i => x i == 1) := rfl

example : antisymmetric ![0,1,2] = ((Real.sqrt 6)⁻¹ : ℂ) := by
  simp [antisymmetric]

example : cluster ![1,1,1,1] = -(1/2 : ℂ) := by
  have h0 : (![1,1,1,1] : HomBasis 4 2) ≠ ![0,0,0,0] := by
    intro h
    have hh := congrFun h 0
    change (1 : Fin 2) = 0 at hh
    exact (by norm_num : (1 : Fin 2) ≠ 0) hh
  have h1 : (![1,1,1,1] : HomBasis 4 2) ≠ ![0,0,1,1] := by
    intro h
    have hh := congrFun h 0
    change (1 : Fin 2) = 0 at hh
    exact (by norm_num : (1 : Fin 2) ≠ 0) hh
  have h2 : (![1,1,1,1] : HomBasis 4 2) ≠ ![1,1,0,0] := by
    intro h
    have hh := congrFun h 2
    change (1 : Fin 2) = 0 at hh
    exact (by norm_num : (1 : Fin 2) ≠ 0) hh
  simp [cluster, h0, h1, h2]

example (psi : EuclideanSpace ℂ (HomBasis 3 2)) : noisyQubits psi 1 = pureDensity psi := by
  simp [noisyQubits]

example : partialTransposeA 0 = 0 := rfl

example (U : LocalBases) (s : Finset (Fin 3)) : postMeasurement U s 0 = 0 := by
  simp [postMeasurement]

example (U : LocalBases) (z : SubBasis (fun _ : Fin 3 => Fin 2) ∅)
    (a : HomBasis 3 2) : measurementProjector U ∅ z a a = 1 := by
  simp [measurementProjector]

example (rho : Matrix (RegisterBasis (fun _ : Fin 0 => Unit))
    (RegisterBasis (fun _ : Fin 0 => Unit)) ℂ) (a b : RegisterBasis (fun _ : Fin 0 => Unit)) :
    singletonProduct rho a b = 1 := by
  simp [singletonProduct]

example (rho : Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ) :
    discordScore true rho = alternativeOn rho Finset.univ := rfl

example {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) :
    conventionalOn rho ∅ = -marginalEntropyBits rho ∅ := by
  simp [conventionalOn]

example (alternative : Bool) (s : Finset (Fin 3))
    (rho : Matrix (HomBasis 3 2) (HomBasis 3 2) ℂ) :
    discord alternative s rho = discordScore alternative rho -
      sSup {v : ℝ | ∃ U : LocalBases,
        v = discordScore alternative (postMeasurement U s rho)} := rfl

end QAlgorithms.Papers.Independent.Support50.P43


