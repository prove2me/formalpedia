-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19
-- name    : QAlgorithms_Papers_Independent_Advance50_P19
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:54:24.417204+00:00
-- url     : https://prove2.me/theorems/a2bf8720-9bb4-4a83-b264-6d0af0fd27cd
-- title:
--   Definitions for Degradability of Fermionic Gaussian Channels
-- statement:
--   The objects the formalized statements of *Degradability of Fermionic Gaussian Channels* (arXiv:1604.01954) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Major`: PDF p.1: two Majorana directions per fermionic mode.
--   - `CARSystem`: PDF p.1: an irreducible CAR representation, on the actual 2^n-dimensional Fock space. No chosen vacuum orbit restricts the allowed parity sector.
--   - `monomial`: PDF p.1: ordered product; the empty Majorana monomial is the identity.
--   - `totalFermionParity`: PDF pp.1,8,11: total parity, with a harmless fixed overall sign convention.
--   - `IsFermionicState`: PDF pp.1,8,11: physical fermionic densities commute with total parity; coherent superpositions across opposite total parity are excluded.
--   - `majoranaContraction`: PDF p.1: two-point Majorana contraction.
--   - `wick`: PDF p.1, Wick's rule: pair the first operator with position j+1, with sign (-1)^j, and recurse. Sufficient fuel is the list length; the zero contraction of every odd list is part of the definition.
--   - `IsGaussianState`: PDF p.1: normalized, parity-preserving Gaussian states, including pure occupied modes and mixtures. Wick's rule is required on every monomial.
--   - `fermionicCovariance`: PDF p.1, Eq.(1): real covariance matrix, with the paper's +i/2 convention.
--   - `fermionicNoiseContraction`: PDF p.2, Eq.(3): contractions of the independent Gaussian noise in the Heisenberg expansion, C_ij = (I-AA^T)_ij - i B_ij. The real symmetric part is necessary even when B=0; it enforces the output CAR.
--   - `gaussianObservable`: PDF p.2, Eq.(3), canonical full CAR extension: expand each output Majorana into system plus independent Gaussian noise; move system factors left with the fermionic sign, and contract the noise by Wick's rule. This gives an actual observable, rather than an unspecified covariance-only map.
--   - `HasFermionicGaussianAction`: PDF p.2, Eq.(3): canonical Gaussian action on the FULL operator algebra. Testing all X and all monomials specifies every matrix entry, including the odd operator sector; Gaussian-state spanning is not assumed for that sector.
--   - `IsFGC`: PDF p.2, Eqs.(3-4): a genuine CPTP fermionic Gaussian channel, not a free affine action on covariance matrices. B is real skew symmetric.
--   - `HasReceiverDilation`: PDF pp.2,7: both partial traces use this SAME pure-environment isometry. The environment is a Hilbert-space register, not a freely chosen second channel.
--   - `Degrades`: PDF pp.2,7: arbitrary CPTP postprocessing, with equality on all operators.
--   - `ChannelDegradable`: PDF pp.2,7: ordinary channel degradability for some pure Stinespring dilation. The accepted fixed-dilation predicate supplies unrestricted CPTP postprocessing. A nonzero finite environment can always be indexed by Fin(e+1).
--   - `ChannelAntidegradable`: PDF pp.2,8: ordinary channel antidegradability uses the accepted reversed postprocessing arrow.
--   - `normalizedChoiDensity`: PDF p.9: normalized ordinary Choi density. Its rank is independent of the reference basis and of the Gaussian choice of maximally entangled vector.
--   - `choiModeRank`: PDF p.9: mode rank is log_2 of the ACTUAL ordinary Choi rank. S9 asserts separately that that rank is exactly a power of two; it is not defined by the desired kernel formula. On a zero map this total auxiliary returns 0.
--   - `nullityC`: Complex kernel dimension, including empty matrices.
--   - `nullityR`: Real kernel dimension, including empty matrices.
--   - `fermionicCPMatrix`: PDF p.2, Eq.(4): complete-positivity matrix, with the source's -iB sign.
--   - `choiCovariance`: PDF pp.2,9: canonical Gaussian Choi covariance. The Choi density itself is independently constructed as normalizedChoiDensity T.
--   - `normalizedNoise`: PDF pp.2-3,9: normalized noise, using the spectral Moore--Penrose inverse square root, with zero inverse on the kernel. Complex matrices merely provide Mathlib's Hermitian functional calculus; the resulting entries are real.
--   - `IsPhaseOrthogonal`: PDF pp.2,7,9: all local phase changes may be orthogonal, including parity-normalizing reflections; no unsupported SO requirement is imposed.
--   - `ImplementsCAR`: PDF pp.1-3,9: actual unitary implementation of a real phase-space operation. The Heisenberg action fixes the covariance transformation sign.
--   - `attenuation`: PDF p.4: one-mode attenuation, in a Fock basis whose target pure state has covariance J. Both Kraus operators are specified on the full qubit algebra.
--   - `capacityObjective`: PDF p.4: the one-parameter coherent-information objective.
--   - `copyDensity`: PDF p.12: n=2^N independent copies, ordered by copy then original mode. Since rho is even, the product density is the graded Fock product as well as the displayed ordinary matrix product.
--   - `copyMajorana`: PDF pp.11-12: the CAR operator of direction r in copy j, with the Jordan--Wigner parity strings of all PRECEDING copies. Ordinary qubit swaps are never substituted for this Fock identification.
--   - `sylvesterCoefficient`: PDF p.12: entries of H_2 tensor ... tensor H_2 divided by sqrt(2^N). Bits are read in the same order for rows and columns, so reversing the tensor order has no effect. N=0 gives the one by one identity.
--   - `IsGaussificationMixer`: PDF p.12: the ACTUAL mixer, specified by its action on the copied CAR operators. The identical real mixer is applied to both Majoranas of every original mode; hence it is passive and local for every original party split. No convergence or Gaussian optimality assumption is hidden in this predicate.
--   - `insertFermionicCopy`: Fill in the retained copy and all spectator occupations for a partial trace.
--   - `mixedCopyMarginal`: PDF p.12: the actual reduced state of copy j after applying U to the independent product input. Evenness makes this contiguous-copy partial trace the fermionic marginal, without discarding Fock regrouping signs.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, https://arxiv.org/abs/1604.01954v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Greplova--Giedke, arXiv:1604.01954v2. Page numbers are PDF pages.
Accepted finite-channel primitives and paper-local CAR definitions fix the full
linear Gaussian extension, including odd Majorana monomials. Physical states are normalized, positive and parity invariant.
Degrading maps are arbitrary CPTP maps on the full matrix algebra.
S1(i) includes the missing Z >= 0 clause; S2 corrects n by n to 2n by 2n.
Deferred nodes and reasons are recorded in the unit's HARD.md and GAPS.json.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1: two Majorana directions per fermionic mode. -/
abbrev Major (n : ℕ) := Fin (2 * n)

/-- PDF p.1: an irreducible CAR representation, on the actual 2^n-dimensional
Fock space. No chosen vacuum orbit restricts the allowed parity sector. -/
structure CARSystem (n : ℕ) where
  majorana : Major n → Matrix (Qubits n) (Qubits n) ℂ
  hermitian : ∀ i, (majorana i).IsHermitian
  anticommutation : ∀ i j,
    majorana i * majorana j + majorana j * majorana i =
      ((if i = j then 2 else 0) : ℂ) • (1 : Matrix (Qubits n) (Qubits n) ℂ)

/-- PDF p.1: ordered product; the empty Majorana monomial is the identity. -/
def monomial {n : ℕ} (s : CARSystem n) (l : List (Major n)) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (l.map s.majorana).prod

/-- PDF pp.1,8,11: total parity, with a harmless fixed overall sign convention. -/
def totalFermionParity {n : ℕ} (s : CARSystem n) : Matrix (Qubits n) (Qubits n) ℂ :=
  (Complex.I ^ n) • monomial s (List.finRange (2 * n))

/-- PDF pp.1,8,11: physical fermionic densities commute with total parity;
coherent superpositions across opposite total parity are excluded. -/
def IsFermionicState {n : ℕ} (s : CARSystem n)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  IsDensityMatrix rho ∧ rho * totalFermionParity s = totalFermionParity s * rho

/-- PDF p.1: two-point Majorana contraction. -/
def majoranaContraction {n : ℕ} (s : CARSystem n)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (i j : Major n) : ℂ :=
  (rho * (s.majorana i * s.majorana j)).trace

/-- PDF p.1, Wick's rule: pair the first operator with position j+1,
with sign (-1)^j, and recurse. Sufficient fuel is the list length; the zero
contraction of every odd list is part of the definition. -/
def wick {I : Type*} (C : I → I → ℂ) : ℕ → List I → ℂ
  | 0, [] => 1
  | 0, _ :: _ => 0
  | _ + 1, [] => 1
  | fuel + 1, i :: tail =>
      ∑ j : Fin tail.length,
        (-1 : ℂ) ^ j.val * C i (tail.get j) * wick C fuel (tail.eraseIdx j.val)

/-- PDF p.1: normalized, parity-preserving Gaussian states, including pure
occupied modes and mixtures. Wick's rule is required on every monomial. -/
def IsGaussianState {n : ℕ} (s : CARSystem n)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  IsFermionicState s rho ∧ ∀ l : List (Major n),
    (rho * monomial s l).trace = wick (majoranaContraction s rho) l.length l

/-- PDF p.1, Eq.(1): real covariance matrix, with the paper's +i/2 convention. -/
def fermionicCovariance {n : ℕ} (s : CARSystem n)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Major n) (Major n) ℝ :=
  fun i j => ((Complex.I / 2) *
    (rho * (s.majorana i * s.majorana j - s.majorana j * s.majorana i)).trace).re

/-- PDF p.2, Eq.(3): contractions of the independent Gaussian noise in the
Heisenberg expansion, C_ij = (I-AA^T)_ij - i B_ij. The real symmetric part
is necessary even when B=0; it enforces the output CAR. -/
def fermionicNoiseContraction {n m : ℕ} (A : Matrix (Major m) (Major n) ℝ)
    (B : Matrix (Major m) (Major m) ℝ) : Major m → Major m → ℂ :=
  fun i j =>
    ((((1 : Matrix (Major m) (Major m) ℝ) - A * A.transpose) i j : ℝ) : ℂ) -
      Complex.I * (B i j : ℂ)

/-- PDF p.2, Eq.(3), canonical full CAR extension: expand each output
Majorana into system plus independent Gaussian noise; move system factors left
with the fermionic sign, and contract the noise by Wick's rule. This gives an
actual observable, rather than an unspecified covariance-only map. -/
def gaussianObservable {n m : ℕ} (s : CARSystem n)
    (A : Matrix (Major m) (Major n) ℝ) (B : Matrix (Major m) (Major m) ℝ)
    (l : List (Major m)) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Fin l.length)).powerset,
    let selected := (List.finRange l.length).filter (fun p => p ∈ S)
    let remaining := (List.finRange l.length).filter (fun p => p ∉ S)
    let crossings := ∑ i : Fin l.length,
      if i ∉ S then (Finset.univ.filter (fun j : Fin l.length => j ∈ S ∧ i < j)).card
      else 0
    ((-1 : ℂ) ^ crossings *
      wick (fermionicNoiseContraction A B) l.length (remaining.map (fun p => l.get p))) •
      (selected.map (fun p => ∑ j : Major n,
        (A (l.get p) j : ℂ) • s.majorana j)).prod

/-- PDF p.2, Eq.(3): canonical Gaussian action on the FULL operator algebra.
Testing all X and all monomials specifies every matrix entry, including the odd
operator sector; Gaussian-state spanning is not assumed for that sector. -/
def HasFermionicGaussianAction {n m : ℕ} (s : CARSystem n) (t : CARSystem m)
    (T : Superop (Qubits n) (Qubits m)) (A : Matrix (Major m) (Major n) ℝ)
    (B : Matrix (Major m) (Major m) ℝ) : Prop :=
  ∀ (X : Matrix (Qubits n) (Qubits n) ℂ) (l : List (Major m)),
    (T X * monomial t l).trace = (X * gaussianObservable s A B l).trace

/-- PDF p.2, Eqs.(3-4): a genuine CPTP fermionic Gaussian channel, not a
free affine action on covariance matrices. B is real skew symmetric. -/
def IsFGC {n m : ℕ} (s : CARSystem n) (t : CARSystem m)
    (T : Superop (Qubits n) (Qubits m)) (A : Matrix (Major m) (Major n) ℝ)
    (B : Matrix (Major m) (Major m) ℝ) : Prop :=
  IsChannel T ∧ B.transpose = -B ∧ HasFermionicGaussianAction s t T A B

/-- PDF pp.2,7: both partial traces use this SAME pure-environment isometry.
The environment is a Hilbert-space register, not a freely chosen second channel. -/
def HasReceiverDilation {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] (T : Superop A B) (V : Matrix (B × E) A ℂ) : Prop :=
  IsIsometry V ∧ ∀ X, T X = receiverChannel V X

/-- PDF pp.2,7: arbitrary CPTP postprocessing, with equality on all operators. -/
def Degrades {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq B] (T : Superop A B) (C : Superop A E) : Prop :=
  ∃ D : Superop B E, IsChannel D ∧ ∀ X, D (T X) = C X

/-- PDF pp.2,7: ordinary channel degradability for some pure Stinespring dilation.
The accepted fixed-dilation predicate supplies unrestricted CPTP postprocessing.
A nonzero finite environment can always be indexed by Fin(e+1). -/
def ChannelDegradable {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (T : Superop A B) : Prop :=
  IsChannel T ∧ ∃ e : ℕ, ∃ V : Matrix (B × Fin (e + 1)) A ℂ,
    HasReceiverDilation T V ∧
      QAlgorithms.Papers.Independent.Information100.P67.IsDegradable V

/-- PDF pp.2,8: ordinary channel antidegradability uses the accepted reversed postprocessing arrow. -/
def ChannelAntidegradable {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (T : Superop A B) : Prop :=
  IsChannel T ∧ ∃ e : ℕ, ∃ V : Matrix (B × Fin (e + 1)) A ℂ,
    HasReceiverDilation T V ∧
      QAlgorithms.Papers.Independent.Information100.P67.IsAntidegradable V

/-- PDF p.9: normalized ordinary Choi density. Its rank is independent of
the reference basis and of the Gaussian choice of maximally entangled vector. -/
def normalizedChoiDensity {A B : Type*} [Fintype A] [DecidableEq A] (T : Superop A B) :
    Matrix (B × A) (B × A) ℂ :=
  fun i j => (Fintype.card A : ℂ)⁻¹ *
    QAlgorithms.Papers.Independent.Information100.P34.choi T (i.2, i.1) (j.2, j.1)

/-- PDF p.9: mode rank is log_2 of the ACTUAL ordinary Choi rank. S9
asserts separately that that rank is exactly a power of two; it is not defined
by the desired kernel formula. On a zero map this total auxiliary returns 0. -/
def choiModeRank {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (T : Superop A B) : ℕ :=
  Nat.log 2 (Matrix.rank (normalizedChoiDensity T))

/-- Complex kernel dimension, including empty matrices. -/
def nullityC {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker M.mulVecLin)

/-- Real kernel dimension, including empty matrices. -/
def nullityR {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker M.mulVecLin)

/-- PDF p.2, Eq.(4): complete-positivity matrix, with the source's -iB sign. -/
def fermionicCPMatrix {n m : ℕ} (A : Matrix (Major m) (Major n) ℝ)
    (B : Matrix (Major m) (Major m) ℝ) : Matrix (Major m) (Major m) ℂ :=
  (1 - A * A.transpose).map Complex.ofReal - Complex.I • B.map Complex.ofReal

/-- PDF pp.2,9: canonical Gaussian Choi covariance. The Choi density itself
is independently constructed as normalizedChoiDensity T. -/
def choiCovariance {n m : ℕ} (A : Matrix (Major m) (Major n) ℝ)
    (B : Matrix (Major m) (Major m) ℝ) :
    Matrix (Major m ⊕ Major n) (Major m ⊕ Major n) ℝ :=
  Matrix.fromBlocks B A (-A.transpose) 0

/-- PDF pp.2-3,9: normalized noise, using the spectral Moore--Penrose
inverse square root, with zero inverse on the kernel. Complex matrices merely
provide Mathlib's Hermitian functional calculus; the resulting entries are real. -/
def normalizedNoise {n m : ℕ} (A : Matrix (Major m) (Major n) ℝ)
    (B : Matrix (Major m) (Major m) ℝ) : Matrix (Major m) (Major m) ℂ :=
  let R := cfc (fun x : ℝ => (Real.sqrt x)⁻¹)
    ((1 - A * A.transpose).map Complex.ofReal)
  R * B.map Complex.ofReal * R

/-- PDF pp.2,7,9: all local phase changes may be orthogonal, including
parity-normalizing reflections; no unsupported SO requirement is imposed. -/
def IsPhaseOrthogonal {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℝ) : Prop :=
  O.transpose * O = 1 ∧ O * O.transpose = 1

/-- PDF pp.1-3,9: actual unitary implementation of a real phase-space
operation. The Heisenberg action fixes the covariance transformation sign. -/
def ImplementsCAR {n : ℕ} (s : CARSystem n) (O : Matrix (Major n) (Major n) ℝ)
    (U : Matrix.unitaryGroup (Qubits n) ℂ) : Prop :=
  IsPhaseOrthogonal O ∧ ∀ i,
    (U : Matrix (Qubits n) (Qubits n) ℂ).conjTranspose * s.majorana i *
      (U : Matrix (Qubits n) (Qubits n) ℂ) =
        ∑ j, (O i j : ℂ) • s.majorana j

/-- PDF p.4: one-mode attenuation, in a Fock basis whose target pure state
has covariance J. Both Kraus operators are specified on the full qubit algebra. -/
def attenuation (p : ℝ) : Superop Bool Bool :=
  krausApply (fun j : Bool => if j then
    (fun a b => if a = false ∧ b = true then (Real.sqrt p : ℂ) else 0)
    else (fun a b => if a = b then
      (if a then (Real.sqrt (1 - p) : ℂ) else 1) else 0))

/-- PDF p.4: the one-parameter coherent-information objective. -/
def capacityObjective (p lambda : ℝ) : ℝ :=
  binEntropy2 ((1 - p) * (1 - lambda) / 2) -
    binEntropy2 (p * (1 - lambda) / 2)

/-- PDF p.12: n=2^N independent copies, ordered by copy then original
mode. Since rho is even, the product density is the graded Fock product as
well as the displayed ordinary matrix product. -/
def copyDensity {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ) (N : ℕ) :
    Matrix (Fin (2 ^ N) → Qubits n) (Fin (2 ^ N) → Qubits n) ℂ :=
  fun x y => ∏ j, rho (x j) (y j)

/-- PDF pp.11-12: the CAR operator of direction r in copy j, with the
Jordan--Wigner parity strings of all PRECEDING copies. Ordinary qubit swaps
are never substituted for this Fock identification. -/
def copyMajorana {n : ℕ} (s : CARSystem n) (N : ℕ)
    (j : Fin (2 ^ N)) (r : Major n) :
    Matrix (Fin (2 ^ N) → Qubits n) (Fin (2 ^ N) → Qubits n) ℂ :=
  fun x y => ∏ k, if k < j then totalFermionParity s (x k) (y k)
    else if k = j then s.majorana r (x k) (y k)
    else if x k = y k then 1 else 0

/-- PDF p.12: entries of H_2 tensor ... tensor H_2 divided by sqrt(2^N).
Bits are read in the same order for rows and columns, so reversing the tensor
order has no effect. N=0 gives the one by one identity. -/
def sylvesterCoefficient (N : ℕ) (j k : Fin (2 ^ N)) : ℝ :=
  (-1 : ℝ) ^ ((Finset.range N).filter
    (fun r => j.val.testBit r = true ∧ k.val.testBit r = true)).card /
      Real.sqrt (2 ^ N : ℝ)

/-- PDF p.12: the ACTUAL mixer, specified by its action on the copied CAR
operators. The identical real mixer is applied to both Majoranas of every
original mode; hence it is passive and local for every original party split.
No convergence or Gaussian optimality assumption is hidden in this predicate. -/
def IsGaussificationMixer {n : ℕ} (s : CARSystem n) (N : ℕ)
    (U : Matrix.unitaryGroup (Fin (2 ^ N) → Qubits n) ℂ) : Prop :=
  ∀ (j : Fin (2 ^ N)) (r : Major n),
    (U : Matrix _ _ ℂ).conjTranspose * copyMajorana s N j r *
      (U : Matrix _ _ ℂ) =
        ∑ k, (sylvesterCoefficient N j k : ℂ) • copyMajorana s N k r

/-- Fill in the retained copy and all spectator occupations for a partial trace. -/
def insertFermionicCopy {n N : ℕ} (j : Fin (2 ^ N)) (a : Qubits n)
    (z : {k : Fin (2 ^ N) // k ≠ j} → Qubits n) : Fin (2 ^ N) → Qubits n :=
  fun k => if h : k = j then a else z ⟨k, h⟩

/-- PDF p.12: the actual reduced state of copy j after applying U to the
independent product input. Evenness makes this contiguous-copy partial trace
the fermionic marginal, without discarding Fock regrouping signs. -/
def mixedCopyMarginal {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (N : ℕ) (U : Matrix.unitaryGroup (Fin (2 ^ N) → Qubits n) ℂ)
    (j : Fin (2 ^ N)) : Matrix (Qubits n) (Qubits n) ℂ :=
  let mixed := (U : Matrix _ _ ℂ) * copyDensity rho N * (U : Matrix _ _ ℂ).conjTranspose
  fun a b => ∑ z : {k : Fin (2 ^ N) // k ≠ j} → Qubits n,
    mixed (insertFermionicCopy j a z) (insertFermionicCopy j b z)

/-- Sanity: zero mixing rounds give the identity coefficient, not 1/sqrt(0). -/
example : sylvesterCoefficient 0 0 0 = 1 := by
  norm_num [sylvesterCoefficient]

/-- Sanity: empty monomials are identities, also at zero modes. -/
example {n : ℕ} (s : CARSystem n) : monomial s [] = 1 := by
  rfl

/-- Sanity: Wick normalization at the empty list is exactly 1. -/
example {I : Type*} (C : I → I → ℂ) : wick C 0 [] = 1 := by
  rfl

/-- Sanity: the one-operator moment is zero, without a vacuum-only restriction. -/
example {I : Type*} (C : I → I → ℂ) (i : I) : wick C 1 [i] = 0 := by
  simp [wick]

/-- Sanity: entropy includes the endpoint 0 log 0 without an undefined value. -/
example : binEntropy2 0 = 0 := by
  simp [binEntropy2]

end QAlgorithms.Papers.Independent.Advance50.P19


