-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
-- name    : QAlgorithms_Papers_Independent_Information100_P75
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:06:45.471565+00:00
-- url     : https://prove2.me/theorems/7afb35a2-6c7e-451d-8ab0-f87257aae8ba
-- title:
--   Definitions for Parallel quantum channel discrimination and numerical ranges in tensor product subspaces
-- statement:
--   The objects the formalized statements of *Parallel quantum channel discrimination and numerical ranges in tensor product subspaces* (arXiv:2609.20781) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mat`
--   - `phase`: PDF p.3: a scalar rotation through an angle measured in radians.
--   - `hermitianReal`: PDF p.3: Hermitian real part, not entrywise real part.
--   - `blend`: PDF p.3, (2.1): the two PSD parts with opposite phases.
--   - `omega`: PDF p.3, (2.1). Outside the source's parameter domain this set is empty.
--   - `numericalRange`: PDF p.3: the density-matrix characterization of the numerical range.
--   - `gammaSet`: PDF p.3: angular feasibility in the fixed half-open interval [-π,π).
--   - `gammaLength`: PDF p.3: Lebesgue length in radians; the set is contained in a finite interval.
--   - `width`: PDF p.3, (2.2): ordinary width, with the explicit numerical-range-zero branch.
--   - `closedWidth`: PDF p.6, Definition 8: overlined width. Only applied to nonzero matrices in results. Its unused total extension at zero is π-|Γ_0|=-π, not ordinary width zero.
--   - `infWidth`: PDF p.3, (2.3): infimum over a complex subspace, which always contains zero. The real infimum is over a nonempty bounded set (ordinary widths lie in [0,π]).
--   - `traceModulusObjective`: PDF p.3, (3.1): sum of complex moduli of trace pairings.
--   - `sdpValue`: PDF p.3, (3.1): the optimal value, with attainment asserted in nativeSdp. All theorem uses have 0≤a<π and a positive matrix dimension.
--   - `tensorSpace`: PDF p.3: tensor subspace is the span of simple Kronecker tensors.
--   - `Register`: PDF p.4: basis labels for a list of finite-dimensional systems.
--   - `listTensor`: PDF p.4, (3.8): finite tensor product, with factor i on register i.
--   - `listTensorSpace`: PDF p.4: span of all products with one member from each subspace.
--   - `tensorPower`: PDF pp.2,4: tensor power subspace; theorems restrict to N≥1.
--   - `witnessAngle`: PDF p.4, (3.2).
--   - `mixedIdentity`: PDF p.4: the specified convention for a zero-width subspace.
--   - `WitnessParts`: PDF p.4, (3.3): admissible PSD parts when the width is positive. At zero width only the conventional identity probe is used, and the unused parts are fixed to zero.
--   - `probe`: PDF p.4: probe computed from admissible parts, with the zero-width convention.
--   - `pairMass`: PDF p.4, (3.6): real positive normalization is the sum of the two PSD-part traces.
--   - `saturatedNumerator`: PDF p.4, (3.7): Hermitian numerator for the saturated case.
--   - `combineProbe`: PDF p.4, (3.5)–(3.7), with the normalization specified in the proof p.9. Neither division is used without a positivity conclusion in tensorWidthConstruction.
--   - `ValidProbe`: PDF p.4 convention and p.8 proof: positive width gives a relaxed annihilator; zero width gives the conventional identity, with no annihilator assertion.
--   - `betaSpace`: PDF p.2: the two explicit generators of the conjecture subspace.
--   - `epigraphBlock`: PDF p.6, (A.1): Hermitian Schur-complement block, with conjugate lower-left entry.
--   - `NativeFeasible`: PDF p.6, (A.1): native SDP feasible variables, with real epigraph scalars.
--   - `nativeValue`: PDF p.6, (A.1): native optimal value. Attainment is a conclusion, never a premise.
--   - `bisect`: PDF p.4: exact-value bisection, starting with [0,π]. The test angle is π−midpoint.
--   - `crossSpace`: PDF pp.2,5: the Kraus cross-product span B_l† A_k (order matters).
--   - `ParallelPerfect`: PDF p.2: operational parallel discrimination. One shared normalized probe (possibly entangled with a positive finite noiseless reference) gives orthogonal output supports. The unknown choice Φ versus Ψ cannot affect the probe. No interleaved operation is present.
--   - `minimumCopies`: PDF p.5, (3.9): the least positive successful copy count, conditional in all uses on existence of a positive successful count. The total fallback is zero.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, https://arxiv.org/abs/2609.20781v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel

/-!
Statements from Bílek, Lewandowska and Kukulski, arXiv:2609.20781v1.
All page numbers below are PDF page numbers. Local definitions are specific to this paper.
The ordinary width and the overlined width of Definition 8 are deliberately distinct.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical
open scoped ComplexConjugate ComplexOrder Matrix
open MeasureTheory

abbrev Mat (ι : Type*) := Matrix ι ι ℂ

/-- PDF p.3: a scalar rotation through an angle measured in radians. -/
def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

/-- PDF p.3: Hermitian real part, not entrywise real part. -/
def hermitianReal {ι : Type*} (X : Mat ι) : Mat ι := (2 : ℂ)⁻¹ • (X + Xᴴ)

/-- PDF p.3, (2.1): the two PSD parts with opposite phases. -/
def blend {ι : Type*} (a : ℝ) (P Q : Mat ι) : Mat ι :=
  phase (a / 2) • P + phase (-a / 2) • Q

/-- PDF p.3, (2.1). Outside the source's parameter domain this set is empty. -/
def omega {ι : Type*} [Fintype ι] (a : ℝ) : Set (Mat ι) :=
  {R | 0 ≤ a ∧ a < Real.pi ∧ ∃ P Q : Mat ι,
    P.PosSemidef ∧ Q.PosSemidef ∧ P.trace + Q.trace = 1 ∧ R = blend a P Q}

/-- PDF p.3: the density-matrix characterization of the numerical range. -/
def numericalRange {ι : Type*} [Fintype ι] (X : Mat ι) : Set ℂ :=
  {z | ∃ R : Mat ι, IsDensityMatrix R ∧ (R * X).trace = z}

/-- PDF p.3: angular feasibility in the fixed half-open interval [-π,π). -/
def gammaSet {ι : Type*} [Fintype ι] (X : Mat ι) : Set ℝ :=
  {t | -Real.pi ≤ t ∧ t < Real.pi ∧ (hermitianReal (phase t • X)).PosSemidef}

/-- PDF p.3: Lebesgue length in radians; the set is contained in a finite interval. -/
def gammaLength {ι : Type*} [Fintype ι] (X : Mat ι) : ℝ :=
  (volume (gammaSet X)).toReal

/-- PDF p.3, (2.2): ordinary width, with the explicit numerical-range-zero branch. -/
def width {ι : Type*} [Fintype ι] (X : Mat ι) : ℝ :=
  if 0 ∈ numericalRange X then Real.pi else Real.pi - gammaLength X

/-- PDF p.6, Definition 8: overlined width. Only applied to nonzero matrices in results.
Its unused total extension at zero is π-|Γ_0|=-π, not ordinary width zero. -/
def closedWidth {ι : Type*} [Fintype ι] (X : Mat ι) : ℝ := Real.pi - gammaLength X

/-- PDF p.3, (2.3): infimum over a complex subspace, which always contains zero.
The real infimum is over a nonempty bounded set (ordinary widths lie in [0,π]). -/
def infWidth {ι : Type*} [Fintype ι] (M : Submodule ℂ (Mat ι)) : ℝ :=
  sInf (width '' (M : Set (Mat ι)))

/-- PDF p.3, (3.1): sum of complex moduli of trace pairings. -/
def traceModulusObjective {ι : Type*} [Fintype ι] {k : ℕ} (X : Fin k → Mat ι) (R : Mat ι) : ℝ :=
  ∑ j, ‖(R * X j).trace‖

/-- PDF p.3, (3.1): the optimal value, with attainment asserted in nativeSdp.
All theorem uses have 0≤a<π and a positive matrix dimension. -/
def sdpValue {ι : Type*} [Fintype ι] {k : ℕ} (a : ℝ) (X : Fin k → Mat ι) : ℝ :=
  sInf (traceModulusObjective X '' omega a)

/-- PDF p.3: tensor subspace is the span of simple Kronecker tensors. -/
def tensorSpace {ι κ : Type*} (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ)) :
    Submodule ℂ (Mat (ι × κ)) :=
  Submodule.span ℂ {T | ∃ X ∈ M, ∃ Y ∈ L, T = Matrix.kronecker X Y}

/-- PDF p.4: basis labels for a list of finite-dimensional systems. -/
abbrev Register {N : ℕ} (d : Fin N → ℕ) := (i : Fin N) → Fin (d i)

/-- PDF p.4, (3.8): finite tensor product, with factor i on register i. -/
def listTensor {N : ℕ} (d : Fin N → ℕ) (X : (i : Fin N) → Mat (Fin (d i))) :
    Mat (Register d) := fun x y => ∏ i, X i (x i) (y i)

/-- PDF p.4: span of all products with one member from each subspace. -/
def listTensorSpace {N : ℕ} (d : Fin N → ℕ)
    (M : (i : Fin N) → Submodule ℂ (Mat (Fin (d i)))) : Submodule ℂ (Mat (Register d)) :=
  Submodule.span ℂ {T | ∃ X : (i : Fin N) → Mat (Fin (d i)),
    (∀ i, X i ∈ M i) ∧ T = listTensor d X}

/-- PDF pp.2,4: tensor power subspace; theorems restrict to N≥1. -/
def tensorPower {ι : Type*} (M : Submodule ℂ (Mat ι)) (N : ℕ) :
    Submodule ℂ (Mat (Fin N → ι)) :=
  Submodule.span ℂ {T | ∃ X : Fin N → Mat ι,
    (∀ i, X i ∈ M) ∧ T = fun x y => ∏ i, X i (x i) (y i)}

/-- PDF p.4, (3.2). -/
def witnessAngle {ι : Type*} [Fintype ι] (M : Submodule ℂ (Mat ι)) : ℝ :=
  Real.pi - infWidth M

/-- PDF p.4: the specified convention for a zero-width subspace. -/
def mixedIdentity (ι : Type*) [Fintype ι] [DecidableEq ι] : Mat ι :=
  ((Fintype.card ι : ℂ)⁻¹) • 1

/-- PDF p.4, (3.3): admissible PSD parts when the width is positive. At zero width
only the conventional identity probe is used, and the unused parts are fixed to zero. -/
def WitnessParts {ι : Type*} [Fintype ι] (M : Submodule ℂ (Mat ι)) (P Q : Mat ι) : Prop :=
  (0 < infWidth M → P.PosSemidef ∧ Q.PosSemidef ∧ P.trace + Q.trace = 1 ∧
    ∀ X ∈ M, (blend (witnessAngle M) P Q * X).trace = 0) ∧
  (infWidth M = 0 → P = 0 ∧ Q = 0)

/-- PDF p.4: probe computed from admissible parts, with the zero-width convention. -/
def probe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Submodule ℂ (Mat ι)) (P Q : Mat ι) : Mat ι :=
  if infWidth M = 0 then mixedIdentity ι else blend (witnessAngle M) P Q

/-- PDF p.4, (3.6): real positive normalization is the sum of the two PSD-part traces. -/
def pairMass {ι κ : Type*} [Fintype ι] [Fintype κ] (P Q : Mat ι) (R S : Mat κ) : ℝ :=
  P.trace.re * R.trace.re + Q.trace.re * S.trace.re

/-- PDF p.4, (3.7): Hermitian numerator for the saturated case. -/
def saturatedNumerator {ι κ : Type*} (R : Mat ι) (S : Mat κ) : Mat (ι × κ) :=
  Matrix.kronecker R Sᴴ + Matrix.kronecker Rᴴ S

/-- PDF p.4, (3.5)–(3.7), with the normalization specified in the proof p.9.
Neither division is used without a positivity conclusion in tensorWidthConstruction. -/
def combineProbe {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ))
    (P Q : Mat ι) (R S : Mat κ) : Mat (ι × κ) :=
  if infWidth M = 0 ∨ infWidth L = 0 then
    Matrix.kronecker (probe M P Q) (probe L R S)
  else if infWidth M + infWidth L < Real.pi then
    ((pairMass P Q R S : ℂ)⁻¹) •
      blend (witnessAngle M + witnessAngle L - Real.pi)
        (Matrix.kronecker P R) (Matrix.kronecker Q S)
  else
    let H := saturatedNumerator (probe M P Q) (probe L R S)
    ((H.trace.re : ℂ)⁻¹) • H

/-- PDF p.4 convention and p.8 proof: positive width gives a relaxed annihilator;
zero width gives the conventional identity, with no annihilator assertion. -/
def ValidProbe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Submodule ℂ (Mat ι)) (R : Mat ι) : Prop :=
  (0 < infWidth M → R ∈ omega (witnessAngle M) ∧ ∀ X ∈ M, (R * X).trace = 0) ∧
  (infWidth M = 0 → R = mixedIdentity ι)

/-- PDF p.2: the two explicit generators of the conjecture subspace. -/
def betaSpace (b : ℝ) : Submodule ℂ (Mat (Fin 3)) :=
  Submodule.span ℂ {Matrix.diagonal ![1, phase b, 0], Matrix.diagonal ![0, 1, phase b]}

/-- PDF p.6, (A.1): Hermitian Schur-complement block, with conjugate lower-left entry. -/
def epigraphBlock (c : ℝ) (z : ℂ) : Mat (Fin 2) := !![(c : ℂ), z; conj z, (c : ℂ)]

/-- PDF p.6, (A.1): native SDP feasible variables, with real epigraph scalars. -/
def NativeFeasible {ι : Type*} [Fintype ι] {k : ℕ} (a : ℝ) (X : Fin k → Mat ι)
    (P Q : Mat ι) (c : Fin k → ℝ) : Prop :=
  P.PosSemidef ∧ Q.PosSemidef ∧ P.trace + Q.trace = 1 ∧
    ∀ j, (epigraphBlock (c j) ((blend a P Q * X j).trace)).PosSemidef

/-- PDF p.6, (A.1): native optimal value. Attainment is a conclusion, never a premise. -/
def nativeValue {ι : Type*} [Fintype ι] {k : ℕ} (a : ℝ) (X : Fin k → Mat ι) : ℝ :=
  sInf {v | ∃ P Q c, NativeFeasible a X P Q c ∧ v = ∑ j, c j}

/-- PDF p.4: exact-value bisection, starting with [0,π]. The test angle is π−midpoint. -/
def bisect {ι : Type*} [Fintype ι] {k : ℕ} (X : Fin k → Mat ι) : ℕ → ℝ × ℝ
  | 0 => (0, Real.pi)
  | t + 1 =>
    let I := bisect X t
    let mid := (I.1 + I.2) / 2
    if sdpValue (Real.pi - mid) X = 0 then (mid, I.2) else (I.1, mid)

/-- PDF pp.2,5: the Kraus cross-product span B_l† A_k (order matters). -/
def crossSpace {d s r t : ℕ} (A : Fin r → Matrix (Fin s) (Fin d) ℂ)
    (B : Fin t → Matrix (Fin s) (Fin d) ℂ) : Submodule ℂ (Mat (Fin d)) :=
  Submodule.span ℂ {X | ∃ k l, X = (B l)ᴴ * A k}

/-- PDF p.2: operational parallel discrimination. One shared normalized probe (possibly
entangled with a positive finite noiseless reference) gives orthogonal output supports.
The unknown choice Φ versus Ψ cannot affect the probe. No interleaved operation is present. -/
def ParallelPerfect {d s : ℕ} (Phi Psi : Superop (Fin d) (Fin s)) (N : ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ ∃ R : Mat (Fin a × (Fin N → Fin d)), IsDensityMatrix R ∧
    idTensorSuperop (R := Fin a) (piSuperop (fun _ : Fin N => Phi)) R *
      idTensorSuperop (R := Fin a) (piSuperop (fun _ : Fin N => Psi)) R = 0

/-- PDF p.5, (3.9): the least positive successful copy count, conditional in all uses
on existence of a positive successful count. The total fallback is zero. -/
def minimumCopies {d s : ℕ} (Phi Psi : Superop (Fin d) (Fin s)) : ℕ :=
  sInf {N | 1 ≤ N ∧ ParallelPerfect Phi Psi N}

/-! Sanity examples for the paper-local definitions. -/

example : phase 0 = 1 := by simp [phase]

example {ι : Type*} (P Q : Mat ι) : blend 0 P Q = P + Q := by simp [blend, phase]

example {ι : Type*} [Fintype ι] (R : Mat ι) :
    traceModulusObjective (fun j : Fin 0 => Fin.elim0 j) R = 0 := by simp [traceModulusObjective]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Submodule ℂ (Mat ι))
    (h : infWidth M = 0) (P Q : Mat ι) : probe M P Q = mixedIdentity ι := by simp [probe, h]

example : mixedIdentity (Fin 1) = 1 := by simp [mixedIdentity]

example (c : ℝ) (z : ℂ) : epigraphBlock c z 1 0 = conj z := by rfl

example {ι : Type*} [Fintype ι] {k : ℕ} (X : Fin k → Mat ι) : bisect X 0 = (0, Real.pi) := rfl

example {ι κ : Type*} (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ))
    (X : Mat ι) (hX : X ∈ M) (Y : Mat κ) (hY : Y ∈ L) :
    Matrix.kronecker X Y ∈ tensorSpace M L :=
  Submodule.subset_span ⟨X, hX, Y, hY, rfl⟩

end QAlgorithms.Papers.Independent.Information100.P75


