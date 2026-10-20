-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
-- name    : QAlgorithms_Papers_Independent_Dependency50_P24
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T16:07:59.1269+00:00
-- url     : https://prove2.me/theorems/e1d44d57-3871-4625-b2ce-804435ad498d
-- title:
--   Definitions for General paradigm for distilling classical key from quantum states
-- statement:
--   The objects the formalized statements of *General paradigm for distilling classical key from quantum states* (arXiv:quant-ph/0506189) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Key`: PDF pp.3–4: d-by-d key register in the distinguished product basis.
--   - `logBits`: PDF p.5 and one-bit normalizations pp.11–12: logarithms in bits.
--   - `keyBlock`: PDF p.5, Eq.(11): shield block selected by two key indices.
--   - `twistingMatrix`: PDF p.4, Eq.(7): full controlled shield unitary.
--   - `twist`: PDF pp.4–6: conjugation by the controlled unitary.
--   - `twistPurification`: PDF pp.5–6, Eq.(17): the SAME purification transported with identity on Eve.
--   - `associatedCCQ`: PDF p.5, Eq.(16): measurement of the key and trace over the shield.
--   - `idealCCQ`: PDF p.4, Eq.(6): uniform correlated key independent of Eve.
--   - `HasKey`: PDF p.4, Definition 1: every unit purification gives ideal key. Theorems carry a density hypothesis, which ensures existence of purifications.
--   - `privateMatrix`: PDF p.4, Eq.(8): pdit constructed from shield state and diagonal controls.
--   - `IsPrivate`: PDF p.4, Definition 3: normalized density with the pdit representation.
--   - `basicPrivate`: PDF p.4, Eq.(9): basic pdit; only the key factor is necessarily pure.
--   - `partyCut`: PDF pp.3,5: reindexing to the physical Alice:Bob cut AA':BB'.
--   - `transposeSecond`: PDF p.5, Eq.(10): transpose on B'.
--   - `transposeBob`: PDF p.5, Eq.(12): simultaneous transpose on B and B'.
--   - `logNegativity`: PDF pp.11,37: logarithmic negativity across AA':BB', in bits.
--   - `xForm`: PDF p.9, Eq.(43): one-operator pbit form, including the external one half.
--   - `HasXPattern`: PDF p.6, Eq.(21): diagonal and anti-diagonal block pairs only.
--   - `privateBitError`: PDF pp.13–14, Eq.(70): visually checked; both inner radicals contain 2 epsilon.
--   - `bipartiteCopies`: PDF pp.12,27: independent copies, with Alice's registers grouped before Bob's.
--   - `regularizedREE`: PDF pp.12,27, Eqs.(59),(154): by subadditivity the stated limit equals this infimum over positive blocklengths. No optimizing blocklength is assumed.
--   - `conditionalShield`: PDF p.11: conditional shield state for key outcome ii, computed from gamma.
--   - `operatorAmplitude`: PDF p.9, Eqs.(39)–(42): rectangular operator amplitude with common polar modulus.
--   - `signedBell`: PDF p.10: Bell projectors, with optional odd parity and minus phase.
--   - `symmetricWerner`: PDF p.10, Eq.(50): symmetric Werner state.
--   - `antisymmetricWerner`: PDF p.10, Eq.(50): antisymmetric Werner state; uses require d >= 2.
--   - `swapPrivate`: PDF p.10, Eq.(48): swap private bit.
--   - `flowerHadamard`: PDF p.11: H tensor ell, reindexed with the accepted bit convention.
--   - `flowerEmbedding`: PDF p.11: W embedded on the maximally correlated shield subspace.
--   - `flowerOperator`: PDF pp.10–11, Eqs.(51)–(53): normalized operator U^T/d, not U^T.
--   - `flowerShield`: PDF p.11: classical maximally correlated shield sigma.
--   - `flowerPrivate`: PDF p.10, Eq.(51): flower state in the displayed block form.
--   - `hidingOne`: PDF p.23, Eq.(133): first hiding state, with Alice/Bob copies grouped.
--   - `hidingTwo`: PDF p.23, Eq.(133): second hiding state.
--   - `hidingFamily`: PDF p.24, Eq.(136): the lower-left difference is fixed by the preceding mixture and (200).
--   - `pairedFlags`: PDF p.29, Eq.(179): two bipartite flags, regrouped across Alice:Bob.
--   - `nptCandidate`: PDF p.29, Eqs.(178)–(179): normalized mixture fixes (180)'s prefactor to 1/8.
--   - `IsEnsemble`: PDF p.35, Eq.(230): normalized finite cq ensemble; zero weights are allowed.
--   - `meanState`: PDF pp.35–37: actual average density.
--   - `cqState`: PDF p.35, Eq.(230): block-diagonal cq state.
--   - `cqProduct`: PDF p.35, Eq.(231): product of the actual marginals.
--   - `meanDistance`: PDF pp.35–36: average full trace norm.
--   - `ensembleMeanRootFidelity`: PDF p.35: finite-ensemble average ROOT fidelity to its mean state. This differs from the accepted teleportation meanFidelity, which averages over input qubits.
--   - `ensembleHolevoBits`: PDF pp.19,36: Holevo information in bits, obtained from the accepted natural-log Holevo information by division by log 2.
--   - `scalingWeights`: PDF p.33, Eq.(215): good and bad key outcome weights.
--   - `scalingEve`: PDF p.33, Eq.(215): good outcomes share |00>, bad ones give |ij> to Eve.
--   - `phaseMatrix`: PDF p.15, Eq.(94): diagonal controlled phases.
--   - `phaseBell`: PDF p.15, Eq.(95): phase-twisted Bell state.
--   - `singletonShield`: PDF p.15: singleton shield embedding of a shieldless state.
--   - `outcomeWeight`: PDF pp.15,31: outcome weight from actual purification coefficients.
--   - `conditionalAmplitude`: PDF pp.15,31: normalized conditional coefficient matrix; at weight zero choose an arbitrary normalized basis vector. The corresponding weighted block vanishes.
--   - `conditionalEve`: PDF pp.15,31: Eve conditional density. For C(s,e)=<s,e|psi_a>, it is (C†C)^T.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, https://arxiv.org/abs/quant-ph/0506189v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

/-!
Horodecki–Horodecki–Horodecki–Oppenheim, quant-ph/0506189v2. All citations are PDF pages.
Coordinates are in the distinguished product basis B (pp.3–4 explicitly allow this convention).
Registers are ordered (A,B),(A',B'); partyCut restores the physical cut (A,A'):(B,B').
The paper and this module concern finite dimensions only. Operational rates are deferred.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Finset

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)
open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.3–4: d-by-d key register in the distinguished product basis. -/
abbrev Key (d : ℕ) := Fin d × Fin d

/-- PDF p.5 and one-bit normalizations pp.11–12: logarithms in bits. -/
def logBits (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- PDF p.5, Eq.(11): shield block selected by two key indices. -/
def keyBlock {d : ℕ} {H : Type*} (rho : Op (Key d × H)) (a b : Key d) : Op H :=
  fun s t => rho (a,s) (b,t)

/-- PDF p.4, Eq.(7): full controlled shield unitary. -/
def twistingMatrix {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) : Op (Key d × H) :=
  fun a b => if a.1 = b.1 then (U a.1 : Op H) a.2 b.2 else 0

/-- PDF pp.4–6: conjugation by the controlled unitary. -/
def twist {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (rho : Op (Key d × H)) : Op (Key d × H) :=
  twistingMatrix U * rho * (twistingMatrix U)ᴴ

/-- PDF pp.5–6, Eq.(17): the SAME purification transported with identity on Eve. -/
def twistPurification {d : ℕ} {H E : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ)
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) : EuclideanSpace ℂ ((Key d × H) × E) :=
  WithLp.toLp 2 fun z => ∑ s, (U z.1.1 : Op H) z.1.2 s * psi ((z.1.1,s),z.2)

/-- PDF p.5, Eq.(16): measurement of the key and trace over the shield. -/
def associatedCCQ {d : ℕ} {H E : Type*} [Fintype H]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) : Op (Key d × E) :=
  fun a b => if a.1 = b.1 then
    ∑ s, psi ((a.1,s),a.2) * conj (psi ((a.1,s),b.2)) else 0

/-- PDF p.4, Eq.(6): uniform correlated key independent of Eve. -/
def idealCCQ {d : ℕ} {E : Type*} (omega : Op E) : Op (Key d × E) :=
  fun a b => if a.1 = b.1 ∧ a.1.1 = a.1.2 then (d : ℂ)⁻¹ * omega a.2 b.2 else 0

/-- PDF p.4, Definition 1: every unit purification gives ideal key.
Theorems carry a density hypothesis, which ensures existence of purifications. -/
def HasKey {d : ℕ} {H : Type*} [Fintype H] (rho : Op (Key d × H)) : Prop :=
  ∀ e : ℕ, 0 < e → ∀ psi : EuclideanSpace ℂ ((Key d × H) × Fin e),
    IsState psi → traceRight (pureDensity psi) = rho →
    ∃ omega : Op (Fin e), IsDensityMatrix omega ∧ associatedCCQ psi = idealCCQ omega

/-- PDF p.4, Eq.(8): pdit constructed from shield state and diagonal controls. -/
def privateMatrix {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (tau : Op H) (U : Fin d → Matrix.unitaryGroup H ℂ) : Op (Key d × H) :=
  fun a b => if a.1.1 = a.1.2 ∧ b.1.1 = b.1.2 then
    (d : ℂ)⁻¹ * ((U a.1.1 : Op H) * tau * (U b.1.1 : Op H)ᴴ) a.2 b.2 else 0

/-- PDF p.4, Definition 3: normalized density with the pdit representation. -/
def IsPrivate {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H] (rho : Op (Key d × H)) : Prop :=
  IsDensityMatrix rho ∧ ∃ tau : Op H, IsDensityMatrix tau ∧
    ∃ U : Fin d → Matrix.unitaryGroup H ℂ, rho = privateMatrix tau U

/-- PDF p.4, Eq.(9): basic pdit; only the key factor is necessarily pure. -/
def basicPrivate {d : ℕ} {H : Type*} (tau : Op H) : Op (Key d × H) :=
  Matrix.kronecker (bellProjector d) tau

/-- PDF pp.3,5: reindexing to the physical Alice:Bob cut AA':BB'. -/
def partyCut {d : ℕ} {S T : Type*} (rho : Op (Key d × (S × T))) :
    Op ((Fin d × S) × (Fin d × T)) :=
  fun a b => rho ((a.1.1,a.2.1),(a.1.2,a.2.2)) ((b.1.1,b.2.1),(b.1.2,b.2.2))

/-- PDF p.5, Eq.(10): transpose on B'. -/
def transposeSecond {S T : Type*} (X : Op (S × T)) : Op (S × T) :=
  fun a b => X (a.1,b.2) (b.1,a.2)

/-- PDF p.5, Eq.(12): simultaneous transpose on B and B'. -/
def transposeBob {d : ℕ} {S T : Type*} (rho : Op (Key d × (S × T))) :
    Op (Key d × (S × T)) :=
  fun a b => rho ((a.1.1,b.1.2),(a.2.1,b.2.2)) ((b.1.1,a.1.2),(b.2.1,a.2.2))

/-- PDF pp.11,37: logarithmic negativity across AA':BB', in bits. -/
def logNegativity {d : ℕ} {S T : Type*} [Fintype S] [Fintype T]
    (rho : Op (Key d × (S × T))) : ℝ := logBits (traceNorm (transposeBob rho))

/-- PDF p.9, Eq.(43): one-operator pbit form, including the external one half. -/
def xForm {H : Type*} [Fintype H] (X : Op H) : Op (Key 2 × H) :=
  fun a b => (1/2 : ℂ) *
    (if a.1 = (0,0) ∧ b.1 = (0,0) then (cfc Real.sqrt (X * Xᴴ)) a.2 b.2
    else if a.1 = (0,0) ∧ b.1 = (1,1) then X a.2 b.2
    else if a.1 = (1,1) ∧ b.1 = (0,0) then Xᴴ a.2 b.2
    else if a.1 = (1,1) ∧ b.1 = (1,1) then (cfc Real.sqrt (Xᴴ * X)) a.2 b.2 else 0)

/-- PDF p.6, Eq.(21): diagonal and anti-diagonal block pairs only. -/
def HasXPattern {H : Type*} (rho : Op (Key 2 × H)) : Prop :=
  ∀ a b, a ≠ b → b ≠ (1-a.1,1-a.2) → keyBlock rho a b = 0

/-- PDF pp.13–14, Eq.(70): visually checked; both inner radicals contain 2 epsilon. -/
def privateBitError (eps : ℝ) : ℝ :=
  2 * Real.sqrt (8 * Real.sqrt (2*eps) + binEntropy2 (2*Real.sqrt (2*eps))) +
    2*Real.sqrt (2*eps)

/-- PDF pp.12,27: independent copies, with Alice's registers grouped before Bob's. -/
def bipartiteCopies {I J : Type*} (rho : Op (I × J)) (n : ℕ) :
    Op ((Fin n → I) × (Fin n → J)) :=
  fun a b => ∏ t, rho (a.1 t,a.2 t) (b.1 t,b.2 t)

/-- PDF pp.12,27, Eqs.(59),(154): by subadditivity the stated limit equals
this infimum over positive blocklengths. No optimizing blocklength is assumed. -/
def regularizedREE {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (rho : Op (I × J)) : ℝ≥0∞ :=
  ⨅ n : ℕ+, relativeEntanglement (bipartiteCopies rho n) / ((n : ℕ) : ℝ≥0∞)

/-- PDF p.11: conditional shield state for key outcome ii, computed from gamma. -/
def conditionalShield {d : ℕ} {H : Type*} (gamma : Op (Key d × H)) (i : Fin d) : Op H :=
  (d : ℂ) • keyBlock gamma (i,i) (i,i)

/-- PDF p.9, Eqs.(39)–(42): rectangular operator amplitude with common polar modulus. -/
def operatorAmplitude {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (tau : Op H) (U : Fin d → Matrix.unitaryGroup H ℂ) : Matrix (Key d × H) H ℂ :=
  fun a s => if a.1.1 = a.1.2 then
    ((Real.sqrt d)⁻¹ : ℂ) * ((U a.1.1 : Op H) * cfc Real.sqrt tau) a.2 s else 0

/-- PDF p.10: Bell projectors, with optional odd parity and minus phase. -/
def signedBell (odd minus : Bool) : Op (Key 2) :=
  pureDensity (WithLp.toLp 2 fun a =>
    if (if odd then a.1 ≠ a.2 else a.1 = a.2) then
      (if minus = true ∧ a.1 = 1 then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)) else 0)

/-- PDF p.10, Eq.(50): symmetric Werner state. -/
def symmetricWerner (d : ℕ) : Op (Fin d × Fin d) :=
  ((d : ℂ)^2 + d)⁻¹ • (1 + QAlgorithms.Papers.Independent.Information100.P76.swapMatrix (I := Fin d))

/-- PDF p.10, Eq.(50): antisymmetric Werner state; uses require d >= 2. -/
def antisymmetricWerner (d : ℕ) : Op (Fin d × Fin d) :=
  ((d : ℂ)^2 - d)⁻¹ • (1 - QAlgorithms.Papers.Independent.Information100.P76.swapMatrix (I := Fin d))

/-- PDF p.10, Eq.(48): swap private bit. -/
def swapPrivate (d : ℕ) : Op (Key 2 × (Fin d × Fin d)) :=
  xForm (((d : ℂ)^2)⁻¹ • QAlgorithms.Papers.Independent.Information100.P76.swapMatrix (I := Fin d))

/-- PDF p.11: H tensor ell, reindexed with the accepted bit convention. -/
def flowerHadamard (ell : ℕ) : Op (Fin (2^ell)) :=
  fun i j => hadamardN ell ((bitsEquivFin ell).symm i) ((bitsEquivFin ell).symm j)

/-- PDF p.11: W embedded on the maximally correlated shield subspace. -/
def flowerEmbedding (ell : ℕ) : Op (Fin (2^ell) × Fin (2^ell)) :=
  fun a b => if a.1 = a.2 ∧ b.1 = b.2 then flowerHadamard ell a.1 b.1 else 0

/-- PDF pp.10–11, Eqs.(51)–(53): normalized operator U^T/d, not U^T. -/
def flowerOperator (ell : ℕ) : Op (Fin (2^ell) × Fin (2^ell)) :=
  (((2^ell : ℕ) : ℂ)⁻¹) • (flowerEmbedding ell).transpose

/-- PDF p.11: classical maximally correlated shield sigma. -/
def flowerShield (ell : ℕ) : Op (Fin (2^ell) × Fin (2^ell)) :=
  fun a b => if a = b ∧ a.1 = a.2 then ((2^ell : ℕ) : ℂ)⁻¹ else 0

/-- PDF p.10, Eq.(51): flower state in the displayed block form. -/
def flowerPrivate (ell : ℕ) : Op (Key 2 × (Fin (2^ell) × Fin (2^ell))) :=
  fun a b => (1/2 : ℂ) *
    (if a.1 = (0,0) ∧ b.1 = (0,0) then flowerShield ell a.2 b.2
    else if a.1 = (1,1) ∧ b.1 = (1,1) then flowerShield ell a.2 b.2
    else if a.1 = (0,0) ∧ b.1 = (1,1) then flowerOperator ell a.2 b.2
    else if a.1 = (1,1) ∧ b.1 = (0,0) then (flowerOperator ell)ᴴ a.2 b.2 else 0)

/-- PDF p.23, Eq.(133): first hiding state, with Alice/Bob copies grouped. -/
def hidingOne (d k : ℕ) : Op ((Fin k → Fin d) × (Fin k → Fin d)) :=
  bipartiteCopies ((1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)) k

/-- PDF p.23, Eq.(133): second hiding state. -/
def hidingTwo (d k : ℕ) : Op ((Fin k → Fin d) × (Fin k → Fin d)) :=
  bipartiteCopies (symmetricWerner d) k

/-- PDF p.24, Eq.(136): the lower-left difference is fixed by the preceding mixture and (200). -/
def hidingFamily (p : ℝ) (d k : ℕ) :
    Op (Key 2 × ((Fin k → Fin d) × (Fin k → Fin d))) :=
  fun a b =>
    if (a.1 = (0,0) ∧ b.1 = (0,0)) ∨ (a.1 = (1,1) ∧ b.1 = (1,1)) then
      ((p/2 : ℝ) : ℂ) * (hidingOne d k + hidingTwo d k) a.2 b.2
    else if (a.1 = (0,0) ∧ b.1 = (1,1)) ∨ (a.1 = (1,1) ∧ b.1 = (0,0)) then
      ((p/2 : ℝ) : ℂ) * (hidingOne d k - hidingTwo d k) a.2 b.2
    else if (a.1 = (0,1) ∧ b.1 = (0,1)) ∨ (a.1 = (1,0) ∧ b.1 = (1,0)) then
      ((1/2-p : ℝ) : ℂ) * hidingTwo d k a.2 b.2 else 0

/-- PDF p.29, Eq.(179): two bipartite flags, regrouped across Alice:Bob. -/
def pairedFlags {S T : Type*} (A B : Op (S × T)) : Op ((S × S) × (T × T)) :=
  fun a b => A (a.1.1,a.2.1) (b.1.1,b.2.1) * B (a.1.2,a.2.2) (b.1.2,b.2.2)

/-- PDF p.29, Eqs.(178)–(179): normalized mixture fixes (180)'s prefactor to 1/8. -/
def nptCandidate (d k : ℕ) :=
  (1/4 : ℂ) •
    (Matrix.kronecker (signedBell false false) (pairedFlags (hidingOne d k) (hidingOne d k)) +
     Matrix.kronecker (signedBell false true) (pairedFlags (hidingOne d k) (hidingTwo d k)) +
     Matrix.kronecker (signedBell true false) (pairedFlags (hidingTwo d k) (hidingOne d k)) +
     Matrix.kronecker (signedBell true true) (pairedFlags (hidingTwo d k) (hidingTwo d k)))

/-- PDF p.35, Eq.(230): normalized finite cq ensemble; zero weights are allowed. -/
def IsEnsemble {L H : Type*} [Fintype L] [Fintype H]
    (p : L → ℝ) (rho : L → Op H) : Prop :=
  (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧ ∀ k, IsDensityMatrix (rho k)

/-- PDF pp.35–37: actual average density. -/
def meanState {L H : Type*} [Fintype L] (p : L → ℝ) (rho : L → Op H) : Op H :=
  ∑ k, (p k : ℂ) • rho k

/-- PDF p.35, Eq.(230): block-diagonal cq state. -/
def cqState {L H : Type*} (p : L → ℝ) (rho : L → Op H) : Op (L × H) :=
  fun a b => if a.1 = b.1 then (p a.1 : ℂ) * rho a.1 a.2 b.2 else 0

/-- PDF p.35, Eq.(231): product of the actual marginals. -/
def cqProduct {L H : Type*} [Fintype L] (p : L → ℝ) (rho : L → Op H) : Op (L × H) :=
  cqState p (fun _ => meanState p rho)

/-- PDF pp.35–36: average full trace norm. -/
def meanDistance {L H : Type*} [Fintype L] [Fintype H]
    (p : L → ℝ) (rho : L → Op H) : ℝ :=
  ∑ k, p k * traceNorm (rho k - meanState p rho)

/-- PDF p.35: finite-ensemble average ROOT fidelity to its mean state.
This differs from the accepted teleportation meanFidelity, which averages over input qubits. -/
def ensembleMeanRootFidelity {L H : Type*} [Fintype L] [Fintype H]
    (p : L → ℝ) (rho : L → Op H) : ℝ :=
  ∑ k, p k * rootFidelity (rho k) (meanState p rho)

/-- PDF pp.19,36: Holevo information in bits, obtained from the accepted natural-log
Holevo information by division by log 2. -/
def ensembleHolevoBits {L H : Type*} [Fintype L] [Fintype H]
    (p : L → ℝ) (rho : L → Op H) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P56.holevo p rho / Real.log 2

/-- PDF p.33, Eq.(215): good and bad key outcome weights. -/
def scalingWeights (d : ℕ) (a : ℝ) : Key d → ℝ :=
  fun ij => if ij.1 = ij.2 then (1-a)/d else a/((d:ℝ)^2-d)

/-- PDF p.33, Eq.(215): good outcomes share |00>, bad ones give |ij> to Eve. -/
def scalingEve (d : ℕ) [NeZero d] (ij : Key d) : Op (Key d) :=
  pureDensity (ket (if ij.1 = ij.2 then (0,0) else ij))

/-- PDF p.15, Eq.(94): diagonal controlled phases. -/
def phaseMatrix (theta : Key 2 → ℝ) : Op (Key 2) :=
  Matrix.diagonal (fun a => Complex.exp ((theta a : ℂ) * Complex.I))

/-- PDF p.15, Eq.(95): phase-twisted Bell state. -/
def phaseBell (theta : Key 2 → ℝ) : Op (Key 2) :=
  phaseMatrix theta * bellProjector 2 * (phaseMatrix theta)ᴴ

/-- PDF p.15: singleton shield embedding of a shieldless state. -/
def singletonShield (rho : Op (Key 2)) : Op (Key 2 × Unit) := fun a b => rho a.1 b.1

/-- PDF pp.15,31: outcome weight from actual purification coefficients. -/
def outcomeWeight {d : ℕ} {H E : Type*} [Fintype H] [Fintype E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a : Key d) : ℝ :=
  ∑ s, ∑ e, Complex.normSq (psi ((a,s),e))

/-- PDF pp.15,31: normalized conditional coefficient matrix; at weight zero choose
an arbitrary normalized basis vector. The corresponding weighted block vanishes. -/
def conditionalAmplitude {d : ℕ} {H E : Type*} [Fintype H] [Fintype E]
    [Nonempty H] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a : Key d) : Matrix H E ℂ :=
  fun s e => if outcomeWeight psi a = 0 then
    if s = Classical.choice (inferInstance : Nonempty H) ∧
       e = Classical.choice (inferInstance : Nonempty E) then 1 else 0
  else psi ((a,s),e) / (Real.sqrt (outcomeWeight psi a) : ℂ)

/-- PDF pp.15,31: Eve conditional density. For C(s,e)=<s,e|psi_a>, it is (C†C)^T. -/
def conditionalEve {d : ℕ} {H E : Type*} [Fintype H] [Fintype E]
    [Nonempty H] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × H) × E)) (a : Key d) : Op E :=
  ((conditionalAmplitude psi a)ᴴ * conditionalAmplitude psi a).transpose

/-! Sanity examples for local bodies, not proofs of source theorems. -/

example {L H : Type*} [Fintype L] [Fintype H]
    (p : L → ℝ) (rho : L → Op H) :
    ensembleHolevoBits p rho =
      QAlgorithms.Papers.Independent.Information100.P56.holevo p rho / Real.log 2 := rfl

example {L H : Type*} [Fintype L] [Fintype H]
    (p : L → ℝ) (rho : L → Op H) :
    ensembleMeanRootFidelity p rho = ∑ k, p k * rootFidelity (rho k) (meanState p rho) := rfl

example {d : ℕ} {H : Type*} (rho : Op (Key d × H)) (a b : Key d) (s t : H) :
    keyBlock rho a b s t = rho (a,s) (b,t) := rfl

example {S T : Type*} (X : Op (S × T)) : transposeSecond (transposeSecond X) = X := rfl

example {d : ℕ} {S T : Type*} (rho : Op (Key d × (S × T))) :
    transposeBob (transposeBob rho) = rho := rfl

example {H : Type*} [Fintype H] (X : Op H) :
    keyBlock (xForm X) (0,0) (1,1) = (1/2 : ℂ) • X := by
  ext s t
  simp [keyBlock, xForm]

example {I J : Type*} (rho : Op (I × J)) (a b : (Fin 0 → I) × (Fin 0 → J)) :
    bipartiteCopies rho 0 a b = 1 := by simp [bipartiteCopies]

example {L H : Type*} (p : L → ℝ) (rho : L → Op H) (a : L) (s t : H) :
    cqState p rho (a,s) (a,t) = (p a : ℂ) * rho a s t := by simp [cqState]

example {I : Type*} [Fintype I] (rho sigma : Op I)
    (h : ¬ (IsDensityMatrix rho ∧ IsDensityMatrix sigma)) :
    relativeEntropyBits rho sigma = ⊤ := by simp [relativeEntropyBits, h]

end QAlgorithms.Papers.Independent.Dependency50.P24


