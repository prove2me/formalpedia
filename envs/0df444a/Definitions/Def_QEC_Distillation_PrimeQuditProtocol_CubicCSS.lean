-- Prove2me | Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
-- name    : QEC_Distillation_PrimeQuditProtocol_CubicCSS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T10:40:56.974103+00:00
-- url     : https://prove2.me/theorems/714e1757-7210-44bf-8406-6e56cc98f984
-- title:
--   Cubic CSS
-- statement:
--   Definitions and structural lemmas for Cubic CSS, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
abbrev PrimeQudit (p : Nat) [NeZero p] : Type :=
  EuclideanSpace Complex (ZMod p)
abbrev PrimeQuditRegisterLabel (p : Nat) (Site : Type u) : Type u :=
  Site → ZMod p
noncomputable local instance primeQuditRegisterLabelFintype (p : Nat) [NeZero p]
    (Site : Type u) [Fintype Site] : Fintype (PrimeQuditRegisterLabel p Site) :=
  Fintype.ofFinite _
abbrev PrimeQuditRegister (p : Nat) (Site : Type u) [NeZero p] : Type u :=
  EuclideanSpace Complex (PrimeQuditRegisterLabel p Site)
def quditBasisKet (p : Nat) [NeZero p] (x : ZMod p) : PrimeQudit p :=
  EuclideanSpace.basisFun (ZMod p) Complex x
def registerBasisKet (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (x : PrimeQuditRegisterLabel p Site) : PrimeQuditRegister p Site :=
  EuclideanSpace.basisFun (PrimeQuditRegisterLabel p Site) Complex x
def phase (p : Nat) [NeZero p] (x : ZMod p) : Complex :=
  ZMod.stdAddChar x
@[simp]
theorem phase_zero (p : Nat) [NeZero p] : phase p 0 = 1 :=
  (ZMod.stdAddChar (N := p)).map_zero_eq_one
theorem phase_add (p : Nat) [NeZero p] (x y : ZMod p) :
    phase p (x + y) = phase p x * phase p y :=
  (ZMod.stdAddChar (N := p)).map_add_eq_mul x y
theorem phase_conj (p : Nat) [NeZero p] (x : ZMod p) :
    starRingEnd Complex (phase p x) = phase p (-x) := by
  simpa [phase] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) x).symm
theorem phase_mul_conj (p : Nat) [NeZero p] (x : ZMod p) :
    phase p x * starRingEnd Complex (phase p x) = 1 := by
  rw [phase_conj, ← phase_add, add_neg_cancel, phase_zero]
def zAmplitude (p : Nat) [NeZero p] (x : ZMod p) : Complex := phase p x
def u13Amplitude (p : Nat) [NeZero p] (x : ZMod p) : Complex := phase p (x ^ 3)
theorem u13Amplitude_mul_conj (p : Nat) [NeZero p] (x : ZMod p) :
    u13Amplitude p x * starRingEnd Complex (u13Amplitude p x) = 1 :=
  phase_mul_conj p (x ^ 3)
def diagonalOperator {Label : Type u} [Fintype Label] (amplitude : Label → Complex) :
    Operator (EuclideanSpace Complex Label) where
  toFun psi := WithLp.toLp 2 fun label => amplitude label * psi label
  map_add' := by
    intro psi chi
    ext label
    change amplitude label * (psi label + chi label) =
      amplitude label * psi label + amplitude label * chi label
    ring
  map_smul' := by
    intro scalar psi
    ext label
    change amplitude label * (scalar * psi label) = scalar * (amplitude label * psi label)
    ring
@[simp]
theorem diagonalOperator_apply {Label : Type u} [Fintype Label]
    (amplitude : Label → Complex) (psi : EuclideanSpace Complex Label) (label : Label) :
    diagonalOperator amplitude psi label = amplitude label * psi label :=
  rfl
theorem diagonalOperator_map_inner {Label : Type u} [Fintype Label]
    (amplitude : Label → Complex)
    (hunit : ∀ label, amplitude label * starRingEnd Complex (amplitude label) = 1)
    (psi chi : EuclideanSpace Complex Label) :
    inner Complex (diagonalOperator amplitude psi) (diagonalOperator amplitude chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [diagonalOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (amplitude label * chi label) *
        (starRingEnd Complex (amplitude label) * starRingEnd Complex (psi label)) =
        (amplitude label * starRingEnd Complex (amplitude label)) *
          (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by rw [hunit]; ring
noncomputable def diagonalLinearEquiv {Label : Type u} [Fintype Label]
    (amplitude inverseAmplitude : Label → Complex)
    (hleft : ∀ label, inverseAmplitude label * amplitude label = 1)
    (hright : ∀ label, amplitude label * inverseAmplitude label = 1) :
    EuclideanSpace Complex Label ≃ₗ[Complex] EuclideanSpace Complex Label where
  toFun := diagonalOperator amplitude
  invFun := diagonalOperator inverseAmplitude
  left_inv := by
    intro psi
    ext label
    simp only [diagonalOperator_apply]
    rw [← mul_assoc, hleft]
    simp
  right_inv := by
    intro psi
    ext label
    simp only [diagonalOperator_apply]
    rw [← mul_assoc, hright]
    simp
  map_add' := (diagonalOperator amplitude).map_add
  map_smul' := (diagonalOperator amplitude).map_smul
noncomputable def zTransport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := diagonalLinearEquiv (zAmplitude p) (fun x => phase p (-x))
    (by
      intro x
      change phase p (-x) * phase p x = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p x * phase p (-x) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (zAmplitude p) (phase_mul_conj p)
@[simp]
theorem zTransport_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    zTransport p psi x = zAmplitude p x * psi x :=
  rfl
def xLabelEquiv (p : Nat) [NeZero p] : ZMod p ≃ ZMod p where
  toFun x := x + 1
  invFun x := x - 1
  left_inv x := by ring
  right_inv x := by ring
noncomputable def xLinearIsometry (p : Nat) [NeZero p] :
    PrimeQudit p ≃ₗᵢ[Complex] PrimeQudit p :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (xLabelEquiv p)
noncomputable def xTransport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := (xLinearIsometry p).toLinearEquiv
  map_inner := fun psi chi => (xLinearIsometry p).inner_map_map psi chi
@[simp]
theorem xTransport_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    xTransport p psi x = psi (x - 1) :=
  rfl
noncomputable def u13Transport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := diagonalLinearEquiv (u13Amplitude p) (fun x => phase p (-(x ^ 3)))
    (by
      intro x
      change phase p (-(x ^ 3)) * phase p (x ^ 3) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p (x ^ 3) * phase p (-(x ^ 3)) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (u13Amplitude p) (u13Amplitude_mul_conj p)
@[simp]
theorem u13Transport_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    u13Transport p psi x = u13Amplitude p x * psi x :=
  rfl
@[simp]
theorem u13Transport_symm_apply (p : Nat) [NeZero p] (psi : PrimeQudit p) (x : ZMod p) :
    (u13Transport p).symm psi x = phase p (-(x ^ 3)) * psi x :=
  rfl
structure PrimeAtLeastFive (p : Nat) : Prop where
  prime : Nat.Prime p
  five_le : 5 ≤ p
def idealU13Resource (p : Nat) [NeZero p] : PrimeQudit p :=
  u13Transport p
    ((Real.sqrt (p : Real) : Complex)⁻¹ • ∑ x : ZMod p, quditBasisKet p x)
def u13ConjugatedXExponent (p : Nat) [NeZero p] (x : ZMod p) : ZMod p :=
  (x + 1) ^ 3 - x ^ 3
def u13ConjugatedXAmplitude (p : Nat) [NeZero p] (x : ZMod p) : Complex :=
  phase p (u13ConjugatedXExponent p x)
def zPowerAmplitude (p : Nat) [NeZero p] (slope x : ZMod p) : Complex :=
  phase p (slope * x)
noncomputable def zPowerTransport (p : Nat) [NeZero p] (slope : ZMod p) :
    UnitaryTransport (PrimeQudit p) (PrimeQudit p) where
  toLinearEquiv := diagonalLinearEquiv (zPowerAmplitude p slope)
    (fun x => phase p (-(slope * x)))
    (by
      intro x
      change phase p (-(slope * x)) * phase p (slope * x) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p (slope * x) * phase p (-(slope * x)) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (zPowerAmplitude p slope)
    (fun x => phase_mul_conj p (slope * x))
@[simp]
theorem zPowerTransport_apply (p : Nat) [NeZero p] (slope : ZMod p)
    (psi : PrimeQudit p) (x : ZMod p) :
    zPowerTransport p slope psi x = zPowerAmplitude p slope x * psi x :=
  rfl
structure U13HierarchyWitness (p : Nat) [NeZero p] : Prop where
  quadratic_conjugatedX : ∀ x : ZMod p,
    u13ConjugatedXExponent p x = 3 * x ^ 2 + 3 * x + 1
  pauli_firstDifference : ∀ x : ZMod p,
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) =
      phase p 6 * zPowerAmplitude p 6 x
  pauli_firstDifference_on_basis : ∀ x : ZMod p,
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) •
        quditBasisKet p x =
      phase p 6 • zPowerTransport p 6 (quditBasisKet p x)
  pauli_slope_ne_zero : (6 : ZMod p) ≠ 0
noncomputable def siteEquivFin (Site : Type u) [Fintype Site] :
    Fin (Fintype.card Site) ≃ Site :=
  (Fintype.equivFin Site).symm
def coordinateSupport {Site : Type u} [DecidableEq Site] (site : Site) : Finset Site :=
  {site}
@[simp]
theorem coordinateSupport_card {Site : Type u} [DecidableEq Site] (site : Site) :
    (coordinateSupport site).card = 1 := by simp [coordinateSupport]
theorem coordinateSupport_disjoint {Site : Type u} [DecidableEq Site]
    {first second : Site} (hne : first ≠ second) :
    Disjoint (coordinateSupport first) (coordinateSupport second) := by
  simpa [coordinateSupport] using (Finset.disjoint_singleton.mpr hne)
def u13AtAmplitude (p : Nat) [NeZero p] {Site : Type u}
    (site : Site) (label : PrimeQuditRegisterLabel p Site) : Complex :=
  u13Amplitude p (label site)
noncomputable def u13AtTransport (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (site : Site) :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  toLinearEquiv := diagonalLinearEquiv (u13AtAmplitude p site)
    (fun label => phase p (-(label site ^ 3)))
    (by
      intro label
      change phase p (-(label site ^ 3)) * phase p (label site ^ 3) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro label
      change phase p (label site ^ 3) * phase p (-(label site ^ 3)) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (u13AtAmplitude p site)
    (fun label => u13Amplitude_mul_conj p (label site))
@[simp]
theorem u13AtTransport_apply (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (site : Site)
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    u13AtTransport p site psi label = u13AtAmplitude p site label * psi label :=
  rfl
noncomputable def physicalU13 (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card Site) =>
    u13AtTransport p (siteEquivFin Site j)
attribute [local instance] primeQuditRegisterLabelFintype
def cubicExponent (p : Nat) [NeZero p] {Site : Type u} [Fintype Site]
    (label : PrimeQuditRegisterLabel p Site) : ZMod p :=
  ∑ site : Site, label site ^ 3
inductive U13LocalGate (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] : Finset Site → Type u
  | at (site : Site) : U13LocalGate p (coordinateSupport site)
noncomputable def physicalU13GateModel (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] :
    FinitePhysicalGateModel Site (PrimeQuditRegister p Site) where
  LocalGate := U13LocalGate p
  realize gate := match gate with
    | .at site => u13AtTransport p site
noncomputable def physicalU13SitewiseFactorization (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] :
    SitewiseTransversalityData (physicalU13GateModel p (Site := Site)) (physicalU13 p) where
  factorCount := Fintype.card Site
  support j := coordinateSupport (siteEquivFin Site j)
  factor j := .at (siteEquivFin Site j)
  pairwise_disjoint := by
    intro i j hij
    exact coordinateSupport_disjoint ((siteEquivFin Site).injective.ne hij)
  realizes := rfl
  support_card_le_one := by
    intro j
    simp [coordinateSupport_card]
def cubicPairing (p : Nat) {Site : Type u} [NeZero p] [Fintype Site]
    (x y z : PrimeQuditRegisterLabel p Site) : ZMod p :=
  ∑ site : Site, x site * y site * z site
structure CubicRowFamily (p : Nat) [NeZero p]
    (Logical Stabilizer Site : Type u)
    [Fintype Logical] [Fintype Stabilizer] [Fintype Site] where
  /-- Rows whose coefficients label the encoded computational basis. -/
  logicalRow : Logical → PrimeQuditRegisterLabel p Site
  /-- Rows summed uniformly in every stabilizer coset. -/
  stabilizerRow : Stabilizer → PrimeQuditRegisterLabel p Site
  /-- The displayed matrix rows are linearly independent over `ZMod p`. -/
  rowIndependent : ∀ (u : Logical → ZMod p) (h : Stabilizer → ZMod p),
    (∑ a : Logical, u a • logicalRow a) +
      ∑ s : Stabilizer, h s • stabilizerRow s = 0 → u = 0 ∧ h = 0
  /-- Every cubic term containing a stabilizer row vanishes, including repetitions. -/
  stabilizerTriple_zero : ∀ (a b c : Logical ⊕ Stabilizer),
    ((∃ s, a = Sum.inr s) ∨ (∃ s, b = Sum.inr s) ∨ (∃ s, c = Sum.inr s)) →
      cubicPairing p (Sum.elim logicalRow stabilizerRow a)
        (Sum.elim logicalRow stabilizerRow b) (Sum.elim logicalRow stabilizerRow c) = 0
  /-- A triple of logical rows vanishes unless all three indices agree. -/
  logicalTriple_offDiagonal_zero : ∀ (a b c : Logical),
    ¬ (a = b ∧ b = c) →
      cubicPairing p (logicalRow a) (logicalRow b) (logicalRow c) = 0
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
local instance _p2m_local_instance_d01bce0bd8_633 : DecidableEq Logical := Classical.decEq _
local instance _p2m_local_instance_d01bce0bd8_634 : DecidableEq Stabilizer := Classical.decEq _
local instance _p2m_local_instance_d01bce0bd8_635 : DecidableEq Site := Classical.decEq _
def row (R : CubicRowFamily p Logical Stabilizer Site) :
    Logical ⊕ Stabilizer → PrimeQuditRegisterLabel p Site
  | Sum.inl a => R.logicalRow a
  | Sum.inr s => R.stabilizerRow s
@[simp]
theorem row_inl (R : CubicRowFamily p Logical Stabilizer Site) (a : Logical) :
    R.row (Sum.inl a) = R.logicalRow a := rfl
@[simp]
theorem row_inr (R : CubicRowFamily p Logical Stabilizer Site) (s : Stabilizer) :
    R.row (Sum.inr s) = R.stabilizerRow s := rfl
def epsilon (R : CubicRowFamily p Logical Stabilizer Site) (a : Logical) : ZMod p :=
  cubicPairing p (R.logicalRow a) (R.logicalRow a) (R.logicalRow a)
def logicalWord (R : CubicRowFamily p Logical Stabilizer Site) (u : Logical → ZMod p) :
    PrimeQuditRegisterLabel p Site :=
  ∑ a : Logical, u a • R.logicalRow a
def stabilizerWord (R : CubicRowFamily p Logical Stabilizer Site) (h : Stabilizer → ZMod p) :
    PrimeQuditRegisterLabel p Site :=
  ∑ s : Stabilizer, h s • R.stabilizerRow s
def cosetLabel (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    PrimeQuditRegisterLabel p Site :=
  -R.logicalWord u + R.stabilizerWord h
def combinedCoefficient (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    Logical ⊕ Stabilizer → ZMod p
  | Sum.inl a => -u a
  | Sum.inr s => h s
def combinedWord (R : CubicRowFamily p Logical Stabilizer Site)
    (q : Logical ⊕ Stabilizer → ZMod p) : PrimeQuditRegisterLabel p Site :=
  ∑ r : Logical ⊕ Stabilizer, q r • R.row r
theorem logicalWord_sub (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) : R.logicalWord (u - v) = R.logicalWord u - R.logicalWord v := by
  classical
  ext site
  simp [logicalWord, Finset.sum_sub_distrib, sub_smul]
theorem stabilizerWord_sub (R : CubicRowFamily p Logical Stabilizer Site)
    (h k : Stabilizer → ZMod p) :
    R.stabilizerWord (h - k) = R.stabilizerWord h - R.stabilizerWord k := by
  classical
  ext site
  simp [stabilizerWord, Finset.sum_sub_distrib, sub_smul]
theorem cosetLabel_eq_implies_logical_eq (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) (h k : Stabilizer → ZMod p)
    (heq : R.cosetLabel u h = R.cosetLabel v k) : u = v := by
  have hzero : R.logicalWord (u - v) + R.stabilizerWord (k - h) = 0 := by
    rw [R.logicalWord_sub, R.stabilizerWord_sub]
    ext site
    have hpoint := congrFun heq site
    change -R.logicalWord u site + R.stabilizerWord h site =
      -R.logicalWord v site + R.stabilizerWord k site at hpoint
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    change R.logicalWord u site - R.logicalWord v site +
      (R.stabilizerWord k site - R.stabilizerWord h site) = 0
    linear_combination -hpoint
  have hIndependent := R.rowIndependent (u - v) (k - h) hzero
  have huv : u - v = 0 := hIndependent.1
  exact sub_eq_zero.mp huv
theorem cosetLabel_injective (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : Function.Injective (R.cosetLabel u) := by
  intro h k heq
  have hzero : R.logicalWord (u - u) + R.stabilizerWord (k - h) = 0 := by
    rw [R.logicalWord_sub, R.stabilizerWord_sub]
    ext site
    have hpoint := congrFun heq site
    change -R.logicalWord u site + R.stabilizerWord h site =
      -R.logicalWord u site + R.stabilizerWord k site at hpoint
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    rw [sub_self, zero_add]
    change R.stabilizerWord k site - R.stabilizerWord h site = 0
    linear_combination -hpoint
  have hIndependent := R.rowIndependent (u - u) (k - h) hzero
  exact (sub_eq_zero.mp hIndependent.2).symm
abbrev StabilizerLabel (p : Nat) (Stabilizer : Type u) := Stabilizer → ZMod p
def cosetNormalization (p : Nat) [NeZero p] (Stabilizer : Type u)
    [Fintype Stabilizer] : Complex :=
  (Real.sqrt (Nat.card (StabilizerLabel p Stabilizer) : Real) : Complex)⁻¹
def cosetKet (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : PrimeQuditRegister p Site :=
  cosetNormalization p Stabilizer •
    ∑ h : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel u h)
theorem uniformCosetSum_inner (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) :
    inner Complex
        (∑ h : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel u h))
        (∑ k : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel v k)) =
      if u = v then (Nat.card (StabilizerLabel p Stabilizer) : Complex) else 0 := by
  classical
  rw [inner_sum]
  simp_rw [sum_inner]
  by_cases huv : u = v
  · subst v
    have hinner (h k : StabilizerLabel p Stabilizer) :
        inner Complex (registerBasisKet p (R.cosetLabel u h))
          (registerBasisKet p (R.cosetLabel u k)) = if h = k then 1 else 0 := by
      simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
      rw [EuclideanSpace.inner_single_left]
      simp [PiLp.single_apply, (R.cosetLabel_injective u).eq_iff]
    simp_rw [hinner]
    simp [Nat.card_eq_fintype_card]
  · rw [if_neg huv]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    have hlabel : R.cosetLabel u k ≠ R.cosetLabel v h :=
      fun heq => huv (R.cosetLabel_eq_implies_logical_eq u v k h heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel]
theorem cosetNormalization_conj_mul_card (R : CubicRowFamily p Logical Stabilizer Site) :
    starRingEnd Complex (cosetNormalization p Stabilizer) * cosetNormalization p Stabilizer *
        (Nat.card (StabilizerLabel p Stabilizer) : Complex) = 1 := by
  have hpos : (0 : Real) < Nat.card (StabilizerLabel p Stabilizer) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (StabilizerLabel p Stabilizer))
  have hsqrt :
      (Real.sqrt (Nat.card (StabilizerLabel p Stabilizer) : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  unfold cosetNormalization
  rw [map_inv₀, Complex.conj_ofReal]
  field_simp
  norm_cast
  exact (Real.sq_sqrt hpos.le).symm
theorem cosetKet_inner (R : CubicRowFamily p Logical Stabilizer Site)
    (u v : Logical → ZMod p) :
    inner Complex (R.cosetKet u) (R.cosetKet v) = if u = v then 1 else 0 := by
  unfold cosetKet
  rw [inner_smul_left, inner_smul_right, uniformCosetSum_inner]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    rw [← mul_assoc]
    exact R.cosetNormalization_conj_mul_card
  · simp [huv]
theorem cosetKet_orthonormal (R : CubicRowFamily p Logical Stabilizer Site) :
    Orthonormal Complex R.cosetKet := by
  rw [orthonormal_iff_ite]
  intro u v
  exact R.cosetKet_inner u v
noncomputable def encodingLinearMap (R : CubicRowFamily p Logical Stabilizer Site) :
    PrimeQuditRegister p Logical →ₗ[Complex] PrimeQuditRegister p Site where
  toFun psi := ∑ u : Logical → ZMod p, psi u • R.cosetKet u
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]
theorem encodingLinearMap_map_inner (R : CubicRowFamily p Logical Stabilizer Site)
    (psi chi : PrimeQuditRegister p Logical) :
    inner Complex (R.encodingLinearMap psi) (R.encodingLinearMap chi) =
      inner Complex psi chi := by
  change inner Complex
      (∑ u : Logical → ZMod p, psi u • R.cosetKet u)
      (∑ u : Logical → ZMod p, chi u • R.cosetKet u) = inner Complex psi chi
  rw [R.cosetKet_orthonormal.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]
noncomputable def encodingIsometry (R : CubicRowFamily p Logical Stabilizer Site) :
    PrimeQuditRegister p Logical →ₗᵢ[Complex] PrimeQuditRegister p Site :=
  R.encodingLinearMap.isometryOfInner R.encodingLinearMap_map_inner
noncomputable def encodedCarrier (R : CubicRowFamily p Logical Stabilizer Site) :
    Submodule Complex (PrimeQuditRegister p Site) :=
  R.encodingIsometry.toLinearMap.range
noncomputable def quantumCode (R : CubicRowFamily p Logical Stabilizer Site) :
    QuantumCode (PrimeQuditRegister p Site) where
  carrier := R.encodedCarrier
noncomputable def encodedCode (R : CubicRowFamily p Logical Stabilizer Site) :
    EncodedCode (PrimeQuditRegister p Logical) (PrimeQuditRegister p Site) where
  code := R.quantumCode
  encoding := LinearIsometry.equivRange R.encodingIsometry
def logicalInverseExponent (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : ZMod p :=
  -(∑ a : Logical, u a ^ 3 * R.epsilon a)
def logicalInverseAmplitude (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) : Complex :=
  phase p (R.logicalInverseExponent u)
noncomputable def logicalInverseU13 (R : CubicRowFamily p Logical Stabilizer Site) :
    UnitaryTransport (PrimeQuditRegister p Logical) (PrimeQuditRegister p Logical) where
  toLinearEquiv := diagonalLinearEquiv R.logicalInverseAmplitude
    (fun u => phase p (-R.logicalInverseExponent u))
    (by
      intro u
      change phase p (-R.logicalInverseExponent u) * phase p (R.logicalInverseExponent u) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro u
      change phase p (R.logicalInverseExponent u) * phase p (-R.logicalInverseExponent u) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner R.logicalInverseAmplitude
    (fun u => phase_mul_conj p (R.logicalInverseExponent u))
@[simp]
theorem logicalInverseU13_apply (R : CubicRowFamily p Logical Stabilizer Site)
    (psi : PrimeQuditRegister p Logical) (u : Logical → ZMod p) :
    R.logicalInverseU13 psi u = R.logicalInverseAmplitude u * psi u :=
  rfl
end CubicRowFamily
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]
noncomputable def physicalU13 (R : CubicRowFamily p Logical Stabilizer Site) :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) :=
  _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p
noncomputable def physicalGateModel (R : CubicRowFamily p Logical Stabilizer Site) :
    FinitePhysicalGateModel Site (PrimeQuditRegister p Site) :=
  physicalU13GateModel p
noncomputable def physicalU13SitewiseFactorization (R : CubicRowFamily p Logical Stabilizer Site) :
    SitewiseTransversalityData R.physicalGateModel R.physicalU13 :=
  _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13SitewiseFactorization p
end CubicRowFamily
namespace CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site] [DecidableEq Site]
end CubicRowFamily
def singleLogicalLabelEquiv (p : Nat) [NeZero p] :
    ZMod p ≃ (Fin 1 → ZMod p) where
  toFun x := fun _ => x
  invFun label := label 0
  left_inv _ := rfl
  right_inv label := by
    funext index
    fin_cases index
    rfl
noncomputable def singleLogicalRegisterEquiv (p : Nat) [NeZero p] :
    PrimeQudit p ≃ₗᵢ[Complex] PrimeQuditRegister p (Fin 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (singleLogicalLabelEquiv p)
noncomputable def singleLogicalRegisterTransport (p : Nat) [NeZero p] :
    UnitaryTransport (PrimeQudit p) (PrimeQuditRegister p (Fin 1)) where
  toLinearEquiv := (singleLogicalRegisterEquiv p).toLinearEquiv
  map_inner := fun psi chi => (singleLogicalRegisterEquiv p).inner_map_map psi chi
noncomputable def fiveSiteSingleLogical : CubicRowFamily 5 (Fin 1) Empty (Fin 5) where
  logicalRow _ site := if site = 0 then 1 else 0
  stabilizerRow s := Empty.elim s
  rowIndependent := by
    intro u h hzero
    constructor
    · funext a
      fin_cases a
      have hpoint := congrFun hzero 0
      simpa using hpoint
    · funext s
      exact Empty.elim s
  stabilizerTriple_zero := by
    intro a b c hcontains
    rcases hcontains with ⟨s, _⟩ | ⟨s, _⟩ | ⟨s, _⟩ <;> exact Empty.elim s
  logicalTriple_offDiagonal_zero := by
    intro a b c hnot
    exfalso
    apply hnot
    fin_cases a
    fin_cases b
    fin_cases c
    exact ⟨rfl, rfl⟩
namespace fiveSiteSingleLogical
noncomputable def encodedCode :
    EncodedCode (PrimeQudit 5) (PrimeQuditRegister 5 (Fin 5)) where
  code := CubicRowFamily.quantumCode fiveSiteSingleLogical
  encoding := (singleLogicalRegisterEquiv 5).trans
    (CubicRowFamily.encodedCode fiveSiteSingleLogical).encoding
noncomputable def logicalInverseU13 :
    UnitaryTransport (PrimeQudit 5) (PrimeQudit 5) where
  toLinearEquiv := ((singleLogicalRegisterTransport 5).trans
    (CubicRowFamily.logicalInverseU13 fiveSiteSingleLogical)).trans
      (singleLogicalRegisterTransport 5).symm |>.toLinearEquiv
  map_inner := ((singleLogicalRegisterTransport 5).trans
    (CubicRowFamily.logicalInverseU13 fiveSiteSingleLogical)).trans
      (singleLogicalRegisterTransport 5).symm |>.map_inner
end fiveSiteSingleLogical
noncomputable def fiveSiteSingleLogical_sitewiseFactorization :
    SitewiseTransversalityData fiveSiteSingleLogical.physicalGateModel
      fiveSiteSingleLogical.physicalU13 :=
  fiveSiteSingleLogical.physicalU13SitewiseFactorization
end QEC.Distillation.KT19PrimeQuditCSS


