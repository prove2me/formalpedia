-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:01.978097+00:00
-- url     : https://prove2.me/theorems/2f7cbd7c-b2ad-42cc-829d-ebfba7fcf61e
-- title:
--   Aeval Root Eq Zero Iff
-- statement:
--   Definitions and structural lemmas for Aeval Root Eq Zero Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AevalRootEqZeroIff.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
namespace GlobalTheory.UTr
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
def IsCsr (P : B[X]) : Prop := P.Monic ∧ C (s (P.coeff 0)) * P = (P.map s).reflect P.natDegree
variable {s}
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in

theorem _root_.GlobalTheory.UTr.IsCsr.conj_mul_coeff_zero {P : B[X]}
    (h : _root_.GlobalTheory.UTr.IsCsr s P) : s (P.coeff 0) * P.coeff 0 = 1 := by
  have h0 := congrArg (fun Q => Q.coeff 0) h.2
  simp only [coeff_C_mul, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, coeff_map,
    coeff_natDegree, h.1.leadingCoeff, map_one] at h0
  exact h0
theorem isCsr_X_sub_C [Nontrivial B] {u : B} : IsCsr s (X - C u) ↔ s u * u = 1 := by
  refine ⟨fun h => by simpa using h.conj_mul_coeff_zero, fun h => ⟨monic_X_sub_C u, ?_⟩⟩
  have e : reflect 1 (X : B[X]) = 1 := by simpa using reflect_monomial (R := B) 1 1
  have e' : C (s u) * C u = (1 : B[X]) := by rw [← C_mul, h, C_1]
  rw [natDegree_X_sub_C, Polynomial.map_sub, map_X, map_C, reflect_sub, e, reflect_C]
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg]
  linear_combination e'
theorem IsCsr.mul {P Q : B[X]} (hP : IsCsr s P) (hQ : IsCsr s Q) : IsCsr s (P * Q) := by
  refine ⟨hP.1.mul hQ.1, ?_⟩
  rw [hP.1.natDegree_mul hQ.1, Polynomial.map_mul, reflect_mul _ _ natDegree_map_le natDegree_map_le, ← hP.2, ← hQ.2,
    mul_coeff_zero, map_mul, C_mul]
  ring
theorem IsCsr.map {P : B[X]} (hP : IsCsr s P) (φ : B →+* B') (hφ : ∀ b, φ (s b) = s' (φ b)) :
    IsCsr s' (P.map φ) := by
  refine ⟨hP.1.map φ, ?_⟩
  nontriviality B'
  have e : s'.comp φ = φ.comp s := RingHom.ext fun b => (hφ b).symm
  rw [hP.1.natDegree_map, Polynomial.map_map, e, ← Polynomial.map_map, reflect_map, ← hP.2, Polynomial.map_mul, map_C, coeff_map, hφ]
variable (s) in

abbrev Csr : Type := {P : B[X] // IsCsr s P}
def Csr.mul (P Q : Csr s) : Csr s := ⟨P.1 * Q.1, P.2.mul Q.2⟩
def Csr.map (P : Csr s) (φ : B →+* B') (hφ : ∀ b, φ (s b) = s' (φ b)) : Csr s' := ⟨P.1.map φ, P.2.map φ hφ⟩
abbrev Csr.Factorisation (P : Csr s) : Type := {p : Csr s × Csr s // p.1.1 * p.2.1 = P.1}
def Csr.mulFactorisation (P₁ P₂ : Csr s) : (P₁.mul P₂).Factorisation := ⟨(P₁, P₂), rfl⟩
def Csr.Factorisation.map {P : Csr s} (p : P.Factorisation) (φ : B →+* B') (hφ : ∀ b, φ (s b) = s' (φ b)) :
    (P.map φ hφ).Factorisation :=
  ⟨(p.1.1.map φ hφ, p.1.2.map φ hφ), (Polynomial.map_mul φ).symm.trans (congrArg (Polynomial.map φ) p.2)⟩
def Csr.Factorisation.res {P : Csr s} (p : P.Factorisation) : B := resultant p.1.1.1 p.1.2.1
def Alg (P : Csr s) : Type := AdjoinRoot P.1
variable (P : Csr s)
instance : CommRing (Alg P) := inferInstanceAs (CommRing (AdjoinRoot P.1))
instance {S : Type} [CommSemiring S] [Algebra S B] : Algebra S (Alg P) := inferInstanceAs (Algebra S (AdjoinRoot P.1))
instance {S : Type} [CommSemiring S] [Algebra S B] : IsScalarTower S B (Alg P) :=
  inferInstanceAs (IsScalarTower S B (AdjoinRoot P.1))
def root : Alg P := AdjoinRoot.root P.1
def powBasis : Module.Basis (Fin P.1.natDegree) B (Alg P) := (AdjoinRoot.powerBasis' P.2.1).basis
instance : Module.Free B (Alg P) := .of_basis (powBasis P)
instance : Module.Finite B (Alg P) := .of_basis (powBasis P)
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

theorem _root_.GlobalTheory.UTr.aeval_root_eq_zero_iff {q : B[X]} :
    aeval (_root_.GlobalTheory.UTr.root P) q = 0 ↔ P.1 ∣ q := by
  change aeval (AdjoinRoot.root P.1) q = 0 ↔ _
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

theorem _root_.GlobalTheory.UTr.aeval_root :
    aeval (_root_.GlobalTheory.UTr.root P) P.1 = 0 :=
  (_root_.GlobalTheory.UTr.aeval_root_eq_zero_iff P).2 dvd_rfl
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

theorem _root_.GlobalTheory.UTr.exists_aeval_root (z : _root_.GlobalTheory.UTr.Alg P) :
    ∃ q : B[X], aeval (_root_.GlobalTheory.UTr.root P) q = z := by
  obtain ⟨q, hq⟩ : ∃ q, AdjoinRoot.mk P.1 q = z := AdjoinRoot.mk_surjective z
  exact ⟨q, (AdjoinRoot.aeval_eq q).trans hq⟩
variable {P} in

theorem Alg.induction {p : Alg P → Prop} (hC : ∀ b, p (algebraMap B _ b)) (hr : p (root P))
    (hadd : ∀ y z, p y → p z → p (y + z)) (hmul : ∀ y z, p y → p z → p (y * z)) (z : Alg P) : p z := by
  obtain ⟨q, rfl⟩ := exists_aeval_root P z
  induction q using Polynomial.induction_on with
  | C a => simpa using hC a
  | add a b ha hb => simpa using hadd _ _ ha hb
  | monomial n a h => rw [pow_succ, ← mul_assoc, map_mul, aeval_X]; exact hmul _ _ h hr
variable {P} in

theorem Alg.ringHom_ext {S : Type} [Ring S] {f g : Alg P →+* S} (hC : ∀ b, f (algebraMap B _ b) = g (algebraMap B _ b))
    (hr : f (root P) = g (root P)) : f = g :=
  RingHom.ext (Alg.induction hC hr (fun y z hy hz => by rw [map_add, map_add, hy, hz])
    fun y z hy hz => by rw [map_mul, map_mul, hy, hz])
def gamma : (Alg P)ˣ :=
  Units.mkOfMulEqOne (root P) (-(algebraMap B _ (s (P.1.coeff 0)) * aeval (root P) P.1.divX)) (by
    have h := aeval_root P
    rw [← X_mul_divX_add P.1, map_add, map_mul, aeval_X, aeval_C] at h
    have h1 := congrArg (algebraMap B (Alg P)) P.2.conj_mul_coeff_zero
    rw [map_mul, map_one] at h1
    linear_combination (-algebraMap B (Alg P) (s (P.1.coeff 0))) * h + h1)
@[simp] theorem val_gamma : (gamma P : Alg P) = root P := rfl
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

theorem _root_.GlobalTheory.UTr.eval₂_gamma_inv :
    P.1.eval₂ ((algebraMap B (_root_.GlobalTheory.UTr.Alg P)).comp s)
      ((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) = 0 := by
  letI := (_root_.GlobalTheory.UTr.gamma P)⁻¹.invertible
  have key := eval₂_reflect_mul_pow (algebraMap B (_root_.GlobalTheory.UTr.Alg P))
    (((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) :
      _root_.GlobalTheory.UTr.Alg P) P.1.natDegree (P.1.map s) (natDegree_map_le)
  have hroot : ⅟(((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) :
      _root_.GlobalTheory.UTr.Alg P) = _root_.GlobalTheory.UTr.root P := rfl
  rw [← eval₂_map, ← key, ← P.2.2, hroot, ← aeval_def, map_mul, _root_.GlobalTheory.UTr.aeval_root, mul_zero, zero_mul]
def conj : Alg P →+* Alg P := AdjoinRoot.lift _ _ (eval₂_gamma_inv P)
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

@[simp] theorem _root_.GlobalTheory.UTr.conj_algebraMap (b : B) :
    _root_.GlobalTheory.UTr.conj P (algebraMap B _ b) = algebraMap B _ (s b) :=
  AdjoinRoot.lift_of _
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

@[simp] theorem _root_.GlobalTheory.UTr.conj_root :
    _root_.GlobalTheory.UTr.conj P (_root_.GlobalTheory.UTr.root P) =
      ((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) :=
  AdjoinRoot.lift_root _
theorem root_mul_conj_root : root P * conj P (root P) = 1 := by rw [conj_root]; exact (gamma P).mul_inv
theorem conj_smul (b : B) (z : Alg P) : conj P (b • z) = s b • conj P z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, conj_algebraMap]
def normU : (Alg P)ˣ →* (Alg P)ˣ := MonoidHom.id _ * Units.map (conj P : Alg P →* Alg P)
@[simp] theorem val_normU (z : (Alg P)ˣ) : (normU P z : Alg P) = z * conj P z := rfl
def tor : Subgroup (Alg P)ˣ := (normU P).ker
variable {P} in

theorem mem_tor {z : (Alg P)ˣ} : z ∈ tor P ↔ (z : Alg P) * conj P z = 1 := Units.ext_iff
theorem gamma_mem_tor : gamma P ∈ tor P := mem_tor.2 (root_mul_conj_root P)
def plus : Subgroup (Alg P)ˣ := (Units.map (conj P : Alg P →* Alg P)).eqLocus (MonoidHom.id _)
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in
variable {P} in

theorem _root_.GlobalTheory.UTr.mem_plus {x : (_root_.GlobalTheory.UTr.Alg P)ˣ} :
    x ∈ _root_.GlobalTheory.UTr.plus P ↔ _root_.GlobalTheory.UTr.conj P x = x := by
  change Units.map _ x = x ↔ _
  rw [Units.ext_iff]
  rfl
def norms : Subgroup (plus P) := (normU P).range.subgroupOf (plus P)
abbrev Cls : Type := plus P ⧸ norms P
variable {P} in

def Cls.rep (c : Cls P) : Alg P := ((Quotient.out c : plus P) : (Alg P)ˣ)
def torInt (O : Subring B) : Subgroup (tor P) := (UnitLemma.intUnits O (Alg P)).subgroupOf (tor P)
section Map
variable {P} {Q : Csr s'} (φ : B →+* B') (h : Q.1 ∣ P.1.map φ)
def algMap : Alg P →+* Alg Q :=
  AdjoinRoot.lift ((algebraMap B' (Alg Q)).comp φ) (root Q) (by
    rw [← eval₂_map]; exact (aeval_root_eq_zero_iff Q).2 h)
@[simp] theorem algMap_algebraMap (b : B) : algMap φ h (algebraMap B _ b) = algebraMap B' _ (φ b) :=
  AdjoinRoot.lift_of _
@[simp] theorem algMap_root : algMap φ h (root P) = root Q := AdjoinRoot.lift_root _
variable (hφ : ∀ b, φ (s b) = s' (φ b))
include hφ
theorem algMap_conj (z : Alg P) : algMap φ h (conj P z) = conj Q (algMap φ h z) := by
  refine RingHom.congr_fun (Alg.ringHom_ext (f := (algMap φ h).comp (conj P)) (g := (conj Q).comp (algMap φ h))
    (fun b => by simp [hφ]) ?_) z
  have h1 := congrArg (algMap φ h) (root_mul_conj_root P)
  rw [map_mul, map_one, algMap_root] at h1
  change algMap φ h (conj P (root P)) = conj Q (algMap φ h (root P))
  rw [algMap_root, conj_root Q]
  exact Units.eq_inv_of_mul_eq_one_left h1
def torMap : tor P →* tor Q :=
  ((Units.map (algMap φ h : Alg P →* Alg Q)).comp (tor P).subtype).codRestrict _ fun z => mem_tor.2 (by
    change algMap φ h (z.1 : Alg P) * conj Q (algMap φ h (z.1 : Alg P)) = 1
    rw [← algMap_conj φ h hφ, ← map_mul, mem_tor.1 z.2, map_one])
def plusMap : plus P →* plus Q :=
  ((Units.map (algMap φ h : Alg P →* Alg Q)).comp (plus P).subtype).codRestrict _ fun z => mem_plus.2 (by
    change conj Q (algMap φ h (z.1 : Alg P)) = algMap φ h (z.1 : Alg P)
    rw [← algMap_conj φ h hφ, mem_plus.1 z.2])
def clsMap : Cls P →* Cls Q :=
  QuotientGroup.map _ _ (plusMap φ h hφ) (by
    rintro x ⟨u, hu⟩
    refine ⟨Units.map (algMap φ h : Alg P →* Alg Q) u, Units.ext ?_⟩
    change algMap φ h (u : Alg P) * conj Q (algMap φ h (u : Alg P)) = algMap φ h (x.1 : Alg P)
    rw [← algMap_conj φ h hφ, ← map_mul, ← val_normU, hu]; rfl)
@[simp] theorem coe_torMap (z : tor P) : ((torMap φ h hφ z).1 : Alg Q) = algMap φ h (z.1 : Alg P) := rfl
end Map
variable {P} in

def Csr.Factorisation.fst (p : P.Factorisation) : Alg P →+* Alg p.1.1 :=
  algMap (RingHom.id B) (by rw [Polynomial.map_id]; exact Dvd.intro _ p.2)
variable {P} in

def Csr.Factorisation.snd (p : P.Factorisation) : Alg P →+* Alg p.1.2 :=
  algMap (RingHom.id B) (by rw [Polynomial.map_id]; exact Dvd.intro_left _ p.2)
def herm (x y z : Alg P) : B := Algebra.trace B _ (x * y * conj P z)
theorem herm_mul_mul (x u y z : Alg P) : herm P x (u * y) (u * z) = herm P (x * (u * conj P u)) y z := by
  rw [herm, herm, map_mul (conj P)]; congr 1; ring
def gram (x : Alg P) : Matrix (Fin P.1.natDegree) (Fin P.1.natDegree) B :=
  Matrix.of fun i j => herm P x (powBasis P j) (powBasis P i)
open Classical in
variable (s) in

def normSign (d : B) : ℤˣ := if ∃ u : Bˣ, d = u * s u then 1 else -1
def etaDet (x : Alg P) : ℤˣ := normSign s (gram P x).det
variable {n : Type} [Fintype n] [DecidableEq n]
def evalMat (g : Matrix n n B) (hg : aeval g P.1 = 0) : Alg P →ₐ[B] Matrix n n B :=
  Ideal.Quotient.liftₐ (Ideal.span {P.1}) (aeval g) fun q hq => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hq
    rw [map_mul, hg, zero_mul]
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in
variable {n : Type} [Fintype n] [DecidableEq n] in

@[simp] theorem _root_.GlobalTheory.UTr.evalMat_root (g : Matrix n n B) (hg : aeval g P.1 = 0) :
    _root_.GlobalTheory.UTr.evalMat P g hg (_root_.GlobalTheory.UTr.root P) = g := by
  change Ideal.Quotient.liftₐ _ _ _ (Ideal.Quotient.mk _ X) = g
  exact aeval_X g
variable {J : Matrix n n B}
open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable {J : Matrix n n B} in

theorem _root_.GlobalTheory.UTr.cT_evalMat (g : _root_.Formalism.UG.UJ s J)
    (hg : aeval g.1.1 P.1 = 0) (z : _root_.GlobalTheory.UTr.Alg P) :
    _root_.Formalism.UG.cT s (_root_.GlobalTheory.UTr.evalMat P _ hg z) * J =
      J * _root_.GlobalTheory.UTr.evalMat P _ hg (_root_.GlobalTheory.UTr.conj P z) := by
  set E := _root_.GlobalTheory.UTr.evalMat P _ hg
  set γ := _root_.GlobalTheory.UTr.gamma P
  have hγ : ((γ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
      _root_.GlobalTheory.UTr.root P := rfl
  have hgU : _root_.Formalism.UG.cT s g.1.1 * J * g.1.1 = J := g.2
  have hroot : E (_root_.GlobalTheory.UTr.root P) = g.1.1 :=
    _root_.GlobalTheory.UTr.evalMat_root P _ hg
  have hgγ : g.1.1 * E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)
      = 1 := by
    calc _ = E (_root_.GlobalTheory.UTr.root P) *
          E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) := by
          rw [hroot]
      _ = 1 := by rw [← map_mul, ← hγ, Units.mul_inv, map_one]
  have hside : _root_.Formalism.UG.cT s g.1.1 * J =
      J * E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) := by
    calc _ = _root_.Formalism.UG.cT s g.1.1 * J * (g.1.1 *
          E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)) := by
          rw [hgγ, mul_one]
      _ = _ := by rw [← mul_assoc, hgU]
  have hcT_alg : ∀ a : B, _root_.Formalism.UG.cT s (algebraMap B (Matrix n n B) a) =
      algebraMap B (Matrix n n B) (s a) := by
    intro a
    unfold _root_.Formalism.UG.cT
    ext i j
    simp [algebraMap_matrix_apply, apply_ite s, eq_comm]
  have hcT_add : ∀ M N : Matrix n n B, _root_.Formalism.UG.cT s (M + N) = _root_.Formalism.UG.cT s M + _root_.Formalism.UG.cT s N := by
    intro M N
    unfold _root_.Formalism.UG.cT
    ext i j
    simp
  obtain ⟨q, rfl⟩ := _root_.GlobalTheory.UTr.exists_aeval_root P z
  induction q using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, AlgHom.commutes, _root_.GlobalTheory.UTr.conj_algebraMap, AlgHom.commutes,
      hcT_alg]
    exact Algebra.commutes _ _
  | add p q hp hq =>
    rw [map_add, map_add, map_add, map_add, hcT_add, add_mul, hp, hq, mul_add]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval _) (C a * X ^ k) X, aeval_X]
    generalize aeval (_root_.GlobalTheory.UTr.root P) (C a * X ^ k) = w at ih ⊢
    simp only [map_mul]
    rw [_root_.Formalism.UG.cT_mul, hroot, _root_.GlobalTheory.UTr.conj_root, mul_assoc, ih, ← mul_assoc, hside, mul_assoc,
      ← map_mul, ← map_mul,
      mul_comm ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)]
def torToU (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) : tor P →* UJ s J :=
  ((Units.map (evalMat P _ hg : Alg P →* Matrix n n B)).comp (tor P).subtype).codRestrict _ fun z => by
    change cT s (evalMat P _ hg (z.1 : Alg P)) * J * evalMat P _ hg (z.1 : Alg P) = J
    rw [cT_evalMat, Matrix.mul_assoc, ← map_mul, mul_comm (conj P _), mem_tor.1 z.2, map_one, Matrix.mul_one]
@[simp] theorem coe_torToU (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) (z : tor P) :
    (torToU P g hg z).1.1 = evalMat P _ hg (z.1 : Alg P) := rfl
theorem torToU_gamma (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) : torToU P g hg ⟨gamma P, gamma_mem_tor P⟩ = g :=
  Subtype.ext (Units.ext (evalMat_root P _ hg))
def torToCent (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) : tor P →* Subgroup.centralizer ({g} : Set (UJ s J)) :=
  (torToU P g hg).codRestrict _ fun z => Subgroup.mem_centralizer_singleton_iff.2 (by
    have := congrArg (torToU P g hg) (mul_comm z ⟨gamma P, gamma_mem_tor P⟩)
    rwa [map_mul, map_mul, torToU_gamma] at this)
theorem hform_mulVec (J g : Matrix n n B) (u v : n → B) :
    hform s J (g *ᵥ u) (g *ᵥ v) = hform s (cT s g * J * g) u v := by
  have key : ∀ (M : Matrix n n B) (a b : n → B), hform s M a b = (s ∘ a) ⬝ᵥ M *ᵥ b := fun M a b => by
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e : s ∘ (g *ᵥ u) = (s ∘ u) ᵥ* cT s g := by
    rw [cT, Matrix.vecMul_transpose]; funext i; exact RingHom.map_mulVec s g u i
  rw [key, key, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
theorem hform_single (J : Matrix n n B) (i j : n) : hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite s, ite_mul]
variable (J) in

abbrev Isom (x : Alg P) : Type := {i : Alg P ≃ₗ[B] (n → B) // ∀ y z, hform s J (i z) (i y) = herm P x y z}
def stdIsom (x : Alg P) : Isom P (gram P x) x :=
  ⟨(powBasis P).equivFun, fun y z => by
    conv_rhs => rw [← (powBasis P).sum_equivFun y, ← (powBasis P).sum_equivFun z]
    simp only [hform, gram, herm, Matrix.of_apply, map_sum, conj_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
      smul_mul_assoc, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring⟩
variable {P}
def mulMat (i : Alg P ≃ₗ[B] (n → B)) : Alg P →ₐ[B] Matrix n n B :=
  (LinearMap.toMatrixAlgEquiv'.toAlgHom.comp (i.conjAlgEquiv B).toAlgHom).comp (Algebra.lmul B (Alg P))
theorem mulMat_mulVec (i : Alg P ≃ₗ[B] (n → B)) (z y : Alg P) : mulMat i z *ᵥ i y = i (z * y) := by
  change LinearMap.toMatrix' (i.conjAlgEquiv B (Algebra.lmul B (Alg P) z)) *ᵥ i y = _
  rw [LinearMap.toMatrix'_mulVec]
  simp [LinearEquiv.conjAlgEquiv_apply]
variable {x x' : Alg P}
def Isom.elt (i : Isom P J x) : UJ s J :=
  ⟨Units.map (mulMat i.1 : Alg P →* Matrix n n B) (gamma P), by
    change cT s (mulMat i.1 (root P)) * J * mulMat i.1 (root P) = J
    ext a b
    obtain ⟨y, hy⟩ := i.1.surjective (Pi.single a 1)
    obtain ⟨z, hz⟩ := i.1.surjective (Pi.single b 1)
    rw [← hform_single (s := s) (_ * _ * _), ← hform_single (s := s) J, ← hform_mulVec, ← hy, ← hz, mulMat_mulVec, mulMat_mulVec,
      i.2, i.2, herm_mul_mul, root_mul_conj_root, mul_one]⟩
def Isom.mulNorm (i : Isom P J x) (u : (Alg P)ˣ) : Isom P J (x * (u * conj P u)) :=
  ⟨(u.mulLeftLinearEquiv B (Alg P)).trans i.1, fun y z => (i.2 _ _).trans (herm_mul_mul P x u y z)⟩
variable (P) in

def IsCyc (g : Matrix n n B) : Prop := ∃ i : Alg P ≃ₗ[B] (n → B), mulMat i (root P) = g
example [Nontrivial B] {α β : B} (hα : s α * α = 1) (hβ : s β * β = 1) :
    (Csr.mulFactorisation ⟨X - C α, isCsr_X_sub_C.2 hα⟩ ⟨X - C β, isCsr_X_sub_C.2 hβ⟩).res = α - β := by
  change resultant (X - C α) (X - C β) = α - β
  rw [natDegree_X_sub_C α, resultant_X_sub_C_left _ _ _ le_rfl]; simp
example : IsCsr (starRingEnd ℂ) (X - C Complex.I) ∧ ¬ IsCsr (starRingEnd ℂ) (X - C 2) :=
  ⟨isCsr_X_sub_C.2 (by simp), fun h => by
    have := isCsr_X_sub_C.1 h
    rw [map_ofNat] at this; norm_num at this⟩
example : normSign (starRingEnd ℂ) (-1) = -1 ∧ normSign (starRingEnd ℂ) 2 = 1 :=
  ⟨if_neg fun ⟨u, hu⟩ => by
    rw [Complex.mul_conj] at hu
    have : (-1 : ℝ) = Complex.normSq u := by exact_mod_cast hu
    linarith [Complex.normSq_nonneg u],
  if_pos ⟨Units.mk0 (1 + Complex.I) (fun h => by simpa using congrArg Complex.re h), by
    simp [Complex.ext_iff]; norm_num⟩⟩
end GlobalTheory.UTr


