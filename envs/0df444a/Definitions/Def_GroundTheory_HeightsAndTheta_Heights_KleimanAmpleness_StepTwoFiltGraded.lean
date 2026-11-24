-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:28.383087+00:00
-- url     : https://prove2.me/theorems/fbab0440-935b-4e93-b5d5-a4e40b65591f
-- title:
--   Step Two Filt Graded
-- statement:
--   Definitions and structural lemmas for Step Two Filt Graded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_of_isHomogeneous_046c5887f5b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
section Laurent
variable (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E]
set_option linter.unusedVariables false in

abbrev LaurentSpace (x : Fin (N + 1) → Ω) (E : Type v) [Zero E] : Type v := ℤ →₀ E
def laurentShift : Module.End Ω (LaurentSpace x E) := Finsupp.lmapDomain E Ω (· + 1)
variable (S) in

def laurentAct : Poly S N →+* Module.End Ω (LaurentSpace x E) :=
  (Polynomial.aeval (laurentShift x E)).toRingHom.comp (cone (S := S) x).toRingHom
instance : Module (Poly S N) (LaurentSpace x E) := Module.compHom _ (laurentAct S x E)
variable {x E}
variable (x) in

def laurentSingle (c : ℤ) (m : E) : LaurentSpace x E := Finsupp.single c m
theorem laurentSingle_apply (c a : ℤ) (m : E) :
    laurentSingle x c m a = if c = a then m else 0 := Finsupp.single_apply
theorem laurent_smul_def (p : Poly S N) (m : LaurentSpace x E) : p • m = laurentAct S x E p m := rfl
theorem laurentShift_pow_single (d : ℕ) (c : ℤ) (m : E) :
    (laurentShift x E ^ d) (laurentSingle x c m) = laurentSingle x (c + d) m := by
  induction d generalizing c with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, Module.End.mul_apply]
    change (laurentShift x E ^ d) (Finsupp.mapDomain (· + 1) (Finsupp.single c m)) = _
    rw [Finsupp.mapDomain_single]
    change (laurentShift x E ^ d) (laurentSingle x (c + 1) m) = _
    rw [ih]
    congr 1
    push_cast
    ring
theorem laurent_smul_single {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) (c : ℤ) (m : E) :
    f • laurentSingle x c m = laurentSingle x (c + d) (aeval x f • m) := by
  rw [laurent_smul_def, laurentAct, RingHom.comp_apply]
  change (Polynomial.aeval (laurentShift x E)) (cone x f) _ = _
  rw [cone_of_isHomogeneous x hf, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    Module.End.mul_apply, laurentShift_pow_single, Module.algebraMap_end_apply]
  exact Finsupp.smul_single _ _ _
variable [Module S E] [IsScalarTower S Ω E]
theorem laurent_smul_apply_of_isHomogeneous {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d)
    (m : LaurentSpace x E) (c : ℤ) : (f • m) c = aeval x f • m (c - d) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [smul_add, Finsupp.add_apply, ha, hb, Finsupp.add_apply, smul_add]
  | single a m =>
    change (f • laurentSingle x a m) c = aeval x f • laurentSingle x a m (c - d)
    rw [laurent_smul_single hf, laurentSingle_apply, laurentSingle_apply]
    by_cases h : a = c - d
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, smul_zero]
theorem laurent_smul_apply (f : Poly S N) (m : LaurentSpace x E) (c : ℤ) :
    (f • m) c = ∑ i ∈ Finset.range (f.totalDegree + 1),
      aeval x (homogeneousComponent i f) • m (c - i) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [Finset.sum_smul, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ =>
    laurent_smul_apply_of_isHomogeneous (homogeneousComponent_isHomogeneous i f) m c
instance : IsScalarTower S (Poly S N) (LaurentSpace x E) where
  smul_assoc s p m := by
    rw [Algebra.smul_def, laurent_smul_def, map_mul, Module.End.mul_apply, ← laurent_smul_def p m]
    change (Polynomial.aeval (laurentShift x E)) (cone x (algebraMap S (Poly S N) s)) _ = _
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.aeval_C,
      Module.algebraMap_end_apply, algebraMap_smul]
end Laurent
section Quot
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
def FinGradedSub.laurent (M : FinGradedSub (S := S) (x := x) E) :
    Submodule (Poly S N) (LaurentSpace x E) where
  carrier := {m | ∀ c, m c ∈ M.piece c}
  add_mem' {a b} ha hb c := by
    rw [Finsupp.add_apply]
    exact add_mem (ha c) (hb c)
  zero_mem' c := by
    rw [Finsupp.zero_apply]
    exact zero_mem _
  smul_mem' f m hm c := by
    rw [laurent_smul_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := M.smul_mem i (c - i) _ _ (homogeneousComponent_isHomogeneous i f) (hm (c - i))
    rwa [sub_add_cancel] at this
theorem FinGradedSub.mem_laurent {M : FinGradedSub (S := S) (x := x) E} {m : LaurentSpace x E} :
    m ∈ M.laurent ↔ ∀ c, m c ∈ M.piece c := Iff.rfl
theorem laurentSingle_mem {M : FinGradedSub (S := S) (x := x) E} {c : ℤ} {z : E} (hz : z ∈ M.piece c) :
    laurentSingle x c z ∈ M.laurent := by
  rw [FinGradedSub.mem_laurent]
  intro a
  rw [laurentSingle_apply]
  split_ifs with h
  · subst h; exact hz
  · exact zero_mem _
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
abbrev quotLaurent : Type v := M₁.laurent ⧸ M₂.laurent.comap M₁.laurent.subtype
def quotIota (c : ℤ) : M₁.piece c →ₗ[S] quotLaurent M₁ M₂ where
  toFun z := Submodule.Quotient.mk ⟨laurentSingle x c z, laurentSingle_mem z.2⟩
  map_add' a b := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact Finsupp.single_add _ _ _
  map_smul' s a := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact (Finsupp.smul_single _ _ _).symm
theorem quotIota_apply (c : ℤ) (z : M₁.piece c) :
    quotIota M₁ M₂ c z = Submodule.Quotient.mk ⟨laurentSingle x c z, laurentSingle_mem z.2⟩ := rfl
theorem smul_quotIota {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) {c : ℤ} (z : M₁.piece c) :
    f • quotIota M₁ M₂ c z =
      quotIota M₁ M₂ (c + d) ⟨aeval x f • (z : E), M₁.smul_mem d c f z hf z.2⟩ := by
  rw [quotIota_apply, quotIota_apply, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_smul]
  exact laurent_smul_single hf c (z : E)
theorem quotIota_eq_zero_iff {c : ℤ} (z : M₁.piece c) :
    quotIota M₁ M₂ c z = 0 ↔ (z : E) ∈ M₂.piece c := by
  rw [quotIota_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · intro h
    have := FinGradedSub.mem_laurent.mp h c
    rwa [laurentSingle_apply, if_pos rfl] at this
  · exact laurentSingle_mem
def laurentCoeff (c : ℤ) : M₁.laurent →ₗ[S] M₁.piece c :=
  LinearMap.codRestrict (M₁.piece c)
    ((Finsupp.lapply c).comp (M₁.laurent.subtype.restrictScalars S)) fun m => m.2 c
def quotProj (c : ℤ) : quotLaurent M₁ M₂ →+ quotLaurent M₁ M₂ :=
  QuotientAddGroup.lift _ ((quotIota M₁ M₂ c).comp (laurentCoeff M₁ c)).toAddMonoidHom
    fun _ hm => AddMonoidHom.mem_ker.mpr ((quotIota_eq_zero_iff M₁ M₂ _).mpr (hm c))
theorem quotProj_iota_self (c : ℤ) (z : M₁.piece c) :
    quotProj M₁ M₂ c (quotIota M₁ M₂ c z) = quotIota M₁ M₂ c z := by
  have h : (⟨laurentSingle x c (z : E) c, FinGradedSub.mem_laurent.mp (laurentSingle_mem z.2) c⟩ :
      M₁.piece c) = z :=
    Subtype.ext (by change laurentSingle x c (z : E) c = (z : E); rw [laurentSingle_apply, if_pos rfl])
  exact congrArg (quotIota M₁ M₂ c) h
theorem quotProj_iota_ne {c c' : ℤ} (h : c' ≠ c) (z : M₁.piece c') :
    quotProj M₁ M₂ c (quotIota M₁ M₂ c' z) = 0 := by
  have h0 : (⟨laurentSingle x c' (z : E) c, FinGradedSub.mem_laurent.mp (laurentSingle_mem z.2) c⟩ :
      M₁.piece c) = 0 :=
    Subtype.ext (by change laurentSingle x c' (z : E) c = 0; rw [laurentSingle_apply, if_neg h])
  exact (congrArg (quotIota M₁ M₂ c) h0).trans (map_zero _)
def quotPiece (c : ℤ) : Submodule S (quotLaurent M₁ M₂) := LinearMap.range (quotIota M₁ M₂ c)
theorem quotProj_coe (c : ℤ) (v : DirectSum ℤ fun c => quotPiece M₁ M₂ c) :
    quotProj M₁ M₂ c (DirectSum.coeAddMonoidHom (quotPiece M₁ M₂) v) = (v c : quotLaurent M₁ M₂) := by
  induction v using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | of c' y =>
    rw [DirectSum.coeAddMonoidHom_of]
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp y.2
    by_cases h : c' = c
    · subst h
      rw [DirectSum.of_eq_same, ← hz, quotProj_iota_self]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), ← hz, quotProj_iota_ne M₁ M₂ h]
      rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, DirectSum.add_apply, Submodule.coe_add]
theorem laurent_eq_sum (m : M₁.laurent) :
    m = ∑ c ∈ (m : LaurentSpace x E).support,
      (⟨laurentSingle x c ((m : LaurentSpace x E) c), laurentSingle_mem (m.2 c)⟩ : M₁.laurent) := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  exact (Finsupp.sum_single (m : LaurentSpace x E)).symm
theorem quotPiece_isInternal : DirectSum.IsInternal (quotPiece M₁ M₂) := by
  constructor
  · intro v w hvw
    refine DFinsupp.ext fun c => Subtype.ext ?_
    rw [← quotProj_coe, ← quotProj_coe, hvw]
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine AddMonoidHom.mem_mrange.mp ?_
    rw [laurent_eq_sum M₁ m, ← Submodule.mkQ_apply, map_sum]
    refine AddSubmonoid.sum_mem _ fun c _ => ⟨DirectSum.of (fun c => quotPiece M₁ M₂ c) c
      ⟨quotIota M₁ M₂ c ⟨_, FinGradedSub.mem_laurent.mp m.2 c⟩, LinearMap.mem_range_self _ _⟩, ?_⟩
    rw [DirectSum.coeAddMonoidHom_of]
    rfl
def quotLaurentGraded : GradedPMod S N (quotLaurent M₁ M₂) where
  piece := quotPiece M₁ M₂
  isInternal := quotPiece_isInternal M₁ M₂
  smul_mem d c f y hf hy := by
    obtain ⟨z, rfl⟩ := hy
    exact ⟨_, (smul_quotIota M₁ M₂ hf z).symm⟩
end Quot
section Filt
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
def filtPiece (A : Submodule (Poly S N) (quotLaurent M₁ M₂)) (c : ℤ) : Submodule S E :=
  (Submodule.comap (quotIota M₁ M₂ c) (A.restrictScalars S)).map (M₁.piece c).subtype
variable {M₁ M₂}
theorem mem_filtPiece {A : Submodule (Poly S N) (quotLaurent M₁ M₂)} {c : ℤ} {z : E} :
    z ∈ filtPiece M₁ M₂ A c ↔ ∃ h : z ∈ M₁.piece c, quotIota M₁ M₂ c ⟨z, h⟩ ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hA⟩
    exact ⟨⟨z, h⟩, hA, rfl⟩
theorem filtPiece_smul_mem (A : Submodule (Poly S N) (quotLaurent M₁ M₂)) {d : ℕ} {c : ℤ} {f : Poly S N}
    {z : E} (hf : f.IsHomogeneous d) (hz : z ∈ filtPiece M₁ M₂ A c) :
    aeval x f • z ∈ filtPiece M₁ M₂ A (c + d) := by
  obtain ⟨h, hA⟩ := mem_filtPiece.mp hz
  refine mem_filtPiece.mpr ⟨M₁.smul_mem d c f z hf h, ?_⟩
  have key := A.smul_mem f hA
  rw [smul_quotIota M₁ M₂ hf] at key
  exact key
variable (M₁ M₂) in

def IsProjStable (A : Submodule (Poly S N) (quotLaurent M₁ M₂)) : Prop :=
  ∀ y ∈ A, ∀ c, quotProj M₁ M₂ c y ∈ A
variable (M₁ M₂) in

def filtSub (A : Submodule (Poly S N) (quotLaurent M₁ M₂))
    (hfg : ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → E), (∀ j, gen j ∈ filtPiece M₁ M₂ A (deg j)) ∧
      ∀ c, filtPiece M₁ M₂ A c ≤ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
        f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f • gen j}) :
    FinGradedSub (S := S) (x := x) E where
  piece := filtPiece M₁ M₂ A
  smul_mem _ _ _ _ hf hm := filtPiece_smul_mem A hf hm
  fg := hfg
end Filt
end
end GroundTheory.Heights₂.Heights.Kleiman


