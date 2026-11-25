-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FracFieldPositiveRowsOmega
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FracFieldPositiveRowsOmega
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:31.935512+00:00
-- url     : https://prove2.me/theorems/d0a851eb-b3bf-4db1-a4c4-3b70cc632808
-- title:
--   Frac Field Positive Rows Omega
-- statement:
--   Definitions and structural lemmas for Frac Field Positive Rows Omega, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FracFieldPositiveRowsOmega.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_isFractionRing_toFracY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
abbrev PolyRingPositiveRowsBase : Type := MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K
abbrev PolyRingPositiveRowsOmega (c : ι) : Type := MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c)
abbrev FracFieldPositiveRowsBase : Type := FractionRing d.PolyRingPositiveRowsBase
abbrev FracFieldPositiveRowsOmega (c : ι) : Type := FractionRing (d.PolyRingPositiveRowsOmega c)
noncomputable def eLX4 : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) :=
  letI := (FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsBase) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hL K d.D d.N)
noncomputable def eEX4 (c : ι) : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) :=
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  IsFractionRing.ringEquivOfRingEquiv (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c))
theorem eEX4_algebraMap (c : ι) (P : MvPolynomial (SVar d.D d.N) (Ω c)) :
    d.eEX4 c (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P) =
      FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1)) (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) P) := by
  letI := (FractionFieldVariableLift.toFracY (d.PolyRingPositiveRowsOmega c) (Fin (d.N + 1))).toAlgebra
  haveI := FractionFieldVariableLift.isFractionRing_toFracY (A := d.PolyRingPositiveRowsOmega c) (σ := Fin (d.N + 1))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c)) P
noncomputable def psiE (c : ι) : d.PolyRingPositiveRowsBase →+* d.FracFieldPositiveRowsOmega c :=
  (algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c)).comp (d.offBaseSubstitution c).toRingHom
theorem psiE_apply (c : ι) (p : d.PolyRingPositiveRowsBase) : d.psiE c p = algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c) (d.offBaseSubstitution c p) := rfl
theorem sumRingEquiv_X_inl' (R S₁ S₂ : Type) [CommSemiring R] (b : S₁) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b := by
  first
  | exact MvPolynomial.sumToIter_Xl R S₁ S₂ b
  | simp [MvPolynomial.sumRingEquiv, MvPolynomial.X, MvPolynomial.monomial, AddMonoidAlgebra.one_def]
theorem sumRingEquiv_X_inr' (R S₁ S₂ : Type) [CommSemiring R] (q : S₂) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.X (Sum.inr q)) =
      MvPolynomial.C (MvPolynomial.X q) := by
  first
  | exact MvPolynomial.sumToIter_Xr R S₁ S₂ q
  | simp [MvPolynomial.sumRingEquiv, MvPolynomial.X, MvPolynomial.monomial, MvPolynomial.C, AddMonoidAlgebra.one_def]
theorem sumRingEquiv_C' (R S₁ S₂ : Type) [CommSemiring R] (a : R) :
    MvPolynomial.sumRingEquiv R S₁ S₂ (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := by
  first
  | exact MvPolynomial.sumToIter_C R S₁ S₂ a
  | simp [MvPolynomial.sumRingEquiv, MvPolynomial.monomial, MvPolynomial.C, AddMonoidAlgebra.one_def]
theorem compat0 (c : ι) (P : KTp K d.D d.N) :
    d.eEX4 c (d.sH c P) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) _
      (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N P)) := by
  have hXlE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrE : ∀ q, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCE : ∀ b, MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hXlL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inl b)) = MvPolynomial.X b :=
    fun b => sumRingEquiv_X_inl' _ _ _ b
  have hXrL : ∀ q, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.X (Sum.inr q)) = MvPolynomial.C (MvPolynomial.X q) :=
    fun q => sumRingEquiv_X_inr' _ _ _ q
  have hCL : ∀ b, MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.C b) = MvPolynomial.C (MvPolynomial.C b) :=
    fun b => sumRingEquiv_C' _ _ _ b
  have hEX : ∀ p, FractionFieldVariableLift.hE (Ω c) d.D d.N (d.jc c) p =
      MvPolynomial.sumRingEquiv (Ω c) (Fin (d.N + 1)) ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (MvPolynomial.rename (FractionFieldVariableLift.eS d.D d.N (d.jc c)) p) := fun p => rfl
  have hLX : ∀ p, FractionFieldVariableLift.hL K d.D d.N p =
      MvPolynomial.sumRingEquiv K (Fin (d.N + 1)) {v : TVar d.D d.N // v.1 ≠ 0} (MvPolynomial.rename (FractionFieldVariableLift.eT d.D d.N) p) := fun p => rfl
  have sac1 : ∀ {β : Type} (y : β) (p : Fin d.N → β),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p (d.jc c) = y :=
    fun y p => Fin.insertNth_apply_same (α := fun _ => _) _ y p
  have sac2 : ∀ {β : Type} (y : β) (p : Fin d.N → β) (k : Fin d.N),
      Fin.succAboveCases (α := fun _ => β) (d.jc c) y p ((d.jc c).succAbove k) = p k :=
    fun y p k => Fin.insertNth_apply_succAbove (α := fun _ => _) _ y p k
  have hpsiC : ∀ a, d.offBaseSubstitution c (MvPolynomial.C a) = MvPolynomial.C (algebraMap K (Ω c) a) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, MvPolynomial.algebraMap_apply]
  have hpsiX : ∀ v, d.offBaseSubstitution c (MvPolynomial.X v) =
      Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
        (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2 := by
    intro v
    simp only [Data.offBaseSubstitution, MvPolynomial.aeval_X]
  have e1 : ∀ a, d.sH c (MvPolynomial.C a) = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N) (MvPolynomial.C (algebraMap K (Ω c) a)) := by
    intro a
    rw [← MvPolynomial.algebraMap_eq (R := K), AlgHom.commutes, ← MvPolynomial.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have e2 : ∀ p, d.sH c (MvPolynomial.X p) = sImg (d.jc c) (d.x c) p := by
    intro p
    simp only [Data.sH, sHom, MvPolynomial.aeval_X]
  have key : (d.eEX4 c).toRingHom.comp (d.sH c).toRingHom =
      (algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))).comp
        ((MvPolynomial.map (d.psiE c)).comp (FractionFieldVariableLift.hL K d.D d.N).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show d.eEX4 c (d.sH c (MvPolynomial.C a)) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.C a)))
      simp [e1, d.eEX4_algebraMap, hEX, hLX, hCE, hCL, FractionFieldVariableLift.toFracY, d.psiE_apply, hpsiC]
    · rintro ⟨i, j⟩
      show d.eEX4 c (d.sH c (MvPolynomial.X (i, j))) = algebraMap (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)) (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c)))
        (MvPolynomial.map (d.psiE c) (FractionFieldVariableLift.hL K d.D d.N (MvPolynomial.X (i, j))))
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac1, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · simp [e2, sImg, sac1, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL, hCE,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, d.psiE_apply, hpsiX, hpsiC]
      · by_cases hi : i = 0
        · subst hi
          simp [e2, sImg, sac2, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY]
        · simp [e2, sImg, sac2, hi, d.eEX4_algebraMap, hEX, hLX, hXlE, hXlL, hXrE, hXrL,
            FractionFieldVariableLift.eS, FractionFieldVariableLift.eT, FractionFieldVariableLift.toFracY, d.psiE_apply, hpsiX]
  exact RingHom.congr_fun key P
theorem psiE_injective (h : d.S1) (c : ι) : Function.Injective (d.psiE c) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have e := d.compat0 c ((FractionFieldVariableLift.hL K d.D d.N).symm (MvPolynomial.C p))
  rw [RingEquiv.apply_symm_apply, MvPolynomial.map_C, hp, map_zero, map_zero] at e
  have e2 := (RingEquiv.map_eq_zero_iff (d.eEX4 c)).mp e
  have e3 := h c (e2.trans (map_zero (d.sH c)).symm)
  have e4 : (MvPolynomial.C p : MvPolynomial (Fin (d.N + 1)) d.PolyRingPositiveRowsBase) = 0 := by
    rw [← RingEquiv.apply_symm_apply (FractionFieldVariableLift.hL K d.D d.N) (MvPolynomial.C p), e3, map_zero]
  exact MvPolynomial.C_eq_zero.mp e4
noncomputable def algLE (h : d.S1) (c : ι) : Algebra d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) :=
  (IsFractionRing.lift (A := d.PolyRingPositiveRowsBase) (K := d.FracFieldPositiveRowsBase) (d.psiE_injective h c)).toAlgebra
end Data
end ReciprocityTheory.ChartRestriction.G.T0


