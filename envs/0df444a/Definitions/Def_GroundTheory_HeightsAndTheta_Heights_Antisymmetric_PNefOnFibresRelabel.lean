-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- name    : GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:43.246255+00:00
-- url     : https://prove2.me/theorems/51c4585d-85b2-4489-b759-9797f5673d47
-- title:
--   PNef On Fibres Relabel
-- statement:
--   Definitions and structural lemmas for PNef On Fibres Relabel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
section RingEquivTransport
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
theorem mem_map_ringEquiv_iff (I : Ideal A) (x : A) : σ x ∈ I.map σ ↔ x ∈ I := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_bijective σ σ.bijective]
theorem map_mem_primeCompl (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] (s : V.primeCompl) :
    σ s ∈ (V.map σ).primeCompl :=
  Ideal.mem_primeCompl_iff.2 fun hs => Ideal.mem_primeCompl_iff.1 s.2 ((mem_map_ringEquiv_iff σ V s).1 hs)
theorem primeCompl_map_ringEquiv (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] :
    V.primeCompl.map σ.toMonoidHom = (V.map σ).primeCompl := by
  ext x
  rw [Submonoid.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact map_mem_primeCompl σ V ⟨s, hs⟩
  · intro hx
    refine ⟨σ.symm x, Ideal.mem_primeCompl_iff.2 fun h' => Ideal.mem_primeCompl_iff.1 hx ?_, by simp⟩
    simpa using (mem_map_ringEquiv_iff σ V (σ.symm x)).2 h'
def locRingEquiv (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] :
    Localization.AtPrime V ≃+* Localization.AtPrime (V.map σ) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime V) (Localization.AtPrime (V.map σ)) σ
    (primeCompl_map_ringEquiv σ V)
theorem locRingEquiv_mk (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] (a : A) (t : V.primeCompl) :
    locRingEquiv σ V (Localization.mk a t) = Localization.mk (σ a) ⟨σ t, map_mem_primeCompl σ V t⟩ := by
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply, locRingEquiv,
    IsLocalization.ringEquivOfRingEquiv_mk']
def quotEquivMap (J : Ideal A) : A ⧸ J ≃+* A' ⧸ J.map σ :=
  Ideal.quotientEquiv J (J.map σ) σ rfl
theorem quotEquivMap_smul (J : Ideal A) (a : A) (m : A ⧸ J) :
    quotEquivMap σ J (a • m) = σ a • quotEquivMap σ J m := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl
section LocLength
variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]
def locQuotMap :
    LocalizedModule V.primeCompl (A ⧸ J) → LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ) :=
  fun x => x.liftOn (fun p => LocalizedModule.mk (quotEquivMap σ J p.1)
      ⟨σ p.2, map_mem_primeCompl σ V p.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    rw [LocalizedModule.mk_eq]
    refine ⟨⟨σ u, map_mem_primeCompl σ V u⟩, ?_⟩
    have := congrArg (quotEquivMap σ J) hu
    simpa only [Submonoid.smul_def, quotEquivMap_smul] using this)
theorem locQuotMap_mk (m : A ⧸ J) (s : V.primeCompl) :
    locQuotMap σ J V (LocalizedModule.mk m s) =
      LocalizedModule.mk (quotEquivMap σ J m) ⟨σ s, map_mem_primeCompl σ V s⟩ := by
  rw [locQuotMap, LocalizedModule.liftOn_mk]
def locQuotSemilinear :
    LocalizedModule V.primeCompl (A ⧸ J) →ₛₗ[(locRingEquiv σ V : Localization.AtPrime V →+*
      Localization.AtPrime (V.map σ))] LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ) where
  toFun := locQuotMap σ J V
  map_add' x y := by
    induction x using LocalizedModule.induction_on with | h m s => ?_
    induction y using LocalizedModule.induction_on with | h m' s' => ?_
    rw [LocalizedModule.mk_add_mk, locQuotMap_mk, locQuotMap_mk, locQuotMap_mk,
      LocalizedModule.mk_add_mk]
    simp only [Submonoid.smul_def, map_add, quotEquivMap_smul]
    congr 1
    ext
    simp
  map_smul' r x := by
    induction r using Localization.induction_on with | H p => ?_
    obtain ⟨a, t⟩ := p
    induction x using LocalizedModule.induction_on with | h m s => ?_
    show locQuotMap σ J V _ = (locRingEquiv σ V (Localization.mk a t)) • locQuotMap σ J V _
    rw [LocalizedModule.mk_smul_mk, locQuotMap_mk, locQuotMap_mk, locRingEquiv_mk,
      LocalizedModule.mk_smul_mk, quotEquivMap_smul]
    congr 1
    ext
    simp
end LocLength
end RingEquivTransport
section Relabel
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
def relabelRingEquiv : MRing ι ≃+* MRing ι' :=
  (MvPolynomial.renameEquiv ℤ (relabelBlocks ε h)).toRingEquiv
end Relabel
end GroundTheory.Heights₂.Heights


