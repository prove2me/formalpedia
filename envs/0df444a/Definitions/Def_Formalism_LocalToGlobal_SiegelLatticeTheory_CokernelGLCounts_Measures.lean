-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_Measures
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_Measures
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:06.138103+00:00
-- url     : https://prove2.me/theorems/a85cd59a-ac01-4494-bda2-2435c0e3a68f
-- title:
--   Measures
-- statement:
--   Definitions and structural lemmas for Measures, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/Measures.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Theorems.Thm_Formalism_UG_P_bc_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Measures
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
section Map
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def tensMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') :
    R ⊗[F] E →+* R' ⊗[F] E :=
  (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
theorem tensMap_sigR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (σ : E →ₐ[F] E) :
    (tensMap (E := E) φ).comp (sigR R σ) = (sigR R' σ).comp (tensMap φ) := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [tensMap, sigR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
theorem tensMap_inclR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (x : E) : tensMap (E := E) φ (inclR R x) = inclR R' x := by
  simp [tensMap, inclR]
def haMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (φ : R →ₐ[F] R') : HA R σ J →* HA R' σ J where
  toFun g := ⟨Formalism.UG.bc (tensMap φ) (HA.mat R σ J g), by
    have h := Formalism.UG.P.bc_mem (sigR R σ) (sigR R' σ) (tensMap (E := E) φ) (tensMap_sigR φ σ) (JR R J)
      (HA.mat R σ J g) g.2
    have hJ : (JR R J).map (tensMap (E := E) φ) = JR R' J := by
      ext i j
      simp [JR, tensMap_inclR]
    rw [hJ] at h
    exact h⟩
  map_one' := by
    apply Subtype.ext
    show Formalism.UG.bc (tensMap φ) (1 : GL (Fin n) (R ⊗[F] E)) = 1
    exact map_one _
  map_mul' g h := by
    apply Subtype.ext
    show Formalism.UG.bc (tensMap φ) (HA.mat R σ J g * HA.mat R σ J h) =
      Formalism.UG.bc (tensMap φ) (HA.mat R σ J g) * Formalism.UG.bc (tensMap φ) (HA.mat R σ J h)
    exact map_mul _ _ _
end Map
section Split
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)
def splitA : HA (AF F) σ J →* HA (Ainf F) σ J × HA (Af F) σ J :=
  MonoidHom.prod (haMap σ J (fstA F)) (haMap σ J (sndA F))
end Split
abbrev amb {G : Type} [Group G] [MeasurableSpace G] {K : Subgroup G} (μ : Measure K) : Measure G :=
  μ.map Subtype.val
section Rec
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
structure MeasG (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (r : ℕ) where

  μG : Measure (HA (AF F) σ J)

  μGinf : Measure (HA (Ainf F) σ J)

  μGf : Measure (HA (Af F) σ J)

  μGv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HA (Fv F v) σ J)

  μB : ∀ X0 : Fin (2 * r + 2) → Fin n → E, Measure (stabT (AF F) σ J X0)
structure MeasW (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) where

  μH : Measure (Hsub (AF F) σ J P)

  μHinf : Measure (Hsub (Ainf F) σ J P)

  μHf : Measure (Hsub (Af F) σ J P)

  μN : Measure (Nsub (AF F) σ J P)

  μNinf : Measure (Nsub (Ainf F) σ J P)

  μNf : Measure (Nsub (Af F) σ J P)

  μSf : Measure (Ssub (Af F) σ J P)

  μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
def MeasG.IsTextNorm {r : ℕ} (M : MeasG σ J r) : Prop :=
  M.μG.IsHaarMeasure ∧ M.μGinf.IsHaarMeasure ∧ M.μGf.IsHaarMeasure ∧ (∀ v, (M.μGv v).IsHaarMeasure) ∧
  (∀ X0, (M.μB X0).IsHaarMeasure) ∧
  M.μG.map (splitA σ J) = M.μGinf.prod M.μGf
def MeasW.IsTextNorm {r : ℕ} {P : Frame E n r} (M : MeasW σ J P) : Prop :=
  M.μH.IsHaarMeasure ∧ M.μHinf.IsHaarMeasure ∧ M.μHf.IsHaarMeasure ∧
  M.μN.IsHaarMeasure ∧ M.μNinf.IsHaarMeasure ∧ M.μNf.IsHaarMeasure ∧
  M.μSf.IsHaarMeasure ∧ (∀ v, (M.μSv v).IsHaarMeasure) ∧
  (amb M.μH).map (splitA σ J) = (amb M.μHinf).prod (amb M.μHf) ∧
  (amb M.μN).map (splitA σ J) = (amb M.μNinf).prod (amb M.μNf) ∧
  amb M.μSf = ((amb M.μNf).prod (amb M.μHf)).map (fun p => p.1 * p.2)
def ratOf {K : Subgroup (HA (AF F) σ J)} : Subgroup K :=
  (HFinIn (AF F) σ J).comap K.subtype
def covol {K : Subgroup (HA (AF F) σ J)} (μ : Measure K) : ℝ :=
  haveI := Classical.propDecidable
  if h : ∃ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ then (μ h.choose).toReal else 0
end Rec
end Formalism.L2.SG.Measures


