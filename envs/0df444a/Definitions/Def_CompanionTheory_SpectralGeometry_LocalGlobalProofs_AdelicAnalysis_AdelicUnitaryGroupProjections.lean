-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:13.860132+00:00
-- url     : https://prove2.me/theorems/aebe95ae-ef3b-4de8-bca9-0b3baf6c7ee0
-- title:
--   Adelic Unitary Group Projections
-- statement:
--   Definitions and structural lemmas for Adelic Unitary Group Projections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.HProj
section Alg
variable {F : Type} (E : Type) [Field F] [Field E] [Algebra F E]
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']
def tm (φ : R →ₐ[F] R') : R ⊗[F] E →+* R' ⊗[F] E :=
  (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
variable {E}
theorem tm_sig (σ : E →ₐ[F] E) (φ : R →ₐ[F] R') (x : R ⊗[F] E) :
    tm E φ (sigR R σ x) = sigR R' σ (tm E φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [tm, sigR]
  | add x y hx hy => simp [hx, hy]
theorem tm_incl (φ : R →ₐ[F] R') (e : E) : tm E φ (inclR R e) = inclR R' e := by
  simp [tm, inclR]
theorem map_cT {A B m p : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : A →+* A) (s' : B →+* B)
    (hs : ∀ x, f (s x) = s' (f x)) (G : Matrix m p A) :
    (cT s G).map f = cT s' (G.map f) := by
  ext i j
  simp [cT, hs]
theorem map_JR {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R') :
    (JR R J).map (tm E φ) = JR R' J := by
  ext i j
  simp [JR, tm_incl]
theorem map_unitary (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :
    (cT (sigR R σ) G * JR R J * G).map (tm E φ) =
      cT (sigR R' σ) (G.map (tm E φ)) * JR R' J * G.map (tm E φ) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_cT (tm E φ) (sigR R σ) (sigR R' σ) (tm_sig σ φ), map_JR]
def hMap (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R') :
    HA R σ J →* HA R' σ J where
  toFun h := ⟨bc (tm E φ) (HA.mat R σ J h), by
    have hh : cT (sigR R σ) ((HA.mat R σ J h : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        ((HA.mat R σ J h : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := (show HR R σ J from h).2
    have := congrArg (fun G => Matrix.map G (tm E φ)) hh
    simp only [map_unitary, map_JR] at this
    exact this⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (bc (tm E φ))
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (bc (tm E φ)) _ _
end Alg
section Lat
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
def Lv (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F}
abbrev evA (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)
end Lat
end GlobalTheory.CompanionTheory.SW.HProj


