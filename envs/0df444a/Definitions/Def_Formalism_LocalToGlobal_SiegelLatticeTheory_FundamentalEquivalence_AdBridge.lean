-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:29.420806+00:00
-- url     : https://prove2.me/theorems/92afee2e-82d0-42c7-9797-829d27383730
-- title:
--   Ad Bridge
-- statement:
--   Definitions and structural lemmas for Ad Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/AdBridge.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
variable (I : AutInst)
abbrev HAd : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
abbrev hmat (h : HAd I) : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
    GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _)
def evV (v : InfinitePlace I.F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    ((Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v).comp
      (RingHom.fst (InfiniteAdeleRing I.F) (FiniteAdeleRing (𝓞 I.F) I.F)))
theorem evV_algebraMap (v : InfinitePlace I.F) (a : I.F) :
    evV I v (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) a) = v.embedding a := by
  first
    | (exact InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm a))
    | (have h := InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm a); simp only [Equiv.apply_symm_apply] at h; exact h)
    | (simp [evV]; done)
def thetaV (v : InfinitePlace I.F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+* ℂ :=
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evV I v with commutes' := fun a => evV_algebraMap I v a } :
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F →ₐ[I.F] ℂ)
    ({ I.φ v with commutes' := I.φ_over v } : I.E →ₐ[I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom
def tauF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F :=
  (Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeRight : Formalism.MainNotions.S.Af I.F →ₐ[I.F] I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F).comp
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F))
    (Algebra.TensorProduct.includeLeft : I.E →ₐ[I.F] I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (fun _ _ => Commute.all _ _)).toRingHom
def ofHAInf (h : HAd I) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  (I.P v)⁻¹ * (hmat I h).map (thetaV I v) * I.P v
def ofHAFin (h : HAd I) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  (hmat I h).map (tauF I)
def IsBridge (e : I.GA ≃ₜ* HAd I) : Prop :=
  ∀ x : I.GA, (∀ v, uMat (x.1 v) = ofHAInf I (e x) v) ∧ I.fmat x.2 = ofHAFin I (e x)
def AdBridgeIso : Prop := ∃ e : I.GA ≃ₜ* HAd I, IsBridge I e
def ratHA : Set (HAd I) :=
  {h | Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h ∈
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J}
def KinfV (v : InfinitePlace I.F) : Set (Formalism.REAL.UJ (I.ε v)) :=
  {k | ∀ a b, I.ε v a ≠ I.ε v b → uMat k a b = 0}
def KGA : Set I.GA := {x | (∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset}
def majV (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ := ((I.P v)⁻¹)ᴴ * (I.P v)⁻¹
def KinfHA : Set (HAd I) :=
  {h | ∀ v, ((hmat I h).map (thetaV I v))ᴴ * majV I v * (hmat I h).map (thetaV I v) = majV I v}
def prF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E →+* Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E)).toRingHom
def KfHA : Set (HAd I) :=
  {h | ∀ v : HeightOneSpectrum (𝓞 I.F),
    Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) ∈
      Formalism.L2.SG.Sub.Kloc v (I.L : Set (Fin I.n → I.E))}
def KHA : Set (HAd I) := KinfHA I ∩ KfHA I
def AdBridgeGF : Prop := ∀ e : I.GA ≃ₜ* HAd I, IsBridge I e → e '' I.GFset = ratHA I
def AdBridgeK : Prop := ∀ e : I.GA ≃ₜ* HAd I, IsBridge I e → e '' KGA I = KHA I
def AdelicIsomorphism : Prop := AdBridgeIso I ∧ AdBridgeGF I ∧ AdBridgeK I
def toHA (hb : AdBridgeIso I) : I.GA ≃ₜ* HAd I := hb.choose
end Formalism.L2.SG.AdBridge


