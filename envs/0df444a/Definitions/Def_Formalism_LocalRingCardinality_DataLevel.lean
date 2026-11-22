-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_DataLevel
-- name    : Formalism_LocalRingCardinality_DataLevel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:19.619812+00:00
-- url     : https://prove2.me/theorems/62ff215a-8e56-4538-ba1e-f81ce719847b
-- title:
--   Data Level
-- statement:
--   Definitions and structural lemmas for Data Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataLevel.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
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
namespace Formalism.BasicNotions
open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
section Defs
variable {F E : Type} [Field F] [CommRing E] [Algebra F E]
@[reducible] def tensTopL (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)
end Defs
def IsProGrp {G : Type} [Group G] [TopologicalSpace G] (g : ℕ) (Uw : Subgroup G) : Prop :=
  IsCompact (Uw : Set G) ∧ ∀ N : Subgroup Uw, IsOpen (N : Set Uw) → N.Normal → ∃ m : ℕ, N.index = g ^ m
section Iw
variable (F : Type) [Field F] [NumberField F] (k : ℕ)
def upperUni (A : Type) [CommRing A] : Set (GL (Fin k) A) :=
  {x | ∀ i j : Fin k, (j < i → (x : Matrix (Fin k) (Fin k) A) i j = 0) ∧
    (x : Matrix (Fin k) (Fin k) A) i i = 1}
def iwU (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin k) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Subgroup.closure (upperUni k _))
end Iw
namespace Spaces
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)
theorem rank0 : (sp.X 0).rank = R.k := by
  simpa [Ranks.N] using sp.X_rank 0 (Nat.zero_le _)
def gram0 : Matrix (Fin R.k) (Fin R.k) E :=
  (sp.X 0).gram.reindex (finCongr sp.rank0) (finCongr sp.rank0)
def crd0 : (sp.X 0).V ≃ₗ[E] (Fin R.k → E) :=
  (sp.X 0).frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr sp.rank0).symm)
def crdLat0 (L : Submodule (𝓞 E) (sp.X 0).V) : Submodule (𝓞 E) (Fin R.k → E) :=
  L.map ((sp.crd0 : (sp.X 0).V →ₗ[E] (Fin R.k → E)).restrictScalars (𝓞 E))
end Spaces
abbrev intV {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
def dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) : Set (n → E) :=
  {y | ∀ x ∈ L, hform σ J x y ∈ (algebraMap (𝓞 E) E).range}
structure ColLevel (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (sp : Spaces R F E) (gp : Fin 2 → ℕ)
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (A : ColumnsAtT R C)
    (clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V) where

  Lb : Submodule (𝓞 E) (Fin R.k → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_span : Submodule.span E (Lb : Set (Fin R.k → E)) = ⊤

  Lb_int : ∀ x ∈ Lb, x ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb

  Lb_dual : ∀ y ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb, (A.T : E) • y ∈ Lb

  Lb_index : Lb.toAddSubgroup.relIndex
    (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb)).toAddSubgroup = A.T ^ (2 * R.f)

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin R.k) (E ⊗[F] v.adicCompletion F))
  Uloc_le : ∀ v, Uloc v ≤ UPts sp.cm.sig sp.gram0 (v.adicCompletion F)

  Uloc_lev : ∀ v, Uloc v ≤ levelVL sp.cm.sig sp.gram0 v Lb

  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → ((A.T : 𝓞 F) ∉ v.asIdeal) →
    Uloc v = levelVL sp.cm.sig sp.gram0 v Lb

  splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  splitG_sig : ∀ i v h x, splitG i v h (sigR sp.cm.sig (v.adicCompletion F) x) =
    swapR _ (splitG i v h x)

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    GL (Fin R.k) (v.adicCompletion F)

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    x ∈ Uloc v ↔ (frG i v h)⁻¹ * bc ((RingHom.fst _ _).comp (splitG i v h).toRingHom) x * frG i v h ∈
      iwU F R.k v

  fM : ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∈ v.asIdeal → Type
  [fM_acg : ∀ v h, AddCommGroup (fM v h)]
  [fM_mod : ∀ v h, Module (intV E v) (fM v h)]
  fT : ∀ v h, latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 Lb)) →ₗ[intV E v] fM v h
  fT_ne : ∀ v h, fT v h ≠ 0
  fT_T : ∀ v h x, fT v h ((A.T : intV E v) • x) = 0

  fM_card : ∀ v h, Nat.card (fM v h) = A.T

  fT_L : ∀ v h x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → fT v h x = 0

  UlocAlt : ∀ v h, Uloc v = levelVL sp.cm.sig sp.gram0 v Lb ⊓ stabFun _ (fT v h)

  U : Subgroup (GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ∧
    ∀ v, bc (prV (E := E) v) x ∈ Uloc v

  U_compact : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsCompact (U : Set (GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
  U_open : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}

  w1 : HeightOneSpectrum (𝓞 F)
  reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal

  y : C.cls 0 → UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c : C.cls 0 =>
    (Quotient.mk'' (y c) : ClassSet
      ((ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))))

  y_lat : ∀ c (x : Fin R.k → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (sp.crdLat0 (clsLat 0 c)) ↔
    ((((y c : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb

  stabI : ∀ c : C.cls 0, C.stab 0 c →* UJ (sp.cm.sig : E →+* E) sp.gram0
  stabI_inj : ∀ c, Function.Injective (stabI c)

  stabI_range : ∀ c (γ : GL (Fin R.k) E) (hγ : γ ∈ UJ (sp.cm.sig : E →+* E) sp.gram0),
    (⟨γ, hγ⟩ : UJ (sp.cm.sig : E →+* E) sp.gram0) ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈
        U.map (MulAut.conj (y c : GL (Fin R.k) _)).toMonoidHom

  stabI_lat : ∀ c (γ : C.stab 0 c) (x : Fin R.k → E),
    x ∈ sp.crdLat0 (clsLat 0 c) ↔
      (((stabI c γ : GL (Fin R.k) E) : Matrix (Fin R.k) (Fin R.k) E) *ᵥ x) ∈ sp.crdLat0 (clsLat 0 c)
attribute [instance] ColLevel.fM_acg ColLevel.fM_mod
namespace ColLevel
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
def ProG (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F)
    IsProGrp (gp i) (L.Uloc v)
end ColLevel
end Formalism.BasicNotions
end


