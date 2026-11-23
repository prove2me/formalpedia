-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF
-- name    : Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:28.456694+00:00
-- url     : https://prove2.me/theorems/e5146048-1427-444b-b3e1-df12f0974446
-- title:
--   Has Inf Exp F
-- statement:
--   Definitions and structural lemmas for Has Inf Exp F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Formalism.IndefR.LiftF
section Chars
variable {C : Type*} [CommGroup C]
def tup (μ0 : ℕ → C) (ξ : C) (j : ℕ) : C := μ0 j * ξ
def attChr (μj η : C) (n : ℕ) : C := if Odd n then μj * η⁻¹ else μj
def chrStep (μ : ℕ → C) (η : C) (j : ℕ) : C × C :=
  if Odd j then (μ j * η⁻¹, μ j) else (μ j, μ j * η⁻¹)
def chrTh (μ : ℕ → C) (η : C) (j : ℕ) : C × C := (μ j, μ j * η⁻¹)
def chrLine (η : C) : C := η⁻¹
def chrLineTop (η : C) : C := η
end Chars
section Step
variable {G H S Sinf Ds Dt : Type*} [MeasurableSpace H]
  [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]
def liftInt (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (s : S) (F : H → ℂ) (g : G) : ℂ :=
  ∫ h in 𝓕, th g h s * F h ∂ν
structure IsIo (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt) : Prop where

  integ : ∀ F : CCs, ∀ φ v g,
    IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν

  eq : ∀ F : CCs, ∀ φ v g,
    liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g = ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g
def IsTPlus (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (ipDt : Dt →ₗ[ℂ] Dt →ₗ⋆[ℂ] ℂ) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) : Prop :=
  ∀ φ v' v, ipDt (T φ v') v = ipDs v' (Tp φ v)
structure IsIoUp [MeasurableSpace G] (νG : Measure G) (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (up : CCt →ₗ[ℂ] CCs) : Prop where

  integ : ∀ u : CCt, ∀ φ v h,
    IntegrableOn (fun g => starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g) 𝓕G νG

  eq : ∀ u : CCt, ∀ φ v h,
    ∫ g in 𝓕G, starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g ∂νG =
      ((up u : CCs) : Ds →ₗ[ℂ] (H → ℂ)) (Tp φ v) h
end Step
section Adj
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
def IsAdjOf (ipM : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (ipN : N →ₗ[ℂ] N →ₗ⋆[ℂ] ℂ) (A : M →ₗ[ℂ] N) (B : N →ₗ[ℂ] M) : Prop :=
  ∀ x y, ipN (A x) y = ipM x (B y)
end Adj
section Chain
variable {G : ℕ → Type*} {D : ℕ → Type*} [∀ j, AddCommGroup (D j)] [∀ j, Module ℂ (D j)]
  (CC : ∀ j, Submodule ℂ (D j →ₗ[ℂ] (G j → ℂ)))
def dnFrom (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) : ∀ n, CC n →ₗ[ℂ] CC 0
  | 0 => LinearMap.id
  | n + 1 => dnFrom io n ∘ₗ io n
def thetaDn (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) (m : ℕ) : CC m →ₗ[ℂ] CC 0 := dnFrom CC io m
def IsChainIo {S Sinf : ℕ → Type*} [∀ j, MeasurableSpace (G j)] [∀ j, AddCommGroup (Sinf j)]
    [∀ j, Module ℂ (Sinf j)] (m : ℕ) (ν : ∀ j, Measure (G j)) (𝓕 : ∀ j, Set (G j))
    (th : ∀ k, G k → G (k + 1) → S k → ℂ) (pt : ∀ k, Sinf k → S k)
    (T : ∀ k, Sinf k →ₗ[ℂ] D (k + 1) →ₗ[ℂ] D k) (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) : Prop :=
  ∀ k < m, IsIo (ν (k + 1)) (𝓕 (k + 1)) (th k) (pt k) (T k) (CC (k + 1)) (CC k) (io k)
def IsThetaUp (ip : ∀ j, CC j →ₗ[ℂ] CC j →ₗ⋆[ℂ] ℂ) (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) (m : ℕ)
    (up : CC 0 →ₗ[ℂ] CC m) : Prop :=
  IsAdjOf (ip m) (ip 0) (thetaDn CC io m) up
end Chain
section Rows
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
def Umu (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) : Submodule ℂ V0 := LinearMap.ker (dn ∘ₗ V0.subtype)
abbrev Qmu (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) : Type _ := V0 ⧸ Umu dn V0
def iota (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) : Qmu dn V0 →ₗ[ℂ] N :=
  (Umu dn V0).liftQ (dn ∘ₗ V0.subtype) le_rfl
def qNormSq (ip : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (q : Qmu dn V0) : ℝ :=
  sInf ((fun x : V0 => (ip x x).re) '' {x | Submodule.Quotient.mk x = q})
def Zmu (up : N →ₗ[ℂ] M) (EE : Submodule ℂ N) : Submodule ℂ M := EE.map up
end Rows
section ThetaP
variable {G' H' S' Sinf' TK Tau : Type*} [MeasurableSpace H']
  [AddCommGroup Sinf'] [Module ℂ Sinf'] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
def thetaPInt (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (f : H' → Tau) (e : TK) (g : G') : ℂ :=
  ∫ h in 𝓕, th g h (pt (io e (f h))) ∂ν
structure IsThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (A : Submodule ℂ (H' → Tau))
    (thP : A →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))) : Prop where

  integ : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν

  eq : ∀ f : A, ∀ e g, thP f e g = thetaPInt ν 𝓕 th pt io f e g
variable {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]
def Zj (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (thP : A →ₗ[ℂ] Amb) (good : Submodule ℂ A) : Submodule ℂ A :=
  (LinearMap.ker thP).orthogonalBilin ipA ⊓ good
def ZjE (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (eThP : A →ₗ[ℂ] Amb) : Submodule ℂ A :=
  (LinearMap.ker eThP).orthogonalBilin ipA
def IsLamP {Sig : Type*} (thW : A →ₗ[ℂ] Amb) (adj : Amb →ₗ[ℂ] A) (part : Sig → Submodule ℂ Amb)
    (lam : Sig → ℝ) : Prop :=
  ∀ σ, ∀ x ∈ part σ, thW (adj x) = (lam σ : ℂ) • x
end ThetaP
section Kap
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
def IsKap {Tup Sig : Type*} (m : ℕ) (dnup : Tup → N →ₗ[ℂ] N) (partE : Sig → Submodule ℂ N)
    (lam : Tup → ℕ → Sig → ℝ) (κ : ℝ) : Prop :=
  ∀ μ σ, ∀ x ∈ partE σ, dnup μ x = ((κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ) • x
end Kap
section Bu
variable {M N Mu : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
def IsBu (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (Bt : Mu → V0 → ℂ) (B : Mu → N → ℂ) : Prop :=
  ∀ φ (x : V0), B φ (iota dn V0 (Submodule.Quotient.mk x)) = Bt φ x
def zeta {I : Type*} [Monoid I] (ξ : I →* Circle) (a : I) : ℂ := ξ a
end Bu
section Statements
variable {M N Mu : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
def UpLiftInProjectedFormSpace (up : N →ₗ[ℂ] M) (EE : Submodule ℂ N) (V0 : Submodule ℂ M) : Prop := EE.map up ≤ V0
def DnIntoEE (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (EE : Submodule ℂ N) : Prop := V0.map dn ≤ EE
def UpInjEE (up : N →ₗ[ℂ] M) (EE : Submodule ℂ N) : Prop := Set.InjOn up EE
def IotaOnto (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (EE : Submodule ℂ N) : Prop :=
  LinearMap.range (iota dn V0) = EE
def BtVanish (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (Bt : Mu → V0 → ℂ) : Prop :=
  ∀ φ, ∀ x ∈ Umu dn V0, Bt φ x = 0
def Prop6iii (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (ζ : ℂ) (Pt : Mu → V0 → ℂ) (B : Mu → N → ℂ) : Prop :=
  ∀ φ (x : V0), ζ * Pt φ x = B φ (iota dn V0 (Submodule.Quotient.mk x))
def IoExists {G H S Sinf Ds Dt : Type*} [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H)
    (th : G → H → S → ℂ) (pt : Sinf → S) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) : Prop :=
  ∃ io, IsIo ν 𝓕 th pt T CCs CCt io
def pet {X : Type*} [MeasurableSpace X] (ν : Measure X) (𝓕 : Set X) (f₁ f₂ : X → ℂ) : ℂ :=
  ∫ x in 𝓕, f₁ x * starRingEnd ℂ (f₂ x) ∂ν
def IsSchur {X Dm : Type*} [MeasurableSpace X] [AddCommGroup Dm] [Module ℂ Dm] (ν : Measure X) (𝓕 : Set X)
    (ipD : Dm →ₗ[ℂ] Dm →ₗ⋆[ℂ] ℂ) (CC : Submodule ℂ (Dm →ₗ[ℂ] (X → ℂ))) (ip : CC →ₗ[ℂ] CC →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ F₁ F₂ : CC, ∀ v v', pet ν 𝓕 ((F₁ : Dm →ₗ[ℂ] (X → ℂ)) v) ((F₂ : Dm →ₗ[ℂ] (X → ℂ)) v') = ip F₁ F₂ * ipD v v'
def AdjointLiftPeterssonIdentity {G H S Sinf Ds Dt : Type*} [MeasurableSpace G] [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) [SFinite ν] (𝓕 : Set H)
    (νG : Measure G) [SFinite νG]
    (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds)
    (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (ipDt : Dt →ₗ[ℂ] Dt →ₗ⋆[ℂ] ℂ)
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ)))
    (ipS : CCs →ₗ[ℂ] CCs →ₗ⋆[ℂ] ℂ) (ipT : CCt →ₗ[ℂ] CCt →ₗ⋆[ℂ] ℂ) (io : CCs →ₗ[ℂ] CCt) (up : CCt →ₗ[ℂ] CCs) :
    Prop :=
  IsSchur ν 𝓕 ipDs CCs ipS → IsSchur νG 𝓕G ipDt CCt ipT → IsTPlus ipDs ipDt T Tp →
    (∃ φ v' v, ipDt (T φ v') v ≠ 0) →
    (∀ (F : CCs) (u : CCt) φ v' v, Integrable (fun q : G × H => th q.1 q.2 (pt φ) *
      (F : Ds →ₗ[ℂ] (H → ℂ)) v' q.2 * starRingEnd ℂ ((u : Dt →ₗ[ℂ] (G → ℂ)) v q.1))
      ((νG.restrict 𝓕G).prod (ν.restrict 𝓕))) →
    IsIo ν 𝓕 th pt T CCs CCt io → IsIoUp νG 𝓕G th pt Tp CCs CCt up → IsAdjOf ipS ipT io up
def ThmA {A Amb Sig : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]
    (thW : A →ₗ[ℂ] Amb) (adj : Amb →ₗ[ℂ] A) (part : Sig → Submodule ℂ Amb) : Prop :=
  ∃ lam : Sig → ℝ, IsLamP thW adj part lam ∧ ∀ σ, part σ ≠ ⊥ → 0 < lam σ
def ThmB {Tup Sig : Type*} (m : ℕ) (dnup : Tup → N →ₗ[ℂ] N) (partE : Sig → Submodule ℂ N)
    (lam : Tup → ℕ → Sig → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ IsKap m dnup partE lam κ
def RatMuC {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]
    (thP : A →ₗ[ℂ] Amb) (Z : Submodule ℂ A) (invariantSubspaceW : Submodule ℂ Amb) : Prop :=
  Set.InjOn thP Z ∧ Z.map thP = invariantSubspaceW
def OrthogonalComplementCharacterisation (ip : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (dn : M →ₗ[ℂ] N) (up : N →ₗ[ℂ] M) (V0 : Submodule ℂ M)
    (EE : Submodule ℂ N) : Prop :=
  ∀ x : M, x ∈ Zmu up EE ↔ x ∈ V0 ∧ ∀ u ∈ Umu dn V0, ip (u : M) x = 0
def ZjAgree {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]
    (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (thP : A →ₗ[ℂ] Amb) (eA : A →ₗ[ℂ] A) (eW : Amb →ₗ[ℂ] Amb) : Prop :=
  (∀ x, eA (eA x) = eA x) → (∀ x y, ipA (eA x) y = ipA x (eA y)) → (∀ x, eW (thP x) = thP (eA x)) →
    (∀ z, ipA z z = 0 → z = 0) → Zj ipA thP (LinearMap.range eA) = ZjE ipA (eW ∘ₗ thP)
def DimQ (dn : M →ₗ[ℂ] N) (V0 : Submodule ℂ M) (EE : Submodule ℂ N) : Prop :=
  Module.finrank ℂ (Qmu dn V0) = Module.finrank ℂ EE
def EEDecomp {Sig : Type*} (ip : N →ₗ[ℂ] N →ₗ⋆[ℂ] ℂ) (partE : Sig → Submodule ℂ N) (EE : Submodule ℂ N) : Prop :=
  (⨆ σ, partE σ) = EE ∧ ∀ σ σ', σ ≠ σ' → ∀ x ∈ partE σ, ∀ y ∈ partE σ', ip x y = 0
def PartsMatch {Sig : Type*} (m : ℕ) {W : ℕ → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (partE : Sig → Submodule ℂ N) (partW : ∀ j, Sig → Submodule ℂ (W j)) : Prop :=
  ∀ σ, partE σ ≠ ⊥ → ∀ j ∈ Finset.Icc 1 m, partW j σ ≠ ⊥
def ThmBLev {L Tup Sig : Type*} (m : ℕ) {NL : L → Type*} [∀ l, AddCommGroup (NL l)] [∀ l, Module ℂ (NL l)]
    (dnup : ∀ l, Tup → NL l →ₗ[ℂ] NL l) (partE : ∀ l, Sig → Submodule ℂ (NL l)) (lam : Tup → ℕ → Sig → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ l, IsKap m (dnup l) (partE l) lam κ
end Statements
section Kernels
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (xi0 : E)
def IsPairKernel (ψ : AddChar (AF F) ℂ) (χS χT : (AEF F E)ˣ →* Circle) {nV nW : ℕ} (JV : Matrix (Fin nV) (Fin nV) E)
    (JW : Matrix (Fin nW) (Fin nW) E) (th : GAF σ JV → GAF σ JW → (WOF F E nV nW → ℂ) → ℂ) : Prop :=
  ∃ ω : GAF σ JV × GAF σ JW →* Module.End ℂ (WOF F E nV nW → ℂ),
    IsWeilDatumOF σ JV JW tauE xi0 ψ χS χT ω ∧ th = fun g h f => thetaKOF ω g h f
def IsStepKernel (ψ : AddChar (AF F) ℂ) (μ : ℕ → (AEF F E)ˣ →* Circle) (η : (AEF F E)ˣ →* Circle) (j : ℕ)
    {nV nW : ℕ} (JV : Matrix (Fin nV) (Fin nV) E) (JW : Matrix (Fin nW) (Fin nW) E)
    (th : GAF σ JV → GAF σ JW → (WOF F E nV nW → ℂ) → ℂ) : Prop :=
  IsPairKernel σ tauE xi0 ψ (chrStep μ η j).1 (chrStep μ η j).2 JV JW th
def IsThPKernel (ψ : AddChar (AF F) ℂ) (μ : ℕ → (AEF F E)ˣ →* Circle) (η : (AEF F E)ˣ →* Circle) (j : ℕ)
    {nV nW : ℕ} (JV : Matrix (Fin nV) (Fin nV) E) (JW : Matrix (Fin nW) (Fin nW) E)
    (th : GAF σ JW → GAF σ JV → (WOF F E nV nW → ℂ) → ℂ) : Prop :=
  IsPairKernel σ tauE xi0 ψ (attChr (μ j) η nV) (attChr (μ j) η nW) JV JW fun h g f => th g h f
def IsChainKernel (ψ : AddChar (AF F) ℂ) (μ : ℕ → (AEF F E)ˣ →* Circle) (η : (AEF F E)ˣ →* Circle) (m : ℕ)
    (n : ℕ → ℕ) (Y : ∀ k, Matrix (Fin (n k)) (Fin (n k)) E)
    (th : ∀ k, GAF σ (Y k) → GAF σ (Y (k + 1)) → (WOF F E (n k) (n (k + 1)) → ℂ) → ℂ) : Prop :=
  ∀ k < m, IsPairKernel σ tauE xi0 ψ (attChr (μ (k + 1)) η (n k)) (attChr (μ (k + 1)) η (n (k + 1))) (Y k) (Y (k + 1))
    (th k)
variable (F) in

def intAfF : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}
variable (F E) in

def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAfF F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}
def UnramEverywhereF (χ : (AEF F E)ˣ →* Circle) : Prop :=
  ∀ x : (AEF F E)ˣ, infPartF F E (x : AEF F E) = 1 → finPartF F E (x : AEF F E) ∈ intAEF F E →
    finPartF F E ((x⁻¹ : (AEF F E)ˣ) : AEF F E) ∈ intAEF F E → χ x = 1
def HasInfExpF (χ : (AEF F E)ˣ →* Circle) (τ : Tau) (a : ℚ) : Prop :=
  ∃ n : ℤ, (n : ℚ) = 2 * a ∧
    AllSome (IsInfFamF (F := F) tauE) fun θ =>
      ∀ x : (AEF F E)ˣ, finPartF F E (x : AEF F E) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPartF F E (x : AEF F E)) = 1) →
        ((χ x : Circle) : ℂ) = (θ τ (infPartF F E (x : AEF F E)) / (‖θ τ (infPartF F E (x : AEF F E))‖ : ℂ)) ^ n
def CharsOK (μ : ℕ → (AEF F E)ˣ →* Circle) (η : (AEF F E)ˣ →* Circle) (m : ℕ) : Prop :=
  IsHeckeCharF η ∧ UnramEverywhereF η ∧ ResEtaF η 1 ∧ (∀ τ, HasInfExpF tauE η τ (1 / 2)) ∧
    ∀ j ∈ Finset.Icc 1 m, IsHeckeCharF (μ j) ∧ ResEtaF (μ j) 0
def PtTheta {Sinf : Type*} (ψ : AddChar (AF F) ℂ) {nV nW : ℕ} (JV : Matrix (Fin nV) (Fin nV) E)
    (JW : Matrix (Fin nW) (Fin nW) E) (pt : Sinf → (WOF F E nV nW → ℂ)) : Prop :=
  ∀ φ, IsThetaFunOF σ JV JW xi0 ψ (pt φ)
end Kernels
end Formalism.IndefR.LiftF
end


