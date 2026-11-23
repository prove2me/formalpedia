-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:06.594903+00:00
-- url     : https://prove2.me/theorems/d6a116d1-968d-491d-b3cf-ed26040e1067
-- title:
--   Idem Not Mem Fil VOne
-- statement:
--   Definitions and structural lemmas for Idem Not Mem Fil VOne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IdemNotMemFilVOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
abbrev tensBil (E : V ⊗[LL] V' ≃ₗ[LL] V'') : V →ₗ[LL] V' →ₗ[LL] V'' :=
  (TensorProduct.mk LL V V').compr₂ E.toLinearMap
section Twist
variable (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') (w : F) (ψ : G → Qp)
  (hw : ∀ g, PD.actdR g w = ψ g • w) (hf : ∀ g x, ψ g • ρ' g (f x) = f (ρ g x))
include hw hf
end Twist
variable [FiniteDimensional Qp K] [CharZero Qp]
namespace Adapted
variable {PD} {ρ : Representation LL G V} {τ : K →ₐ[Qp] LL} {ι : Type} [Fintype ι]
    {d : ι → V ⊗[Qp] F} {k : ι → ℤ} (h : Adapted PD ρ τ d k)
include h
end Adapted
end GlobalTheory.DRFil


