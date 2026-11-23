-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:00.315716+00:00
-- url     : https://prove2.me/theorems/0745d6e0-9a7b-4ac0-b026-a1f3653303b5
-- title:
--   Is Irreducible Iff Of Linear Equiv
-- statement:
--   Definitions and structural lemmas for Is Irreducible Iff Of Linear Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
namespace GlobalTheory.SmGL.MultiIrr
section General
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
theorem mem_smooth_of_eventually {P : Subgroup G} {σ : Representation F P W} (f : indSpace P σ)
    (h : ∀ᶠ u in nhds (1 : G), ∀ x, f.1 (x * u) = f.1 x) : f ∈ smoothPart (ind P σ) :=
  mem_smoothPart_of_nhds (h.mono fun _ hu => Subtype.ext (funext hu))
theorem eventually_of_smooth {P : Subgroup G} {σ : Representation F P W} (f : smoothPart (ind P σ)) :
    ∀ᶠ u in nhds (1 : G), ∀ x, f.1.1 (x * u) = f.1.1 x :=
  Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun _ hu x =>
    congrFun (congrArg Subtype.val hu) x
def indPull {P : Subgroup G} {Q : Subgroup H} {σ : Representation F P V} {τ : Representation F Q W}
    (φ : G →* H) (hφ : Continuous φ) (κ : W →ₗ[F] V)
    (h : ∀ p : P, ∃ q : Q, (q : H) = φ p ∧ ∀ w, σ p (κ w) = κ (τ q w)) :
    smoothPart (ind Q τ) →ₗ[F] smoothPart (ind P σ) where
  toFun f := ⟨⟨fun g => κ (f.1.1 (φ g)), fun p g => by
      obtain ⟨q, hq, hs⟩ := h p
      show κ (f.1.1 (φ (p * g))) = σ p (κ (f.1.1 (φ g)))
      rw [map_mul, ← hq, f.1.2 q, hs]⟩,
    mem_smooth_of_eventually _ (((hφ.tendsto' 1 1 (map_one φ)).eventually (eventually_of_smooth f)).mono
      fun u hu x => by
        show κ (f.1.1 (φ (x * u))) = κ (f.1.1 (φ x))
        rw [map_mul, hu])⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (funext fun _ => map_add κ _ _))
  map_smul' _ _ := Subtype.ext (Subtype.ext (funext fun _ => map_smul κ _ _))
def ev {P : Subgroup H} (ρ : Representation F P W) (x : H) : smoothPart (ind P ρ) →ₗ[F] W where
  toFun f := f.1.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] in

def coord (l : V →ₗ[F] F) (W : Type) [AddCommGroup W] [Module F W] : V ⊗[F] W →ₗ[F] W :=
  (TensorProduct.lid F W).toLinearMap ∘ₗ l.rTensor W
end General
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
def relabel (R : Type) [CommRing R] (e : a ≃ b) : GL a R ≃* GL b R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv
variable {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
def headTail (m : Fin (s + 1) → Type) : m 0 ⊕ (Σ i : Fin s, m i.succ) ≃ Σ i, m i :=
  Equiv.ofBijective (Sum.elim (fun x => ⟨0, x⟩) fun y => ⟨y.1.succ, y.2⟩) ⟨by
    rintro (x | ⟨i, x⟩) (y | ⟨j, y⟩) h
    · simpa using h
    · exact absurd (congrArg Sigma.fst h) (Fin.succ_ne_zero _).symm
    · exact absurd (congrArg Sigma.fst h) (Fin.succ_ne_zero _)
    · obtain rfl : i = j := Fin.succ_injective _ (congrArg Sigma.fst h)
      simpa using h, by
    rintro ⟨i, x⟩
    induction i using Fin.cases with
    | zero => exact ⟨.inl x, rfl⟩
    | succ i => exact ⟨.inr ⟨i, x⟩, rfl⟩⟩
def tensorCons (X : Fin (s + 1) → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] :
    X 0 ⊗[ℂ] (⨂[ℂ] i : Fin s, X i.succ) ≃ₗ[ℂ] ⨂[ℂ] i, X i :=
  LinearEquiv.ofLinear
    (TensorProduct.lift (PiTensorProduct.lift.toLinearMap ∘ₗ (PiTensorProduct.tprod ℂ).curryLeft))
    (PiTensorProduct.lift (LinearMap.uncurryLeft
      { toFun := fun x => (TensorProduct.mk ℂ _ _ x).compMultilinearMap (PiTensorProduct.tprod ℂ)
        map_add' := fun x y => by ext; simp [TensorProduct.add_tmul]
        map_smul' := fun c x => by ext; simp [TensorProduct.smul_tmul'] }))
    (by ext x; simp) (by ext x y; simp)
end Local
end GlobalTheory.SmGL.MultiIrr


