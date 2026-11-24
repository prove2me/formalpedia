-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:55.371286+00:00
-- url     : https://prove2.me/theorems/034b7078-2626-49d0-b306-21f2decafa43
-- title:
--   Adjoint Operator Identities
-- statement:
--   Definitions and structural lemmas for Adjoint Operator Identities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/AdjointOperatorIdentities.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_phiOne_dia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section Notions
variable {n : Type}
def KeepsFinite (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  ∀ φ : Form k n ℂ, (Function.support φ).Finite → (Function.support (A φ)).Finite
def IsScaledUnitaryOn (W : Submodule ℂ (Form k n ℂ)) (a : ℂ) (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  Set.BijOn A {φ | φ ∈ W ∧ (Function.support φ).Finite} {φ | φ ∈ W ∧ (Function.support φ).Finite} ∧
    ∀ φ ∈ W, ∀ φ' ∈ W, (Function.support φ).Finite → (Function.support φ').Finite →
      cntIp (A φ) (A φ') = a * cntIp φ φ'
def IsUnitStable {V : Type} [AddCommGroup V] [Module 𝓀[k] V] (S : Finset {x : V // x ≠ 0}) : Prop :=
  ∀ (c : 𝓀[k]ˣ) (x y : {x : V // x ≠ 0}), x ∈ S → y.1 = (c : 𝓀[k]) • x.1 → y ∈ S
end Notions
variable (k) in

structure Vanishing (n : Type) [Fintype n] [DecidableEq n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k) :
    Prop where

  trLat_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], trLat L φ = 0

  trKer_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], trKer L φ = 0

  partial_lat : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (S : Finset {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}), IsUnitStable (k := k) S → ∑ f ∈ S, φ (ofDual L f) = 0

  partial_ker : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (S : Finset {x : Red L // x ≠ 0}), IsUnitStable (k := k) S → ∑ x ∈ S, φ (up L ϖ x) = 0

  invariant_eq_zero : ∀ (π : Representation ℂ (GL n k) M) (P : Pair k n) (v : levelVec π P),
    formOf π P v ∈ Mram k n M → ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (θ : M →ₗ[ℂ] M'),
    ((∀ g ∈ latStab P.lat, ∀ w, θ (π g w) = θ w) ∨ (∀ g ∈ latStab P.ker, ∀ w, θ (π g w) = θ w)) → θ v = 0
variable (k) in

structure OperatorIdentities (n : Type) [Fintype n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k)
    (χ : AddChar 𝓀[k] ℂ) : Prop where

  FFStar_formula : ∀ (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] [Fintype {x : Red L // x ≠ 0}]
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    FFStar ϖ χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L ϖ x)

  FFStar_mul_FF : (FFStar ϖ χ * FF ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr

  FF_mul_FFStar : (FF ϖ χ * FFStar ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr'

  FFStar_FF_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ (FF ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_FFStar_ram : ∀ φ ∈ Mram k n M, FF ϖ χ (FFStar ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_mem_ram : ∀ φ ∈ Mram k n M, FF ϖ χ φ ∈ Mram k n M

  FFStar_mem_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ φ ∈ Mram k n M

  D_dia : ∀ c : 𝓀[k]ˣ, (D ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * D ϖ

  FF_dia : ∀ c : 𝓀[k]ˣ, (FF ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FF ϖ χ

  FF_eq_D_Gs : ∀ φ ∈ Mram k n M, FF ϖ χ φ = D ϖ (Gs χ φ)

  Gs_mul_GsStar : (Gs χ * GsStar χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm

  D_U_ram : ∀ φ ∈ Mram k n M, D ϖ (U ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  U_D_ram : ∀ φ ∈ Mram k n M, U ϖ (D ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  FFStar_dia : ∀ c : 𝓀[k]ˣ, (FFStar ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FFStar ϖ χ

  U_dia : ∀ c : 𝓀[k]ˣ, (U ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * U ϖ

  dia_mem_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M, dia c φ ∈ Mram k n M

  phiOne_dia : ∀ (c : 𝓀[k]ˣ) (m : Type) [Fintype m] (P : Pair k n) (Q : Pair k m),
    phiOne (c • P) (c • Q) = phiOne P Q

  twisted_class_sum : ∀ (ε : 𝓀[k]ˣ) (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    ∑ x : {x : Red L // x ≠ 0}, χ (-((ε : 𝓀[k]) * f.1 x.1)) • φ (up L ϖ x) = dia ε (FFStar ϖ χ φ) (ofDual L f)

  sign_FFStar_sign_FF : (dia (-1) * FFStar ϖ χ * (dia (-1) * FF ϖ χ) : Module.End ℂ (Form k n M)) =
    FFStar ϖ χ * FF ϖ χ

  sign_ram : ∀ φ ∈ Mram k n M,
    dia (-1) (FFStar ϖ χ (dia (-1) (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  unit_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M,
    dia c (FFStar ϖ χ (dia c⁻¹ (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ
variable (k) in

structure AdjointIdentities (n : Type) [Fintype n] (ϖ : Unif k) (χ : AddChar 𝓀[k] ℂ) : Prop where

  FF_finite : KeepsFinite (n := n) (FF ϖ χ) ∧ KeepsFinite (n := n) (FFStar ϖ χ)

  D_finite : KeepsFinite (n := n) (D ϖ) ∧ KeepsFinite (n := n) (U ϖ)

  FF_adj : IsAdj (n := n) (FF ϖ χ) (FFStar ϖ χ)

  FF_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (FF ϖ χ)

  Gs_adj : IsAdj (n := n) (Gs χ) (GsStar χ)

  U_adj : IsAdj (n := n) (U ϖ) (D ϖ)

  dia_adj : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c) (dia c⁻¹)

  dia_unitary : ∀ c : 𝓀[k]ˣ, IsScaledUnitaryOn (n := n) ⊤ 1 (dia c) ∧ IsScaledUnitaryOn (Mram k n ℂ) 1 (dia c)

  sign_adj : IsAdj (n := n) (dia (-1) * FF ϖ χ) (dia (-1) * FFStar ϖ χ)

  sign_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia (-1) * FF ϖ χ)

  unit_unitary : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c⁻¹ * FF ϖ χ) (dia c * FFStar ϖ χ) ∧
    IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia c⁻¹ * FF ϖ χ)
def PairOperatorStatement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (n : Type) [Fintype n] [DecidableEq n],
    (∀ (M : Type) [AddCommGroup M] [Module ℂ M],
      Vanishing k n M ϖ ∧ OperatorIdentities k n M ϖ (resChar ψ hψ ϖ)) ∧
    AdjointIdentities k n ϖ (resChar ψ hψ ϖ)
section Examples
example {n : Type} (W : Submodule ℂ (Form k n ℂ)) : IsScaledUnitaryOn W 1 1 :=
  ⟨Set.bijOn_id _, fun _ _ _ _ _ _ => (one_mul _).symm⟩
example {V : Type} [AddCommGroup V] [Module 𝓀[k] V] [Fintype {x : V // x ≠ 0}] :
    IsUnitStable (k := k) (Finset.univ : Finset {x : V // x ≠ 0}) := fun _ _ _ _ _ => Finset.mem_univ _
example {n : Type} [Fintype n] [Nonempty n] (a : ℂ) : ¬ IsScaledUnitaryOn (k := k) (n := n) ⊤ a 0 := by
  classical
  obtain ⟨P⟩ : Nonempty (Pair k n) := inferInstance
  rintro ⟨h, -⟩
  obtain ⟨φ, -, hφ⟩ := h.surjOn (show Pi.single P (1 : ℂ) ∈ {φ : Form k n ℂ | φ ∈ (⊤ : Submodule ℂ _) ∧ (Function.support φ).Finite} from
    ⟨trivial, (Set.finite_singleton P).subset Pi.support_single_subset⟩)
  simpa using congrFun hφ P
end Examples
end GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities


