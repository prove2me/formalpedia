-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
-- name    : Formalism_CharacterColumnKernels_StatementColKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:43.324798+00:00
-- url     : https://prove2.me/theorems/4efb6e09-1353-493a-84e1-03318ced1a3a
-- title:
--   Statement Col Ker
-- statement:
--   Definitions and structural lemmas for Statement Col Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementColKer.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.NG
def colDO {A T' O M G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [CommRing O] [Group G]
    [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) : M →ₗ[O] (D → M) where
  toFun v g := ((((χ g)⁻¹ : T'ˣ) : T') • r g) • v - v
  map_add' v w := by ext g; simp only [smul_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm]
def evalO {A O N M : Type*} [Ring A] [CommRing O] [AddCommGroup N] [Module A N] [AddCommGroup M]
    [Module A M] [Module O M] [SMulCommClass A O M] (x : N) : (N →ₗ[A] M) →ₗ[O] M where
  toFun φ := φ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def kerY {A T' O M G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [CommRing O] [Group G]
    [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι] (D : ι → Subgroup G)
    (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) :
    Submodule O (ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) :=
  ⨅ y : Ymod r χ E, LinearMap.ker (evalO (Submodule.Quotient.mk ((y, 0) : ColFreeJ A r χ E ι j)))
def StatColKer : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (ℓ : ℕ) (e' : ι → ℕ),
    (∀ m : d → KO O, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : d → KO O, (algebraMap T' A δ) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j l) → (d → KO O)),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁)) →
      (fun g : D l => ∑ a, Kc l a g • s a) ∈ LinearMap.range (colDO (O := O) r χ (D l)) →
      ∀ a, ((ℓ : O) ^ e' l) • s a = 0) →
    Module.length O (kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0) ≤
      ∑ l, ((j l : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' l : ℕ∞) +
          IsDiscreteValuationRing.addVal O δO) +
        Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)))) +
      (Fintype.card ι : ℕ∞) * (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO
def StatBlockRhoColumn : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ι' : Type*) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ : ℕ),
    (∀ m : d → KO O, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : d → KO O, (algebraMap T' A δ) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j (colIdx l)) → (d → KO O)),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) →
    ∀ (ρM : Representation O G (d → KO O))
      (Ψ : (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A] (d → KO O))
        →ₗ[O] coZ1s ρM),
    LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 →
    (∀ h, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δO * δO) • v = 0) →
    ∀ (what₂ : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (lenRow : ι' → ℕ∞)
      (Q : Submodule O (H1z ρM)) (s : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card d
    let h0 : ι' → ℕ∞ := fun w => Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D w)))
    (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (d → KO O)) ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ
end Formalism.NG


