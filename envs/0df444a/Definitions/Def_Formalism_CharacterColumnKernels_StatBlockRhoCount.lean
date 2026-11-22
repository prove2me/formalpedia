-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
-- name    : Formalism_CharacterColumnKernels_StatBlockRhoCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:24.949815+00:00
-- url     : https://prove2.me/theorems/f4071189-e48d-4aa8-b5f7-8dd4f0f1e2ac
-- title:
--   Stat Block Rho Count
-- statement:
--   Definitions and structural lemmas for Stat Block Rho Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatBlockRhoCount.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
def StatBlockRhoAbs : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type*) [Group G]
    (d : Type) [Fintype d] (ρM : Representation O G (d → KO O)) (H : Type*) [AddCommGroup H]
    [Module O H] (Ψ : H →ₗ[O] coZ1s ρM) (δ : O),
    (∀ h : H, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δ * δ) • v = 0) →
    ∀ (ι : Type*) [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
      (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
      (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞) (ℓ : ℕ) (e' j : ι → ℕ) (h0 : ι → ℕ∞),
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δ
    let N : ℕ∞ := Fintype.card d
    (∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))), F w ≤ A ∧
      Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A) →
    (∀ w ∈ cols, ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + (cols.card : ℕ∞) * N * vδ →
    Module.length O H ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ
abbrev ColData (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) (δ : O)
    (e' j : ℕ) (Xw : Type*) [AddCommGroup Xw] [Module O Xw] (d : Type) [Fintype d] : Type _ :=
  (Fin j → LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' * δ))) × Xw ×
    LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δ)
def StatKerCount : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Hk : Type*) [AddCommGroup Hk]
    [Module O Hk] (ι : Type*) (cols : Finset ι) (ℓ : ℕ) (δ : O) (e' j : ι → ℕ) (d : Type) [Fintype d]
    (Xw : ι → Type*) [∀ w, AddCommGroup (Xw w)] [∀ w, Module O (Xw w)] (h0 : ι → ℕ∞),
    (∀ w, Module.length O (Xw w) ≤ h0 w) →
    ∀ f : Hk →ₗ[O] ((w : cols) → ColData O ℓ δ (e' w) (j w) (Xw w) d), Function.Injective f →
      Module.length O Hk ≤
        ∑ w ∈ cols, ((j w : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' w : ℕ∞) +
          IsDiscreteValuationRing.addVal O δ) + h0 w) +
        (cols.card : ℕ∞) * (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δ
def StatBlockRhoCount : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type*) [Group G]
    (d : Type) [Fintype d] (ρM : Representation O G (d → KO O)) (H : Type*) [AddCommGroup H]
    [Module O H] (Ψ : H →ₗ[O] coZ1s ρM) (δ : O),
    (∀ h : H, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δ * δ) • v = 0) →
    ∀ (ι : Type*) [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
      (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
      (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞) (ℓ : ℕ) (e' j : ι → ℕ) (h0 : ι → ℕ∞),
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δ
    let N : ℕ∞ := Fintype.card d
    (∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))), F w ≤ A ∧
      Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A) →
    (∀ w ∈ cols, ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    ∀ (Xw : ι → Type*) [∀ w, AddCommGroup (Xw w)] [∀ w, Module O (Xw w)],
      (∀ w, Module.length O (Xw w) ≤ h0 w) →
      ∀ f : LinearMap.ker Ψ →ₗ[O] ((w : cols) → ColData O ℓ δ (e' w) (j w) (Xw w) d),
      Function.Injective f →
    Module.length O H ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ
end Formalism.NG


