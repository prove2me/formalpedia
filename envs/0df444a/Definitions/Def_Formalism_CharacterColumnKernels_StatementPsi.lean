-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementPsi
-- name    : Formalism_CharacterColumnKernels_StatementPsi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:59.163573+00:00
-- url     : https://prove2.me/theorems/e2cd1193-3616-4a65-a8da-1bb79de2532e
-- title:
--   Statement Psi
-- statement:
--   Definitions and structural lemmas for Statement Psi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementPsi.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
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
section U
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
def uElt (r : G →* A) (χ : G →* T'ˣ) (g : G) : A := (((χ g)⁻¹ : T'ˣ) : T') • r g
theorem uElt_one (r : G →* A) (χ : G →* T'ˣ) : uElt r χ 1 = 1 := by
  simp [uElt]
theorem uElt_mul (r : G →* A) (χ : G →* T'ˣ) (g h : G) :
    uElt r χ (g * h) = uElt r χ g * uElt r χ h := by
  simp only [uElt, map_mul, mul_inv, Units.val_mul]
  rw [smul_mul_smul_comm]
def uRep (O : Type*) [CommRing O] {M : Type*} [AddCommGroup M] [Module A M] [Module O M]
    [SMulCommClass A O M] (r : G →* A) (χ : G →* T'ˣ) : Representation O G M where
  toFun g := DistribSMul.toLinearMap O M (uElt r χ g)
  map_one' := by
    refine LinearMap.ext fun m => ?_
    simp [uElt_one]
  map_mul' g h := by
    refine LinearMap.ext fun m => ?_
    simp [uElt_mul, mul_smul]
theorem ycoc_mul (r : G →* A) (χ : G →* T'ˣ) (E : A) (g h : G) :
    ycoc r χ E (g * h) = ycoc r χ E g + uElt r χ g * ycoc r χ E h := by
  have hu : ∀ x, (((χ x)⁻¹ : T'ˣ) : T') • r x = uElt r χ x := fun x => rfl
  simp only [ycoc, hu, uElt_mul]
  noncomm_ring
end U
section Psi
variable {O A T' G : Type*} [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {M : Type*} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
def yGen (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (g : G) :
    ColNNJ r χ E e₁ δ D j Kc k0 :=
  Submodule.Quotient.mk ((⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩, 0) : ColFreeJ A r χ E ι j)
theorem yGen_mul (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (g h : G) :
    yGen r χ E e₁ δ D j Kc k0 (g * h) =
      yGen r χ E e₁ δ D j Kc k0 g + uElt r χ g • yGen r χ E e₁ δ D j Kc k0 h := by
  unfold yGen
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    simp [ycoc_mul]
  · simp
def colPsi (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) :
    (ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) →ₗ[O] coZ1s (uRep O (M := M) r χ) where
  toFun φ := ⟨fun g => φ (yGen r χ E e₁ δ D j Kc k0 g), fun g h => by
    simp only [yGen_mul, map_add, map_smul]
    rfl⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
end Psi
def StatColPsiKer : Prop :=
  ∀ (O A T' G : Type*) [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A),
    LinearMap.ker (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0) =
      kerY (O := O) (M := M) r χ E e₁ δ D j Kc k0
def StatCobColumn : Prop :=
  ∀ (O A T' G : Type*) [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [Module T' M] [IsScalarTower T' A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (s : Finset G) (t : G → T'),
    E = ∑ g ∈ s, t g • r g → E * E = δ • E → (∀ m : M, E • m = 0) →
    (∀ m : M, δ • m = δO • m) → (∀ m : M, (∑ g ∈ s, t g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (v : M),
      ((colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ : coZ1s (uRep O (M := M) r χ)) : G → M) =
        coD0 (uRep O (M := M) r χ) v →
      (δO * δO) • v = 0
def BlockRhoFull₂ : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    [Module T' (d → KO O)] [IsScalarTower T' A (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ι' : Type*) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ : ℕ) (sE : Finset G) (tE : G → T'),
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : d → KO O, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : d → KO O, δ • m = δO • m) →
    (∀ m : d → KO O, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j (colIdx l)) → (d → KO O)),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) →
    let ρM := uRep O (M := d → KO O) r χ
    let Ψ := colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
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


