-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
-- name    : Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:31.319517+00:00
-- url     : https://prove2.me/theorems/0292b524-1d9e-426b-b339-f7b502e76484
-- title:
--   Character Column Kernel Equality Form
-- statement:
--   Definitions and structural lemmas for Character Column Kernel Equality Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/CharacterColumnKernelEqualityForm.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementPsi
import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_StatementGC
import Definitions.Def_Formalism_CharacterColumnKernels_StatementNG
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
def StatColKerChiC : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A),
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : d → KO O, (algebraMap T' A δ) • m = δO • m) →
    Module.length O (kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0) ≤
      ∑ l, Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) +
      (Fintype.card ι : ℕ∞) * (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO
def StatColKerChiOne : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (ℓ : ℕ) (e' : ι → ℕ),
    (∀ g (m : d → KO O), uElt r χ g • m = m) →
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = δO • m) →
    (∀ m : d → KO O, (algebraMap T' A δ) • m = δO • m) →
    (∀ l, ∃ g ∈ D l, ∃ c : O, IsUnit c ∧
      ∀ m : d → KO O, k0 l g • m = ((ℓ : O) ^ e' l * δO * c) • m) →
    Module.length O (kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0) ≤
      ∑ l, (Fintype.card d : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' l : ℕ∞) +
          2 * IsDiscreteValuationRing.addVal O δO) +
      (Fintype.card ι : ℕ∞) * (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO
def StatBlockChiCFull : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    [Module T' (d → KO O)] [IsScalarTower T' A (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ι' : Type*) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ) (sE : Finset G) (tE : G → T'),
    Fintype.card d = 1 →
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : d → KO O, δ • m = δO • m) →
    (∀ m : d → KO O, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    let ρM := uRep O (M := d → KO O) r χ
    let Ψ := colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (Sha H0 : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ cols, Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D w))) ≤ H0) →
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ Sha →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (d → KO O)) ≤
      Sha + eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w
def StatBlockChiOneFull : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    [Module T' (d → KO O)] [IsScalarTower T' A (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ι' : Type*) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ),
    Fintype.card d = 1 →
    (∀ g (m : d → KO O), uElt r χ g • m = m) →
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = δO • m) →
    (∀ m : d → KO O, δ • m = δO • m) →
    (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
      ∀ m : d → KO O, k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * c) • m) →
    let ρM := uRep O (M := d → KO O) r χ
    let Ψ := colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (vhE : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ vhE →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (d → KO O)) ≤
      vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
        eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        ∑ w ∈ qs, vζ w
abbrev blockRestrictedRepresentationType {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*} {d : Type}
    [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {α : Type}
    [DecidableEq α] (bl : d → α)
    (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O) (k : α) : Type _ :=
  LatQ O {a // bl a = k} (ρk k).toRingHom
def characterColumnKernelEqualityForm : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      [IsNoetherian R' R'],
    (∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    ∀ (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
      [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
      (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
      (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → R')
      (k0 : ι → G → R'),
      E * E = algebraMap Tc R' δ * E → e₁ * e₁ = e₁ →
    (∀ x', p x' ∉ Z →
      ∃ δx : FractionRing O, δx ≠ 0 ∧ (∀ v : EvalSp O d R' x', δ • v = δx • v) ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E)) = 1 ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁)) = 1 ∧
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : G, ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ L : Submodule (FractionRing O) (D (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l))) ≤ L ∧
        (∀ a, ∀ s ∈ LinearMap.range
            (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁),
          (fun g : D (colIdx l) => Kc l a g • s) ∈ L) ∧
        (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E),
          (fun g : D (colIdx l) => k0 l g • s) ∈ L) ∧
        Module.rank (FractionRing O)
            (L ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))).comap
              L.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))) : ℕ))) →
    ∀ (g₀ : ℕ)
      (n : Fin g₀ → ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0),
      Submodule.span R' (Set.range n) = ⊤ →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] → [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)] →
      [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] →
      ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
      (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) →
    ∀ (sE : Finset G) (tE : G → Tc) (δO : O) (ℓ cB : ℕ) (what₂ qs : Finset ℕ) (lenRow : ℕ → ℕ∞)
      (deg : ℕ → ℕ) (vζ : ℕ → ℕ∞) (s vhE H0 : ℕ∞) (Sha : ℕ → ℕ∞),
      E = ∑ g ∈ sE, tE g • r g → (∀ l g, ∃ a : R', k0 l g = a * E) →
    let NNc := ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D w)))

    (∀ m : blockRestrictedRepresentationType bl ρk 0, E • m = 0) → (∀ m : blockRestrictedRepresentationType bl ρk 0, δ • m = δO • m) →
    (∀ m : blockRestrictedRepresentationType bl ρk 0, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j (colIdx l)) → blockRestrictedRepresentationType bl ρk 0),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) →
    (let ρM := uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ
     let Ψ := colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ (fun l => D (colIdx l))
       (fun l => j (colIdx l)) Kc k0
     ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
      (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
        Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
        ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
      (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
      (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
      Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s) →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, δ • m = δO • m) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (D w))) ≤ H0) ∧
      (let ρM := uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ
       let Ψ := colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ (fun l => D (colIdx l))
         (fun l => j (colIdx l)) Kc k0
       ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
        (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
          Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
          ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
        (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
          Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
          ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
        (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
        (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
        Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤
          Sha ((c : ℕ) - 1))) →

    (let c1 : Fin (t + 1) := ⟨1, by omega⟩
     (∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
     (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, δ • m = δO • m) ∧
     (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
       ∀ m : blockRestrictedRepresentationType bl ρk c1, k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * c) • m) ∧
     (let ρM := uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ
      let Ψ := colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ (fun l => D (colIdx l))
        (fun l => j (colIdx l)) Kc k0
      ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
       (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
         Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
         ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
       (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
         Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
         ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
       (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
       (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
       Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ vhE)) →
    vcc T Z (p π') ≤
      ∑ w ∈ what₂, lenRow w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, vζ w
end Formalism.NG


