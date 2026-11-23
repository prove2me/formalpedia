-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
-- name    : Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:59.334973+00:00
-- url     : https://prove2.me/theorems/25479aac-185e-445e-b28a-da85c9c29634
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/CoprimeLiftBounds/Statement.lean

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_WachLatticeTwists_StatementDual
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
namespace Formalism.RepresentationBoundsCohomology.BR
open Formalism.NG
section Gens
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
def yY (r : G →* A) (χ : G →* T'ˣ) (E : A) (g : G) : Ymod r χ E :=
  ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩
variable (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
  (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
def nuGen (l : ι) : ColNNJ r χ E e₁ δ D j Kc k0 :=
  Submodule.Quotient.mk (colGenJ 0 l 1 0 0)
def sigGen (l : ι) (a : Fin (j l)) : ColNNJ r χ E e₁ δ D j Kc k0 :=
  Submodule.Quotient.mk (colGenJ 0 l 0 (Pi.single a 1) 0)
def sigmaZeroColumnGenerator (l : ι) : ColNNJ r χ E e₁ δ D j Kc k0 :=
  Submodule.Quotient.mk (colGenJ 0 l 0 0 1)
end Gens
def twRep {O D : Type*} [CommRing O] [Group D] (ε : D →* Oˣ) (N : Type*) [AddCommGroup N]
    [Module O N] : Representation O D N where
  toFun g := ((ε g : Oˣ) : O) • LinearMap.id
  map_one' := by
    refine LinearMap.ext fun m => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun m => ?_
    simp [mul_smul, smul_comm ((ε g : Oˣ) : O)]
def unrH1 {O G M : Type*} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (I : Subgroup G) : Submodule O (H1z ρ) :=
  LinearMap.ker (resH1 ρ I)
def divBy {O X : Type*} [CommRing O] [AddCommGroup X] [Module O X] (F : Submodule O X) (a : O) :
    Submodule O X :=
  F.comap (LinearMap.lsmul O X a)
def StatRel : Prop :=
  ∀ (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (l : ι),
    E • φ (nuGen r χ E e₁ δ D j Kc k0 l) = 0 ∧
    (∀ a, e₁ • φ (sigGen r χ E e₁ δ D j Kc k0 l a) = φ (sigGen r χ E e₁ δ D j Kc k0 l a)) ∧
    algebraMap T' A δ • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l) =
      E • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l) ∧
    ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) +
        (uElt r χ g • φ (nuGen r χ E e₁ δ D j Kc k0 l) - φ (nuGen r χ E e₁ δ D j Kc k0 l)) =
      algebraMap T' A δ • (∑ a, Kc l a g • φ (sigGen r χ E e₁ δ D j Kc k0 l a) +
        k0 l g • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l))
def StatColRho : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (ℓ : ℕ) (e' : ι → ℕ) (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j l) → G → L),
    (∀ (a : A) v x, tens (a • v) x = a • tens v x) →
    (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) →
    (∀ l a, ∀ g ∈ D l, Kc l a g • v₁ = ((ℓ : O) ^ e' l) • κ l a g) →
    (∀ m : M, E • m = 0) → (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : M, algebraMap T' A δ • m = δO • m) →
    ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (l : ι),
      (∃ x : Fin (j l) → KO O, ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) +
          (uElt r χ g • φ (nuGen r χ E e₁ δ D j Kc k0 l) - φ (nuGen r χ E e₁ δ D j Kc k0 l)) =
        (δO * (ℓ : O) ^ e' l) • ∑ a, tens (κ l a g) (x a)) ∧
      ∀ F : Submodule O (H1z (resRep (uRep O (M := M) r χ) (D l))),
        (∀ (z : coZ1s (resRep (uRep O (M := M) r χ) (D l))) (x : Fin (j l) → KO O),
          (∀ g : D l, (z : D l → M) g = ∑ a, tens (κ l a g) (x a)) → Submodule.mkQ _ z ∈ F) →
        resH1 (uRep O (M := M) r χ) (D l)
          (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) ∈ F
def StatLiftBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L]
    (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) (Dl : Subgroup G) (j : ℕ) (Kc : Fin j → G → A)
    (ℓ e' : ℕ) (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L) (κ : Fin j → G → L),
    (∀ (a : A) v x, tens (a • v) x = a • tens v x) →
    (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) → e₁ * e₁ = e₁ →
    (∀ a, ∀ g ∈ Dl, Kc a g • v₁ = ((ℓ : O) ^ e') • κ a g) →
    (∀ x : Fin j → KO O, (fun g : Dl => ∑ a, tens (κ a g) (x a)) ∈
        LinearMap.range (colDO (O := O) (M := M) r χ Dl) → ∀ a, tens v₁ (x a) = 0) →
    ∀ s : Fin j → M, (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O M e₁)) →
      (fun g : Dl => ∑ a, Kc a g • s a) ∈ LinearMap.range (colDO (O := O) (M := M) r χ Dl) →
      ∀ a, ((ℓ : O) ^ e') • s a = 0
def SelmerFInjective : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (D : Type*) [Group D] (L V M : Type*) [AddCommGroup L] [Module O L] [AddCommGroup V]
    [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    [AddCommGroup M] [Module O M]
    (ρL : Representation O D L) (ρV : Representation (FractionRing O) D V)
    (ρM : Representation O D M) (i : L →ₗ[O] V) (q : V →ₗ[O] M),
    Function.Injective i → Function.Surjective q → LinearMap.ker q = LinearMap.range i →
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range i) →
    (∀ g v, i (ρL g v) = ρV g (i v)) → (∀ g v, q (ρV g v) = ρM g (q v)) →
    ∀ (Ff : Submodule O (H1z ρL)) (j : ℕ) (κ : Fin j → coZ1s ρL),
    (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff → z ∈ Ff) →
    (∀ a, (Submodule.mkQ _ (κ a) : H1z ρL) ∈ Ff) →
    (∀ z ∈ Ff, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL)) = 0) →
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 → b = 0) →
    ∀ (x : Fin j → FractionRing O) (m : M),
      (∀ g, q (∑ a, x a • i ((κ a : D → L) g)) = ρM g m - m) →
      ∀ a, x a ∈ (1 : Submodule O (FractionRing O))
def StatRowCup : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [IsScalarTower O A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (Dw : Subgroup G) (ε : Dw →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O Dw T₁) (ρ₂ : Representation O Dw T₂)
    (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    (C₁ : (Dw → T₁) → Prop) (CN2 : (Dw → Dw → Ymod r χ E) → Prop)
    (CN : (Dw → Ymod r χ E) → Prop) (CA : (Dw → A) → Prop) (CP : (Dw → KO O) → Prop),
    (∀ g b, inc (ρ₁ g b) =
      ((ε g : Oˣ) : O) • (((χ (g : G) : T'ˣ) : T') • (inc b * r ((g : G)⁻¹)))) →
    IsEquivMap ρ₁ ρ₂ π →
    (∀ b m, γ (π b) m = lam (inc b • m)) →
    (∀ a, C₁ a → CN2 (fun g h => inc (a g) • (uElt r χ (g : G) • yY r χ E (h : G)))) →
    (∀ a, C₁ a → CA (fun g => -(inc (a g) * (uElt r χ (g : G) * E)))) →
    (∀ (ψ : Ymod r χ E →ₗ[O] KO O) f, CN f → CP (fun g => ψ (f g))) →
    (∀ z ∈ characterColumnKernelPairSetVariant (twRep ε (Ymod r χ E)), CN2 z →
      (∃ f, CA f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε g : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c, CN c ∧ ∀ g h, z g h = ((ε g : Oˣ) : O) • c h - c (g * h) + c g) →
    ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (a : Dw → T₁), a ∈ characterColumnKernelSet ρ₁ → C₁ a →
      ∃ c, CP c ∧ ∀ g h : Dw,
        γ (π (a g)) (uElt r χ (g : G) • φ (yGen r χ E e₁ δ D j Kc k0 (h : G))) =
          ((ε g : Oˣ) : O) • c h - c (g * h) + c g
def StatRowRho : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Dw : Type*) [Group Dw] (M : Type*) [AddCommGroup M] [Module O M]
    (ρM : Representation O Dw M) (ε : Dw →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O Dw T₁) (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O)
    (C₁ : (Dw → T₁) → Prop) (CP : (Dw → KO O) → Prop)
    (Hc : Submodule O (H1z ρM)) (Cs : Type*) [AddCommGroup Cs] [Module O Cs]
    (cls : (Dw → T₂) → Cs) (pr : Hc →ₗ[O] Cs →ₗ[O] KO O) (Fs Im : Submodule O Cs)
    (X : Set (coZ1s ρM)),
    (∀ (a : Dw → T₁) (b : coZ1s ρM) (hb : Submodule.mkQ _ b ∈ Hc), a ∈ characterColumnKernelSet ρ₁ → C₁ a →
      (∃ c, CP c ∧ ∀ g h : Dw, γ (π (a g)) (ρM g ((b : Dw → M) h)) =
        ((ε g : Oˣ) : O) • c h - c (g * h) + c g) →
      pr ⟨Submodule.mkQ _ b, hb⟩ (cls (fun g => π (a g))) = 0) →
    (∀ x ∈ Im, ∃ a ∈ characterColumnKernelSet ρ₁, C₁ a ∧ x = cls (fun g => π (a g))) →
    Im ≤ Fs →
    (∀ b ∈ X, Submodule.mkQ _ b ∈ Hc) →
    (∀ b ∈ X, ∀ a ∈ characterColumnKernelSet ρ₁, C₁ a → ∃ c, CP c ∧ ∀ g h : Dw,
      γ (π (a g)) (ρM g ((b : Dw → M) h)) = ((ε g : Oˣ) : O) • c h - c (g * h) + c g) →
    ∃ B : Submodule O (H1z ρM), (annih pr Fs).map Hc.subtype ≤ B ∧
      Module.length O (B ⧸ ((annih pr Fs).map Hc.subtype).comap B.subtype) ≤
        Module.length O (Fs ⧸ Im.comap Fs.subtype) ∧
      ∀ b ∈ X, Submodule.mkQ _ b ∈ B
def StatRowTB : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [IsScalarTower O A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (Dw : Subgroup G) (ℓ c cB deg : ℕ)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw))),
    F ≤ Hc → c ≤ cB →
    (∀ φ, resH1 (uRep O (M := M) r χ) Dw
      (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) ∈ Hc) →
    (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
      ∀ z : coZ1s (resRep (uRep O (M := M) r χ) Dw),
        (∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : G))) →
        ((ℓ : O) ^ c) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) Dw)) ∈ F) →
    Module.length O (↥(Hc ⊓ divBy F ((ℓ : O) ^ c)) ⧸
        F.comap (Hc ⊓ divBy F ((ℓ : O) ^ c)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (c : ℕ∞) * ((deg : ℕ∞) + 1) →
    ∃ B : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)), F ≤ B ∧
      Module.length O (B ⧸ F.comap B.subtype) ≤
        Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cB : ℕ∞) * ((deg : ℕ∞) + 2) ∧
      ∀ φ, resH1 (uRep O (M := M) r χ) Dw
        (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) ∈ B
def StatQAlg : Prop :=
  ∀ (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (γ : G) (ζ : T'),
    (r γ - 1) * (r γ - algebraMap T' A ζ) = 0 → ((χ γ : T'ˣ) : T') = ζ →
    (r γ - 1) * ycoc r χ E γ = 0
def StatQPlace : Prop :=
  ∀ (O : Type*) [CommRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (Dw : Subgroup G) (I : Subgroup Dw) (γ : Dw) (ζ : T') (ζO : O) (n : Dw → ℕ),
    γ ∈ I →
    (r (γ : G) - 1) * (r (γ : G) - algebraMap T' A ζ) = 0 → ((χ (γ : G) : T'ˣ) : T') = ζ →
    (∀ g ∈ I, r (g : G) = r (γ : G) ^ n g ∧ χ (g : G) = χ (γ : G) ^ n g) →
    (∀ g ∈ I, ∀ m : M, uElt r χ (g : G) • m = m) →
    (∀ m : M, r (γ : G) • m = ζO • m) →
    (∀ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M,
      (ζO - 1) • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) = 0) ∧
    ∃ B : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)),
      unrH1 (resRep (uRep O (M := M) r χ) Dw) I ≤ B ∧
      Module.length O (B ⧸ (unrH1 (resRep (uRep O (M := M) r χ) Dw) I).comap B.subtype) ≤
        Module.length O (LinearMap.ker (DistribSMul.toLinearMap O M (ζO - 1))) ∧
      ∀ φ, resH1 (uRep O (M := M) r χ) Dw
        (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) ∈ B
def StatColChiC : Prop :=
  ∀ (O : Type*) [CommRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A),
    (∀ m : M, e₁ • m = 0) → (∀ m : M, E • m = 0) → (∀ l g, ∃ a : A, k0 l g = a * E) →
    ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (l : ι),
      resH1 (uRep O (M := M) r χ) (D l)
        (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = 0
def StatColChiOne : Prop :=
  ∀ (O : Type*) [CommRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (ℓ : ℕ) (e' : ι → ℕ) (u : ι → G → O),
    (∀ g (m : M), uElt r χ g • m = m) → (∀ m : M, e₁ • m = 0) → (∀ m : M, E • m = δO • m) →
    (∀ m : M, algebraMap T' A δ • m = δO • m) →
    (∀ l, ∀ g ∈ D l, ∀ m : M, k0 l g • m = ((ℓ : O) ^ e' l * δO * u l g) • m) →
    ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (l : ι),
      δO • φ (nuGen r χ E e₁ δ D j Kc k0 l) = 0 ∧
      (∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) =
        (δO * δO * (ℓ : O) ^ e' l * u l g) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l)) ∧
      ∀ I : Subgroup (D l), (∀ g ∈ I, u l (g : G) = 0) →
        resH1 (uRep O (M := M) r χ) (D l)
          (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) ∈
          unrH1 (resRep (uRep O (M := M) r χ) (D l)) I
def StatUnrOutside : Prop :=
  ∀ (O : Type*) [CommRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (I : Subgroup G), (∀ g ∈ I, r g = 1 ∧ χ g = 1) →
    (∀ g ∈ I, ycoc r χ E g = 0) ∧
    ∀ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M,
      (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) :
        H1z (uRep O (M := M) r χ)) ∈ unrH1 (uRep O (M := M) r χ) I
def StatUnrS : Prop :=
  ∀ (O : Type*) [CommRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (I : Subgroup G),
    (∀ g ∈ I, ∃ a : A, a * ((r g - algebraMap T' A ((χ g : T'ˣ) : T')) * E) = 0 ∧
      ∀ m : M, a • m = 0 → m = 0) →
    ∀ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M,
      (∀ g ∈ I, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0) ∧
      (Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) :
        H1z (uRep O (M := M) r χ)) ∈ unrH1 (uRep O (M := M) r χ) I
end Formalism.RepresentationBoundsCohomology.BR


