-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_StatBridgeChiOne
-- name    : Formalism_WachLatticeTwists_CoprimeLiftBounds_StatBridgeChiOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:36.703564+00:00
-- url     : https://prove2.me/theorems/fe724743-5326-477c-b58a-7fc6058dd6a8
-- title:
--   Stat Bridge Chi One
-- statement:
--   Definitions and structural lemmas for Stat Bridge Chi One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/CoprimeLiftBounds/StatBridgeChiOne.lean

import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
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
section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
def InRowRho (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (γ : T₂ →ₗ[O] M →ₗ[O] KO O)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    {Cs : Type*} [AddCommGroup Cs] [Module O Cs] (cls : (Dw → T₂) → Cs)
    (pr : Hc →ₗ[O] Cs →ₗ[O] KO O) (Fs Im : Submodule O Cs) : Prop :=
  ∃ (C₁ : (Dw → T₁) → Prop) (CN2 : (Dw → Dw → Ymod r χ E) → Prop)
    (CN : (Dw → Ymod r χ E) → Prop) (CA : (Dw → A) → Prop) (CP : (Dw → KO O) → Prop),
    (∀ a, C₁ a → CN2 (fun g h => inc (a g) • (uElt r χ (g : G) • yY r χ E (h : G)))) ∧
    (∀ a, C₁ a → CA (fun g => -(inc (a g) * (uElt r χ (g : G) * E)))) ∧
    (∀ (ψ : Ymod r χ E →ₗ[O] KO O) f, CN f → CP (fun g => ψ (f g))) ∧
    (∀ z ∈ characterColumnKernelPairSetVariant (twRep (ε.comp Dw.subtype) (Ymod r χ E)), CN2 z →
      (∃ f, CA f ∧ ∀ g h, ((z g h : Ymod r χ E) : A) =
        ((ε (g : G) : Oˣ) : O) • f h - f (g * h) + f g) →
      ∃ c, CN c ∧ ∀ g h, z g h = ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) ∧
    (∀ (a : Dw → T₁) (b : coZ1s (resRep (uRep O (M := M) r χ) Dw))
      (hb : Submodule.mkQ _ b ∈ Hc), a ∈ characterColumnKernelSet (resRep ρ₁ Dw) → C₁ a →
      (∃ c, CP c ∧ ∀ g h : Dw, γ (π (a g)) (uElt r χ (g : G) • (b : Dw → M) h) =
        ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) →
      pr ⟨Submodule.mkQ _ b, hb⟩ (cls (fun g => π (a g))) = 0) ∧
    (∀ x ∈ Im, ∃ a ∈ characterColumnKernelSet (resRep ρ₁ Dw), C₁ a ∧ x = cls (fun g => π (a g))) ∧
    Im ≤ Fs ∧ F = (annih pr Fs).map Hc.subtype
def OutRho (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (what₂ : Finset ℕ) (lenRow : ℕ → ℕ∞) (s : ℕ∞) : Prop :=
  let ρM := uRep O (M := M) r χ
  let Ψ := colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0
  ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
    (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
    (∀ w ∈ univ.image colIdx, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 ρM (D w))) ≤ s
def OutChi (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (what₂ qs : Finset ℕ) (rowB vζ : ℕ → ℕ∞) (s : ℕ∞) : Prop :=
  let ρM := uRep O (M := M) r χ
  let Ψ := colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0
  ∃ (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (Q : Submodule O (H1z ρM)),
    (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ rowB w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) ∧
    (∀ w ∈ univ.image colIdx, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) ∧
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) ∧
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ qs ∪ univ.image colIdx,
      (F w).comap (resH1 ρM (D w))) ≤ s
def InRho (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L] (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type*} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    {Cs : ℕ → Type*} [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l a, ∀ g ∈ D (colIdx l), Kc l a g • v₁ = ((ℓ : O) ^ e' (colIdx l)) • κ l a g) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  (∀ l (x : Fin (j (colIdx l)) → KO O), (fun g : D (colIdx l) => ∑ a, tens (κ l a g) (x a)) ∈
    LinearMap.range (colDO (O := O) (M := M) r χ (D (colIdx l))) → ∀ a, x a = 0) ∧
  (∀ φ, Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG) ∧
  (∀ w ∈ what₂, HcG ≤ (Hc w).comap (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  (∀ w ∈ what₂, InRowRho M r χ E (D w) ε ρ₁ inc π γ (Hc w) (F w) (cls w) (pr w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s
def InChi (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (ℓ cB : ℕ) (what₂ qs : Finset ℕ) (deg cT : ℕ → ℕ) (s : ℕ∞)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type*} (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ) : Prop :=
  (∀ w ∈ what₂, F w ≤ Hc w ∧ cT w ≤ cB ∧
    (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ D w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
      ∀ z : coZ1s (resRep (uRep O (M := M) r χ) (D w)),
        (∀ g : D w, (z : D w → M) g = ψ (yY r χ E (g : G))) →
        ((ℓ : O) ^ cT w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) (D w))) ∈ F w) ∧
    Module.length O (↥(Hc w ⊓ divBy (F w) ((ℓ : O) ^ cT w)) ⧸
        (F w).comap (Hc w ⊓ divBy (F w) ((ℓ : O) ^ cT w)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cT w : ℕ∞) * ((deg w : ℕ∞) + 1)) ∧
  (∀ w ∈ qs, F w = unrH1 (resRep (uRep O (M := M) r χ) (D w)) (I w) ∧ γ w ∈ I w ∧
    (r (γ w : G) - 1) * (r (γ w : G) - algebraMap T' A (ζ w)) = 0 ∧
    ((χ (γ w : G) : T'ˣ) : T') = ζ w ∧
    (∀ g ∈ I w, r (g : G) = r (γ w : G) ^ n w g ∧ χ (g : G) = χ (γ w : G) ^ n w g) ∧
    (∀ g ∈ I w, ∀ m : M, uElt r χ (g : G) • m = m) ∧
    (∀ m : M, r (γ w : G) • m = ζO w • m)) ∧
  (∀ φ, Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG) ∧
  (∀ w ∈ what₂, HcG ≤ (Hc w).comap (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ v, ∀ g ∈ IS v, ∃ a : A, a * ((r g - algebraMap T' A ((χ g : T'ˣ) : T')) * E) = 0 ∧
    ∀ m : M, a • m = 0 → m = 0) ∧
  Module.length O ↥((HcG ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
      ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
    ⨅ w ∈ what₂ ∪ qs ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s
end Defs
def StatBridgeRho : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [IsScalarTower O A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo : Type*) (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    (Cs : ℕ → Type*) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)),
    e₁ * e₁ = e₁ → (∀ m : M, E • m = 0) → (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : M, algebraMap T' A δ • m = δO • m) →
    InRho M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im →
    (∀ l (s : Fin (j (colIdx l)) → M),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O M e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) (M := M) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) ∧
    OutRho (O := O) M r χ E e₁ δ colIdx D j Kc k0 what₂
      (fun w => Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype)) s
def StatBridgeChiC : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [IsScalarTower O A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ cB : ℕ) (what₂ qs : Finset ℕ)
    (deg cT : ℕ → ℕ) (s : ℕ∞)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo VS : Type*) (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ),
    (∀ m : M, e₁ • m = 0) → (∀ m : M, E • m = 0) → (∀ l g, ∃ a : A, k0 l g = a * E) →
    InChi M r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg cT s HcG Hc F Io IS I γ ζ ζO n →
    OutChi (O := O) M r χ E e₁ δ colIdx D j Kc k0 what₂ qs
      (fun w => Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cB : ℕ∞) * ((deg w : ℕ∞) + 2))
      (fun w => Module.length O (LinearMap.ker (DistribSMul.toLinearMap O M (ζO w - 1)))) s
def StatBridgeChiOne : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [IsScalarTower O A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ cB : ℕ) (what₂ qs : Finset ℕ)
    (deg cT : ℕ → ℕ) (s : ℕ∞)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo VS : Type*) (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ)
    (u : ι → G → O),
    (∀ g (m : M), uElt r χ g • m = m) → (∀ m : M, e₁ • m = 0) → (∀ m : M, E • m = δO • m) →
    (∀ m : M, algebraMap T' A δ • m = δO • m) →
    (∀ l, ∀ g ∈ D (colIdx l), ∀ m : M,
      k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * u l g) • m) →
    (∀ l, ∀ g ∈ I (colIdx l), u l (g : G) = 0) → (∀ l, ∃ g ∈ D (colIdx l), u l g = 1) →
    (∀ l, unrH1 (resRep (uRep O (M := M) r χ) (D (colIdx l))) (I (colIdx l)) ≤ F (colIdx l)) →
    InChi M r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg cT s HcG Hc F Io IS I γ ζ ζO n →
    (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
      ∀ m : M, k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * c) • m) ∧
    OutChi (O := O) M r χ E e₁ δ colIdx D j Kc k0 what₂ qs
      (fun w => Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cB : ℕ∞) * ((deg w : ℕ∞) + 2))
      (fun w => Module.length O (LinearMap.ker (DistribSMul.toLinearMap O M (ζO w - 1)))) s
end Formalism.RepresentationBoundsCohomology.BR


