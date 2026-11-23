-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
-- name    : Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:34.65601+00:00
-- url     : https://prove2.me/theorems/03df1fd1-835c-4c2c-be1e-2d9858d2e413
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/CharacterSplitJumps/Statement.lean

import Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_H2KilledByTateDuality
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_StatBridgeChiOne
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
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
namespace Formalism.RepresentationBoundsCohomology.JT
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
def TBIn {ℓ : ℕ} [Fact ℓ.Prime] (D : TBData ℓ) (s m e d : ℕ) (U : Finset ℤ) : Prop :=
  d ≠ 0 ∧ D.Comm ∧ D.LES ∧ D.DeRham ∧
  TorsKilled ℓ D.HYL (cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s))) ∧
  D.tateDualityKillsH2 s e ∧ D.Kill3 s e ∧ D.Free3 s e ∧ D.Recip (beta ℓ s e) ∧ D.Cor d
def TBFullIn {ℓ : ℕ} [Fact ℓ.Prime] (D : TBData ℓ) (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ) :
    Prop :=
  1 ≤ s ∧ (ℓ = 2 → 2 ≤ s) ∧ s ≤ m ∧ PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s ∧
  PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m ∧ d ≠ 0 ∧
  ∃ (L : LLData ℓ (e + 1)) (K : XiAdicFiltrationData ℓ) (T : Twist ℓ D.HGe)
    (_ : D.HYL ≃ₗ[ℤ_[ℓ]] L.HK) (_ : D.HWe ≃ₗ[ℤ_[ℓ]] K.H e),
    (∀ k, (L.piece k).Inputs w U (0 + k)) ∧ L.LES ∧ L.T5 ∧ L.CorRes (ℓ ^ (m - s)) ∧
    K.Inputs u e ∧ T.InfRes 1 ∧ T.T4 ∧ T.T3 ∧ (∀ x : D.HB, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) ∧
    (∀ x, ((ℓ : ℤ_[ℓ]) ^ (s + ceilE ℓ e)) • D.bW (D.gE (T.infm x)) ∈ D.La0) ∧
    D.Comm ∧ D.LES ∧ D.DeRham ∧ D.tateDualityKillsH2 s e ∧ D.Recip (beta ℓ s e) ∧ D.Cor d
structure TBBridge (ℓ : ℕ) [Fact ℓ.Prime] {X : Type} [AddCommGroup X] (F : AddSubgroup X) (x : X) where

  D : TBData ℓ

  b : D.HAK →+ X
  map_y : b D.yK = x
  map_f : ∀ a ∈ D.HfK, b a ∈ F
def StatTB1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] (X : Type) [AddCommGroup X] [Module O X]
    (F : Submodule O X) (x : X) (B : TBBridge ℓ F.toAddSubgroup x) (s m e d : ℕ) (U : Finset ℤ),
    TBIn B.D s m e d U → ((ℓ : O) ^ cTB ℓ s m e (padicValNat ℓ d) U) • x ∈ F
def StatTB1Full : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] (X : Type) [AddCommGroup X] [Module O X]
    (F : Submodule O X) (x : X) (B : TBBridge ℓ F.toAddSubgroup x) (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ)
    (U : Finset ℤ),
    TBFullIn B.D u w s m e d U → ((ℓ : O) ^ cTB ℓ s m e (padicValNat ℓ d) U) • x ∈ F
def QuotShape {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type}
    [AddCommGroup X] [Module O X] (Hc F : Submodule O X) (deg : ℕ) : Prop :=
  ∃ (Cy : Type) (_ : AddCommGroup Cy) (_ : Module O Cy)
    (ι : (Fin deg → KO O) →ₗ[O] (Hc ⧸ F.comap Hc.subtype))
    (π : (Hc ⧸ F.comap Hc.subtype) →ₗ[O] Cy),
    Function.Injective ι ∧ Function.Exact ι π ∧ ∃ c0 : Cy, ∀ y : Cy, ∃ a : O, y = a • c0
def StatTB2 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [AddCommGroup X]
    [Module O X] (Hc F : Submodule O X) (deg : ℕ), QuotShape Hc F deg →
    ∀ ℓ c : ℕ,
    Module.length O (↥(Hc ⊓ divBy F ((ℓ : O) ^ c)) ⧸ F.comap (Hc ⊓ divBy F ((ℓ : O) ^ c)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (c : ℕ∞) * ((deg : ℕ∞) + 1)
def cBAll (ℓ t : ℕ) (what₂ : Finset ℕ) (s m gK : ℕ → ℕ) (U : ℕ → Finset ℤ) : ℕ :=
  what₂.sup fun w => cB ℓ (s w) (m w) t (gK w) (U w)
def StatCB : Prop :=
  ∀ (ℓ t e : ℕ) (what₂ : Finset ℕ) (s m gK : ℕ → ℕ) (U : ℕ → Finset ℤ), e < t → ∀ w ∈ what₂,
    cTB ℓ (s w) (m w) e (gK w) (U w) ≤ cBAll ℓ t what₂ s m gK U
section Defs
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
def InChiRows (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (D : ℕ → Subgroup G) (ℓ cB : ℕ) (what₂ : Finset ℕ)
    (deg cT : ℕ → ℕ) (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w)))) : Prop :=
  ∀ w ∈ what₂, F w ≤ Hc w ∧ cT w ≤ cB ∧
    (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ D w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
      ∀ z : coZ1s (resRep (uRep O (M := M) r χ) (D w)),
        (∀ g : D w, (z : D w → M) g = ψ (yY r χ E (g : G))) →
        ((ℓ : O) ^ cT w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) (D w))) ∈ F w) ∧
    Module.length O (↥(Hc w ⊓ divBy (F w) ((ℓ : O) ^ cT w)) ⧸
        (F w).comap (Hc w ⊓ divBy (F w) ((ℓ : O) ^ cT w)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cT w : ℕ∞) * ((deg w : ℕ∞) + 1)
def InChiRest (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (what₂ qs : Finset ℕ) (s : ℕ∞)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ) : Prop :=
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
def RowIn (ℓ : ℕ) [Fact ℓ.Prime] (M : Type) [AddCommGroup M] [Module A M] [Module O M]
    [SMulCommClass A O M] (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ) (deg : ℕ) : Prop :=
  F ≤ Hc ∧
  (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    ∀ z : coZ1s (resRep (uRep O (M := M) r χ) Dw),
      (∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : G))) →
      ∃ B : TBBridge ℓ F.toAddSubgroup
          (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) Dw)),
        TBFullIn B.D u w s m e d U) ∧
  QuotShape Hc F deg
end Defs
def StatInChiSplit : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ cB : ℕ) (what₂ qs : Finset ℕ)
    (deg cT : ℕ → ℕ) (s : ℕ∞)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo VS : Type) (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ),
    InChi M r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg cT s HcG Hc F Io IS I γ ζ ζO n ↔
      InChiRows M r χ E D ℓ cB what₂ deg cT Hc F ∧
      InChiRest M r χ E e₁ δ colIdx D j Kc k0 what₂ qs s HcG Hc F Io IS I γ ζ ζO n
def StatRows : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (D : ℕ → Subgroup G) (what₂ : Finset ℕ) (deg : ℕ → ℕ)
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (t e : ℕ) (u wm : ℕ → ℤ_[ℓ]ˣ) (s m d : ℕ → ℕ) (U : ℕ → Finset ℤ), e < t →
    (∀ w ∈ what₂, RowIn ℓ M r χ E (D w) (Hc w) (F w) (u w) (wm w) (s w) (m w) e (d w) (U w) (deg w)) →
    InChiRows M r χ E D ℓ (cBAll ℓ t what₂ s m (fun w => padicValNat ℓ (d w)) U) what₂ deg
      (fun w => cTB ℓ (s w) (m w) e (padicValNat ℓ (d w)) (U w)) Hc F
def StatChiC : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [IsScalarTower O A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (what₂ qs : Finset ℕ)
    (deg : ℕ → ℕ) (sel : ℕ∞)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo VS : Type) (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ)
    (t e : ℕ) (u wm : ℕ → ℤ_[ℓ]ˣ) (s m d : ℕ → ℕ) (U : ℕ → Finset ℤ), e < t →
    (∀ x : M, e₁ • x = 0) → (∀ x : M, E • x = 0) → (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ w ∈ what₂, RowIn ℓ M r χ E (D w) (Hc w) (F w) (u w) (wm w) (s w) (m w) e (d w) (U w) (deg w)) →
    InChiRest M r χ E e₁ δ colIdx D j Kc k0 what₂ qs sel HcG Hc F Io IS I γ ζ ζO n →
    OutChi (O := O) M r χ E e₁ δ colIdx D j Kc k0 what₂ qs
      (fun w => Module.length O (O ⧸ Ideal.span {(ℓ : O)}) *
        (cBAll ℓ t what₂ s m (fun w => padicValNat ℓ (d w)) U : ℕ∞) * ((deg w : ℕ∞) + 2))
      (fun w => Module.length O (LinearMap.ker (DistribSMul.toLinearMap O M (ζO w - 1)))) sel
def StatChiOne : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    [IsScalarTower O A M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (what₂ qs : Finset ℕ)
    (deg : ℕ → ℕ) (sel : ℕ∞)
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo VS : Type) (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ)
    (uu : ι → G → O)
    (t : ℕ) (u wm : ℕ → ℤ_[ℓ]ˣ) (s m d : ℕ → ℕ) (U : ℕ → Finset ℤ), 0 < t →
    (∀ g (x : M), uElt r χ g • x = x) → (∀ x : M, e₁ • x = 0) → (∀ x : M, E • x = δO • x) →
    (∀ x : M, algebraMap T' A δ • x = δO • x) →
    (∀ l, ∀ g ∈ D (colIdx l), ∀ x : M,
      k0 l g • x = ((ℓ : O) ^ e' (colIdx l) * δO * uu l g) • x) →
    (∀ l, ∀ g ∈ I (colIdx l), uu l (g : G) = 0) → (∀ l, ∃ g ∈ D (colIdx l), uu l g = 1) →
    (∀ l, unrH1 (resRep (uRep O (M := M) r χ) (D (colIdx l))) (I (colIdx l)) ≤ F (colIdx l)) →
    (∀ w ∈ what₂, RowIn ℓ M r χ E (D w) (Hc w) (F w) (u w) (wm w) (s w) (m w) 0 (d w) (U w) (deg w)) →
    InChiRest M r χ E e₁ δ colIdx D j Kc k0 what₂ qs sel HcG Hc F Io IS I γ ζ ζO n →
    (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
      ∀ x : M, k0 l g • x = ((ℓ : O) ^ e' (colIdx l) * δO * c) • x) ∧
    OutChi (O := O) M r χ E e₁ δ colIdx D j Kc k0 what₂ qs
      (fun w => Module.length O (O ⧸ Ideal.span {(ℓ : O)}) *
        (cBAll ℓ t what₂ s m (fun w => padicValNat ℓ (d w)) U : ℕ∞) * ((deg w : ℕ∞) + 2))
      (fun w => Module.length O (LinearMap.ker (DistribSMul.toLinearMap O M (ζO w - 1)))) sel
def HZeroHypotheses {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (U : Finset ℤ) : Prop :=
  1 ≤ m ∧ (ℓ = 2 → 2 ≤ m) ∧ PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m ∧ 0 ∉ U ∧ U.Nonempty ∧
  D.piece.Inputs w U 0 ∧ D.Union ∧ D.Flat ∧ D.LES ∧ D.Inv
structure HZeroRowPlaceData (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (d : Type) (Mrow : Type) [AddCommGroup Mrow] [Module O Mrow] where

  D : InvariantsCohomologyData ℓ

  N : Submodule O (d → KO O)
  idn : D.M ≃+ N

  Cs : Type
  [gCs : AddCommGroup Cs]
  [mCs : Module O Cs]
  con : N →ₗ[O] Cs
  inc : Mrow →ₗ[O] Cs
attribute [instance] HZeroRowPlaceData.gCs HZeroRowPlaceData.mCs
def HZeroTorsionLengthOnePlace : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type) [Fintype d] (Mrow : Type) [AddCommGroup Mrow] [Module O Mrow]
    (B : HZeroRowPlaceData ℓ O d Mrow) (w : ℤ_[ℓ]ˣ) (m : ℕ) (U : Finset ℤ),
    HZeroHypotheses B.D w m U → Function.Injective B.inc →
    Submodule.torsion O B.Cs ≤ LinearMap.range B.con →
    ∃ H : Submodule O (d → KO O), (∀ x ∈ H, ((ℓ : O) ^ c0 ℓ m U) • x = 0) ∧
      Module.length O (Submodule.torsion O Mrow) ≤ Module.length O H
def jumpsDualTwist (J : Multiset ℤ) : Finset ℤ := (J.map fun u => -u - 1).toFinset
def JumpsOfDualTwist : Prop :=
  ∀ J : Multiset ℤ, (0 ∉ jumpsDualTwist J ↔ (-1 : ℤ) ∉ J) ∧ ((jumpsDualTwist J).Nonempty ↔ J ≠ 0)
def HZeroSplitAllPlaces : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type) [Fintype d] (cols : Finset ℕ) (conj nlam : ℕ → ℕ)
    (Mrow : ℕ → Type) [∀ w, AddCommGroup (Mrow w)] [∀ w, Module O (Mrow w)]
    (cloudR lowsR : ∀ w, Fin (nlam w) → Multiset ℤ) (τ : ∀ w, Fin (nlam w))
    (B : ∀ w, HZeroRowPlaceData ℓ O d (Mrow (conj w))) (wm : ℕ → ℤ_[ℓ]ˣ) (mm : ℕ → ℕ),
    (∀ w ∈ cols, (-1 : ℤ) ∉ cloudR w (τ w) + lowsR w (τ w) ∧ cloudR w (τ w) + lowsR w (τ w) ≠ 0 ∧
      1 ≤ mm w ∧ (ℓ = 2 → 2 ≤ mm w) ∧ PadicInt.valuation ((wm w : ℤ_[ℓ]) - 1) = mm w ∧
      (B w).D.piece.Inputs (wm w) (jumpsDualTwist (cloudR w (τ w) + lowsR w (τ w))) 0 ∧
      (B w).D.Union ∧ (B w).D.Flat ∧ (B w).D.LES ∧ (B w).D.Inv ∧
      Function.Injective (B w).inc ∧
      Submodule.torsion O (B w).Cs ≤ LinearMap.range (B w).con) →
    ∀ w ∈ cols, ∃ H : Submodule O (d → KO O),
      (∀ x ∈ H, ((ℓ : O) ^ c0 ℓ (mm w) (jumpsDualTwist (cloudR w (τ w) + lowsR w (τ w)))) • x = 0) ∧
      Module.length O (Submodule.torsion O (Mrow (conj w))) ≤ Module.length O H
def StatBKbConv : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A HV HT' HV' : Type) [AddCommGroup A] [Module O A]
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT']
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV'),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : A, (∀ t, pr x t = 0) → x = 0) →
    (HfV.restrictScalars O).map q = annih pr ((HfV'.restrictScalars O).comap j')
def StatBKbBoth : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A HV HT' HV' : Type) [AddCommGroup A] [Module O A]
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT']
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV'),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) → (∀ b, b ∈ HfV' ↔ ∀ a ∈ HfV, pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : A, (∀ t, pr x t = 0) → x = 0) →
    (HfV'.restrictScalars O).comap j' = annih pr.flip ((HfV.restrictScalars O).map q) ∧
    (HfV.restrictScalars O).map q = annih pr ((HfV'.restrictScalars O).comap j')
def StatRowBK : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (X : Type) [AddCommGroup X] [Module O X] (Hc : Submodule O X)
    (HV Cs HV' : Type)
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup Cs] [Module O Cs] [Module.Finite O Cs]
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] Hc) (j' : Cs →ₗ[O] HV') (pr : Hc →ₗ[O] Cs →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV')
    (F : Submodule O X) (Fs : Submodule O Cs),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : Hc, (∀ t, pr x t = 0) → x = 0) →
    F = ((HfV.restrictScalars O).map q).map Hc.subtype → Fs = (HfV'.restrictScalars O).comap j' →
    F = (annih pr Fs).map Hc.subtype
def StatPropLocBK : Prop :=
  ∀ (O A HV HT' HV' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A]
    [AddCommGroup HV] [Module (FractionRing O) HV] [Module O HV]
    [IsScalarTower O (FractionRing O) HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT']
    [AddCommGroup HV'] [Module (FractionRing O) HV'] [Module O HV']
    [IsScalarTower O (FractionRing O) HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (pair : HV →ₗ[FractionRing O] HV' →ₗ[FractionRing O] FractionRing O)
    (HfV : Submodule (FractionRing O) HV) (HfV' : Submodule (FractionRing O) HV') (ℓ e' d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] HT')
    (ι₁ ι₂ : Type) (P : ι₁ → LOC.DirectPush O A HV q) (Q : ι₂ → LOC.DualPush O A HT' pr),
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', pair a b = 0) →
    (∀ f : HV' →ₗ[FractionRing O] FractionRing O, ∃ a, ∀ b, pair a b = f b) →
    (∀ a t, pr (q a) t = Submodule.Quotient.mk (pair a (j' t))) →
    (∀ x : A, (∀ t, pr x t = 0) → x = 0) →
    LinearMap.range δ = Submodule.torsion O HT' →
    (∀ i, (P i).Fun (HfV.restrictScalars O) ∧ (P i).Lift ℓ e') →
    (∀ i, (Q i).Fun ∧ (Q i).Orth ∧ (Q i).Lift ((HfV'.restrictScalars O).comap j') ℓ e') →
    (∀ i, ∀ y ∈ (P i).HfY, ((ℓ : O) ^ e') • (P i).φs y ∈ (HfV.restrictScalars O).map q) ∧
    (∀ i, ∀ y ∈ (Q i).HfY, ((ℓ : O) ^ e') • (Q i).φs y ∈ (HfV.restrictScalars O).map q) ∧
    Module.length O (LOC.pushSpan P Q ⧸
        ((HfV.restrictScalars O).map q).comap (LOC.pushSpan P Q).subtype) ≤
      ((Module.finrank O ↥((HfV'.restrictScalars O).comap j') + d : ℕ) : ℕ∞) *
        ((e' : ℕ∞) * LOC.eO O ℓ)
end Formalism.RepresentationBoundsCohomology.JT


