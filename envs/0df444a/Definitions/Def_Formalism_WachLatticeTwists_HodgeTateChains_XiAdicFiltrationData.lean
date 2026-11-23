-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_XiAdicFiltrationData
-- name    : Formalism_WachLatticeTwists_HodgeTateChains_XiAdicFiltrationData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:10.527839+00:00
-- url     : https://prove2.me/theorems/8c59a1e3-58c4-489b-9c32-9c0854280e22
-- title:
--   Xi Adic Filtration Data
-- statement:
--   Definitions and structural lemmas for Xi Adic Filtration Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/HodgeTateChains/XiAdicFiltrationData.lean

import Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_InvariantsCohomologyData
import Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
structure Twist (ℓ : ℕ) [Fact ℓ.Prime] (E : Md ℓ) where

  HH : Md ℓ

  Wm : Md ℓ

  WX : Md ℓ

  gX : WX →ₗ[ℤ_[ℓ]] WX
  infm : Wm →ₗ[ℤ_[ℓ]] E
  infX : WX →ₗ[ℤ_[ℓ]] E
  res : E →ₗ[ℤ_[ℓ]] HH
namespace Twist
variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Md ℓ} (T : Twist ℓ E)
def InfRes (c : ℤ_[ℓ]) : Prop :=
  (∀ y, T.res y = 0 ↔ ∃ w x, y = T.infm w + T.infX x) ∧
  ∀ w x, T.infm w + T.infX x = 0 ↔ (∃ w', w = c • w' - w') ∧ ∃ x', x = T.gX x' - x'
def T4 : Prop := ∀ y : T.HH, (ℓ : ℤ_[ℓ]) • y = 0
def T3 : Prop := ∀ x, ∃ y, (ℓ : ℤ_[ℓ]) • x = T.gX y - y
end Twist
def StatTwistKill : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ (j : ℤ), j ≠ 0 → ∀ (E : Md ℓ) (T : Twist ℓ E),
    T.InfRes ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) → T.T4 → T.T3 →
      ∀ y : E, ((ℓ : ℤ_[ℓ]) ^ (1 + s + padicValInt ℓ j)) • y = 0
structure XiAdicFiltrationData (ℓ : ℕ) [Fact ℓ.Prime] where

  H : ℕ → Md ℓ

  Gr : ℕ → Md ℓ
  tw : ∀ k, Twist ℓ (Gr k)
  f : ∀ k, Gr k →ₗ[ℤ_[ℓ]] H (k + 1)
  p : ∀ k, H (k + 1) →ₗ[ℤ_[ℓ]] H k
def XiAdicFiltrationData.Inputs {ℓ : ℕ} [Fact ℓ.Prime] (K : XiAdicFiltrationData ℓ) (u : ℤ_[ℓ]ˣ) (e : ℕ) : Prop :=
  (∀ x : K.H 0, x = 0) ∧ (∀ k < e, Function.Exact (K.f k) (K.p k)) ∧
  ∀ k < e, (K.tw k).InfRes ((u ^ ((k : ℤ) - e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) ∧ (K.tw k).T4 ∧ (K.tw k).T3
def StatKill3 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ (e : ℕ) (K : XiAdicFiltrationData ℓ), K.Inputs u e →
      ∀ x : K.H e, ((ℓ : ℤ_[ℓ]) ^ cPrime ℓ s e) • x = 0
def StatFree3 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ) (G HB : Md ℓ) (T : Twist ℓ G) (b : G →ₗ[ℤ_[ℓ]] HB)
    (La0 : Submodule ℤ_[ℓ] HB),
    T.InfRes 1 → T.T4 → T.T3 → (∀ x : HB, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →
    (∀ w, ((ℓ : ℤ_[ℓ]) ^ N) • b (T.infm w) ∈ La0) →
      ∀ x : G, ((ℓ : ℤ_[ℓ]) ^ (1 + N)) • b x ∈ La0
def StatTBFull : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) → s ≤ m →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (D : TBData ℓ) (L : LLData ℓ (e + 1)) (K : XiAdicFiltrationData ℓ) (T : Twist ℓ D.HGe)
      (_ : D.HYL ≃ₗ[ℤ_[ℓ]] L.HK) (_ : D.HWe ≃ₗ[ℤ_[ℓ]] K.H e), d ≠ 0 →
    (∀ k, (L.piece k).Inputs w U (0 + k)) → L.LES → L.T5 → L.CorRes (ℓ ^ (m - s)) →
    K.Inputs u e →
    T.InfRes 1 → T.T4 → T.T3 → (∀ x : D.HB, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →
    (∀ x, ((ℓ : ℤ_[ℓ]) ^ (s + ceilE ℓ e)) • D.bW (D.gE (T.infm x)) ∈ D.La0) →
    D.Comm → D.LES → D.DeRham → D.tateDualityKillsH2 s e → D.Recip (beta ℓ s e) → D.Cor d →
      ((ℓ : ℤ_[ℓ]) ^ cTB ℓ s m e (padicValNat ℓ d) U) • D.yK ∈ D.HfK
def StatTBLen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : Type) [Fintype n] (Q Cy : Type) [AddCommGroup Q] [Module O Q] [AddCommGroup Cy] [Module O Cy]
    (ι : (n → Formalism.NG.KO O) →ₗ[O] Q) (π : Q →ₗ[O] Cy),
    Function.Injective ι → Function.Exact ι π → (∃ c0 : Cy, ∀ y : Cy, ∃ a : O, y = a • c0) →
    ∀ (N : Submodule O Q) (ℓ c : ℕ), (∀ x ∈ N, ((ℓ : O) ^ c) • x = 0) →
    Module.length O N ≤
      ((Fintype.card n : ℕ∞) + 1) * ((c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}))
end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic


