-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_InvariantsCohomologyData
-- name    : Formalism_WachLatticeTwists_HodgeTateChains_InvariantsCohomologyData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:01.194617+00:00
-- url     : https://prove2.me/theorems/60e28c53-6594-4dab-a7e1-c2a0b0be48d7
-- title:
--   Invariants Cohomology Data
-- statement:
--   Definitions and structural lemmas for Invariants Cohomology Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/HodgeTateChains/InvariantsCohomologyData.lean

import Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_Statement
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
open Polynomial
abbrev Md (ℓ : ℕ) [Fact ℓ.Prime] := ModuleCat.{0} ℤ_[ℓ]
structure Piece (ℓ : ℕ) [Fact ℓ.Prime] (A : Md ℓ) where

  E : Md ℓ

  HH : Md ℓ

  Wm : Md ℓ

  WX : Md ℓ

  gm : Wm →ₗ[ℤ_[ℓ]] Wm

  gX : WX →ₗ[ℤ_[ℓ]] WX

  lam : A →ₗ[ℤ_[ℓ]] E

  io : E →ₗ[ℤ_[ℓ]] A

  infm : Wm →ₗ[ℤ_[ℓ]] E

  infX : WX →ₗ[ℤ_[ℓ]] E

  res : E →ₗ[ℤ_[ℓ]] HH
namespace Piece
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Md ℓ} (P : Piece ℓ A)
def Sandwich : Prop := ∀ x, P.io (P.lam x) = (ℓ : ℤ_[ℓ]) • x
def InfRes : Prop :=
  (∀ y, P.res y = 0 ↔ ∃ w x, y = P.infm w + P.infX x) ∧
  ∀ w x, P.infm w + P.infX x = 0 ↔ (∃ w', w = P.gm w' - w') ∧ ∃ x', x = P.gX x' - x'
def T4 : Prop := ∀ y : P.HH, (ℓ : ℤ_[ℓ]) • y = 0
def T3 : Prop := (∀ x, P.gX x = x → x = 0) ∧ ∀ x, ∃ y, (ℓ : ℤ_[ℓ]) • x = P.gX y - y
def HodgeTate (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Prop :=
  (∀ x : P.Wm, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) ∧ aeval P.gm (HTpoly ℓ w U i) = 0
def Inputs (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Prop :=
  P.Sandwich ∧ P.InfRes ∧ P.T4 ∧ P.T3 ∧ P.HodgeTate w U i
end Piece
def StatPiece : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ) (A : Md ℓ) (P : Piece ℓ A), P.Inputs w U i →
      TorsKilled ℓ A (2 + max 1 (rI ℓ m U i))
structure LLData (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where

  HK : Md ℓ

  Hm : ℕ → Md ℓ

  Gr : ℕ → Md ℓ

  piece : ∀ k, Piece ℓ (Gr k)

  f : ∀ k, Gr k →ₗ[ℤ_[ℓ]] Hm (k + 1)

  p : ∀ k, Hm (k + 1) →ₗ[ℤ_[ℓ]] Hm k

  res : HK →ₗ[ℤ_[ℓ]] Hm n

  cor : Hm n →ₗ[ℤ_[ℓ]] HK
namespace LLData
variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (D : LLData ℓ n)
def LES : Prop := (∀ x : D.Hm 0, x = 0) ∧ ∀ k, Function.Exact (D.f k) (D.p k)
def T5 : Prop := ∀ k, ∀ x : D.Gr k, D.f k x = 0 → ∃ j : ℕ, ((ℓ : ℤ_[ℓ]) ^ j) • x = 0
def CorRes (d : ℕ) : Prop := ∀ x, D.cor (D.res x) = d • x
end LLData
def StatLL : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (a : ℤ) (n d : ℕ) (D : LLData ℓ n), d ≠ 0 →
    (∀ k, (D.piece k).Inputs w U (a + k)) → D.LES → D.T5 → D.CorRes d →
      TorsKilled ℓ D.HK (cLL ℓ m U a (a + n) d)
structure InvariantsCohomologyData (ℓ : ℕ) [Fact ℓ.Prime] where

  M : Md ℓ

  A : Md ℓ

  piece : Piece ℓ A

  H0WeightInvariants : Md ℓ

  jm : H0WeightInvariants →ₗ[ℤ_[ℓ]] piece.Wm

  jX : H0WeightInvariants →ₗ[ℤ_[ℓ]] piece.WX

  invariantsModPower : ℕ → Md ℓ

  red : ∀ r, H0WeightInvariants →ₗ[ℤ_[ℓ]] invariantsModPower r

  dl : ∀ r, invariantsModPower r →ₗ[ℤ_[ℓ]] A

  emb : ∀ r, Submodule.torsionBy ℤ_[ℓ] M ((ℓ : ℤ_[ℓ]) ^ r) →ₗ[ℤ_[ℓ]] invariantsModPower r
namespace InvariantsCohomologyData
variable {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ)
def Union : Prop := ∀ x : D.M, ∃ r : ℕ, ((ℓ : ℤ_[ℓ]) ^ r) • x = 0
def Flat : Prop := ∀ r, Function.Injective (D.emb r)
def LES : Prop := ∀ r, Function.Exact (D.red r) (D.dl r)
def Inv : Prop :=
  (∀ x, D.jm x = 0 → D.jX x = 0 → x = 0) ∧
  ∀ x, D.piece.gm (D.jm x) = D.jm x ∧ D.piece.gX (D.jX x) = D.jX x
end InvariantsCohomologyData
def InvariantsKilledByPower : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ), 0 ∉ U → U.Nonempty → ∀ D : InvariantsCohomologyData ℓ,
    D.piece.Inputs w U 0 → D.Union → D.Flat → D.LES → D.Inv →
      ∀ x : D.M, ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x = 0
structure TBData (ℓ : ℕ) [Fact ℓ.Prime] where

  HY : Md ℓ

  HYL : Md ℓ

  Hr : Md ℓ

  HrL : Md ℓ

  Zr : Md ℓ

  ZrL : Md ℓ

  HW : Md ℓ

  HWL : Md ℓ

  secondCohomologyTwist : Md ℓ

  HV : Md ℓ

  HB : Md ℓ

  HA : Md ℓ

  HGe : Md ℓ

  HWe : Md ℓ

  HAK : Md ℓ
  iY : HY →ₗ[ℤ_[ℓ]] HYL
  f1 : HY →ₗ[ℤ_[ℓ]] Hr
  fL : HYL →ₗ[ℤ_[ℓ]] HrL
  ir : Hr →ₗ[ℤ_[ℓ]] HrL
  q : Zr →ₗ[ℤ_[ℓ]] Hr
  bd : Hr →ₗ[ℤ_[ℓ]] secondCohomologyTwist
  iZ : Zr →ₗ[ℤ_[ℓ]] ZrL
  qL : ZrL →ₗ[ℤ_[ℓ]] HrL
  kL : HWL →ₗ[ℤ_[ℓ]] ZrL
  jZ : Zr →ₗ[ℤ_[ℓ]] HV

  ex : HV →ₗ[ℤ_[ℓ]] HB
  bZ : ZrL →ₗ[ℤ_[ℓ]] HB
  bW : HWL →ₗ[ℤ_[ℓ]] HB
  jW : HW →ₗ[ℤ_[ℓ]] HV
  pr : HV →ₗ[ℤ_[ℓ]] HA
  aR : Hr →ₗ[ℤ_[ℓ]] HA
  gE : HGe →ₗ[ℤ_[ℓ]] HWL
  pE : HWL →ₗ[ℤ_[ℓ]] HWe

  La0 : Submodule ℤ_[ℓ] HB
  res : HAK →ₗ[ℤ_[ℓ]] HA
  cor : HA →ₗ[ℤ_[ℓ]] HAK

  HfK : Submodule ℤ_[ℓ] HAK

  y : HY

  yK : HAK
namespace TBData
variable {ℓ : ℕ} [Fact ℓ.Prime] (D : TBData ℓ)
def Comm : Prop :=
  (∀ x, D.ir (D.f1 x) = D.fL (D.iY x)) ∧ (∀ z, D.qL (D.iZ z) = D.ir (D.q z)) ∧
  (∀ z, D.bZ (D.iZ z) = D.ex (D.jZ z)) ∧ (∀ x, D.bZ (D.kL x) = D.bW x) ∧
  (∀ x, D.pr (D.jW x) = 0) ∧ (∀ z, D.aR (D.q z) = D.pr (D.jZ z)) ∧
  D.res D.yK = D.aR (D.f1 D.y)
def LES : Prop :=
  Function.Exact D.q D.bd ∧ Function.Exact D.kL D.qL ∧ Function.Exact D.gE D.pE
def DeRham : Prop := ∃ k : ℕ, ((ℓ : ℤ_[ℓ]) ^ k) • D.iY D.y = 0
def tateDualityKillsH2 (s e : ℕ) : Prop := ∀ x : D.secondCohomologyTwist, ((ℓ : ℤ_[ℓ]) ^ (s + padicValNat ℓ (e + 1))) • x = 0
def Kill3 (s e : ℕ) : Prop := ∀ x : D.HWe, ((ℓ : ℤ_[ℓ]) ^ cPrime ℓ s e) • x = 0
def Free3 (s e : ℕ) : Prop :=
  ∀ x : D.HGe, ((ℓ : ℤ_[ℓ]) ^ (1 + s + ceilE ℓ e)) • D.bW (D.gE x) ∈ D.La0
def Recip (β : ℤ) : Prop :=
  ∀ (x : D.HB) (k n : ℕ), ((ℓ : ℤ_[ℓ]) ^ k) • x ∈ D.La0 → (n : ℤ) = k + β →
    ∃ z : D.HW, ((ℓ : ℤ_[ℓ]) ^ n) • x = D.ex (D.jW z)
def Cor (d : ℕ) : Prop :=
  (∀ x, D.cor (D.res x) = d • x) ∧ ∀ z : D.HV, D.ex z = 0 → D.cor (D.pr z) ∈ D.HfK
end TBData
def StatTB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (s m e d : ℕ) (U : Finset ℤ) (D : TBData ℓ), d ≠ 0 →
    D.Comm → D.LES → D.DeRham →
    TorsKilled ℓ D.HYL (cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s))) →
    D.tateDualityKillsH2 s e → D.Kill3 s e → D.Free3 s e → D.Recip (beta ℓ s e) → D.Cor d →
      ((ℓ : ℤ_[ℓ]) ^ cTB ℓ s m e (padicValNat ℓ d) U) • D.yK ∈ D.HfK
end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic


