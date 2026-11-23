-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
-- name    : Formalism_WachLatticeTwists_LatticeDualFibres_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:54.195372+00:00
-- url     : https://prove2.me/theorems/b0c4223d-a236-43f5-a5dd-b9910db1c2c5
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/Statement.lean

import Definitions.Def_Formalism_WachLatticeTwists_Statement
import Definitions.Def_Formalism_WachLatticeTwists_StatementDual
import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.LOC
def eO (O : Type u) [CommRing O] (ℓ : ℕ) : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
def toKO (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    FractionRing O →ₗ[O] KO O := Submodule.mkQ _
def mulSub {O : Type u} [CommRing O] (a : O) (M : Type u) [AddCommGroup M] [Module O M] :
    Submodule O M := LinearMap.range (LinearMap.lsmul O M a)
structure DirectPush (O A HV : Type u) [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup HV]
    [Module O HV] (q : HV →ₗ[O] A) where
  HY : Type u
  HVY : Type u
  HL : Type u
  HVL : Type u
  [gY : AddCommGroup HY] [mY : Module O HY]
  [gVY : AddCommGroup HVY] [mVY : Module O HVY]
  [gL : AddCommGroup HL] [mL : Module O HL]
  [gVL : AddCommGroup HVL] [mVL : Module O HVL]

  jY : HY →ₗ[O] HVY

  jL : HL →ₗ[O] HVL

  p1 : HL →ₗ[O] HY

  p2 : HVL →ₗ[O] HV

  φs : HY →ₗ[O] A
  comm : ∀ x : HL, φs (p1 x) = q (p2 (jL x))

  HfVY : Submodule O HVY

  HfVL : Submodule O HVL
attribute [instance] DirectPush.gY DirectPush.mY DirectPush.gVY DirectPush.mVY DirectPush.gL
  DirectPush.mL DirectPush.gVL DirectPush.mVL
namespace DirectPush
variable {O A HV : Type u} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup HV]
    [Module O HV] {q : HV →ₗ[O] A} (P : DirectPush O A HV q)
def HfY : Submodule O P.HY := P.HfVY.comap P.jY
def HfL : Submodule O P.HL := P.HfVL.comap P.jL
def Fun (HfV : Submodule O HV) : Prop := P.HfVL ≤ HfV.comap P.p2
def Lift (ℓ e' : ℕ) : Prop := ∀ y ∈ P.HfY, ((ℓ : O) ^ e') • y ∈ P.HfL.map P.p1
end DirectPush
structure DualPush (O A HT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HT'] [Module O HT']
    (pr : A →ₗ[O] HT' →ₗ[O] KO O) where
  HY : Type u
  HVY : Type u
  HVY' : Type u
  HLb : Type u
  HVLb : Type u
  [gY : AddCommGroup HY] [mY : Module O HY]
  [gVY : AddCommGroup HVY] [mVY : Module O HVY]
  [gVY' : AddCommGroup HVY'] [mVY' : Module O HVY']
  [gLb : AddCommGroup HLb] [mLb : Module O HLb]
  [gVLb : AddCommGroup HVLb] [mVLb : Module O HVLb]

  jY : HY →ₗ[O] HVY

  jLb : HLb →ₗ[O] HVLb

  p1 : HLb →ₗ[O] HT'

  p2 : HVLb →ₗ[O] HVY'

  φs : HY →ₗ[O] A

  prF : HVY →ₗ[O] HVY' →ₗ[O] FractionRing O
  cup : ∀ (y : HY) (x : HLb), pr (φs y) (p1 x) = toKO O (prF (jY y) (p2 (jLb x)))

  HfVY : Submodule O HVY

  HfVY' : Submodule O HVY'

  HfVLb : Submodule O HVLb
attribute [instance] DualPush.gY DualPush.mY DualPush.gVY DualPush.mVY DualPush.gVY' DualPush.mVY'
  DualPush.gLb DualPush.mLb DualPush.gVLb DualPush.mVLb
namespace DualPush
variable {O A HT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HT'] [Module O HT']
    {pr : A →ₗ[O] HT' →ₗ[O] KO O} (Q : DualPush O A HT' pr)
def HfY : Submodule O Q.HY := Q.HfVY.comap Q.jY
def HfLb : Submodule O Q.HLb := Q.HfVLb.comap Q.jLb
def Fun : Prop := Q.HfVLb ≤ Q.HfVY'.comap Q.p2
def Orth : Prop := ∀ x ∈ Q.HfVY, ∀ x' ∈ Q.HfVY', Q.prF x x' = 0
def Lift (HfT' : Submodule O HT') (ℓ e' : ℕ) : Prop :=
  ∀ κ ∈ HfT', ((ℓ : O) ^ e') • κ ∈ Q.HfLb.map Q.p1
end DualPush
def StatLocDirect : Prop :=
  ∀ (O A HV : Type u) [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup HV] [Module O HV]
    (q : HV →ₗ[O] A) (HfV : Submodule O HV) (P : DirectPush O A HV q) (ℓ e' : ℕ),
    P.Fun HfV → P.Lift ℓ e' →
    ∀ y ∈ P.HfY, ((ℓ : O) ^ e') • P.φs y ∈ HfV.map q
def StatLocDualOrth : Prop :=
  ∀ (O A HT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HT'] [Module O HT']
    (pr : A →ₗ[O] HT' →ₗ[O] KO O) (HfT' : Submodule O HT') (Q : DualPush O A HT' pr) (ℓ e' : ℕ),
    Q.Fun → Q.Orth → Q.Lift HfT' ℓ e' →
    ∀ y ∈ Q.HfY, ((ℓ : O) ^ e') • Q.φs y ∈ annih pr HfT'
def StatLocTorsDual : Prop :=
  ∀ (O A H : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    (pr : A →ₗ[O] H →ₗ[O] KO O) (M : Submodule O H) (S : Submodule O A) (a : O),
    (∀ s ∈ S, a • s ∈ annih pr M) →
    Module.length O (S ⧸ (annih pr M).comap S.subtype) ≤
      Module.length O (M ⧸ mulSub a M)
def StatLocTorsGen : Prop :=
  ∀ (O Q : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup Q] [Module O Q] [Module.Finite O Q] (d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] Q), Function.Surjective δ →
    ∃ g : (Fin d → O) →ₗ[O] Q, Function.Surjective g
def StatLocGen : Prop :=
  ∀ (O M : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] M), Submodule.torsion O M ≤ LinearMap.range δ →
    ∃ g : (Fin (Module.finrank O M + d) → O) →ₗ[O] M, Function.Surjective g
def StatLocQuotLen : Prop :=
  ∀ (O M : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] M), Submodule.torsion O M ≤ LinearMap.range δ →
    ∀ ℓ e : ℕ, Module.length O (M ⧸ mulSub ((ℓ : O) ^ e) M) ≤
      ((Module.finrank O M + d : ℕ) : ℕ∞) * ((e : ℕ∞) * eO O ℓ)
def pushSpan {O A HV HT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HV] [Module O HV] [AddCommGroup HT'] [Module O HT']
    {q : HV →ₗ[O] A} {pr : A →ₗ[O] HT' →ₗ[O] KO O} {ι₁ ι₂ : Type u}
    (P : ι₁ → DirectPush O A HV q) (Q : ι₂ → DualPush O A HT' pr) : Submodule O A :=
  (⨆ i, (P i).HfY.map (P i).φs) ⊔ (⨆ i, (Q i).HfY.map (Q i).φs)
def StatPropLoc : Prop :=
  ∀ (O A HV HT' HV' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HV] [Module O HV]
    [AddCommGroup HT'] [Module O HT'] [Module.Finite O HT']
    [AddCommGroup HV'] [Module O HV'] [Module.IsTorsionFree O HV']
    (q : HV →ₗ[O] A) (j' : HT' →ₗ[O] HV') (pr : A →ₗ[O] HT' →ₗ[O] KO O)
    (HfV : Submodule O HV) (HfV' : Submodule O HV') (ℓ e' d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] HT')
    (ι₁ ι₂ : Type u) (P : ι₁ → DirectPush O A HV q) (Q : ι₂ → DualPush O A HT' pr),
    HfV.map q = annih pr (HfV'.comap j') →
    LinearMap.range δ = Submodule.torsion O HT' →
    (∀ i, (P i).Fun HfV ∧ (P i).Lift ℓ e') →
    (∀ i, (Q i).Fun ∧ (Q i).Orth ∧ (Q i).Lift (HfV'.comap j') ℓ e') →
    (∀ i, ∀ y ∈ (P i).HfY, ((ℓ : O) ^ e') • (P i).φs y ∈ HfV.map q) ∧
    (∀ i, ∀ y ∈ (Q i).HfY, ((ℓ : O) ^ e') • (Q i).φs y ∈ HfV.map q) ∧
    Module.length O (pushSpan P Q ⧸ (HfV.map q).comap (pushSpan P Q).subtype) ≤
      ((Module.finrank O ↥(HfV'.comap j') + d : ℕ) : ℕ∞) * ((e' : ℕ∞) * eO O ℓ)
end Formalism.RepresentationBoundsCohomology.LOC


