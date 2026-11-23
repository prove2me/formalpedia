-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
-- name    : Formalism_CoboundaryTransfers_StatementBridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:39.782038+00:00
-- url     : https://prove2.me/theorems/c1de5a47-68c8-42c0-b7ca-e515c8c6501c
-- title:
--   Statement Bridge
-- statement:
--   Definitions and structural lemmas for Statement Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/StatementBridge.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_WachModuleLifts_StatementW
import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_FrobeniusContraction_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
open Formalism
section CL
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
def baseOfCL (B : CL.W.Base p A) : Base ℤ_[p] A where
  p := p
  hp := Fact.out
  φ := B.φA
  γ := B.γA
  X := B.π₀
  Q := B.q
  comm := B.comm
  φX := by
    obtain ⟨v, hv⟩ := B.hφ
    exact ⟨B.q ^ (p - 1) * v, by rw [hv]; ring⟩
variable {B : CL.W.Base p A} {η : ℕ}
def ofCL {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : CL.W.WachMod B η D) : WachMod (baseOfCL B) η D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.π₀_inj
  Q_bij := W.q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_QN := W.γ_qN
variable {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']
def homOfCL {W : CL.W.WachMod B η D} {W' : CL.W.WachMod B η D'} (F : CL.W.Hom W W') :
    Hom (ofCL W) (ofCL W') where
  f := F.f
  φ_comm := F.φ_comm
  γ_comm := F.γ_comm
  N_le := F.N_le
def sesOfCL {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    {W₀ : CL.W.WachMod B η D₀} {W₁ : CL.W.WachMod B η D₁} {W₂ : CL.W.WachMod B η D₂}
    (S : CL.W.SES W₀ W₁ W₂) : SES (ofCL W₀) (ofCL W₁) (ofCL W₂) where
  ι := homOfCL S.ι
  π := homOfCL S.π
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat
end CL
section CLback
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
def toCL (B : Base ℤ_[p] A) (hp : B.p = p) (hq : B.QLin) (hφ : B.PhiX (p - 1)) :
    CL.W.Base p A where
  φA := B.φ
  γA := B.γ
  π₀ := B.X
  q := B.Q
  hq := by rw [hq, hp]; simp
  hφ := hφ
  comm := B.comm
def WachMod.toCL {B : Base ℤ_[p] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] (W : WachMod B M D) (hp : B.p = p)
    (hq : B.QLin) (hφ : B.PhiX (p - 1)) : CL.W.WachMod (toCL B hp hq hφ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  π₀_inj := W.X_inj
  q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_qN := W.γ_QN
end CLback
section LIFT
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
def baseOfLIFT (B : LIFT.Base ℓ A) : Base ℤ_[ℓ] A where
  p := ℓ
  hp := Fact.out
  φ := B.φA
  γ := B.γA
  X := B.X
  Q := B.Q
  comm := B.comm
  φX := ⟨B.Q, B.φX⟩
variable {B : LIFT.Base ℓ A} {M : ℕ}
def ofLIFT {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : LIFT.WD B M D)
    (hγ : ∀ y : D, B.Q ^ M • y ∈ W.N → ∃ y' : D, B.Q ^ M • y' ∈ W.N ∧ W.γ y - y = B.X • y') :
    WachMod (baseOfLIFT B) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.X_inj
  Q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_QN := hγ
def toLIFT (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q)
    (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) : LIFT.Base ℓ A where
  φA := B.φ
  γA := B.γ
  X := B.X
  Q := B.Q
  u := u
  comm := B.comm
  φX := hφ
  γX := hγX
  γQ := by
    obtain ⟨v, hv, ⟨t, rfl⟩, hγ⟩ := hγQ
    exact ⟨t, hv, by rw [hγ, mul_comm]⟩
def WachMod.toLIFT {B : Base ℤ_[ℓ] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] (W : WachMod B M D) (u : ℤ_[ℓ]ˣ)
    (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.WD (toLIFT B u hφ hγX hγQ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.X_inj
  Q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
end LIFT
def baseOfArchimedeanComponents {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : WachCohomologyFacts.Base O A) :
    Base O A where
  p := B.ℓ
  hp := B.hℓ
  φ := B.φ
  γ := B.γ
  X := B.X
  Q := B.q
  comm := B.comm
  φX := ⟨B.u * (B.X + (B.ℓ : A)) ^ (B.ℓ - 1), by rw [B.hφX]; ring⟩
def CLAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : CL.W.Base p A) (η : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : CL.W.WachMod B η D),
    (∀ y, (ofCL W).QInv y ↔ W.QInv y) ∧ (∀ y z, (ofCL W).C1 y z ↔ W.C1 y z) ∧
    (∀ ω, (ofCL W).C2 ω ↔ W.C2 ω) ∧ (∀ y z, (ofCL W).d1 y z = W.d1 y z) ∧
    (∀ y z, (ofCL W).Cocycle y z ↔ W.Cocycle y z) ∧ (∀ ω, (ofCL W).IsCob2 ω ↔ W.IsCob2 ω) ∧
    (∀ c, (ofCL W).TorsKilled c ↔ CL.W.TorsKilled W c)
def CLTransfer : Prop :=
  DiagramChase₂ → CoboundaryTransfer → GammaOnto → CL.W.LiftW ∧ CL.W.ClaimW ∧ CL.W.GammaOnto
def LIFTGammaQN : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : LIFT.Base ℓ A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : LIFT.WD B M D),
    ∀ y : D, B.Q ^ M • y ∈ W.N → ∃ y' : D, B.Q ^ M • y' ∈ W.N ∧ W.γ y - y = B.X • y'
def LIFTTransfer : Prop := DiagramChase₂ → GradedStep → LIFT.UChase ∧ LIFT.GradedStep
def WachDatumIsWachModule : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : WachCohomologyFacts.Base O A) (E : WachCohomologyFacts.Amb B AA) (n : ℕ)
    [NeZero n] (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
    [Module O V] [IsScalarTower O AA V] [IsScalarTower O A V] (W : WachCohomologyFacts.WachDatum E n V) (M : ℕ),
    IsUnit (1 + B.X * B.c) →
    (∀ i, ∀ x ∈ W.N i, B.q ^ M • W.φ i x ∈ W.N (i + 1)) →
    ∃ W' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V),
      W'.N = Submodule.pi Set.univ W.N ∧ ⇑W'.φ = ⇑W.Φ ∧ ⇑W'.γ = ⇑W.Γ ∧
      W'.Z1 = W.Z1 ∧ W'.B1 = W.B1 ∧ W'.Zf = W.Zf
def WachMorphismIsHom : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : WachCohomologyFacts.Base O A) (E : WachCohomologyFacts.Amb B AA) (n : ℕ)
    [NeZero n]
    (V₁ : Type) [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
    [Module O V₁] [IsScalarTower O AA V₁] [IsScalarTower O A V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
    [Module O V₂] [IsScalarTower O AA V₂] [IsScalarTower O A V₂]
    (W₁ : WachCohomologyFacts.WachDatum E n V₁) (W₂ : WachCohomologyFacts.WachDatum E n V₂) (hm : WachCohomologyFacts.Hom W₁ W₂) (M : ℕ)
    (W₁' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V₁)) (W₂' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V₂)),
    W₁'.N = Submodule.pi Set.univ W₁.N → ⇑W₁'.φ = ⇑W₁.Φ → ⇑W₁'.γ = ⇑W₁.Γ →
    W₂'.N = Submodule.pi Set.univ W₂.N → ⇑W₂'.φ = ⇑W₂.Φ → ⇑W₂'.γ = ⇑W₂.Γ →
    ∃ F : Hom W₁' W₂', ⇑F.f2 = ⇑(hm.fD.prodMap hm.fD) ∧ F.col = hm.col ∧
      (∀ e, F.LiftF e ↔ hm.LIFT e) ∧ (∀ g, W₂'.FIN g ↔ W₂.FIN g)
end Formalism.CoboundaryTransfers


