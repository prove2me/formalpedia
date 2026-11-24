-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:42.895801+00:00
-- url     : https://prove2.me/theorems/03defa51-e6f1-4d2d-a286-deff88a9a0c4
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace PI.ScRefExists.Sk
def GE (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.E) : Prop := ∃ t : 𝓞 I.E, x = (g : I.E) * (t : I.E)
def hG (I : Formalism.MainNotions.S.AutInst) (x y : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J x y
def SplitG (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
    Nat.card {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2
def IsTheta (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (θ : 𝓞 I.E) : Prop :=
  GE I g ((θ : I.E) * θ - θ) ∧ GE I g ((θ : I.E) * star (θ : I.E)) ∧
    GE I g (1 - (θ : I.E) - star (θ : I.E))
def ThetaEx : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ), 1 ≤ g → SplitG I g → ∃ θ : 𝓞 I.E, IsTheta I g θ
def IdemLift : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (θ : 𝓞 I.E), 1 ≤ g → SplitG I g → IsTheta I g θ →
    ∃ ε : I.E ⊗[I.F] Af I.F, ε ∈ IntAf I.F I.E ∧ ε * ε = ε ∧ ε * sigA I ε = 0 ∧
      ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) (θ : I.E))
def LocGlob : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (t : I.E), Formalism.UG.inclE (F := I.F) (Af I.F) t ∈ IntAf I.F I.E →
    ∃ s : 𝓞 I.E, (s : I.E) = t
def gL (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E) {y | ∃ x ∈ I.L, y = (g : I.E) • x}
def GlobW : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    1 ≤ g → SplitG I g → IsTheta I g θ → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M g → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ (z : Fin I.n → I.E) (b bd : Fin k → Fin I.n → I.E),
      z ∈ I.L ∧ (∀ i, b i ∈ I.L ∧ bd i ∈ I.L) ∧
      (∀ a, hG I (e a) z = 0 ∧ hG I (f a) z = 0) ∧
      (∀ a i, hG I (e a) (b i) = 0 ∧ hG I (f a) (b i) = 0 ∧
        hG I (e a) (bd i) = 0 ∧ hG I (f a) (bd i) = 0) ∧
      GE I g (hG I z z + 1) ∧
      (∀ i, GE I g ((θ : I.E) * hG I z (b i)) ∧ GE I g (star (θ : I.E) * hG I z (bd i))) ∧
      (∀ i j, GE I g ((θ : I.E) * (hG I (bd i) (b j) - if i = j then 1 else 0))) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E)
        (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
          Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ⊔ gL I g
def Glue : Prop := ThetaEx → IdemLift → LocGlob → GlobW → PI.ScRefExists.Target
end PI.ScRefExists.Sk


