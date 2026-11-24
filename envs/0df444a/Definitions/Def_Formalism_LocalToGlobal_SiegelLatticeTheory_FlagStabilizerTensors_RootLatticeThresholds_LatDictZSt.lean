-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:09.634558+00:00
-- url     : https://prove2.me/theorems/30acfa22-9ee9-4904-838d-4621c16a8d3a
-- title:
--   Lat Dict ZSt
-- statement:
--   Definitions and structural lemmas for Lat Dict ZSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZSt.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace Formalism.L2.SG.Pf.LatDictZ.Z0
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
def SemiGenus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    Formalism.HermitianLatticesTheory.IsCMUnram E → Formalism.UG.IsHerm (starRingEnd E) J → J.det ≠ 0 →
    ∀ L M : Submodule (𝓞 E) (Fin n → E), L.FG → M.FG →
      Submodule.span E (L : Set (Fin n → E)) = ⊤ → Submodule.span E (M : Set (Fin n → E)) = ⊤ →
      SelfDual J L → SelfDual J M →
      ∀ p : Ideal (𝓞 E), p.IsMaximal →
        ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧
          ∀ v, v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔
            ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v
def SemiGenusZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    Formalism.HermitianLatticesTheory.IsCMUnram E → Formalism.UG.IsHerm (starRingEnd E) J → J.det ≠ 0 →
    ∀ {r : ℕ} (s : Fin r → Fin n → E) (z : Fin n → E) (L M : Submodule (𝓞 E) (Fin n → E)),
      L.FG → M.FG →
      Submodule.span E (L : Set (Fin n → E)) = ⊤ → Submodule.span E (M : Set (Fin n → E)) = ⊤ →
      SelfDual J L → SelfDual J M →
      (∀ a, Formalism.UG.hform (starRingEnd E) J (s a) z = 0) →
      (∀ w ∈ Submodule.span E (Set.range s), w ∈ L ↔ w ∈ M) →
      (∀ w ∈ L, ∃ w₁ ∈ L, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      (∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      z ∈ L → z ∈ M →
      (∀ c : E, c • z ∈ L → c ∈ (algebraMap (𝓞 E) E).range) →
      (∀ c : E, c • z ∈ M → c ∈ (algebraMap (𝓞 E) E).range) →
      ∀ p : Ideal (𝓞 E), p.IsMaximal →
        ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧
          (∀ a, (γ : Matrix (Fin n) (Fin n) E) *ᵥ s a = s a) ∧ (γ : Matrix (Fin n) (Fin n) E) *ᵥ z = z ∧
          ∀ v, v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔
            ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v
def LocFinite : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)),
    L.FG → M.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → Submodule.span E (M : Set (Fin n → E)) = ⊤ →
    {p : Ideal (𝓞 E) | p.IsMaximal ∧ Formalism.HermitianLatticesTheory.loc (K := E) p M ≠ Formalism.HermitianLatticesTheory.loc (K := E) p L}.Finite
def AdelGlue : Prop :=
  ∀ (I : AutInst) {r : ℕ} (s : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (M : Submodule (𝓞 I.E) (Fin I.n → I.E)),
    M.FG → Submodule.span I.E (M : Set (Fin I.n → I.E)) = ⊤ →
    {p : Ideal (𝓞 I.E) | p.IsMaximal ∧ locE I p M ≠ locE I p I.L}.Finite →
    ∀ γ : Ideal (𝓞 I.E) → GL (Fin I.n) I.E,
      (∀ p, γ p ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) →
      (∀ p a, (γ p : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ s a = s a) →
      (∀ p, (γ p : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = z) →
      (∀ p : Ideal (𝓞 I.E), p.IsMaximal → ∀ v, v ∈ locE I p M ↔
        ∃ w ∈ locE I p I.L, (γ p : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = v) →
      ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ iv I (s a) = iv I (s a)) ∧ I.fmat x *ᵥ iv I z = iv I z ∧ abelian₂ I x = M
end Formalism.L2.SG.Pf.LatDictZ.Z0


