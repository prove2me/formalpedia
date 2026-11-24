-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZ
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZ
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:03.110096+00:00
-- url     : https://prove2.me/theorems/0eac72de-a242-46d6-8aae-5f2fe94f14e1
-- title:
--   Lat Dict Z
-- statement:
--   Definitions and structural lemmas for Lat Dict Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZ.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_HermitianLattices_StatementLat
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
open scoped TensorProduct
namespace Formalism.L2.SG.Pf.LatDictZ
open Formalism.MainNotions.S PIW.AdelClassFin
abbrev locE (I : AutInst) (p : Ideal (𝓞 I.E)) (L : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Formalism.HermitianLatticesTheory.loc (K := I.E) p L
abbrev hE (I : AutInst) (x y : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J x y
def Prim (I : AutInst) (M : Submodule (𝓞 I.E) (Fin I.n → I.E)) (z : Fin I.n → I.E) : Prop :=
  ∀ c : I.E, c • z ∈ M → c ∈ (algebraMap (𝓞 I.E) I.E).range
def SplitU (I : AutInst) {r : ℕ} (s : Fin r → Fin I.n → I.E) (M : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  ∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ Submodule.span I.E (Set.range s) ∧ ∀ a, hE I (s a) (w - w₁) = 0
def LamGenus : Prop :=
  ∀ (I : AutInst) (x : I.Gf) (p : Ideal (𝓞 I.E)), p.IsMaximal →
    ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      ∀ v, v ∈ locE I p (abelian₂ I x) ↔ ∃ w ∈ locE I p I.L, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = v
def ZOrbit : Prop :=
  ∀ (I : AutInst) {r : ℕ} (s : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (M : Submodule (𝓞 I.E) (Fin I.n → I.E)),
    M.FG → Submodule.span I.E (M : Set (Fin I.n → I.E)) = ⊤ → SelfDual I.J M →
    (∀ a, hE I (s a) z = 0) →
    (∀ w ∈ Submodule.span I.E (Set.range s), w ∈ I.L ↔ w ∈ M) →
    SplitU I s I.L → SplitU I s M →
    z ∈ I.L → z ∈ M → Prim I I.L z → Prim I M z →
    ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ iv I (s a) = iv I (s a)) ∧ I.fmat x *ᵥ iv I z = iv I z ∧ abelian₂ I x = M
end Formalism.L2.SG.Pf.LatDictZ


