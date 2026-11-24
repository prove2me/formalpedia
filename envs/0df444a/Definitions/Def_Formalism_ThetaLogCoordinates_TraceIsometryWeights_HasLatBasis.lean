-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:19.992798+00:00
-- url     : https://prove2.me/theorems/331e007a-ca6a-4db0-9613-dbc99888d122
-- title:
--   Has Lat Basis
-- statement:
--   Definitions and structural lemmas for Has Lat Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/HasLatBasis.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_graded_of
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity
section gen
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
def res (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) : GlW K U n where
  E := fun a b => (G.E a b).restrict (fun x hx => hU a b x hx)
  comm := fun a b c d x => by
    apply Subtype.ext
    have := G.comm a b c d (x : V)
    split_ifs at this ⊢ <;> simpa using this
  comp := fun μ => (G.comp μ).restrict (fun x hx => G.graded_of hU μ x hx)
  dec := fun x => by
    obtain ⟨S, hS⟩ := G.dec (x : V)
    exact ⟨S, fun μ hμ => Subtype.ext (by simpa using hS μ hμ)⟩
  sum_comp := fun x S hS => by
    apply Subtype.ext
    have := G.sum_comp (x : V) S (fun μ hμ => by simpa using congrArg Subtype.val (hS μ hμ))
    simpa using this
  idem := fun μ ν x => by
    apply Subtype.ext
    have := G.idem μ ν (x : V)
    split_ifs at this ⊢ <;> simpa using this
  diag := fun c μ x => by
    apply Subtype.ext
    simpa using G.diag c μ (x : V)
  shift := fun a b μ x => by
    apply Subtype.ext
    simpa using G.shift a b μ (x : V)
def IsoW (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : Submodule K V :=
  G.gS {v | G.IsHW la v ∧ v ∈ W}
def WtBound2 {V₁ V₂ : Type} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ) : Prop :=
  ∀ (μ ν : Fin n → ℤ) (x : V₁) (y : V₂), x ≠ 0 → y ≠ 0 → y ∈ W → G₁.IsWt μ x → G₂.IsWt ν y → ∀ c, |ν c - μ c| ≤ (l : ℤ)
end gen
section padic
variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ}
def DeltaLat (G : GlW ℚ_[p] V n) (s : Set V) : AddSubgroup V :=
  sInf {L | s ⊆ L ∧ ZpClosed p L ∧ DivStable G.E L}
def HasLatBasis (M : AddSubgroup V) (U : Submodule ℚ_[p] V) : Prop :=
  ∃ (k : ℕ) (b : Module.Basis (Fin k) ℚ_[p] U), (∀ i, ((b i : U) : V) ∈ M) ∧
    ∀ x : U, (x : V) ∈ M → ∀ i, ‖b.repr x i‖ ≤ 1
structure LatData (G : GlW ℚ_[p] V n) (W : Submodule ℚ_[p] V) (M : AddSubgroup V) (l : ℕ) : Prop where
  stable : G.Stable W
  fd : FiniteDimensional ℚ_[p] W
  finW : G.FinW W
  bound : ∀ (μ ν : Fin n → ℤ) (x y : V), x ≠ 0 → y ≠ 0 → x ∈ W → y ∈ W → G.IsWt μ x → G.IsWt ν y →
    ∀ c, |ν c - μ c| ≤ (l : ℤ)
  closed : ZpClosed p M
  div : DivStable G.E M
  graded : ∀ μ, ∀ x ∈ M, G.comp μ x ∈ M
  basis : ∀ U : Submodule ℚ_[p] V, U ≤ W → HasLatBasis p M U
end padic
end Formalism.InvariantFactorPaths.PW


