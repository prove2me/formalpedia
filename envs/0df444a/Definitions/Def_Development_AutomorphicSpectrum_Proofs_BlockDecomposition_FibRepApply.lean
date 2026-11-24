-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:24.652012+00:00
-- url     : https://prove2.me/theorems/2645475e-3e3c-4868-8da4-bd5f275250d0
-- title:
--   Fib Rep Apply
-- statement:
--   Definitions and structural lemmas for Fib Rep Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FibRepApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingTopEmb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof Matrix Topology
namespace GlobalTheory.CompanionTheory.ThetaGLLen
section Abstract
variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]
def twRel (ρ : Representation ℂ Γ V) (ψ : Γ →* ℂˣ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (γ : Γ) (v : V), w = ρ γ v - (ψ γ : ℂ) • v}
theorem twRel_stable (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ) (g : G) (v : V)
    (hv : v ∈ twRel (τ.comp (MonoidHom.inl Γ G)) ψ) :
    τ (1, g) v ∈ twRel (τ.comp (MonoidHom.inl Γ G)) ψ := by
  have h : twRel (τ.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).comap (τ (1, g)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, u, rfl⟩
    refine Submodule.subset_span ⟨γ, τ (1, g) u, ?_⟩
    have e : τ (1, g) (τ (γ, 1) u) = τ (γ, 1) (τ (1, g) u) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      simp
    simp [e]
  exact h hv
def coinv (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ) :
    Representation ℂ G (V ⧸ twRel (τ.comp (MonoidHom.inl Γ G)) ψ) :=
  Representation.quotient (τ.comp (MonoidHom.inr Γ G) : Representation ℂ G V) _
    (fun g v hv => twRel_stable τ ψ g v hv)
end Abstract
section Fibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
def fibChar (μ : kˣ →* ℂˣ) : GL a k × (GL c k × GL d k) →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k (((Fintype.card c : ℂ) + Fintype.card d) / 2))).comp (MonoidHom.fst _ _) *
    (detChar c (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k (-(Fintype.card d : ℂ) / 2))).comp
      ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
    (detChar d (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k ((Fintype.card c : ℂ) / 2))).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))
def fibBase (κ : ℕ) : Representation ℂ (GL a k × GL c k) (SB (RankIn k a c {κ})) :=
  sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)
def fibRep (μ : kˣ →* ℂˣ) (κ : ℕ) :
    Representation ℂ (GL a k × (GL c k × GL d k)) (SB (RankIn k a c {κ})) :=
  twist ((fibBase a c κ).comp ((MonoidHom.id _).prodMap (MonoidHom.fst _ _))) (fibChar a c d μ)
def rightRep (κ : ℕ) : Representation ℂ (GL a k) (SB (RankIn k a c {κ})) :=
  (fibBase a c κ).comp (MonoidHom.inl _ _)
end Fibre
end GlobalTheory.CompanionTheory.ThetaGLLen


