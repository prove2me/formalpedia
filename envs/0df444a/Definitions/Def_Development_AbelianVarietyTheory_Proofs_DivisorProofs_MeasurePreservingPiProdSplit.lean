-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:06.478058+00:00
-- url     : https://prove2.me/theorems/7bf2a3cb-ef84-4bd0-b2de-08199a835a6a
-- title:
--   Measure Preserving Pi Prod Split
-- statement:
--   Definitions and structural lemmas for Measure Preserving Pi Prod Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Theorems.Thm_GlobalTheory_FunObj_Kept_not_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
section Fubini
variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSpace (γ i)]
def piProdSplit (α β : ι → Type*) [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)] :
    (∀ i, α i × β i) ≃ᵐ (∀ i, α i) × (∀ i, β i) where
  toEquiv := Equiv.arrowProdEquivProdArrow ι α β
  measurable_toFun := (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst).prodMk
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd)
  measurable_invFun := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
end Fubini
section Step
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
variable (n c n') in

abbrev KeptVar : Type _ := {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Kept rs}
variable (n c n') in

abbrev FreeVar : Type _ := {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (c / 2 + 1) rs}
open Classical in
variable (n c n') in

def stepVarEquiv : KeptVar n c n' ⊕ FreeVar n c n' ≃ StepVar n c n' where
  toFun := Sum.elim (fun rs => ⟨rs.1, Or.inr rs.2⟩) fun rs => ⟨rs.1, Or.inl rs.2⟩
  invFun rs := if h : Kept rs.1 then .inl ⟨rs.1, h⟩ else .inr ⟨rs.1, rs.2.resolve_right h⟩
  left_inv := by
    rintro (rs | rs)
    · exact dif_pos rs.2
    · exact dif_neg fun h => Kept.not_free h rs.2
  right_inv rs := by by_cases h : Kept rs.1 <;> simp [h]
def joinVars (p : (KeptVar n c n' → k) × (FreeVar n c n' → k)) : StepVar n c n' → k :=
  fun rs => Sum.elim p.1 p.2 ((stepVarEquiv n c n').symm rs)
def keptPart (e : StepVar n c n' → k) : KeptVar n c n' → k := fun rs => e ⟨rs.1, Or.inr rs.2⟩
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [MeasurableSpace k] [BorelSpace k]
end Step
variable {k : Type*} [Field k] (G : Grid k)
abbrev KeptVars : Type _ :=
  ∀ j : Fin (G.m - 1), KeptVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) → k
variable {G}
def keptCol (w : KeptVars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) : k :=
  keptPt (w j) (.inl r) (.inr ⟨(G.m - 2 - j) / 2, by omega⟩)
def keptRow (x : ColArgs G) (w : KeptVars G) (j : ℕ) (s : Fin (topRank G j)) : k :=
  if h : j < G.m - 1 then ∑ l : Fin (G.m - 2 - j),
    if l.val = (G.m - 2 - j) / 2 then keptPt (w ⟨j, h⟩) (.inr l) (.inl s) else 0
  else x j (topLast G (j + 1)) s
def pairPhase (x : ColArgs G) (w : KeptVars G) : k :=
  ∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, keptRow x w (j + 1) r * keptCol w j r else 0
variable (hs : 1 ≤ G.s)
def stepDatum (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (j : Fin (G.m - 1))
    (z : Matrix (Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1)) k) : ℂ :=
  φ (.theta G.m j) (z.reindex (frame (by have := topRank_add hs (j + 1); have := j.2; show _ = G.rank (G.m, j + 1); omega))
    (frame (by have := topRank_add hs j; have := j.2; show _ = G.rank (G.m, j); omega)))ᵀ
def lastMap (hm : 0 < G.m) (x : ColArgs G) : Matrix (Fin (G.rank (G.m, G.m - 1 + 1))) (Fin (G.rank (G.m, G.m - 1))) k :=
  (x (G.m - 1)).submatrix (Fin.castLE (by have := topRank_add hs (G.m - 1 + 1); omega))
    (Fin.cast (by have := topRank_add hs (G.m - 1); omega))
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
open Classical in
variable (G) in

def keptVol : Measure (KeptVars G) := Measure.pi fun _ => Measure.pi fun _ => ν
def contractIntegrand (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G)
    (w : KeptVars G) : ℂ :=
  (∏ j : Fin (G.m - 1), flatStep ψ ν (stepDatum hs φ j) (x j) (w j)) * (ψ (-pairPhase x w) : ℂ)
variable {ψ}
end GlobalTheory.FunObj


