-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:37.68695+00:00
-- url     : https://prove2.me/theorems/6c9b629e-262d-4c6d-822e-7def91ff583a
-- title:
--   Par Ind Jac Placing
-- statement:
--   Definitions and structural lemmas for Par Ind Jac Placing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParIndJacPlacing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
namespace GlobalTheory.SmGL.Placing
section General
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
def indLeft [TopologicalSpace G] [IsTopologicalGroup G] {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (w * g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      have : w * (q * g) = p * (w * g) := by rw [hp]; group
      show f.1.1 (w * (q * g)) = τ q (f.1.1 (w * g))
      rw [this, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
        have hg' : ind P σ g f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (w * x)
        show f.1.1 (w * (x * g)) = f.1.1 (w * x)
        rw [← mul_assoc]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end General
section Blocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
def Moves {ι : Type} (e e' : ι ≃ n) (w : GL n R) : Prop :=
  ∀ (g : GL n R) x y, ((w * g * w⁻¹ : GL n R) : Matrix n n R) (e' x) (e' y) =
    (g : Matrix n n R) (e x) (e y)
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R}
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem Moves.parab (h : Moves e e' w) {g : GL n R} (hg : g ∈ parab R e) :
    w * g * w⁻¹ ∈ parab R e' :=
  mem_parab_iff.2 fun a b i j hab => (h g _ _).trans (mem_parab_iff.1 hg a b i j hab)
theorem Moves.unipRad (h : Moves e e' w) {g : GL n R} (hg : g ∈ unipRad R e) :
    w * g * w⁻¹ ∈ unipRad R e' :=
  mem_unipRad.2 ⟨h.parab (mem_unipRad.1 hg).1,
    fun a i j => (h g _ _).trans ((mem_unipRad.1 hg).2 a i j)⟩
theorem Moves.leviProj (h : Moves e e' w) (p : SmGL.parab R e) :
    leviProj R e' ⟨_, h.parab p.2⟩ = leviProj R e p := by
  funext a
  ext i j
  exact h p _ _
omit [LinearOrder α] in

theorem Moves.leviEmb (h : Moves e e' w) (g : Levi R m) :
    w * leviEmb R e g * w⁻¹ = leviEmb R e' g := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e'.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e'.surjective j
  rw [h]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same]
  · rw [leviEmb_apply_ne R e g hab, leviEmb_apply_ne R e' g hab]
end Blocks
open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
theorem conj_mem_parab_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {g : GL n R} (hg : g ∈ _root_.GlobalTheory.SmGL.parab R e) :
    w * g * w⁻¹ ∈ _root_.GlobalTheory.SmGL.parab R e' := by
  have hg' : Matrix.BlockTriangular (g : Matrix n n R) (_root_.GlobalTheory.SmGL.blk e) := hg
  change Matrix.BlockTriangular _ (_root_.GlobalTheory.SmGL.blk e')
  intro i j hij
  obtain ⟨x, rfl⟩ := e'.surjective i
  obtain ⟨y, rfl⟩ := e'.surjective j
  rw [hw]
  exact hg' (by simpa [_root_.GlobalTheory.SmGL.blk] using hij)
end GlobalTheory.SmGL.Placing


