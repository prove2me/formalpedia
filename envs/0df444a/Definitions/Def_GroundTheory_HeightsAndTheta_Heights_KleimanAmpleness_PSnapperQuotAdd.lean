-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:35:04.603828+00:00
-- url     : https://prove2.me/theorems/d2b222e9-d89a-5187-b097-ce6fea99b1b0
-- title:
--   PSnapper Quot Add
-- statement:
--   Definitions and structural lemmas for PSnapper Quot Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace SnapperQuotientAdditivity
section Top
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
theorem cdeg_top (i : ℕ) : Cech.Cdeg G (fun _ => (⊤ : Submodule R _)) i = ⊤ := by
  ext s; simp [Cech.Cdeg]
theorem cocyDeg_top (i : ℕ) : Cech.cocyDeg G (fun _ => ⊤) ρ i = LinearMap.ker (Cech.d G ρ i) := by
  rw [Cech.cocyDeg, cdeg_top, inf_top_eq]
theorem bdryDeg_top (i : ℕ) : Cech.bdryDeg G (fun _ => ⊤) ρ i = Cech.bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i => rw [Cech.bdryDeg, Cech.bdry, cdeg_top, Submodule.map_top]
def hdegTopEquiv (i : ℕ) : Cech.Hdeg G (fun _ => ⊤) ρ i ≃ₗ[R] Cech.H G ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i)) (by
    ext z
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [bdryDeg_top] at hy
      exact hy
    · intro hz
      refine ⟨⟨z.1, (cocyDeg_top G ρ i).symm ▸ z.2⟩, ?_, rfl⟩
      rw [bdryDeg_top]; exact hz)
end Top
section Quot
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
def quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
  (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I)
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    (fun _ hy => hy)
def quotPr (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id (by intro _ hy; exact h32 I hy)
end Quot
end SnapperQuotientAdditivity
end
end GroundTheory.Heights₂.Heights.Kleiman


