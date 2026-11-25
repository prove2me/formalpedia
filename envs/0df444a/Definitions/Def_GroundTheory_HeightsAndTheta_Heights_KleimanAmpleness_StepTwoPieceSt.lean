-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoPieceSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoPieceSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:38.903315+00:00
-- url     : https://prove2.me/theorems/1dd8148c-f870-45c7-b486-d27c59458698
-- title:
--   Step Two Piece St
-- statement:
--   Definitions and structural lemmas for Step Two Piece St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoPieceSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
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
def StepTwo.Piece.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (N₀ N₁ : FinGradedSub (S := S) (x := x) E) (g : E) (e : ℤ)
    (pp : Ideal (Poly S N)), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := S) x ≤ pp → g ∈ N₁.piece e →
    (∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g}) →
    (∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) →
    ∀ (Q : LineBundle S x) (c : ℤ),
      ((∃ j, (X j : Poly S N) ∉ pp) →
        Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c - e)))
          ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) 1)) →
      Subsingleton (SubSystem.quotH ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
        ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)
section Hypotheses
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable (S x E) in

def FinGradedSub.zero : FinGradedSub (S := S) (x := x) E where
  piece _ := ⊥
  smul_mem _ _ _ m _ hm := by
    rw [Submodule.mem_bot] at hm ⊢
    rw [hm, smul_zero]
  fg := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun _ => bot_le⟩
variable (k : Type u) [Field k]
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


