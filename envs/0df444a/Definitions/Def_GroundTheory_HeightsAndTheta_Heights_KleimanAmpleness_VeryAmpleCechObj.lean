-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:17:15.313248+00:00
-- url     : https://prove2.me/theorems/11a5c777-91f5-48b1-9142-d702150ee301
-- title:
--   Very Ample Cech Obj
-- statement:
--   Definitions and structural lemmas for Very Ample Cech Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleCechObj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
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
noncomputable section
universe u v w
section Aug
variable (S : Type u) [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {n : ℕ}
def Cech.AugExact {y : Fin (n + 1) → Ω} (G : Chart y → Submodule S E) (B : Submodule S E) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ b ∈ B, (∀ _ : Cech.Idx (support y) 0, b = 0) → b = 0) ∧
  (∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G 0,
      Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G (p + 1),
    Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) (p + 1) s = 0 →
      ∃ t ∈ Cech.Cdeg (fun _ : Chart y => E) G p,
        Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) p t = s
end Aug
section Z
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E] {r : ℕ}
def secsOnZChart (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (I : Chart x)
    (J : Chart h) : Submodule S E :=
  Submodule.span S {e | ∃ n : ℕ, xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I}
def secsOnZ (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (J : Chart h) : Submodule S E :=
  ⨅ I : Chart x, secsOnZChart G H h I J
end Z
end
end GroundTheory.Heights₂.Heights.Kleiman


