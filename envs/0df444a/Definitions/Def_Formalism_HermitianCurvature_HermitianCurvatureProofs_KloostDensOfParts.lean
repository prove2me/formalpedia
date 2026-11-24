-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:14:30.61552+00:00
-- url     : https://prove2.me/theorems/5d023ea1-16ab-4292-9f71-c3cca8b55b19
-- title:
--   Kloost Dens Of Parts
-- statement:
--   Definitions and structural lemmas for Kloost Dens Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KloostDensOfParts.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBJ
open MeasureTheory Formalism.FourierDecayAlt
def KCls {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Ψ : G.Mat n → V) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0
def FubTop : Prop :=
  ∀ (β : ℂ) (p s : ℕ) (σ : Equiv.Perm (Fin (p + s))) (d : Fin (p + s) → ℂ) (σh : Equiv.Perm (Fin p))
    (dh : Fin p → ℂ) (σb : Equiv.Perm (Fin s)) (db : Fin s → ℂ) (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (Ψ : G.Mat (p + s) → V),
    (∀ i, dh i ≠ 0) → (∀ i, db i ≠ 0) → U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat σb db) → KCls Ψ →
    U.PhiTop (p := p + s) (s := 0) β σ d Ψ (fun x => x.elim0) =
      U.PhiTop (p := s) (s := 0) β σb db (U.PhiTop (p := p) (s := s) β σh dh Ψ) (fun x => x.elim0)
def FreezeLast : Prop :=
  ∀ (β : ℂ) (p : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Ψ : G.Mat (p + 1) → V), KCls Ψ → ∀ c : ℂ, c ≠ 0 →
    ∃ Ψc : G.Mat p → V, KCls Ψc ∧ ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
      U.PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) = U.PhiTop (p := p) (s := 0) β σ d Ψc (fun x => x.elim0)
def OmLongTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (z : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      z ≠ 0 → U.hMat σ d = G.ptLong (n + 1) z →
      G.OmLong β n Φ z = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)
def OmBlockTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (t c : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      t ≠ 0 → c ≠ 0 → U.hMat σ d = G.ptBlock n t c →
      G.OmBlock β n Φ t c = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)
def KloostDensOfParts : Prop := FubTop → FreezeLast → OmLongTop → OmBlockTop → KB.KloostDens
end Formalism.FourierDecayAlt.P.PBJ


