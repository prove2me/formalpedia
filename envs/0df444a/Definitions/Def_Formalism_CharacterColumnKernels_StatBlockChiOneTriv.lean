-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
-- name    : Formalism_CharacterColumnKernels_StatBlockChiOneTriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:26.994907+00:00
-- url     : https://prove2.me/theorems/1d958649-4bdd-4df2-8a00-32429c9174f3
-- title:
--   Stat Block Chi One Triv
-- statement:
--   Definitions and structural lemmas for Stat Block Chi One Triv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatBlockChiOneTriv.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
def StatBlockChiOneTriv : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type*) [Group G]
    (H : Type*) [AddCommGroup H] [Module O H]
    (Ψ : H →ₗ[O] coZ1s (Representation.trivial O G (Unit → KO O))) (δ : O),
    ∀ (ι : Type*) [DecidableEq ι] (lrows qs cols : Finset ι) (D : ι → Subgroup G)
      (F : ∀ w, Submodule O (H1z (resRep (Representation.trivial O G (Unit → KO O)) (D w))))
      (Q : Submodule O (H1z (Representation.trivial O G (Unit → KO O)))) (vhE : ℕ∞) (ℓ cB : ℕ)
      (deg : ι → ℕ) (vζ : ι → ℕ∞) (e' : ι → ℕ),
    let ρM := Representation.trivial O G (Unit → KO O)
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δ
    (∀ w ∈ lrows, ∃ A : Submodule O (H1z (resRep ρM (D w))), F w ≤ A ∧
      Module.length O (A ⧸ (F w).comap A.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A) →
    (∀ w ∈ qs, ∃ A : Submodule O (H1z (resRep ρM (D w))), F w ≤ A ∧
      Module.length O (A ⧸ (F w).comap A.subtype) ≤ vζ w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A) →
    (∀ w ∈ cols, ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ vhE →
    Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) + (cols.card : ℕ∞) * vδ →
    Module.length O H ≤
      vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
        eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        ∑ w ∈ qs, vζ w
end Formalism.NG


