-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_IsoExpand
-- name    : Formalism_EllipticTorsion_IsoExpand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:20.625525+00:00
-- url     : https://prove2.me/theorems/ab257d16-928a-4763-8892-e417affcf8bd
-- title:
--   Iso Expand
-- statement:
--   Definitions and structural lemmas for Iso Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/IsoExpand.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace Formalism.ELL
def quadDiff {M T : Type u} [AddCommGroup M] [AddCommGroup T] (φ : M → T) (a b : M) : T :=
  φ (a + b) - φ a - φ b
def QuadHyp {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T) : Prop :=
  (∀ a a' b : M, quadDiff φ (a + a') b - quadDiff φ a b - quadDiff φ a' b ∈ N) ∧
  φ 0 ∈ N ∧
  (∀ (α : O) (t : M), φ (α • t) - nrm α • φ t ∈ N) ∧
  (∀ (α : O) (a b : M), quadDiff φ (α • a) b - quadDiff φ a (bar α • b) ∈ N)
def IsoExpand : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∑ i, φ (∑ e, y e i • t e))
        - ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
            + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
                quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) ∈ N
def IsoVanish : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∀ e e', ∑ i, bar (y e i) * y e' i = 0) → (∀ e, ∑ i, nrm (y e i) = 0) →
        (∑ i, φ (∑ e, y e i • t e)) ∈ N
end Formalism.ELL


