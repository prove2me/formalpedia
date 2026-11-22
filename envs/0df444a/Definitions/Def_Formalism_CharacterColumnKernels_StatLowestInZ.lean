-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatLowestInZ
-- name    : Formalism_CharacterColumnKernels_StatLowestInZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:50.646415+00:00
-- url     : https://prove2.me/theorems/5f878349-d925-442b-859b-f2aed65d27fb
-- title:
--   Stat Lowest In Z
-- statement:
--   Definitions and structural lemmas for Stat Lowest In Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatLowestInZ.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.NG
def blockSum {Ir ι : Type*} (tw : ℤ → Ir → Ir) (I : Finset ι) (rp : ι → Multiset Ir) (dd : ι → ℕ) :
    Multiset Ir :=
  ∑ i ∈ I, ∑ k ∈ range (dd i), (rp i).map (tw ((dd i : ℤ) - 1 - 2 * k))
def StatLowestInZ : Prop :=
  ∀ (Ir Irb : Type*) (rk : Ir → ℕ) (wt : Ir → ℤ) (tw : ℤ → Ir → Ir) (red : Ir → Multiset Irb)
    (rkb : Irb → ℕ),
    (∀ σ, 1 ≤ rk σ) → (∀ τ, 1 ≤ rkb τ) → (∀ σ, ((red σ).map rkb).sum = rk σ) →
    (∀ σ, tw 0 σ = σ) → (∀ a b σ, tw (a + b) σ = tw a (tw b σ)) →
    (∀ b σ, wt (tw b σ) = wt σ - b) → (∀ b σ, rk (tw b σ) = rk σ) →
    (∀ b σ, (red (tw b σ)).map rkb = (red σ).map rkb) →
    ∀ (ι : Type*) (I : Finset ι) (rp : ι → Multiset Ir) (dd : ι → ℕ) (w₀ : ℤ) (t : ℕ),
      2 ≤ t → (∀ i ∈ I, 1 ≤ dd i) → (∀ i ∈ I, ∀ σ ∈ rp i, wt σ = w₀) →
      Multiset.card (((blockSum tw I rp dd).bind red).filter (fun τ => 1 < rkb τ)) = 1 →
      Multiset.card (((blockSum tw I rp dd).bind red).filter (fun τ => rkb τ = 1)) = t →
    ∀ χ₁ : Ir, rk χ₁ = 1 → wt χ₁ = w₀ - ((t : ℤ) - 1) → χ₁ ∈ blockSum tw I rp dd →
      ∃ i ∈ I, dd i = t ∧ rp i = {tw (-((t : ℤ) - 1)) χ₁}
end Formalism.NG


