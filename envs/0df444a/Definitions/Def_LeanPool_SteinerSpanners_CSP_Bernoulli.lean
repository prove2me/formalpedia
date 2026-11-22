-- Prove2me | Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli
-- name    : LeanPool_SteinerSpanners_CSP_Bernoulli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:48:37.36355+00:00
-- url     : https://prove2.me/theorems/c0c1774b-afda-46fb-9899-d6c838ba6a04
-- title:
--   Bernoulli
-- statement:
--   Definitions and structural lemmas for Bernoulli, from Goran Zuzic; David P. Woodruff; Vahab Mirrokni; LeanPool contributors's pinned Polynomial lower bounds for high-dimensional Steiner spanners development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/SteinerSpanners/CSP/Bernoulli.lean

module
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
def sequentialTailWeight {ι β γ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β]
  (p : ι → ℝ) (Pool : Finset β)
  (M_wit : (m : ℕ) → (Fin m → β) → β → Finset γ)
  (Q : (m : ℕ) → (Fin m → β) → β → γ → Finset ι) : ℕ → (m : ℕ) → (Fin m → β) → Finset ι → (ι →
      Bool) → ℝ :=
  fun r => Nat.rec
    (motive := fun _ => (m : ℕ) → (Fin m → β) → Finset ι → (ι → Bool) → ℝ)
    (fun _ _ Acc ω => if ∀ i ∈ Acc, ω i = true then bernWeight p ω else 0)
    (fun _ ih m z_prev Acc ω =>
      ∑ b ∈ Pool \ Finset.univ.image z_prev,
        ∑ w ∈ M_wit m z_prev b,
          ih (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω)
    r
end Helpers
end HighDimSteinerSpanners.Proofs.CSP


