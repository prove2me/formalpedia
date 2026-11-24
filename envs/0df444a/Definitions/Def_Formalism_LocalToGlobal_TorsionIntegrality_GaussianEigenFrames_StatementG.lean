-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementG
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_StatementG
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:03.968425+00:00
-- url     : https://prove2.me/theorems/3c0f9b51-691c-44df-807b-1df9336b5584
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussianEigenFrames/StatementG.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.GD
def TensorBlock : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (E : Type) [Field E] (H : Type) [Fintype H] [DecidableEq H]
    (emb : Bool × H → (E →+* K)) (Ja Jl Jr : Type) [Fintype Ja] [Fintype Jl] [Fintype Jr]
    (hA : Ja → Ja → E) (hl : Jl → Jl → E) (hr : Jr → Jr → E) (N0 N1 : ℕ)
    (Gc : Bool × H → Ja → K) (P : Bool × H → Jl → Fin N0 → K) (P' : Bool × H → Jr → Fin N1 → K)
    (th : K) (u : H → K), ‖th‖ ≤ 1 →
    (∀ τ ρ : Bool × H, ρ ≠ τ → ∀ α', ∑ α, Gc τ α * emb ρ (hA α α') = 0) →
    (∀ t, u t = ∑ α, ∑ α', Gc (false, t) α * emb (false, t) (hA α α') * Gc (true, t) α') →
    (∀ t, ‖u t‖ ≤ 1) →
    (∀ t a a', ∃ e : K, ‖e‖ ≤ 1 ∧
      ∑ l, ∑ l₂, P (false, t) l a * emb (false, t) (hl l l₂) * P (true, t) l₂ a' =
        (if a = a' then 1 else 0) + th * e) →
    (∀ t b b', ∃ e : K, ‖e‖ ≤ 1 ∧
      ∑ r, ∑ r₂, P' (false, t) r b * emb (false, t) (hr r r₂) * P' (true, t) r₂ b' =
        (if b = b' then 1 else 0) + th * e) →
    ∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : K, ‖e‖ ≤ 1 ∧
      ∑ j : Ja × Jl × Jr, ∑ k : Ja × Jl × Jr,
        (Gc (false, t) j.1 * P (false, t) j.2.1 ab.1 * P' (false, t) j.2.2 ab.2) *
          (∑ ρ, emb ρ (hA j.1 k.1 * hl j.2.1 k.2.1 * hr j.2.2 k.2.2)) *
          (Gc (true, t) k.1 * P (true, t) k.2.1 ab'.1 * P' (true, t) k.2.2 ab'.2) =
        (if ab = ab' then u t else 0) + th * e
end Formalism.L2.Th1.GD


