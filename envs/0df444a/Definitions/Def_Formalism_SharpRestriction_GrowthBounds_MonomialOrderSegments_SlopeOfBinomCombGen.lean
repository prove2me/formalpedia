-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:09.832527+00:00
-- url     : https://prove2.me/theorems/9fb106b9-086c-4422-9024-47d1fb5a954a
-- title:
--   Slope Of Binom Comb Gen
-- statement:
--   Definitions and structural lemmas for Slope Of Binom Comb Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
def Slope (TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop) (c : ℕ) (f : (σ →₀ ℕ) → K) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (lam : ι → K) (n : ι → ℕ) (b : ι → (σ →₀ ℕ) → K),
    (∀ k, ((n k : ℕ) : WithTop ℚ) ≤ v (lam k ^ 6)) ∧ (∀ k, TotallyRealRoots (n k) (b k)) ∧
    (∀ k α, 0 ≤ v (b k α)) ∧ ∀ α, (c : WithTop ℚ) ≤ v (f α - ∑ k, lam k * b k α)
structure CostOK (TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop) : Prop where
  one : TotallyRealRoots 0 (fun _ => 1)
  mul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α)
  add : ∀ n f g, TotallyRealRoots n f → TotallyRealRoots n g → TotallyRealRoots n (fun α => f α + g α)
  smul : ∀ n (a : K) f, TotallyRealRoots n f → TotallyRealRoots n (fun α => a * f α)
  mono : ∀ m n f, m ≤ n → TotallyRealRoots m f → TotallyRealRoots n f
variable {v}
namespace Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
end Slope
namespace CostOK
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
end CostOK
section Binom
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
end Binom
section DiagCost
open MvPolynomial
def CostV {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (fam : Set (Finset L)) (n : ℕ)
    (f : (L × Fin r →₀ ℕ) → K) : Prop :=
  ∀ S ∈ fam, ∀ (θ : ℝ) (F : MvPolynomial (L × Fin r) K), vala sg S θ F → vala sg S (θ - n) (dg f F)
end DiagCost
end Formalism.MainNotions.PlaneGram


