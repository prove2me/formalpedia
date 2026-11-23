-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_LocBasisPlace
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_LocBasisPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:02.625151+00:00
-- url     : https://prove2.me/theorems/d04a43ed-0bac-41be-875e-5da970061c77
-- title:
--   Loc Basis Place
-- statement:
--   Definitions and structural lemmas for Loc Basis Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/UnitTraceSumBounds/LocBasisPlace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.MainNotions.Ext
def LeafOne : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ t : PowerSeries ℚ, PowerSeries.constantCoeff t = 0 →
    (∀ n : ℕ, ∑ k ∈ range (n + 1), PowerSeries.coeff n (t ^ (p ^ (2 * k))) / (p : ℚ) ^ k = if n = 1 then 1 else 0) →
    (∑ k ∈ range (p ^ 3 + 1), PowerSeries.coeff (p ^ 3) (t ^ (p ^ (2 * k + 1))) / (p : ℚ) ^ (k + 1)) ≠ 0 ∧
    padicValRat p (∑ k ∈ range (p ^ 3 + 1), PowerSeries.coeff (p ^ 3) (t ^ (p ^ (2 * k + 1))) / (p : ℚ) ^ (k + 1))
      = -((p : ℤ) + 1)
end Formalism.MainNotions.Ext
open NumberField
namespace Formalism.MainNotions.Ext
def RayBoundIQ : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], Module.finrank ℚ K0 = 2 → IsEmpty (K0 →+* ℝ) →
    ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
      1 ≤ Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) ∧
      (Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) : ℝ) ≤
        4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)
def NormOnePow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ x, c (c x) = x) →
    ∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) → 𝔞 * 𝔟 = 1 →
      ∃ (h : ℕ) (z : E), 0 < h ∧ z * c z = 1 ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {z}
def LocBasisPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ρ : E →+* ℂ_[p]) (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)), L.FG → Submodule.span E (L : Set (Fin N → E)) = ⊤ →
    ∃ P : Matrix (Fin N) (Fin N) E, P.det ≠ 0 ∧
      (∀ a, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, s • x = ∑ a, c a • P.transpose a
def LocBasisSemi : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (p : ℕ), p.Prime →
    ∀ Y : Submodule (𝓞 K) V, Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 K, (s : K) • y = ∑ i, ((c i : 𝓞 K) : K) • b i
end Formalism.MainNotions.Ext


