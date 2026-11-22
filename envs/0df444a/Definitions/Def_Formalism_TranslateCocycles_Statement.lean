-- Prove2me | Definitions.Def_Formalism_TranslateCocycles_Statement
-- name    : Formalism_TranslateCocycles_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:48.427393+00:00
-- url     : https://prove2.me/theorems/c5b0fcfc-d8c9-4d98-84d1-5f77b2a8de9f
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TranslateCocycles/Statement.lean

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
namespace Formalism.CG
open Finset
def canTranslate {E : Type} [AddCommGroup E] (H : E → E → ℂ) (x : E) (F : E → ℂ) : E → ℂ :=
  fun z => F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)
def JetScale : Prop :=
  ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] (E F : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (L : E →L[𝕜] E) (f : E → F) (n : ℕ),
    ContDiff 𝕜 n f → ∀ (v : Fin n → E) (c : Fin n → 𝕜), (∀ k, L (v k) = c k • v k) → ∀ x : E,
      iteratedFDeriv 𝕜 n (f ∘ L) x v = (∏ k, c k) • iteratedFDeriv 𝕜 n f (L x) v
def HermScale : Prop :=
  ∀ (T : Type) [Fintype T] (V : T → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (h : ∀ τ, V τ →ₗ[ℂ] V τ →ₗ⋆[ℂ] ℂ) (c : T → ℂ) (g : ℂ),
    (∀ τ, starRingEnd ℂ (c τ) * c τ = g) →
    ∀ z w : (∀ τ, V τ), ∑ τ, h τ (c τ • z τ) (c τ • w τ) = g * ∑ τ, h τ (z τ) (w τ)
def TranslateScale : Prop :=
  ∀ (E : Type) [AddCommGroup E] (H : E → E → ℂ) (L : E →+ E) (g : ℂ),
    (∀ z w, H (L z) (L w) = g * H z w) → ∀ (F : E → ℂ) (b z : E),
      canTranslate H (L b) F (L z) = canTranslate (fun z w => g * H z w) b (F ∘ L) z
def ValueIdentity : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (H : E → E → ℂ) (L : E →L[ℂ] E) (g : ℂ),
    (∀ z w, H (L z) (L w) = g * H z w) → ∀ (σ : E → ℂ) (b : E) (n : ℕ),
    ContDiff ℂ n σ → ContDiff ℂ n (fun z => H z (L b)) →
    ∀ (v : Fin n → E) (c : Fin n → ℂ), (∀ k, L (v k) = c k • v k) →
      iteratedFDeriv ℂ n (canTranslate (fun z w => g * H z w) b (σ ∘ L)) 0 v =
        (∏ k, c k) * iteratedFDeriv ℂ n (canTranslate H (L b) σ) 0 v
def QuasiPeriod : Prop :=
  ∀ (E : Type) [AddCommGroup E] (H : E → E → ℂ),
    (∀ z z' w, H (z + z') w = H z w + H z' w) → (∀ z w w', H z (w + w') = H z w + H z w') →
    ∀ (Th : E → ℂ) (l : E) (α : ℂ),
      (∀ z, Th (z + l) =
        α * Complex.exp ((Real.pi : ℂ) * H z l + (Real.pi : ℂ) * H l l / 2) * Th z) →
      ∀ t z : E, canTranslate H (t + l) Th z =
        α * Complex.exp ((Real.pi : ℂ) * (H t l - H l t) / 2) * canTranslate H t Th z
def QuasiPeriodUnit : Prop :=
  ∀ (E : Type) (H : E → E → ℂ), (∀ z w, H w z = starRingEnd ℂ (H z w)) →
    ∀ t l : E, ‖Complex.exp ((Real.pi : ℂ) * (H t l - H l t) / 2)‖ = 1
def QuasiPeriodRoot : Prop :=
  ∀ (E : Type) [AddCommGroup E] (H : E → E → ℂ),
    (∀ z z' w, H (z + z') w = H z w + H z' w) → (∀ z w, H w z = starRingEnd ℂ (H z w)) →
    ∀ (N : ℕ) (t l : E), (∃ m : ℤ, (H (N • t) l).im = m) →
      Complex.exp ((Real.pi : ℂ) * (H t l - H l t) / 2) ^ (2 * N) = 1
def TranslateCocycle : Prop :=
  ∀ (E : Type) [AddCommGroup E] (H : E → E → ℂ),
    (∀ z z' w, H (z + z') w = H z w + H z' w) → (∀ z w w', H z (w + w') = H z w + H z w') →
    ∀ (F : E → ℂ) (x y z : E), canTranslate H x (canTranslate H y F) z =
      Complex.exp ((Real.pi : ℂ) * (H y x - H x y) / 2) * canTranslate H (x + y) F z
def NormValuation : Prop :=
  ∀ (K : Type) [Field K] (v : AddValuation K (WithTop ℚ)) (σ : K ≃+* K) (g : K), v g = 1 →
    ∀ (T : Type) [Fintype T] (a : T → K), (∀ τ, a τ * σ (a τ) = g) → ∀ D : T → ℕ,
      v (∏ τ, a τ ^ D τ) + v (σ (∏ τ, a τ ^ D τ)) = (((∑ τ, D τ : ℕ) : ℚ) : WithTop ℚ)
def Colour : Prop :=
  ∀ (K : Type) [Field K] (v : AddValuation K (WithTop ℚ)) (σ : K ≃+* K) (g : K), v g = 1 →
    ∀ a x y : K, a * σ a = g → 0 ≤ v x → 0 ≤ v y → x * a + y * σ a = 1 →
      0 ≤ v a → 0 ≤ v (σ a) → (v a = 0 ∧ v (σ a) = 1) ∨ (v a = 1 ∧ v (σ a) = 0)
def EquivariantBasis : Prop :=
  ∀ (U X R : Type) [Group U] [MulAction U X] [CommRing R] (ψ : U →* Rˣ),
    (∀ (u : U) (x : X), u • x = x → u = 1) →
    ∀ s : MulAction.orbitRel.Quotient U X → X,
      (∀ o, (Quotient.mk'' (s o) : MulAction.orbitRel.Quotient U X) = o) →
      Function.Bijective
        (fun (f : {f : X → R // ∀ (u : U) (x : X), f (u • x) = (ψ u : R) * f x})
          (o : MulAction.orbitRel.Quotient U X) => f.1 (s o))
def ColumnBothPlaces : Prop :=
  ∀ (J : Finset ℕ) (colL colLb vc vcb E : ℝ) (nnL nnLb Dpi : ℕ → ℝ),
    (∀ j ∈ J, nnL j + nnLb j = Dpi j) → vc + vcb = 0 →
    -(∑ j ∈ J, nnL j) + vc - E ≤ colL → -(∑ j ∈ J, nnLb j) + vcb - E ≤ colLb →
      -(∑ j ∈ J, Dpi j) - 2 * E ≤ colL + colLb
def BalanceG : Prop :=
  ∀ (J T P : Finset ℕ) (D del : ℝ), 0 < D → 0 < del →
    ∀ (colL colLb : ℝ) (aL aLb Dpi Dp Dm eta etab top : ℕ → ℝ) (k : ℝ) (w e1 e2 : ℕ → ℕ → ℝ)
      (Ecol CA rL rLb Etw : ℝ),
    -(∑ j ∈ J, Dpi j) - Ecol ≤ colL + colLb →
    ∑ j ∈ J, (aL j + aLb j) ≤ ∑ j ∈ J, (-2 * (Dp j + Dm j) * D + eta j + etab j)
        + 2 * (J.card : ℝ) * (CA * D + (rL + rLb) / del) + Etw →
    (∀ j ∈ J, Dpi j ≤ ∑ t ∈ T, top t + ∑ τ ∈ P, (k * w j τ + e1 j τ)) →
    (∀ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) ≤ Dp j + Dm j) →
      -((J.card : ℝ) * ∑ t ∈ T, top t + ∑ j ∈ J, ∑ τ ∈ P, (w j τ + e1 j τ + e2 j τ)
          + ∑ j ∈ J, (eta j + etab j) / (2 * D))
        - Ecol - (J.card : ℝ) * (CA + (rL + rLb) / (del * D)) - Etw / (2 * D)
      ≤ (2 * colL + 2 * colLb) / 2 - (∑ j ∈ J, (aL j + aLb j) / D) / 2
end Formalism.CG


