-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:50.424284+00:00
-- url     : https://prove2.me/theorems/fdb4ddff-b69b-4470-97e2-38b9fe5047f6
-- title:
--   Ph Norm Closed
-- statement:
--   Definitions and structural lemmas for Ph Norm Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/PhNormClosed.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
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
namespace Formalism.L2.Th1.C
def EndIntClosed : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv : PowerSeries K, PowerSeries.constantCoeff l = 0 →
      IsClosed {a : K | EndInt R l linv a}
def BinomClosed : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → IsClosed {z : K | IsBinomScalar R z}
def PhNormClosed : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv ph : PowerSeries K, PowerSeries.constantCoeff l = 0 →
      PowerSeries.constantCoeff linv = 0 → PowerSeries.constantCoeff ph = 0 →
      IsClosed {p : K × K | PhNormAt R l linv ph p.1 p.2}
def ZLinClosed : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv ph : PowerSeries K, PowerSeries.constantCoeff l = 0 →
      PowerSeries.constantCoeff linv = 0 → PowerSeries.constantCoeff ph = 0 →
      IsClosed {z : K | ZLinAt R l linv ph z}
def ZLinInt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph → ∀ n : ℤ, ZLinAt R l linv ph (n : K)
def EndoAll : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv ph : PowerSeries K, Frame R l linv ph → F1 R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] [TopologicalSpace O] (τ : O →+* K),
    Continuous τ → Continuous (star : O → O) →
    (∀ z : O, star z = z → τ z ∈ closure (Set.range (fun n : ℤ => (n : K)))) →
    (2 : K)⁻¹ ∈ R → IsUnit (2 : O) → (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    ∀ Dn : Set O, (∀ α : Oˣ, (α : O) ∈ closure Dn) →
    (∀ α ∈ Dn, EndInt R l linv (τ α) ∧ PhNormAt R l linv ph (τ α) (τ (star α))) →
    ∀ α : O, EndInt R l linv (τ α) ∧ PhNormAt R l linv ph (τ α) (τ (star α)) ∧
      AdjAt R l linv ph (τ α) (τ (star α))
end Formalism.L2.Th1.C


