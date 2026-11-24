-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SigmaConstantAgrees
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SigmaConstantAgrees
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:32.469492+00:00
-- url     : https://prove2.me/theorems/74ee8f10-d09c-4b1b-a630-2851db4b0939
-- title:
--   Sigma Constant Agrees
-- statement:
--   Definitions and structural lemmas for Sigma Constant Agrees, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/SigmaConstantAgrees.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
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
def SigmaConstantAgrees : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (fa fb : G →+ G) (wp : G → K) (al be : K),
    (∀ Q, fb Q = 0 ↔ ∃ T, fa T = Q) → (∀ Q, fa Q = 0 ↔ ∃ T, fb T = Q) →
    (∀ T, fa T ≠ 0 → al ^ 2 * wp (fa T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), (wp (T + P) - wp P)) →
    (∀ T, fb T ≠ 0 → be ^ 2 * wp (fb T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fb P = 0 ∧ P ≠ 0), (wp (T + P) - wp P)) →
    al ^ 2 ≠ ((Finset.univ.filter (fun P => fa P = 0)).card : K) →
    be ^ 2 ≠ ((Finset.univ.filter (fun P => fb P = 0)).card : K) →
    s2Of (fun P : {P : G // fa P = 0 ∧ P ≠ 0} => wp P) al =
      s2Of (fun P : {P : G // fb P = 0 ∧ P ≠ 0} => wp P) be
def EndoAllLocal : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv ph : PowerSeries K, Frame R l linv ph → F1 R l linv ph →
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [StarRing O] [TopologicalSpace O] (τ : O →+* K),
    (∃ x y z : IsLocalRing.ResidueField O, x ≠ y ∧ y ≠ z ∧ x ≠ z) →
    Continuous τ → Continuous (star : O → O) →
    (∀ z : O, star z = z → τ z ∈ closure (Set.range (fun n : ℤ => (n : K)))) →
    (2 : K)⁻¹ ∈ R → IsUnit (2 : O) →
    ∀ Dn : Set O, (∀ α : Oˣ, (α : O) ∈ closure Dn) →
    (∀ α ∈ Dn, EndInt R l linv (τ α) ∧ PhNormAt R l linv ph (τ α) (τ (star α))) →
    ∀ α : O, EndInt R l linv (τ α) ∧ PhNormAt R l linv ph (τ α) (τ (star α)) ∧
      AdjAt R l linv ph (τ α) (τ (star α))
def SplitVanishSeries : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → AdjAt R l linv ph a b → ZLinAt R l linv ph a → ZLinAt R l linv ph b →
    IsBinomScalar R (a - b)⁻¹ → a ≠ b →
    (∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) ∧
    (PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R → LG R ph)
def JetsAll : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    IsLogPair l linv → IsOneUnit R (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 3 ≤ i → jet l ph i ∈ R) →
    PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    AdjAt R l linv ph a b → (a - b)⁻¹ ∈ R → a ≠ b →
    ∀ i : ℕ, jet l (mvExp (-ph) : PowerSeries K) i ∈ R
end Formalism.L2.Th1.C


