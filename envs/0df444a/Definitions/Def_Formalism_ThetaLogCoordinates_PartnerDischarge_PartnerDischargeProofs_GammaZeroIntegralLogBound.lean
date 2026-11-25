-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_PartnerDischarge_PartnerDischargeProofs_GammaZeroIntegralLogBound
-- name    : Formalism_ThetaLogCoordinates_PartnerDischarge_PartnerDischargeProofs_GammaZeroIntegralLogBound
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:36.970852+00:00
-- url     : https://prove2.me/theorems/2c214f73-3a30-401d-95bc-b5fb033fd0de
-- title:
--   Gamma Zero Integral Log Bound
-- statement:
--   Definitions and structural lemmas for Gamma Zero Integral Log Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerDischarge/PartnerDischargeProofs/GammaZeroIntegralLogBound.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerDischarge_StatementPW
import Definitions.Def_Formalism_PolynomialDimension_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeTheoremOfDischarge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
noncomputable def lgB (p a r : ℕ) : ℝ := Real.logb p (4 * a + r) + 1
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open Finset Formalism.GM Formalism.GM.MeanGammaLemmas
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open MvPolynomial Finset Formalism.GM Formalism.GM.M
def MeanGamB : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (z : ℕ) (w : Fin r → ℤ) (n₀ : ℕ)
    (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ) (s d Yw a : ℕ) (E κ : ℝ)
    (U V : ℕ → Matrix (Fin n₀) (Fin n₀) ℚ_[p]) (dg : ℕ → Fin n₀ → ℚ_[p]),
    (ρ : ℕ) = r - 1 → 2 ≤ r → LLw.vec (Fin.last K) = true →
    LinearIndependent ℤ_[p] f → Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w →
    (∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b)) →
    (∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e) →
    1 ≤ E → 1 ≤ Yw → 0 < d → IsCoprime (d : ℤ) p → LLw.total ≤ s →
    (∀ x, LLw.deg x ≤ a) → s + d * (Yw - 1) ≤ a → z ≤ a →
    ((K + 3) * r ^ 2 : ℝ) * lgB p a r ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ →
    (∀ j < Yw, (∀ x y, ‖U j x y‖ ≤ 1) ∧ (∀ x y, ‖V j x y‖ ≤ 1) ∧ ‖(U j).det‖ = 1 ∧ ‖(V j).det‖ = 1 ∧
      (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p LLw ρ z (s + d * j) (f x) (f y)) =
        U j * Matrix.diagonal (dg j) * V j) →
    (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw ≤
      n₀ * (2 * (LLw.total : ℝ) / Yw + (C₀ * κ + 2 * (LLw.total : ℝ) * lgB p a r / Yw) / E)
def TheoremMB : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a : ℕ) (E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ ∧ HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ ∧
      ∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * lgB p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open Polynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open Formalism.GM Formalism.GM.TM Formalism.GM.M MvPolynomial Finset
def PointMB : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ →
    HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ → HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ →
    (∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    ∀ (nb : Fin T.t → (Fin r → ℤ) → ℕ)
      (f : ∀ i w, Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
      (U V : ∀ i w, Matrix (Fin (nb i w)) (Fin (nb i w)) ℚ_[p]) (dg : ∀ i w, Fin (nb i w) → ℚ_[p])
      (fw : ∀ i : Fin T.t, (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      (∀ i w, LinearIndependent ℤ_[p] (f i w) ∧
        Submodule.span ℤ_[p] (Set.range (f i w)) =
          MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) →
      (∀ i w, (∀ x y, ‖U i w x y‖ ≤ 1) ∧ (∀ x y, ‖V i w x y‖ ≤ 1) ∧ ‖(U i w).det‖ = 1 ∧ ‖(V i w).det‖ = 1 ∧
        (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) *
          tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) (f i w x) (f i w y)) =
          U i w * Matrix.diagonal (dg i w) * V i w) →
      (∀ i w, fw i w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
        (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw i w ≠ 0)) →
      (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋ : ℝ) ≤
        ∑ i, ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
          (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)
def PartnerMB : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ →
    HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ → HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ →
    (∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    ∀ (nb : Fin T.t → (Fin r → ℤ) → ℕ)
      (f : ∀ i w, Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
      (U V : ∀ i w, Matrix (Fin (nb i w)) (Fin (nb i w)) ℚ_[p]) (dg : ∀ i w, Fin (nb i w) → ℚ_[p])
      (fw : ∀ i : Fin T.t, (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      (∀ i w, LinearIndependent ℤ_[p] (f i w) ∧
        Submodule.span ℤ_[p] (Set.range (f i w)) =
          MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) →
      (∀ i w, (∀ x y, ‖U i w x y‖ ≤ 1) ∧ (∀ x y, ‖V i w x y‖ ≤ 1) ∧ ‖(U i w).det‖ = 1 ∧ ‖(V i w).det‖ = 1 ∧
        (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) *
          tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) (f i w x) (f i w y)) =
          U i w * Matrix.diagonal (dg i w) * V i w) →
      (∀ i w, fw i w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
        (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw i w ≠ 0)) →
      ∃ L₁ : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]),
        L₁ ≤ YZ p (r := r) (LL.setTies T n) T.J T.thr ∧
        (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), c ≠ 0 → x ∈ YZ p (r := r) (LL.setTies T n) T.J T.thr →
          c • x ∈ L₁ → x ∈ L₁) ∧
        (∀ u ∈ L₁, (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ L₁ → u = c • x → IsUnit c) →
          ∃ u' ∈ YZ p (r := r) (LL.setTies T n) T.J T.thr,
            (p : ℝ) ^ (-⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋) ≤
              ‖fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) u) u'‖) ∧
        ((Module.finrank ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) - Module.finrank ℤ_[p] L₁ : ℕ) : ℝ) ≤
          ∑ i, ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open Formalism.GM Formalism.GM.TM Formalism.GM.M Formalism.CountingSumsFrames MvPolynomial Finset
def TieOpsB : Prop :=
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ →
    HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ → HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ →
    (∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    ∀ (nb : Fin T.t → (Fin r → ℤ) → ℕ)
      (f : ∀ i w, Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
      (U V : ∀ i w, Matrix (Fin (nb i w)) (Fin (nb i w)) ℚ_[p]) (dg : ∀ i w, Fin (nb i w) → ℚ_[p])
      (fw : ∀ i : Fin T.t, (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      (∀ i w, LinearIndependent ℤ_[p] (f i w) ∧
        Submodule.span ℤ_[p] (Set.range (f i w)) =
          MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) →
      (∀ i w, (∀ x y, ‖U i w x y‖ ≤ 1) ∧ (∀ x y, ‖V i w x y‖ ≤ 1) ∧ ‖(U i w).det‖ = 1 ∧ ‖(V i w).det‖ = 1 ∧
        (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) *
          tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) (f i w x) (f i w y)) =
          U i w * Matrix.diagonal (dg i w) * V i w) →
      (∀ i w, fw i w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
        (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw i w ≠ 0)) →
      ∀ i : Fin T.t, ∃ (Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
        (K : ℕ), (K : ℝ) ≤ C₂ * κ ∧
        (∀ y ∈ Y p (r := r) (LL.setTies T n) T.J T.thr, Tm y ∈ Y p (r := r) (LL.setTies T n) T.J T.thr) ∧
        (∀ y ∈ YZ p (r := r) (LL.setTies T n) T.J T.thr,
          ((p : ℚ_[p]) ^ K) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
        (∀ u ∈ Y p (r := r) (LL.setTies T n) T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) (LL.setTies T n) T.J T.thr,
          fockN p (LL.setTies T n) (T.phi p (LL.setTies T n) i u) (Tm u') =
            (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p (LL.setTies T n) (πm u) u') ∧
        (∀ j : Fin T.t, i < j → ∀ u ∈ Y p (r := r) (LL.setTies T n) T.J (T.thrUpTo i),
          πm (T.phi p (LL.setTies T n) j u) = T.phi p (LL.setTies T n) j (πm u)) ∧
        ((Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T n) T.J T.thr) -
            Module.finrank ℚ_[p] ((Y p (r := r) (LL.setTies T n) T.J T.thr ⊓
              LinearMap.ker (πm - LinearMap.id) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) : ℕ) : ℝ) ≤
          ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)
def YPartnerB : Prop :=
  ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (a : ℕ) (κ : ℝ),
    2 ≤ r → ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ → HypP p LL ρ ⌈κ / (N + 2)⌉₊ →
    ∀ z ∈ YZ p (r := r) LL J M,
      (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) →
      ∃ z'' ∈ YZ p (r := r) LL J M, ∃ K₀ : ℕ, (K₀ : ℝ) ≤ C₃ * κ ∧
        (p : ℝ) ^ (-(K₀ : ℤ)) ≤ ‖fockN p LL z z''‖
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open Formalism.GM Formalism.GM.M Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO MvPolynomial Finset
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
end Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds
open MvPolynomial Finset Formalism.GM.M Formalism.GM Formalism.InvariantFactorPaths.PW
end Formalism.InvariantFactorPaths.OddLevelGainBounds


