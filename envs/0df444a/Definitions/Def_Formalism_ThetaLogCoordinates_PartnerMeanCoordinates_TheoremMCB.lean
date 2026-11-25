-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
-- name    : Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:56:32.918865+00:00
-- url     : https://prove2.me/theorems/a9dadb89-5bd9-4415-ac2a-3f7799a53d0d
-- title:
--   Theorem MCB
-- statement:
--   Definitions and structural lemmas for Theorem MCB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/TheoremMCB.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerDischarge_PartnerDischargeProofs_GammaZeroIntegralLogBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.MC
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.InvariantFactorPaths.OddLevelGainBounds.TB
def GamIntC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ PolZ p r LL → f' ∈ PolZ p r LL →
    ∃ c : ℕ → ℤ_[p], ∀ n, LL.total ≤ n →
      ((p : ℚ_[p]) ^ ((N + 4) * (r * Nat.log p (LL.total + LL.deg (Fin.last N) + r)) +
          6 * Nat.log p (LL.total + LL.deg (Fin.last N) + r))) * tieGam p LL ρ z n f f' =
        ∑ i ∈ range (LL.total + LL.deg (Fin.last N) + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])
def MeanGamC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (z : ℕ) (w : Fin r → ℤ) (n₀ : ℕ)
    (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ) (s d Yw a : ℕ) (E κ κ4 : ℝ)
    (U V : ℕ → Matrix (Fin n₀) (Fin n₀) ℚ_[p]) (dg : ℕ → Fin n₀ → ℚ_[p]),
    (ρ : ℕ) = r - 1 → 2 ≤ r → LLw.vec (Fin.last K) = true →
    LinearIndependent ℤ_[p] f → Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w →
    (∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b)) →
    (∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e) →
    1 ≤ E → 1 ≤ Yw → 0 < d → IsCoprime (d : ℤ) p → LLw.total ≤ s →
    (∀ x, LLw.deg x ≤ a) → s + d * (Yw - 1) ≤ a → z ≤ a →
    (((K + 4) * r + 6 : ℝ)) * lgB p a r ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ4 →
    (∀ j < Yw, (∀ x y, ‖U j x y‖ ≤ 1) ∧ (∀ x y, ‖V j x y‖ ≤ 1) ∧ ‖(U j).det‖ = 1 ∧ ‖(V j).det‖ = 1 ∧
      (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p LLw ρ z (s + d * j) (f x) (f y)) =
        U j * Matrix.diagonal (dg j) * V j) →
    (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw ≤
      n₀ * (2 * (LLw.total : ℝ) / Yw + ((κ + 3 * lgB p a r + κ4) + 2 * (LLw.total : ℝ) * lgB p a r / Yw) / E)
def TieOpsC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (e1 : ℕ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ →
    HypP p (LL.setTies T n) ρ e1 → HypW p (r := r) (LL.setTies T n) e1 →
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
        (K : ℕ), K ≤ e1 * (N + 2) ∧
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
def YPartnerC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ),
    2 ≤ r → HypP p LL ρ e1 →
    ∀ z ∈ YZ p (r := r) LL J M,
      (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) →
      ∃ z'' ∈ YZ p (r := r) LL J M, (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) ≤ ‖fockN p LL z z''‖
def PartnerMC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (e1 : ℕ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ → ((e1 * (N + 2) : ℕ) : ℝ) ≤ κ →
    HypP p (LL.setTies T n) ρ e1 → HypW p (r := r) (LL.setTies T n) e1 →
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
            (p : ℝ) ^ (-⌊(T.t : ℝ) * (E + κ) + κ⌋) ≤
              ‖fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) u) u'‖) ∧
        ((Module.finrank ℤ_[p] (YZ p (r := r) (LL.setTies T n) T.J T.thr) - Module.finrank ℤ_[p] L₁ : ℕ) : ℝ) ≤
          ∑ i, ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)
def PointMC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (e1 : ℕ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    ((N + 2) * r ^ 2 : ℝ) * lgB p a r ≤ κ → ((e1 * (N + 2) : ℕ) : ℝ) ≤ κ →
    HypP p (LL.setTies T n) ρ e1 → HypW p (r := r) (LL.setTies T n) e1 →
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
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ : ℝ) ≤
        ∑ i, ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
          (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)
def TheoremMCB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a : ℕ) (E κ κ4 : ℝ) (e1 : ℕ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ a) → (∀ i, T.z i ≤ a) →
    (3 / 2 : ℝ) * (((N + 2) * r ^ 2 : ℝ) * lgB p a r) ≤ κ → ((e1 * (N + 2) : ℕ) : ℝ) ≤ κ → 3 * lgB p a r + κ4 ≤ κ →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      HypP p (LL.setTies T n) ρ e1 ∧ HypW p (r := r) (LL.setTies T n) e1 ∧
      ∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ4) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + κ) + κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (2 * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * lgB p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
end Formalism.InvariantFactorPaths.MC


