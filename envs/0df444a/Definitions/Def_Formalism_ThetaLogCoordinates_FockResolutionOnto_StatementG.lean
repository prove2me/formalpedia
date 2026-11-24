-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:07.629807+00:00
-- url     : https://prove2.me/theorems/58b233d3-6261-4fae-9785-59940dee0560
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/StatementG.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW MvPolynomial Finset
noncomputable def EX (p : ℕ) [Fact p.Prime] {K s : ℕ} (LL : Letters (K + 1)) (c : ℤ) (a b : Fin (s + 1)) :
    MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p] :=
  Fin.cases
    (Fin.cases ((((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K (s + 1))) (fun j => dW p K (Fin.castSucc j)) b)
    (fun i => Fin.cases (Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i))
      (fun j => glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j)) b) a
def wtX {K s : ℕ} (LL : Letters (K + 1)) (c : ℤ) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) : Fin (s + 1) → ℤ :=
  Fin.cases (c - ∑ a : Fin (s + 1), (m (Fin.last K, a) : ℤ)) (fun i => wt LL (K + 1) (Fin.castSucc i) m)
def GXExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K s : ℕ) (LL : Letters (K + 1)) (c : ℤ), LL.vec (Fin.last K) = true →
    ∃ G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1),
      G.E = EX p LL c ∧ ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0
def UDivInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) (k : ℕ), a ∈ Cs →
    ∀ x ∈ IntPol p (Fin (K + 1) × Fin r),
      ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) x ∈ IntPol p (Fin (K + 1) × Fin r)
def DWDivInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (a : Fin r) (k : ℕ),
    ∀ x ∈ IntPol p (Fin (K + 1) × Fin r),
      ((k.factorial : ℚ_[p]))⁻¹ • ((dW p K a) ^ k) x ∈ IntPol p (Fin (K + 1) × Fin r)
def XVanish : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (ρ : Fin r) (c : ℤ) (o : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true →
    c + (∑ i : Fin (K + 1), if i = Fin.last K then 0 else (LL.deg i : ℤ)) < o →
    Pol p r (setLast LL o) ⊓ FreeOf p (Fin.last K, ρ) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) = ⊥
def ResSatL (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (c0 : ℕ) : Prop :=
  ∀ x ∈ XSp p LL J M ρ, x ∈ IntPol p (Fin (K + 1) × Fin r) →
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ c0) • x
def ResSatLThm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true →
    ResSatL p LL J M ρ (2 * (r.choose 2 * Nat.log p (4 * LL.total + r - 1)))
def GradedBoundOfSaturation : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 c0 : ℕ) (κ : ℝ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true →
    (∀ o ≤ LLw.deg (Fin.last K), HypP p (setLast LLw o) ρ e1 ∧ HypE p (setLast LLw o) ρ e1) →
    (∀ e ≤ LLw.deg (Fin.last K), ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ c0) →
    (((K + 5) * e1 + 2 * c0 : ℕ) : ℝ) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
def GramBoundUnconditional : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (κ : ℝ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true →
    (((K + 5) * kapC p r LLw.total + 4 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1)) : ℕ) : ℝ) ≤ κ →
    GramDeterminantGradedHypothesis p LLw J M ρ κ
def GramBoundUnconditionalExponent : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (a : ℕ) (κ : ℝ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → LLw.total ≤ 2 * a →
    2 * (((K + 3) * r ^ 2 : ℝ) * lgV2 p a r) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
def TheoremMFree : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a : ℕ) (E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    2 * (((N + 2) * r ^ 2 : ℝ) * lgV2 p a r) ≤ κ →
    2 * a * N + r ≤ p ^ 2 * (8 * a + r) ^ 2 →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * lgV2 p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
end Formalism.InvariantFactorPaths.L4


