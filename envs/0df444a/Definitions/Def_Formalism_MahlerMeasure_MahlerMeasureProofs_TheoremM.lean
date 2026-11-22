-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:08.170641+00:00
-- url     : https://prove2.me/theorems/686fb0b9-9bf3-4b72-b970-4f68683a46ef
-- title:
--   Theorem M
-- statement:
--   Definitions and structural lemmas for Theorem M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.TM
section S0
open M MvPolynomial Finset
variable {N : ℕ}
end S0
section S1
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
end S1
section S2
open M Finset Matrix
variable {p : ℕ} [Fact p.Prime]
end S2
section S3
open Finset
end S3
section S4
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
def AdaptedBasisExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ),
    ∃ (n₀ : ℕ) (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ),
      LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w ∧
      (∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b)) ∧
      ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e
noncomputable def filL (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]) :=
  L ⊓ (MvPolynomial.restrictSupport ℚ_[p] {m | e ≤ m v}).restrictScalars ℤ_[p]
def AdStep (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (e : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → MvPolynomial σ ℚ_[p]) (ord : ι → ℕ),
    LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = filL L v e ∧
    (∀ b, HasOrder v (ord b) (f b) ∧ e ≤ ord b) ∧
    ∀ e', e ≤ e' → Submodule.span ℤ_[p] (f '' {b | e' ≤ ord b}) = filL L v e'
end S4
section S5
open M MvPolynomial Finset
def PointM : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
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
end S5
section S6
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
theorem fock_eq_sum (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  unfold fock
  apply Finset.sum_subset hs
  intro m _ hm
  rw [notMem_support_iff.mp hm, zero_mul, zero_mul]
theorem fock_add_left (F F' G : MvPolynomial σ ℚ_[p]) : fock p (F + F') G = fock p F G + fock p F' G := by
  classical
  rw [fock_eq_sum (F + F') G (F.support ∪ F'.support) support_add,
    fock_eq_sum F G (F.support ∪ F'.support) subset_union_left,
    fock_eq_sum F' G (F.support ∪ F'.support) subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_add]; ring
theorem fock_smul_left (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p (c • F) G = c * fock p F G := by
  classical
  rw [fock_eq_sum (c • F) G F.support (support_smul), fock_eq_sum F G F.support subset_rfl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_smul, smul_eq_mul]; ring
theorem fock_add_right (F G G' : MvPolynomial σ ℚ_[p]) : fock p F (G + G') = fock p F G + fock p F G' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_add]; ring
theorem fock_smul_right (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p F (c • G) = c * fock p F G := by
  unfold fock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_smul, smul_eq_mul]; ring
noncomputable def fockBil {N r : ℕ} (LL : Letters N)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
  LinearMap.mk₂ ℚ_[p] (fun x y => fockN p LL (φ x) y)
    (fun x x' y => by simp only [fockN, map_add, fock_add_left, add_div])
    (fun c x y => by simp only [fockN, map_smul, fock_smul_left, smul_eq_mul, mul_div_assoc])
    (fun x y y' => by simp only [fockN, fock_add_right, add_div])
    (fun c x y => by simp only [fockN, fock_smul_right, smul_eq_mul, mul_div_assoc])
def PartnerM : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
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
end S6
end Formalism.GM.TM
namespace Formalism.GM
end Formalism.GM


