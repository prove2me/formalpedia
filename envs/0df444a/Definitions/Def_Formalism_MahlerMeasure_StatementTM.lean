-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_StatementTM
-- name    : Formalism_MahlerMeasure_StatementTM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:42.933559+00:00
-- url     : https://prove2.me/theorems/dfdd998e-556b-4a28-a437-e8943376ffa7
-- title:
--   Statement TM
-- statement:
--   Definitions and structural lemmas for Statement TM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/StatementTM.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
def Letters.takeD {N : ℕ} (LL : Letters N) (k : ℕ) : Letters k where
  vec := fun i => if h : (i : ℕ) < N then LL.vec ⟨i, h⟩ else false
  deg := fun i => if h : (i : ℕ) < N then LL.deg ⟨i, h⟩ else 0
open Classical in

noncomputable def Letters.setTies {N : ℕ} (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) : Letters N where
  vec := LL.vec
  deg := fun a => if h : ∃ i, T.pos i + 1 = (a : ℕ) then n (Classical.choose h) else LL.deg a
def TieData.thrUpTo (T : TieData) (i : Fin T.t) : Fin T.q → WithTop ℤ :=
  fun k => if T.J k ≤ T.pos i + 1 then T.thr k else ⊤
noncomputable def TieData.phis (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (T : TieData) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (List.finRange T.t).foldr (fun i acc => (T.phi p LL i) ∘ₗ acc) LinearMap.id
noncomputable def TieData.Ffull (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] (LL : Letters N) (T : TieData) (i : Fin T.t)
    (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  rename (fun x : Fin (T.pos i + 1 + 1) × Fin r =>
      (if h : (x.1 : ℕ) < N then (⟨x.1, h⟩ : Fin N) else ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, x.2))
    (freeze p (LL.takeD (T.pos i + 1)) ρ n f)
noncomputable def TieData.YYsp (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p (LL.setTies T n) T.J T.thr ⊓
    Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T n) (T.pos i + 2) (T.Ffull p (LL.setTies T n) i ρ (n i) f),
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q}
def WeightSpaceDimMonotone : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData), T.Admissible LL →
    ∀ (ρ : Fin r), (ρ : ℕ) = r - 1 → 2 ≤ r → ∀ (i : Fin T.t) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
      (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w → f ≠ 0 →
      ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i →
      ∀ n' : ℕ, n i ≤ n' →
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n f) ≤
          Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i n') f)
def MonoCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData), T.Admissible LL →
    ∀ (ρ : Fin r), (ρ : ℕ) = r - 1 → 2 ≤ r → ∀ (i : Fin T.t) (n : Fin T.t → ℕ),
      ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i →
      ∀ fw : (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
        (∀ w, fw w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
          (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw w ≠ 0)) →
        ∑ᶠ w, Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) *
            Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw w)) =
          Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T n) T.J T.thr)
def MeanGam : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (z : ℕ) (w : Fin r → ℤ) (n₀ : ℕ)
    (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ) (s d Yw a : ℕ) (E κ : ℝ)
    (U V : ℕ → Matrix (Fin n₀) (Fin n₀) ℚ_[p]) (dg : ℕ → Fin n₀ → ℚ_[p]),
    (ρ : ℕ) = r - 1 → 2 ≤ r → LLw.vec (Fin.last K) = true →
    LinearIndependent ℤ_[p] f → Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w →
    (∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b)) →
    (∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e) →
    1 ≤ E → 1 ≤ Yw → 0 < d → IsCoprime (d : ℤ) p → LLw.total ≤ s →
    (∀ x, LLw.deg x ≤ 2 * a) → s + d * (Yw - 1) ≤ 2 * a → z ≤ 2 * a →
    ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ →
    (∀ j < Yw, (∀ x y, ‖U j x y‖ ≤ 1) ∧ (∀ x y, ‖V j x y‖ ≤ 1) ∧ ‖(U j).det‖ = 1 ∧ ‖(V j).det‖ = 1 ∧
      (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p LLw ρ z (s + d * j) (f x) (f y)) =
        U j * Matrix.diagonal (dg j) * V j) →
    (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw ≤
      n₀ * (2 * (LLw.total : ℝ) / Yw + (C₀ * κ + 2 * (LLw.total : ℝ) * lgV2 p a r / Yw) / E)
def TheoremM : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a : ℕ) (E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ ∧ HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ ∧
      ∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
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
end Formalism.GM.M


