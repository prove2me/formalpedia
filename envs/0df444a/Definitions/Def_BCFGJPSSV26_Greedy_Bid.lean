-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Bid
-- name    : BCFGJPSSV26_Greedy_Bid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:05.592436+00:00
-- url     : https://prove2.me/theorems/89845a2f-e6eb-4eab-8529-1ae5099e1150
-- title:
--   BCFGJPSSV26.Greedy.Bid — The bid
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Bid` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The bid `β(x, y) = [x - γ y]⁺` of [BCFGJPSSV26a, Section 4] for `γ = 153/125`
--   (`BCFGJPSSV26.Greedy.bid`), and the bound `ρ = 2 - (γ - 1)² = 1.949824` on the factor-revealing
--   program (`BCFGJPSSV26.Greedy.ρ`). All quantities of the analysis are rationals.
--
--   The chain lemmas (`BCFGJPSSV26.Greedy.bid_chain`, `BCFGJPSSV26.Greedy.bid_chain_le`,
--   `BCFGJPSSV26.Greedy.bid_group`) bound a sum of bids along an antitone sequence: they are the
--   telescoping steps of the cost analysis.
--
--   **Contents.** The module is published as a whole: 26 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Bid`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Bid.lean

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Bid` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The bid

The bid `β(x, y) = [x - γ y]⁺` of [BCFGJPSSV26a, Section 4] for `γ = 153/125`
(`BCFGJPSSV26.Greedy.bid`), and the bound `ρ = 2 - (γ - 1)² = 1.949824` on the factor-revealing
program (`BCFGJPSSV26.Greedy.ρ`). All quantities of the analysis are rationals.

The chain lemmas (`BCFGJPSSV26.Greedy.bid_chain`, `BCFGJPSSV26.Greedy.bid_chain_le`,
`BCFGJPSSV26.Greedy.bid_group`) bound a sum of bids along an antitone sequence: they are the
telescoping steps of the cost analysis.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- The constant `γ = 153/125 = 1.224` of the bid. -/
def γ : ℚ := 153 / 125

/-- The bound `ρ = 2 - (γ - 1)² = 1.949824` on the factor-revealing program at `γ`. -/
def ρ : ℚ := 2 - (γ - 1) ^ 2

theorem one_le_γ : 1 ≤ γ := by norm_num [γ]

theorem γ_le : γ ≤ 153 / 125 := le_rfl

theorem ρ_eq : ρ = 30466 / 15625 := by norm_num [ρ, γ]

theorem one_le_ρ : 1 ≤ ρ := by norm_num [ρ_eq]

theorem ρ_lt : ρ < 1.9499 := by norm_num [ρ_eq]

/-- The bid `β(x, y) = [x - γ y]⁺`. -/
def bid (x y : ℚ) : ℚ := max (x - γ * y) 0

theorem bid_nonneg (x y : ℚ) : 0 ≤ bid x y := le_max_right _ _

theorem bid_mono_left {x x' : ℚ} (h : x ≤ x') (y : ℚ) : bid x y ≤ bid x' y :=
  max_le_max (by linarith) le_rfl

theorem bid_anti_right (x : ℚ) {y y' : ℚ} (h : y ≤ y') : bid x y' ≤ bid x y := by
  have := one_le_γ
  exact max_le_max (by nlinarith) le_rfl

theorem bid_le_left {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) : bid x y ≤ x := by
  have := one_le_γ
  exact max_le (by nlinarith) hx

theorem bid_eq_zero_of_le {x y : ℚ} (h : x ≤ y) (hy : 0 ≤ y) : bid x y = 0 := by
  have := one_le_γ
  exact max_eq_right (by nlinarith)

theorem bid_self {x : ℚ} (hx : 0 ≤ x) : bid x x = 0 := bid_eq_zero_of_le le_rfl hx

theorem bid_zero_right {x : ℚ} (hx : 0 ≤ x) : bid x 0 = x := by
  simp [bid, hx]

theorem bid_eq_of_le {x y : ℚ} (h : γ * y ≤ x) : bid x y = x - γ * y :=
  max_eq_left (by linarith)

theorem bid_le_sub {x y : ℚ} (hxy : y ≤ x) (hy : 0 ≤ y) : bid x y ≤ x - y := by
  have := one_le_γ
  exact max_le (by nlinarith) (by linarith)

/-- Raising the first argument by `c ≥ 0` raises the bid by at most `c`. -/
theorem bid_add_le {c : ℚ} (hc : 0 ≤ c) (x y : ℚ) : bid (x + c) y ≤ bid x y + c := by
  unfold bid
  rcases le_total (x - γ * y) 0 with h | h
  · rw [max_eq_right h]
    exact max_le (by linarith) (by linarith)
  · rw [max_eq_left h]
    exact max_le (by linarith) (by linarith)

/-- The bid is `1`-Lipschitz in its first argument. -/
theorem bid_sub_bid_le (x x' y : ℚ) : bid x y - bid x' y ≤ max (x - x') 0 := by
  rcases le_total (x - x') 0 with hc | hc
  · rw [max_eq_right hc]
    have := bid_mono_left (show x ≤ x' by linarith) y
    linarith
  · rw [max_eq_left hc]
    have h := bid_add_le hc x' y
    rw [show x' + (x - x') = x by ring] at h
    linarith

/-- **Superadditivity**: for `x₁ ≥ x₂ ≥ x₃ ≥ 0`, `β(x₁, x₂) + β(x₂, x₃) ≤ β(x₁, x₃)`. -/
theorem bid_superadd {x₁ x₂ x₃ : ℚ} (h₃ : 0 ≤ x₃) (h₂ : x₃ ≤ x₂) (h₁ : x₂ ≤ x₁) :
    bid x₁ x₂ + bid x₂ x₃ ≤ bid x₁ x₃ := by
  have hγ := one_le_γ
  have key : bid x₁ x₂ ≤ bid x₁ x₃ := bid_anti_right _ h₂
  unfold bid at *
  rcases le_total (x₂ - γ * x₃) 0 with h' | h'
  · rw [max_eq_right h', add_zero]
    exact key
  · rw [max_eq_left h']
    rcases le_total (x₁ - γ * x₂) 0 with h | h
    · rw [max_eq_right h, zero_add]
      exact le_max_of_le_left (by nlinarith)
    · rw [max_eq_left h]
      exact le_max_of_le_left (by nlinarith)

/-- The bid is homogeneous. -/
theorem bid_smul {c : ℚ} (hc : 0 < c) (x y : ℚ) : bid (c * x) (c * y) = c * bid x y := by
  unfold bid
  rw [mul_max_of_nonneg _ _ hc.le, mul_zero, mul_sub]
  ring_nf

/-- An antitone sequence on `[a, b]` stays below its first term. -/
theorem chain_le {x : ℕ → ℚ} {a b : ℕ} (hx : ∀ s, a ≤ s → s < b → x (s + 1) ≤ x s) :
    ∀ s, a ≤ s → s ≤ b → x s ≤ x a := by
  intro s has hsb
  induction s, has using Nat.le_induction with
  | base => exact le_rfl
  | succ s hs ih => exact (hx s hs (by omega)).trans (ih (by omega))

/-- An antitone sequence on `[a, b]` stays above its last term. -/
theorem le_chain {x : ℕ → ℚ} {a b : ℕ} (hx : ∀ s, a ≤ s → s < b → x (s + 1) ≤ x s) :
    ∀ s, a ≤ s → s ≤ b → x b ≤ x s := by
  intro s has hsb
  have h := chain_le (x := x) (a := s) (b := b) (fun r hr hr' ↦ hx r (by omega) hr') b hsb le_rfl
  exact h

/-- **Chain lemma**: along an antitone nonnegative sequence, the bids between consecutive
terms and the last term add up to at most the first term. -/
theorem bid_chain {x : ℕ → ℚ} {a b : ℕ} (hab : a ≤ b)
    (hx : ∀ s, a ≤ s → s < b → x (s + 1) ≤ x s) (h0 : 0 ≤ x b) :
    ∑ s ∈ Finset.Ico a b, bid (x s) (x (s + 1)) + x b ≤ x a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hb : x (b + 1) ≤ x b := hx b hab (by omega)
    have ih' := ih (fun s h1 h2 ↦ hx s h1 (by omega)) (h0.trans hb)
    rw [Finset.sum_Ico_succ_top hab]
    have := bid_le_sub hb h0
    linarith

/-- **Chain lemma, grouped**: along an antitone nonnegative sequence, the bids between
consecutive terms add up to at most the bid between the endpoints. -/
theorem bid_chain_le {x : ℕ → ℚ} {a b : ℕ} (hab : a ≤ b)
    (hx : ∀ s, a ≤ s → s < b → x (s + 1) ≤ x s) (h0 : 0 ≤ x b) :
    ∑ s ∈ Finset.Ico a b, bid (x s) (x (s + 1)) ≤ bid (x a) (x b) := by
  induction b, hab using Nat.le_induction with
  | base => simpa using bid_nonneg _ _
  | succ b hab ih =>
    have hb : x (b + 1) ≤ x b := hx b hab (by omega)
    have ih' := ih (fun s h1 h2 ↦ hx s h1 (by omega)) (h0.trans hb)
    have hba : x b ≤ x a := chain_le hx b hab (by omega)
    rw [Finset.sum_Ico_succ_top hab]
    have := bid_superadd h0 hb hba
    linarith

/-- **Chain lemma over a subsequence**: for indices `t 0 ≤ t 1 ≤ … ≤ t L`, the bids between
consecutive terms on `[t 0, t L)` add up to at most the bids between consecutive `x (t l)`. -/
theorem bid_group {x : ℕ → ℚ} (t : ℕ → ℕ) {L : ℕ} (ht : ∀ l < L, t l ≤ t (l + 1))
    (hx : ∀ s, t 0 ≤ s → s < t L → x (s + 1) ≤ x s) (h0 : 0 ≤ x (t L)) :
    ∑ s ∈ Finset.Ico (t 0) (t L), bid (x s) (x (s + 1)) ≤
      ∑ l ∈ Finset.range L, bid (x (t l)) (x (t (l + 1))) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hmono : ∀ l ≤ L, t 0 ≤ t l := by
      intro l hl
      induction l with
      | zero => exact le_rfl
      | succ l ihl => exact (ihl (by omega)).trans (ht l (by omega))
    have h0L : t 0 ≤ t L := hmono L le_rfl
    have hL : t L ≤ t (L + 1) := ht L (by omega)
    have hxL : x (t (L + 1)) ≤ x (t L) :=
      le_chain (a := t 0) (b := t (L + 1)) hx (t L) h0L hL
    have ih' := ih (fun l hl ↦ ht l (by omega)) (fun s h1 h2 ↦ hx s h1 (by omega))
      (h0.trans hxL)
    rw [← Finset.sum_Ico_consecutive _ h0L hL, Finset.sum_range_succ]
    have := bid_chain_le hL (fun s h1 h2 ↦ hx s (h0L.trans h1) h2) h0
    linarith

end BCFGJPSSV26.Greedy


