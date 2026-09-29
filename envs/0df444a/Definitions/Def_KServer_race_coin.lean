-- Prove2me | Definitions.Def_KServer_race_coin
-- name    : KServer_race_coin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T15:21:23.045536+00:00
-- url     : https://prove2.me/theorems/caa819d9-97ca-408d-91a5-b95a80c56f93
-- title:
--   The coin-tree measure
-- statement:
--   The probability measure of a path-dependent coin tree: for per-step weights $W_j$ depending on the exact coin prefix, the weight of a string $c \in \{0,1\}^{\kappa}$ is the product $$P(c) = \prod_{j<\kappa} W_j(c|_{<j}, c_j).$$ If the two choices at every step have weights summing to one, the total mass is one — proved by splitting off the last coin through the equivalence $(\mathrm{Fin}\,(\kappa+1) \to \mathrm{Bool}) \simeq (\mathrm{Fin}\,\kappa \to \mathrm{Bool}) \times \mathrm{Bool}$ — and positive per-step weights give positive masses. This is the sample-space factor carrying the coin phase of the BCR race.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace Race

/-! ### The coin-tree measure

Path-dependent coin weights on `Fin κ → Bool`: the weight of a string is
the product of per-step weights, each depending on the exact prefix.  If
the two choices at every step have weights summing to one, the total mass
is one; positive per-step weights give positive masses. -/

/-- Restrict a coin string to its first `j` coins. -/
def restrict {κ : ℕ} (c : Fin κ → Bool) (j : ℕ) (hj : j ≤ κ) : Fin j → Bool :=
  fun i => c ⟨i, by omega⟩

/-- The product weight of a coin string under per-step prefix weights. -/
noncomputable def coinWt {κ : ℕ}
    (W : (j : ℕ) → (Fin j → Bool) → Bool → ℝ) (c : Fin κ → Bool) : ℝ :=
  ∏ j : Fin κ, W j (restrict c j (le_of_lt j.isLt)) (c j)

theorem coinWt_pos {κ : ℕ} {W : (j : ℕ) → (Fin j → Bool) → Bool → ℝ}
    (hW : ∀ j p b, 0 < W j p b) (c : Fin κ → Bool) : 0 < coinWt W c :=
  Finset.prod_pos fun j _ => hW _ _ _

/-- Splitting off the last coin. -/
noncomputable def snocEquiv (κ : ℕ) :
    (Fin (κ + 1) → Bool) ≃ (Fin κ → Bool) × Bool where
  toFun c := (fun i => c i.castSucc, c (Fin.last κ))
  invFun p := Fin.snoc p.1 p.2
  left_inv c := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · show (Fin.snoc (fun i => c i.castSucc) (c (Fin.last κ))
          : Fin (κ + 1) → Bool) j.castSucc = c j.castSucc
      rw [Fin.snoc_castSucc]
    · show (Fin.snoc (fun i => c i.castSucc) (c (Fin.last κ))
          : Fin (κ + 1) → Bool) (Fin.last κ) = c (Fin.last κ)
      rw [Fin.snoc_last]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      show (Fin.snoc p.1 p.2 : Fin (κ + 1) → Bool) i.castSucc = p.1 i
      rw [Fin.snoc_castSucc]
    · show (Fin.snoc p.1 p.2 : Fin (κ + 1) → Bool) (Fin.last κ) = p.2
      rw [Fin.snoc_last]

theorem snocEquiv_symm_castSucc {κ : ℕ} (p : Fin κ → Bool) (b : Bool)
    (j : Fin κ) : ((snocEquiv κ).symm (p, b)) j.castSucc = p j := by
  show (Fin.snoc p b : Fin (κ + 1) → Bool) j.castSucc = p j
  rw [Fin.snoc_castSucc]

theorem snocEquiv_symm_last {κ : ℕ} (p : Fin κ → Bool) (b : Bool) :
    ((snocEquiv κ).symm (p, b)) (Fin.last κ) = b := by
  show (Fin.snoc p b : Fin (κ + 1) → Bool) (Fin.last κ) = b
  rw [Fin.snoc_last]

theorem restrict_snoc {κ : ℕ} (p : Fin κ → Bool) (b : Bool) (j : ℕ)
    (hj : j ≤ κ) (hj' : j ≤ κ + 1) :
    restrict ((snocEquiv κ).symm (p, b)) j hj' = restrict p j hj := by
  funext i
  show ((snocEquiv κ).symm (p, b)) ⟨(i : ℕ), by omega⟩ = p ⟨(i : ℕ), by omega⟩
  have h1 : (⟨(i : ℕ), by omega⟩ : Fin (κ + 1))
      = (⟨(i : ℕ), by omega⟩ : Fin κ).castSucc := rfl
  rw [h1, snocEquiv_symm_castSucc]

theorem sum_coinWt {κ : ℕ} {W : (j : ℕ) → (Fin j → Bool) → Bool → ℝ}
    (hsum : ∀ j p, W j p true + W j p false = 1) :
    ∑ c : Fin κ → Bool, coinWt W c = 1 := by
  induction κ with
  | zero =>
    haveI : Subsingleton (Fin 0 → Bool) :=
      ⟨fun a b => funext fun i => i.elim0⟩
    rw [Fintype.sum_subsingleton _ (fun i : Fin 0 => true)]
    unfold coinWt
    rw [Finset.univ_eq_empty, Finset.prod_empty]
  | succ κ ih =>
    rw [← Equiv.sum_comp (snocEquiv κ).symm (coinWt W)]
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ (p : Fin κ → Bool) (b : Bool),
        coinWt W ((snocEquiv κ).symm (p, b))
          = coinWt W p * W κ p b := by
      intro p b
      unfold coinWt
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun j _ => ?_
        show W (j : ℕ) (restrict ((snocEquiv κ).symm (p, b)) (j : ℕ)
            (by omega)) (((snocEquiv κ).symm (p, b)) j.castSucc) = _
        rw [restrict_snoc p b (j : ℕ) (le_of_lt j.isLt) (by omega),
          snocEquiv_symm_castSucc]
      · show W κ (restrict ((snocEquiv κ).symm (p, b)) κ (by omega))
            (((snocEquiv κ).symm (p, b)) (Fin.last κ)) = _
        rw [restrict_snoc p b κ (le_refl κ) (by omega), snocEquiv_symm_last]
        congr 1
    calc ∑ p : Fin κ → Bool, ∑ b : Bool, coinWt W ((snocEquiv κ).symm (p, b))
        = ∑ p : Fin κ → Bool, coinWt W p * (W κ p true + W κ p false) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [show (Finset.univ : Finset Bool) = {true, false} by rfl]
          rw [Finset.sum_insert (by simp), Finset.sum_singleton,
            hsplit p true, hsplit p false]
          ring
      _ = ∑ p : Fin κ → Bool, coinWt W p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hsum κ p, mul_one]
      _ = 1 := ih

end Race

end KServer


