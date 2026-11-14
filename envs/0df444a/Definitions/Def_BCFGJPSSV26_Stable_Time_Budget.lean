-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_Budget
-- name    : BCFGJPSSV26_Stable_Time_Budget
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:58:26.482013+00:00
-- url     : https://prove2.me/theorems/73629cbd-b673-4910-af9d-776077794758
-- title:
--   BCFGJPSSV26.Stable.Time.Budget — The budget and the number of trials
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.Budget` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The arithmetic of the parameters. The budget `B = 2^(e₁ L) (|I| + 2)^(e₁)`,
--   `e₁ = 10⁶ N²` (`BCFGJPSSV26.Stable.Par.budget`) is at least each of
--
--   * `(k m)^p`, so that the local search tries all swaps (`BCFGJPSSV26.Stable.Par.budget_ls₁`);
--   * `2 N k |I| + 2`, so that it makes all its improvements (`BCFGJPSSV26.Stable.Par.budget_ls₂`);
--   * `R = N^(200 s + 1)`, so that all trials run (`BCFGJPSSV26.Stable.Par.R_le_budget`);
--   * `N^s`, so that the greedy enumerates all of `[N]^ρ`, `ρ ≤ s`
--     (`BCFGJPSSV26.Stable.Par.pow_s_le_budget`);
--   * the number `R Ctr b` of coins read (`BCFGJPSSV26.Stable.Par.coinLen_le_budget`).
--
--   The `R` trials, each good with probability at least `q = N^(-200 s)`, all fail with probability
--   at most `(1 - q)^R ≤ e^(-q R) = e^(-N) ≤ 1/N` (`BCFGJPSSV26.Stable.Prm.one_sub_q_pow_le`).
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_Budget`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/Budget.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Params
public import Definitions.Def_BCFGJPSSV26_Combine_Algorithm

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.Budget` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The budget and the number of trials

The arithmetic of the parameters. The budget `B = 2^(e₁ L) (|I| + 2)^(e₁)`,
`e₁ = 10⁶ N²` (`BCFGJPSSV26.Stable.Par.budget`) is at least each of

* `(k m)^p`, so that the local search tries all swaps (`BCFGJPSSV26.Stable.Par.budget_ls₁`);
* `2 N k |I| + 2`, so that it makes all its improvements (`BCFGJPSSV26.Stable.Par.budget_ls₂`);
* `R = N^(200 s + 1)`, so that all trials run (`BCFGJPSSV26.Stable.Par.R_le_budget`);
* `N^s`, so that the greedy enumerates all of `[N]^ρ`, `ρ ≤ s`
  (`BCFGJPSSV26.Stable.Par.pow_s_le_budget`);
* the number `R Ctr b` of coins read (`BCFGJPSSV26.Stable.Par.coinLen_le_budget`).

The `R` trials, each good with probability at least `q = N^(-200 s)`, all fail with probability
at most `(1 - q)^R ≤ e^(-q R) = e^(-N) ≤ 1/N` (`BCFGJPSSV26.Stable.Prm.one_sub_q_pow_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

namespace Par

variable {I : Instance} {N L : ℕ}

/-- The facilities are at most the length of the encoding: the table has a row for each. -/
private theorem m_le_length (I : Instance) : I.m ≤ (encInstance I).length := by
  have h : (distTable I).length ≤ (Encoding.encList (Encoding.encList Encoding.encRat)
      (distTable I)).length :=
    Turing.MultiTapeTM.length_le_length_encList _ _
  have hlen : (distTable I).length = I.n + I.m := by simp [distTable]
  rw [Combine.length_encInstance]
  omega

/-- A bound `2^a (|I| + 2)^c` with `a ≤ 10⁶ N² L` and `c ≤ 10⁶ N` is within the budget. -/
private theorem le_budget {A a c : ℕ} (h : A ≤ 2 ^ a * ((encInstance I).length + 2) ^ c)
    (ha : a ≤ 10 ^ 6 * (N ^ 2 * L)) (hc : c ≤ 10 ^ 6 * N) : A ≤ budget N I L := by
  have hN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
  unfold budget stableTime e₁
  refine h.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) ?_)
    (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [mul_assoc]
  exact ha

private theorem two_pow_le (ℓ c : ℕ) : 2 ^ c ≤ (ℓ + 2) ^ c :=
  Nat.pow_le_pow_left (by omega) c

private theorem le_pow_self (ℓ c : ℕ) : c ≤ (ℓ + 2) ^ c :=
  Nat.lt_two_pow_self.le.trans (two_pow_le ℓ c)

/-- `N ≤ 2^N`, so `N^a ≤ 2^(N a)`. -/
private theorem pow_le_two_pow (N a : ℕ) : N ^ a ≤ 2 ^ (N * a) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le a

theorem budget_ls₁ (hk : I.k ≤ I.m) (hN : 1 ≤ N) : (I.k * I.m) ^ p N ≤ budget N I L := by
  have hm := m_le_length I
  set ℓ := (encInstance I).length
  refine le_budget (a := 0) (c := 2 * p N) ?_ (Nat.zero_le _) (by unfold p; omega)
  rw [pow_zero, one_mul, pow_mul]
  refine Nat.pow_le_pow_left ?_ _
  rw [sq]
  exact Nat.mul_le_mul (by omega) (by omega)

theorem budget_ls₂ (hk : I.k ≤ I.m) (hN : 1 ≤ N) :
    2 * N * I.k * (encInstance I).length + 2 ≤ budget N I L := by
  have hm := m_le_length I
  set ℓ := (encInstance I).length
  refine le_budget (a := 0) (c := 2 * N + 2) ?_ (Nat.zero_le _) (by omega)
  rw [pow_zero, one_mul, pow_add]
  have h1 : I.k * ℓ ≤ ℓ * ℓ := Nat.mul_le_mul_right _ (by omega)
  have h2 : N * (I.k * ℓ) ≤ N * (ℓ * ℓ) := Nat.mul_le_mul_left _ h1
  calc 2 * N * I.k * ℓ + 2 ≤ (2 * N) * (ℓ + 2) ^ 2 := by
        have : (ℓ + 2) ^ 2 = ℓ * ℓ + 4 * ℓ + 4 := by ring
        rw [this]
        nlinarith
    _ ≤ (ℓ + 2) ^ (2 * N) * (ℓ + 2) ^ 2 := Nat.mul_le_mul_right _ (le_pow_self ℓ _)

theorem R_le_budget (hN : 1 ≤ N) : R N L ≤ budget N I L := by
  set ℓ := (encInstance I).length
  refine le_budget (a := N * (200 * s N L)) (c := N) ?_ ?_ (by omega)
  · unfold R
    refine (pow_le_two_pow N _).trans ?_
    rw [mul_add, mul_one, pow_add]
    exact Nat.mul_le_mul_left _ (two_pow_le ℓ N)
  · have : N * (200 * s N L) = 126400 * (N ^ 2 * L) := by unfold s; ring
    omega

theorem pow_s_le_budget (hN : 1 ≤ N) : N ^ s N L ≤ budget N I L := by
  refine le_budget (a := N * s N L) (c := 0) ?_ ?_ (by omega)
  · rw [pow_zero, mul_one]
    exact pow_le_two_pow N _
  · have : N * s N L = 632 * (N ^ 2 * L) := by unfold s; ring
    omega

theorem coinLen_le_budget (hk : I.k ≤ I.m) (hN : 1 ≤ N) : coinLen N I L ≤ budget N I L := by
  have hm := m_le_length I
  set ℓ := (encInstance I).length
  refine le_budget (a := N * (200 * s N L) + 26 * s N L) (c := N + 5 + (7 * N + 1)) ?_ ?_
    (by omega)
  · unfold coinLen
    have hR : R N L ≤ 2 ^ (N * (200 * s N L)) * (ℓ + 2) ^ N := by
      unfold R
      refine (pow_le_two_pow N _).trans ?_
      rw [mul_add, mul_one, pow_add]
      exact Nat.mul_le_mul_left _ (two_pow_le ℓ N)
    have hC : Ctr N L I.k ≤ 2 ^ (26 * s N L) * (ℓ + 2) ^ 5 := by
      have h1 : 26 * s N L + 1 ≤ 2 ^ (26 * s N L) := Nat.lt_two_pow_self
      have h2 : ℓ + 20 ≤ (ℓ + 2) ^ 5 := by
        have : 2 ≤ ℓ + 2 := by omega
        have h16 : 16 ≤ (ℓ + 2) ^ 4 := by
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ (ℓ + 2) ^ 4 := Nat.pow_le_pow_left this 4
        calc ℓ + 20 ≤ 16 * (ℓ + 2) := by omega
          _ ≤ (ℓ + 2) ^ 4 * (ℓ + 2) := Nat.mul_le_mul_right _ h16
          _ = (ℓ + 2) ^ 5 := by ring
      calc Ctr N L I.k ≤ (26 * s N L + 1) * (ℓ + 20) := by
            unfold Ctr M₂
            nlinarith
        _ ≤ _ := Nat.mul_le_mul h1 h2
    have hb : bits N ℓ ≤ (ℓ + 2) ^ (7 * N + 1) := by
      have h1 : 7 * N ≤ (ℓ + 2) ^ (7 * N) := le_pow_self ℓ _
      calc bits N ℓ ≤ 7 * N * (ℓ + 2) := by unfold bits; nlinarith
        _ ≤ (ℓ + 2) ^ (7 * N) * (ℓ + 2) := Nat.mul_le_mul_right _ h1
        _ = _ := by ring
    calc R N L * Ctr N L I.k * bits N ℓ ≤
        (2 ^ (N * (200 * s N L)) * (ℓ + 2) ^ N) * (2 ^ (26 * s N L) * (ℓ + 2) ^ 5) *
          (ℓ + 2) ^ (7 * N + 1) := Nat.mul_le_mul (Nat.mul_le_mul hR hC) hb
      _ = _ := by ring
  · have : N * (200 * s N L) + 26 * s N L ≤ 142832 * (N ^ 2 * L) := by
      have h : N * L ≤ N ^ 2 * L := Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) N)
      have : N * (200 * s N L) + 26 * s N L = 126400 * (N ^ 2 * L) + 16432 * (N * L) := by
        unfold s; ring
      omega
    omega

end Par

/-- `stableTime` grows with the exponent. -/
theorem stableTime_mono {e e' : ℕ} (h : e ≤ e') (x : Instance × ℕ) :
    stableTime e x ≤ stableTime e' x := by
  unfold stableTime
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h))
    (Nat.pow_le_pow_right (by omega) h)

namespace Prm

variable (P : Prm)

theorem q_nonneg (L : ℕ) : 0 ≤ P.q L := by
  unfold q
  positivity

theorem q_le_one (L : ℕ) : P.q L ≤ 1 := by
  unfold q
  rw [div_le_one (by have := P.N_pos'; positivity)]
  exact one_le_pow₀ (by have := P.N_ge; linarith)

/-- **All trials fail** with probability at most `1/N`. -/
theorem one_sub_q_pow_le (L : ℕ) : (1 - P.q L) ^ Par.R P.N L ≤ 1 / P.N := by
  have hN := P.N_pos'
  have hqR : P.q L * (Par.R P.N L : ℕ) = P.N := by
    unfold q Par.R
    push_cast
    rw [pow_succ]
    field_simp
  calc (1 - P.q L) ^ Par.R P.N L ≤ Real.exp (-P.q L) ^ Par.R P.N L :=
        pow_le_pow_left₀ (by linarith [P.q_le_one L]) (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-P.N) := by
        rw [← Real.exp_nat_mul, mul_neg, mul_comm, hqR]
    _ ≤ 1 / P.N := by
        rw [Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le hN (by linarith [Real.add_one_le_exp (P.N : ℝ)])

end Prm

end BCFGJPSSV26.Stable


