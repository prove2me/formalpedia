-- Prove2me | Definitions.Def_BCFGJPSSV26_Combine_Analysis
-- name    : BCFGJPSSV26_Combine_Analysis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:13:13.992412+00:00
-- url     : https://prove2.me/theorems/161c2adb-9eeb-4813-b00d-daedc094031c
-- title:
--   BCFGJPSSV26.Combine.Analysis — The analysis of the algorithm of Theorem 1.1
-- statement:
--   This is module `BCFGJPSSV26.Combine.Analysis` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   * **Optima** (`BCFGJPSSV26.Combine.opt_k₀_le`): no more than `m` facilities are ever open, so
--     `opt (min(k, m)) ≤ opt k`.
--   * **A stable number of centers** (`BCFGJPSSV26.Combine.exists_stable`), the argument of
--     [BCFGJPSSV26a, Section 1.1, step (ii)]: if `opt (k - c) > (1 + ε) opt k`, then some
--     `k' ∈ (k - c, k]` has `opt (k' - 1) ≥ ρ opt k'` (or `k' = 1`) and `opt k' ≤ (1 + ε) opt k`,
--     whenever `ρ^c ≤ 1 + ε`: otherwise `opt (k - c) < ρ^c opt k`. With `ρ = 1 + 1/(M c)`,
--     `ρ^c ≤ e^(1/M) ≤ M/(M - 1)` (`BCFGJPSSV26.Combine.one_add_pow_le`).
--   * **Coins** (`BCFGJPSSV26.Combine.coinProb_window`): an event about one block of the coins has
--     the probability it has on that block alone.
--
--   **Contents.** The module is published as a whole: 9 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Combine_Analysis`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Combine/Analysis.lean

module

public import Definitions.Def_BCFGJPSSV26_Combine_Algorithm
public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Combine.Analysis` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The analysis of the algorithm of Theorem 1.1

* **Optima** (`BCFGJPSSV26.Combine.opt_k₀_le`): no more than `m` facilities are ever open, so
  `opt (min(k, m)) ≤ opt k`.
* **A stable number of centers** (`BCFGJPSSV26.Combine.exists_stable`), the argument of
  [BCFGJPSSV26a, Section 1.1, step (ii)]: if `opt (k - c) > (1 + ε) opt k`, then some
  `k' ∈ (k - c, k]` has `opt (k' - 1) ≥ ρ opt k'` (or `k' = 1`) and `opt k' ≤ (1 + ε) opt k`,
  whenever `ρ^c ≤ 1 + ε`: otherwise `opt (k - c) < ρ^c opt k`. With `ρ = 1 + 1/(M c)`,
  `ρ^c ≤ e^(1/M) ≤ M/(M - 1)` (`BCFGJPSSV26.Combine.one_add_pow_le`).
* **Coins** (`BCFGJPSSV26.Combine.coinProb_window`): an event about one block of the coins has
  the probability it has on that block alone.
-/

@[expose] public section

namespace BCFGJPSSV26.Combine

/-! ### Optima -/

theorem cost_nonneg {I : Instance} (hI : I.Valid) (S : Finset (Fin I.m)) : 0 ≤ I.cost S :=
  Finset.sum_nonneg fun _ _ ↦ Real.iInf_nonneg fun _ ↦ by
    unfold Instance.dist
    exact_mod_cast hI.nonneg _ _

theorem opt_nonneg {I : Instance} (hI : I.Valid) (ℓ : ℕ) : 0 ≤ I.opt ℓ :=
  Real.iInf_nonneg fun S ↦ cost_nonneg hI S.1

/-- **At most `m` facilities are open**, so `opt (min(k, m)) ≤ opt k`. -/
theorem opt_k₀_le {I : Instance} (hI : I.Valid) : I.opt (k₀ I) ≤ I.opt I.k := by
  have : Nonempty {S : Finset (Fin I.m) // S.Nonempty ∧ S.card ≤ I.k} :=
    ⟨⟨{⟨0, hI.one_le_m⟩}, by simp, by simpa using hI.one_le_k⟩⟩
  refine le_ciInf fun S ↦ ?_
  have hS : S.1.Nonempty ∧ S.1.card ≤ k₀ I :=
    ⟨S.2.1, le_min S.2.2 (by simpa using S.1.card_le_univ)⟩
  have hbdd : BddBelow (Set.range fun S : {S : Finset (Fin I.m) // S.Nonempty ∧
      S.card ≤ k₀ I} ↦ I.cost S.1) := ⟨0, by rintro _ ⟨S, rfl⟩; exact cost_nonneg hI _⟩
  exact ciInf_le hbdd ⟨S.1, hS⟩

/-! ### A stable number of centers -/

/-- If no `k₀ - i` for `i < j` is stable, the optimum grows by at most `ρ` at each step. -/
theorem opt_le_pow (O : ℕ → ℝ) {k₀ : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ j, (∀ i < j, ¬ (2 ≤ k₀ - i → ρ * O (k₀ - i) ≤ O (k₀ - i - 1))) →
      O (k₀ - j) ≤ ρ ^ j * O k₀
  | 0, _ => by simp
  | j + 1, h => by
    have ih := opt_le_pow O hρ j fun i hi ↦ h i (by omega)
    have hj := h j (by omega)
    push Not at hj
    obtain ⟨-, hlt⟩ := hj
    rw [show k₀ - (j + 1) = k₀ - j - 1 by omega, pow_succ']
    calc O (k₀ - j - 1) ≤ ρ * O (k₀ - j) := hlt.le
      _ ≤ ρ * (ρ ^ j * O k₀) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ * ρ ^ j * O k₀ := by ring

/-- **A stable number of centers.** Unless `k₀ > c` and `opt (k₀ - c) ≤ (1 + ε) opt k₀`, some
`k₀ - j` with `j < min(c, k₀)` is stable with factor `ρ` and has `opt (k₀ - j) ≤ (1 + ε) opt k₀`,
when `ρ^c ≤ 1 + ε`. -/
theorem exists_stable (O : ℕ → ℝ) {k₀ c : ℕ} {ρ ε : ℝ} (hk₀ : 1 ≤ k₀) (hρ : 1 ≤ ρ)
    (hρc : ρ ^ c ≤ 1 + ε) (hO : 0 ≤ O k₀) (hA : ¬ (c < k₀ ∧ O (k₀ - c) ≤ (1 + ε) * O k₀)) :
    ∃ j < min c k₀, (2 ≤ k₀ - j → ρ * O (k₀ - j) ≤ O (k₀ - j - 1)) ∧
      O (k₀ - j) ≤ (1 + ε) * O k₀ := by
  classical
  have hex : ∃ j, j < min c k₀ ∧ (2 ≤ k₀ - j → ρ * O (k₀ - j) ≤ O (k₀ - j - 1)) := by
    by_contra hno
    push Not at hno
    rcases le_or_gt k₀ c with hkc | hck
    · obtain ⟨h2, -⟩ := hno (k₀ - 1) (by omega)
      omega
    · have h := opt_le_pow O (k₀ := k₀) (ρ := ρ) (by linarith) c fun i hi ↦ by
        have := hno i (by omega)
        push Not
        exact this
      exact hA ⟨hck, h.trans (mul_le_mul_of_nonneg_right hρc hO)⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  have h := opt_le_pow O (k₀ := k₀) (ρ := ρ) (by linarith) (Nat.find hex) fun i hi hs ↦
    Nat.find_min hex hi ⟨by have := (Nat.find_spec hex).1; omega, hs⟩
  have hle : ρ ^ Nat.find hex ≤ ρ ^ c :=
    pow_le_pow_right₀ hρ (by have := (Nat.find_spec hex).1; omega)
  exact h.trans (mul_le_mul_of_nonneg_right (hle.trans hρc) hO)

/-- **`(1 + 1/(M c))^c ≤ M/(M - 1)`**: it is at most `e^(1/M)`. -/
theorem one_add_pow_le {M c : ℕ} (hM : 2 ≤ M) (hc : 1 ≤ c) :
    (1 + 1 / ((M * c : ℕ) : ℝ)) ^ c ≤ 1 / (1 - 1 / (M : ℝ)) := by
  have hMc : (0 : ℝ) < ((M * c : ℕ) : ℝ) := by
    have : 1 ≤ M * c := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have h1 : 1 + 1 / ((M * c : ℕ) : ℝ) ≤ Real.exp (1 / ((M * c : ℕ) : ℝ)) := by
    linarith [Real.add_one_le_exp (1 / ((M * c : ℕ) : ℝ))]
  calc (1 + 1 / ((M * c : ℕ) : ℝ)) ^ c ≤ Real.exp (1 / ((M * c : ℕ) : ℝ)) ^ c :=
        pow_le_pow_left₀ (by positivity) h1 c
    _ = Real.exp (1 / (M : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
        push_cast
        field_simp
    _ ≤ 1 / (1 - 1 / (M : ℝ)) := by
        refine Real.exp_bound_div_one_sub_of_interval (by positivity) ?_
        have : (2 : ℝ) ≤ M := by exact_mod_cast hM
        rw [div_lt_one (by linarith)]
        linarith

/-! ### Coins -/

theorem coinProb_mono {N : ℕ} {P Q : List Bool → Prop} (h : ∀ r, P r → Q r) :
    coinProb N P ≤ coinProb N Q := by
  classical
  unfold coinProb
  gcongr
  exact Fintype.card_subtype_mono _ _ fun r ↦ h _

theorem coinProb_of_forall {N : ℕ} {P : List Bool → Prop} (h : ∀ r, P r) : coinProb N P = 1 := by
  classical
  unfold coinProb
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv fun r ↦ h (List.ofFn r))]
  simp

/-- **An event about one block of the coins** has the probability it has on that block. -/
theorem coinProb_window {N o T : ℕ} (P : List Bool → Prop) (h : o + T ≤ N) :
    coinProb N (fun r ↦ P ((r.drop o).take T)) = coinProb T P := by
  classical
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold coinProb
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Encoding.natCard_window]
  push_cast
  rw [pow_add, pow_add, pow_add]
  field_simp

end BCFGJPSSV26.Combine


