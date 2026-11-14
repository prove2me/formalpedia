-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
-- name    : BCFGJPSSV26_Stable_Alg_Trial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:19:28.668085+00:00
-- url     : https://prove2.me/theorems/d44a1937-a672-405c-9186-cfe531bec4dd
-- title:
--   BCFGJPSSV26.Stable.Alg.Trial — One trial
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.Trial` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   A trial (`BCFGJPSSV26.Stable.trial`) reads `Ctr = 6 s + M₂ + k` chunks: the client sampling reads
--   the first `6 s`, the cluster sampling the next `M₂`, and the coloring of the kept centers the last
--   `k`; it returns the candidates of all guesses `p' ≤ s`
--   (`BCFGJPSSV26.Stable.trialCands`).
--
--   A trial is **good** (`BCFGJPSSV26.Stable.TrialGood`) if the local search or one of its candidates,
--   made into `k` facilities by `BCFGJPSSV26.sanitizeK`, costs at most `(1.89 + 1000/N) opt`
--   (`BCFGJPSSV26.Stable.bound`).
--
--   * `BCFGJPSSV26.Stable.Hyp.trialCands_good` ([BCFGJPSSV26b, Section 3.5]): if the client sampling
--     and the cluster sampling give good outcomes and the coloring satisfies the color event of a
--     partition, the candidate of the guess `|O_P|` exists and the local search or it is within the
--     bound, by `BCFGJPSSV26.Stable.Partition.costF_candidate_le`,
--     `BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS` and
--     `BCFGJPSSV26.Stable.Partition.min_le_bound`.
--   * `BCFGJPSSV26.Stable.Hyp.card_trialGood`: at least `q K^Ctr` chunk vectors give a good trial,
--     `q = N^(-200 s)`, by `BCFGJPSSV26.Stable.card_append_ge` from the process lemmas of the two
--     samplings and the color coding.
--
--   **Contents.** The module is published as a whole: 9 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Hyp.card_trialGood` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Trial.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClientSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.Trial` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# One trial

A trial (`BCFGJPSSV26.Stable.trial`) reads `Ctr = 6 s + M₂ + k` chunks: the client sampling reads
the first `6 s`, the cluster sampling the next `M₂`, and the coloring of the kept centers the last
`k`; it returns the candidates of all guesses `p' ≤ s`
(`BCFGJPSSV26.Stable.trialCands`).

A trial is **good** (`BCFGJPSSV26.Stable.TrialGood`) if the local search or one of its candidates,
made into `k` facilities by `BCFGJPSSV26.sanitizeK`, costs at most `(1.89 + 1000/N) opt`
(`BCFGJPSSV26.Stable.bound`).

* `BCFGJPSSV26.Stable.Hyp.trialCands_good` ([BCFGJPSSV26b, Section 3.5]): if the client sampling
  and the cluster sampling give good outcomes and the coloring satisfies the color event of a
  partition, the candidate of the guess `|O_P|` exists and the local search or it is within the
  bound, by `BCFGJPSSV26.Stable.Partition.costF_candidate_le`,
  `BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS` and
  `BCFGJPSSV26.Stable.Partition.min_le_bound`.
* `BCFGJPSSV26.Stable.Hyp.card_trialGood`: at least `q K^Ctr` chunk vectors give a good trial,
  `q = N^(-200 s)`, by `BCFGJPSSV26.Stable.card_append_ge` from the process lemmas of the two
  samplings and the color coding.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- The candidates of a trial, from the chunks of its three parts. -/
def trialCands (N : ℕ) (x : Raw) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch₁ ch₂ ch₃ : ℕ → ℕ) :
    List (List ℕ) :=
  let s := Par.s N L
  let b := Par.bits N (encRaw x).length
  let Λ₁ := csRun N x LS s b ch₁
  let st := ksRun N x LS Λ₁ s b ch₂
  let LS' := ksLS' LS st
  (List.range (s + 1)).filterMap fun p' ↦
    candidate N x s B LS' (Λ₁ ++ st.dums) (colors b LS' ch₃) p'

/-- **A trial**, reading its chunks through `ch`. -/
def trial (N : ℕ) (x : Raw) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) : List (List ℕ) :=
  trialCands N x L LS B (window ch 0 (6 * Par.s N L)) (window ch (6 * Par.s N L) (Par.M₂ N L))
    (window ch (6 * Par.s N L + Par.M₂ N L) x.k)

/-- The bound of the main theorem: `(1.89 + 1000/N) opt k`. -/
noncomputable def bound (P : Prm) (I : Instance) : ℝ := (1.89 + 1000 / P.N) * I.opt I.k

/-- **A good trial**: the local search or a candidate is within the bound. -/
def TrialGood (P : Prm) (I : Instance) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) : Prop :=
  ∃ T ∈ LS :: trial P.N (toRaw I) L LS B ch, I.costF (I.centers (sanitizeK I.m I.k T)) ≤ bound P I

/-- A trial reads only its `Ctr` chunks. -/
theorem trial_window (N : ℕ) (x : Raw) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) :
    trial N x L LS B (window ch 0 (Par.Ctr N L x.k)) = trial N x L LS B ch := by
  unfold trial
  rw [window_window ch (o := 0) (M := Par.Ctr N L x.k) (o' := 0) (M' := 6 * Par.s N L)
      (by unfold Par.Ctr; omega),
    window_window ch (o := 0) (M := Par.Ctr N L x.k) (o' := 6 * Par.s N L) (M' := Par.M₂ N L)
      (by unfold Par.Ctr; omega),
    window_window ch (o := 0) (M := Par.Ctr N L x.k) (o' := 6 * Par.s N L + Par.M₂ N L)
      (M' := x.k) (by unfold Par.Ctr; omega)]
  simp only [zero_add]

/-- A trial on a vector of chunks reads its three parts. -/
theorem trial_toCh (N : ℕ) (I : Instance) (L : ℕ) (LS : List ℕ) (B : ℕ) {K : ℕ}
    (z : Fin (Par.Ctr N L I.k) → Fin K) :
    trial N (toRaw I) L LS B (toCh z) = trialCands N (toRaw I) L LS B
      (toCh fun i ↦ z (Fin.castAdd _ (Fin.castAdd _ i)))
      (toCh fun i ↦ z (Fin.castAdd _ (Fin.natAdd _ i)))
      (toCh fun i ↦ z (Fin.natAdd _ i)) := by
  unfold trial
  have h₀ : window (toCh z) 0 (6 * Par.s N L + Par.M₂ N L) =
      toCh fun i ↦ z (Fin.castAdd I.k i) := window_toCh_castAdd z
  have h₁ : window (toCh z) 0 (6 * Par.s N L) =
      toCh fun i ↦ z (Fin.castAdd _ (Fin.castAdd _ i)) := by
    have := window_window (toCh z) (o := 0) (M := 6 * Par.s N L + Par.M₂ N L) (o' := 0)
      (M' := 6 * Par.s N L) (by omega)
    rw [zero_add] at this
    rw [← this, h₀, window_toCh_castAdd]
  have h₂ : window (toCh z) (6 * Par.s N L) (Par.M₂ N L) =
      toCh fun i ↦ z (Fin.castAdd _ (Fin.natAdd _ i)) := by
    have := window_window (toCh z) (o := 0) (M := 6 * Par.s N L + Par.M₂ N L)
      (o' := 6 * Par.s N L) (M' := Par.M₂ N L) le_rfl
    rw [zero_add] at this
    rw [← this, h₀, window_toCh_natAdd]
  have h₃ : window (toCh z) (6 * Par.s N L + Par.M₂ N L) I.k =
      toCh fun i ↦ z (Fin.natAdd _ i) := window_toCh_natAdd z
  rw [h₁, h₂, Raw.k_toRaw, h₃]

namespace Ctx

variable (X : Ctx)

/-- The outcome of the client sampling on the chunks `ch`. -/
def csOut (LS : List ℕ) (ch : ℕ → ℕ) : List DumQ := csRun X.P.N (toRaw X.I) LS X.s X.b ch

/-- The final state of the cluster sampling on the chunks `ch₁`, `ch₂`. -/
def ksOut (LS : List ℕ) (ch₁ ch₂ : ℕ → ℕ) : KSState :=
  ksRun X.P.N (toRaw X.I) LS (X.csOut LS ch₁) X.s X.b ch₂

end Ctx

/-- The per-trial success probability is at most the product of those of the parts. -/
theorem Hyp.q_le_prod {X : Ctx} (H : Hyp X) :
    X.P.q X.L ≤ X.P.q₁ ^ (2 * X.s) * X.P.q₂ ^ Par.M₂ X.P.N X.L * (1 / 4) ^ X.s := by
  have hN := X.P.N_ge
  have hN0 := X.P.N_pos'
  have hs : 1 ≤ Par.s X.P.N X.L :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) X.P.N_pos) H.one_le_L
  have h₁ : 1 / (X.P.N : ℝ) ^ 10 ≤ X.P.q₁ := by
    unfold Prm.q₁
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (440 : ℝ) ≤ (X.P.N : ℝ) ^ 2 := by nlinarith
    calc 440 * (X.P.N : ℝ) ^ 8 ≤ (X.P.N : ℝ) ^ 2 * (X.P.N : ℝ) ^ 8 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (X.P.N : ℝ) ^ 10 := by ring
  have h₂ : 1 / (X.P.N : ℝ) ^ 4 ≤ X.P.q₂ := by
    unfold Prm.q₂
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc 12 * (X.P.N : ℝ) ^ 3 ≤ (X.P.N : ℝ) * (X.P.N : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (X.P.N : ℝ) ^ 4 := by ring
  have h₃ : 1 / (X.P.N : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hq₁ : 0 ≤ X.P.q₁ := le_trans (by positivity) h₁
  have hq₂ : 0 ≤ X.P.q₂ := le_trans (by positivity) h₂
  have hexp : 10 * (2 * X.s) + 4 * Par.M₂ X.P.N X.L + X.s ≤ 200 * X.s := by
    change 10 * (2 * Par.s X.P.N X.L) + 4 * (20 * Par.s X.P.N X.L + 20) + Par.s X.P.N X.L ≤
      200 * Par.s X.P.N X.L
    omega
  calc X.P.q X.L = 1 / (X.P.N : ℝ) ^ (200 * X.s) := rfl
    _ ≤ 1 / (X.P.N : ℝ) ^ (10 * (2 * X.s) + 4 * Par.M₂ X.P.N X.L + X.s) :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ (by linarith) hexp)
    _ = (1 / (X.P.N : ℝ) ^ 10) ^ (2 * X.s) * (1 / (X.P.N : ℝ) ^ 4) ^ Par.M₂ X.P.N X.L *
          (1 / (X.P.N : ℝ)) ^ X.s := by
        ring
    _ ≤ _ :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) h₁ _)
          (pow_le_pow_left₀ (by positivity) h₂ _) (by positivity) (pow_nonneg hq₁ _))
          (pow_le_pow_left₀ (by positivity) h₃ _) (by positivity)
          (mul_nonneg (pow_nonneg hq₁ _) (pow_nonneg hq₂ _))

end BCFGJPSSV26.Stable


