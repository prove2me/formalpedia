-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
-- name    : BCFGJPSSV26_Stable_Alg_Mixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:47.198337+00:00
-- url     : https://prove2.me/theorems/b5b56a5f-aba7-4105-87d9-7d4e25c5a57f
-- title:
--   BCFGJPSSV26.Stable.Alg.Mixed — Exact dummies and mixed sets
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.Mixed` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The algorithm's dummies are pairs `(ℓ, r)` of a point number (client `j`, or `n + i` for
--   facility `i`) and a rational radius (`BCFGJPSSV26.Stable.DumQ`). Over the exact table
--   (`BCFGJPSSV26.Raw`) the algorithm computes the distance to a list of dummies, `dMaxQ` for the empty
--   list (`BCFGJPSSV26.Raw.dDumsQ`), the distance to a mixed set (`BCFGJPSSV26.Raw.dMixQ`), its
--   clusters (`BCFGJPSSV26.Raw.clusterMixQ`) and costs (`BCFGJPSSV26.Raw.costMixOnQ`), and the balls
--   (`BCFGJPSSV26.Raw.ballQ`). They agree with the real notions of `BCFGJPSSV26/Stable/Dummy.lean` on
--   the dummies `BCFGJPSSV26.Stable.toDums I Λ` when all leaders are points of `I`
--   (`BCFGJPSSV26.Raw.ValidDums`).
--
--   Radii are taken from the grid `r₀ N⁻³ ((N + 1)/N)^x`, `x < 10 N² + 1`
--   (`BCFGJPSSV26.Stable.grid`), which covers `[ε³ r₀, ε⁻⁷ r₀]` with consecutive ratio `1 + ε`
--   (`BCFGJPSSV26.Stable.exists_grid_mem`).
--
--   **Contents.** The module is published as a whole: 20 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Mixed.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Dummy
public import Definitions.Def_BCFGJPSSV26_Stable_Params

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.Mixed` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Exact dummies and mixed sets

The algorithm's dummies are pairs `(ℓ, r)` of a point number (client `j`, or `n + i` for
facility `i`) and a rational radius (`BCFGJPSSV26.Stable.DumQ`). Over the exact table
(`BCFGJPSSV26.Raw`) the algorithm computes the distance to a list of dummies, `dMaxQ` for the empty
list (`BCFGJPSSV26.Raw.dDumsQ`), the distance to a mixed set (`BCFGJPSSV26.Raw.dMixQ`), its
clusters (`BCFGJPSSV26.Raw.clusterMixQ`) and costs (`BCFGJPSSV26.Raw.costMixOnQ`), and the balls
(`BCFGJPSSV26.Raw.ballQ`). They agree with the real notions of `BCFGJPSSV26/Stable/Dummy.lean` on
the dummies `BCFGJPSSV26.Stable.toDums I Λ` when all leaders are points of `I`
(`BCFGJPSSV26.Raw.ValidDums`).

Radii are taken from the grid `r₀ N⁻³ ((N + 1)/N)^x`, `x < 10 N² + 1`
(`BCFGJPSSV26.Stable.grid`), which covers `[ε³ r₀, ε⁻⁷ r₀]` with consecutive ratio `1 + ε`
(`BCFGJPSSV26.Stable.exists_grid_mem`).
-/

@[expose] public section

namespace BCFGJPSSV26

open Finset

namespace Stable

/-- An exact dummy: the number of its leader and its radius. -/
abbrev DumQ : Type := ℕ × ℚ

/-- The radius grid: `r₀ N⁻³ ((N + 1)/N)^x`. -/
def grid (N : ℕ) (r₀ : ℚ) (x : ℕ) : ℚ := r₀ / (N : ℚ) ^ 3 * (((N : ℚ) + 1) / N) ^ x

/-- **The grid is fine enough**: every `d ∈ [ε³ r₀, ε⁻⁷ r₀ / (1 + ε)]` has a grid point in
`[d, (1 + ε) d]`, for `r₀ > 0`. -/
theorem exists_grid_mem {N : ℕ} (hN : 2 ≤ N) {r₀ d : ℝ} (hr₀ : 0 < r₀)
    (hd : r₀ / (N : ℝ) ^ 3 ≤ d) (hd' : (1 + 1 / (N : ℝ)) * d ≤ (N : ℝ) ^ 7 * r₀) (q₀ : ℚ)
    (hq : (q₀ : ℝ) = r₀) :
    ∃ x < Par.Gr N, d ≤ (grid N q₀ x : ℝ) ∧ (grid N q₀ x : ℝ) ≤ (1 + 1 / (N : ℝ)) * d := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set ρ : ℝ := 1 + 1 / (N : ℝ) with hρ
  have hinv : 0 ≤ 1 / (N : ℝ) := by positivity
  have hρ1 : 1 ≤ ρ := by linarith
  have hg : ∀ x, (grid N q₀ x : ℝ) = r₀ / (N : ℝ) ^ 3 * ρ ^ x := by
    intro x
    unfold grid
    push_cast
    rw [hq, hρ]
    congr 2
    field_simp
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hbig : (N : ℝ) ^ 10 ≤ ρ ^ (10 * N ^ 2) := by
    have h1 : (2 : ℝ) ≤ ρ ^ N := by
      have := one_add_mul_le_pow (a := 1 / (N : ℝ)) (by linarith) N
      rw [mul_one_div_cancel hN0.ne'] at this
      linarith
    have h2 : (N : ℝ) ≤ 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self.le
    calc (N : ℝ) ^ 10 ≤ (2 ^ N) ^ 10 := pow_le_pow_left₀ hN0.le h2 10
      _ = 2 ^ (10 * N) := by rw [← pow_mul, mul_comm]
      _ ≤ (ρ ^ N) ^ (10 * N) := pow_le_pow_left₀ (by norm_num) h1 _
      _ = ρ ^ (10 * N ^ 2) := by rw [← pow_mul]; ring_nf
  have h10 : d ≤ (grid N q₀ (10 * N ^ 2) : ℝ) := by
    rw [hg]
    have h1 : d ≤ ρ * d := le_mul_of_one_le_left hd0.le hρ1
    have h2 : (N : ℝ) ^ 7 * r₀ = r₀ / (N : ℝ) ^ 3 * (N : ℝ) ^ 10 := by
      field_simp
    have h3 : r₀ / (N : ℝ) ^ 3 * (N : ℝ) ^ 10 ≤ r₀ / (N : ℝ) ^ 3 * ρ ^ (10 * N ^ 2) :=
      mul_le_mul_of_nonneg_left hbig (by positivity)
    linarith
  have hex : ∃ x, d ≤ (grid N q₀ x : ℝ) := ⟨_, h10⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · have := Nat.find_min' hex h10
    unfold Par.Gr
    omega
  · rcases hx : Nat.find hex with _ | x
    · rw [hg, pow_zero, mul_one]
      exact hd.trans (le_mul_of_one_le_left hd0.le hρ1)
    · have hlt : ¬ d ≤ (grid N q₀ x : ℝ) := Nat.find_min hex (by omega)
      rw [hg] at hlt ⊢
      push Not at hlt
      rw [pow_succ]
      calc r₀ / (N : ℝ) ^ 3 * (ρ ^ x * ρ) = (r₀ / (N : ℝ) ^ 3 * ρ ^ x) * ρ := by ring
        _ ≤ d * ρ := mul_le_mul_of_nonneg_right hlt.le (by linarith)
        _ = ρ * d := mul_comm _ _

/-- The dummies of an instance given by exact dummies whose leaders are points; the others are
dropped. -/
noncomputable def toDums (I : Instance) (Λ : List DumQ) : List (Dummy I) :=
  Λ.filterMap fun l ↦
    if h : l.1 < I.n + I.m then some ⟨finSumFinEquiv.symm ⟨l.1, h⟩, l.2⟩ else none

theorem toDums_append (I : Instance) (Λ Λ' : List DumQ) :
    toDums I (Λ ++ Λ') = toDums I Λ ++ toDums I Λ' := List.filterMap_append

theorem toDums_nil (I : Instance) : toDums I [] = [] := rfl

theorem toDums_cons {I : Instance} {l : DumQ} (h : l.1 < I.n + I.m) (Λ : List DumQ) :
    toDums I (l :: Λ) = ⟨finSumFinEquiv.symm ⟨l.1, h⟩, l.2⟩ :: toDums I Λ := by
  simp [toDums, h]

/-- The number of the point numbered `l` is `l`. -/
theorem ptIdx_finSumFinEquiv_symm {I : Instance} {l : ℕ} (h : l < I.n + I.m) :
    I.ptIdx (finSumFinEquiv.symm ⟨l, h⟩) = l := by
  rw [Instance.ptIdx_eq, Equiv.apply_symm_apply]

end Stable

namespace Raw

open Stable

/-- All leaders are points. -/
def ValidDums (x : Raw) (Λ : List DumQ) : Prop := ∀ l ∈ Λ, l.1 < x.n + x.m

/-- The distance from the point numbered `a` to the nearest dummy of `Λ`, `dMaxQ` if none. -/
def dDumsQ (x : Raw) (a : ℕ) (Λ : List DumQ) : ℚ :=
  Λ.foldr (fun l acc ↦ min (x.dist a l.1 + l.2) acc) x.dMaxQ

/-- The distance from the point numbered `a` to the mixed set `(F, Λ)`. -/
def dMixQ (x : Raw) (a : ℕ) (F : List ℕ) (Λ : List DumQ) : ℚ := min (x.dSetQ a F) (x.dDumsQ a Λ)

/-- The cluster of `c` in the mixed set `(F, Λ)`: the clients whose nearest facility of `F` is
`c` and that are not strictly nearer to a dummy. -/
def clusterMixQ (x : Raw) (F : List ℕ) (Λ : List DumQ) (c : ℕ) : List ℕ :=
  (List.range x.n).filter fun j ↦ decide (x.nearQ j F = c) && decide (x.dSetQ j F ≤ x.dDumsQ j Λ)

/-- The cost of the clients of `D` in the mixed set `(F, Λ)`. -/
def costMixOnQ (x : Raw) (F : List ℕ) (Λ : List DumQ) (D : List ℕ) : ℚ :=
  (D.map fun j ↦ x.dMixQ j F Λ).sum

/-- The ball of a dummy: the facilities within its radius of its leader. -/
def ballQ (x : Raw) (l : DumQ) : List ℕ :=
  (List.range x.m).filter fun i ↦ decide (x.fdist l.1 i ≤ l.2)

variable {I : Instance}

theorem length_toDums {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ) :
    (toDums I Λ).length = Λ.length := by
  induction Λ with
  | nil => rfl
  | cons l Λ ih =>
    rw [toDums_cons (hΛ l List.mem_cons_self), List.length_cons, List.length_cons,
      ih fun l' hl' ↦ hΛ l' (List.mem_cons_of_mem _ hl')]

/-- **Exact distances to dummies.** -/
theorem dDumsQ_toRaw {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ) (a : I.Pt) :
    ((toRaw I).dDumsQ (I.ptIdx a) Λ : ℝ) = dDums I a (toDums I Λ) := by
  induction Λ with
  | nil => exact dMaxQ_toRaw I
  | cons l Λ ih =>
    have hl : l.1 < I.n + I.m := hΛ l List.mem_cons_self
    rw [toDums_cons hl]
    unfold dDumsQ dDums
    rw [List.foldr_cons, List.foldr_cons]
    have ih' := ih fun l' hl' ↦ hΛ l' (List.mem_cons_of_mem _ hl')
    unfold dDumsQ dDums at ih'
    rw [Rat.cast_min, ih', Rat.cast_add]
    congr 2
    have := dist_toRaw a (finSumFinEquiv.symm ⟨l.1, hl⟩)
    rw [ptIdx_finSumFinEquiv_symm] at this
    unfold Instance.dd
    rw [this]

theorem dMixQ_toRaw {F : List ℕ} (hF : ∀ i ∈ F, i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) (a : I.Pt) :
    ((toRaw I).dMixQ (I.ptIdx a) F Λ : ℝ) = dMix I a (I.centers F) (toDums I Λ) := by
  rw [dMixQ, Rat.cast_min, dSetQ_toRaw a hF, dDumsQ_toRaw hΛ a]
  rfl

theorem mem_clusterMixQ {F : List ℕ} (hF : F ≠ []) (hFm : ∀ i ∈ F, i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) {c : Fin I.m} {j : Fin I.n} :
    j.1 ∈ (toRaw I).clusterMixQ F Λ c ↔ j ∈ clusterMix I (I.centers F) (toDums I Λ) c := by
  classical
  rw [clusterMixQ, List.mem_filter, clusterMix, mem_filter,
    Instance.mem_cluster (Instance.centers_nonempty hF hFm)]
  simp only [List.mem_range, n_toRaw, j.2, true_and, Bool.and_eq_true, decide_eq_true_eq]
  rw [← Instance.ptIdx_inl, nearQ_toRaw _ hF hFm, Fin.val_inj, ← Rat.cast_le (K := ℝ),
    dSetQ_toRaw _ hFm, dDumsQ_toRaw hΛ]

theorem mem_ballQ {l : DumQ} (hl : l.1 < I.n + I.m) {i : Fin I.m} :
    i.1 ∈ (toRaw I).ballQ l ↔
      i ∈ (⟨finSumFinEquiv.symm ⟨l.1, hl⟩, (l.2 : ℝ)⟩ : Dummy I).ball := by
  rw [ballQ, List.mem_filter, Dummy.mem_ball]
  simp only [List.mem_range, m_toRaw, i.2, true_and, decide_eq_true_eq]
  have := dist_toRaw (finSumFinEquiv.symm ⟨l.1, hl⟩) (Sum.inr i)
  rw [ptIdx_finSumFinEquiv_symm, Instance.ptIdx_inr] at this
  rw [← Rat.cast_le (K := ℝ), fdist, n_toRaw, this]
  rfl

/-- If every dummy of `toDums I Λ` has a nonempty ball, every exact ball is nonempty. -/
theorem ballQ_ne_nil {Λ : List DumQ} (hΛ : (toRaw I).ValidDums Λ)
    (h : ∀ l ∈ toDums I Λ, l.ball.Nonempty) : ∀ l ∈ Λ, (toRaw I).ballQ l ≠ [] := by
  intro l hl
  have hl' : l.1 < I.n + I.m := hΛ l hl
  have hmem : (⟨finSumFinEquiv.symm ⟨l.1, hl'⟩, (l.2 : ℝ)⟩ : Dummy I) ∈ toDums I Λ :=
    List.mem_filterMap.2 ⟨l, hl, by simp [hl']⟩
  obtain ⟨i, hi⟩ := h _ hmem
  exact List.ne_nil_of_mem ((mem_ballQ hl').2 hi)

end Raw

end BCFGJPSSV26


