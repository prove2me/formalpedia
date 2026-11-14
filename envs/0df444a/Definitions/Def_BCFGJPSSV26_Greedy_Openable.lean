-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Openable
-- name    : BCFGJPSSV26_Greedy_Openable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:02.845207+00:00
-- url     : https://prove2.me/theorems/8b383fea-855a-4b61-8ab0-6059ecf399fa
-- title:
--   BCFGJPSSV26.Greedy.Openable — Openable facilities and the exact tests
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Openable` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Definitions D.1 and D.2], for a profile `D` (the distances `d(j, S)` of the
--   clients to the open set `S`, capped) at time `θ`. A client `j` is **inactive** if
--   `θ ≥ (1 - δ) D j`, and its value is `mval θ D j = min (θ, (1 - δ) D j)`: `θ` if active,
--   `(1 - δ) d(j, S)` if inactive.
--
--   * **`(1, η)`-openable** (`BCFGJPSSV26.Greedy.Open1`): `∑_j β(mval j, (1 - δ) d(j, i)) ≥ f - n η`.
--   * **`(2, η)`-openable, restricted** (`BCFGJPSSV26.Greedy.Open2`): for some `T ∈ [θ, (1 + ε²) θ]`,
--     the bids `τ_j = mT θ D i T j` satisfy (iii) and (iv). These are the bids
--     `τ_j = min (T, (1 - δ) d(j, S), (1 + ε) θ - d(j, i))` on the active clients of `B(i, εθ)` and
--     `θ` on the other active clients; inactive clients get `(1 - δ) D j`. They satisfy (i), (ii)
--     and (v) of the paper's definition (`BCFGJPSSV26.Greedy.mT_triangle` for (v)), so `Open2` implies
--     the paper's `(2, η)`-openability. This one-parameter family is the one the paper's proofs
--     construct (proofs of [BCFGJPSSV26a, Lemma E.6], step "Increasing θ", and of
--     [BCFGJPSSV26a, Lemma D.11]), and "no facility is `Open2`" is all the analysis uses of maximality
--     (`BCFGJPSSV26.Greedy.noOver_raise`, `BCFGJPSSV26.Greedy.maximal_transfer`). The test is exact
--     and computable (`BCFGJPSSV26.Greedy.test2_iff`): no linear program is solved.
--   * **No overbidding** (`BCFGJPSSV26.Greedy.NoOver`): `∑_j β(mval j, d(j, i₀)) ≤ f` for all `i₀`
--     (the inequality of [BCFGJPSSV26a, Lemma D.9]).
--   * **Candidates** (`BCFGJPSSV26.Greedy.Cand`): [BCFGJPSSV26a, Definition E.5], with respect to the
--     open set itself (which the paper shows equivalent).
--
--   The key lemma (`BCFGJPSSV26.Greedy.key_lemma`) compares the overbidding of `i₀` under the bids of
--   `i` with what `i₀` itself can collect; it gives the restricted pay-to-open lemma
--   (`BCFGJPSSV26.Greedy.payToOpen`, [BCFGJPSSV26a, Lemma D.11]) and the step "increasing `θ`" of
--   [BCFGJPSSV26a, Lemma E.6] (`BCFGJPSSV26.Greedy.noOver_raise`).
--
--   **Contents.** The module is published as a whole: 68 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.key_lemma`, `BCFGJPSSV26.Greedy.maximal_transfer`, `BCFGJPSSV26.Greedy.noOver_raise`, `BCFGJPSSV26.Greedy.test2_iff`, `BCFGJPSSV26.Greedy.testT_iff` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Openable`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Openable.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Space
import Mathlib.Data.Finset.Max

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Openable` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Openable facilities and the exact tests

[BCFGJPSSV26a, Definitions D.1 and D.2], for a profile `D` (the distances `d(j, S)` of the
clients to the open set `S`, capped) at time `θ`. A client `j` is **inactive** if
`θ ≥ (1 - δ) D j`, and its value is `mval θ D j = min (θ, (1 - δ) D j)`: `θ` if active,
`(1 - δ) d(j, S)` if inactive.

* **`(1, η)`-openable** (`BCFGJPSSV26.Greedy.Open1`): `∑_j β(mval j, (1 - δ) d(j, i)) ≥ f - n η`.
* **`(2, η)`-openable, restricted** (`BCFGJPSSV26.Greedy.Open2`): for some `T ∈ [θ, (1 + ε²) θ]`,
  the bids `τ_j = mT θ D i T j` satisfy (iii) and (iv). These are the bids
  `τ_j = min (T, (1 - δ) d(j, S), (1 + ε) θ - d(j, i))` on the active clients of `B(i, εθ)` and
  `θ` on the other active clients; inactive clients get `(1 - δ) D j`. They satisfy (i), (ii)
  and (v) of the paper's definition (`BCFGJPSSV26.Greedy.mT_triangle` for (v)), so `Open2` implies
  the paper's `(2, η)`-openability. This one-parameter family is the one the paper's proofs
  construct (proofs of [BCFGJPSSV26a, Lemma E.6], step "Increasing θ", and of
  [BCFGJPSSV26a, Lemma D.11]), and "no facility is `Open2`" is all the analysis uses of maximality
  (`BCFGJPSSV26.Greedy.noOver_raise`, `BCFGJPSSV26.Greedy.maximal_transfer`). The test is exact
  and computable (`BCFGJPSSV26.Greedy.test2_iff`): no linear program is solved.
* **No overbidding** (`BCFGJPSSV26.Greedy.NoOver`): `∑_j β(mval j, d(j, i₀)) ≤ f` for all `i₀`
  (the inequality of [BCFGJPSSV26a, Lemma D.9]).
* **Candidates** (`BCFGJPSSV26.Greedy.Cand`): [BCFGJPSSV26a, Definition E.5], with respect to the
  open set itself (which the paper shows equivalent).

The key lemma (`BCFGJPSSV26.Greedy.key_lemma`) compares the overbidding of `i₀` under the bids of
`i` with what `i₀` itself can collect; it gives the restricted pay-to-open lemma
(`BCFGJPSSV26.Greedy.payToOpen`, [BCFGJPSSV26a, Lemma D.11]) and the step "increasing `θ`" of
[BCFGJPSSV26a, Lemma E.6] (`BCFGJPSSV26.Greedy.noOver_raise`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

/-! ### The quantities -/

/-- The value of client `j` at time `θ`: `θ` if active, `(1 - δ) D j` if inactive. -/
def mval (θ : ℚ) (D : Fin n → ℚ) (j : Fin n) : ℚ := min θ ((1 - P.δ) * D j)

/-- The left side of `(1, η)`-openability of `i`. -/
def lhs1 (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : ℚ :=
  ∑ j, bid (mval P θ D j) ((1 - P.δ) * d j i)

/-- The overbidding of facility `i₀`: `∑_j β(mval j, d(j, i₀))`. -/
def over (θ : ℚ) (D : Fin n → ℚ) (i₀ : Fin m) : ℚ := ∑ j, bid (mval P θ D j) (d j i₀)

/-- The bid of an active client at distance `e` from `i`, for the parameter `T`:
`min (T, (1 + ε) θ - e)` (at least `θ`) if `e ≤ εθ`, else `θ`. -/
def gT (θ e T : ℚ) : ℚ := if e ≤ P.ε * θ then max θ (min T ((1 + P.ε) * θ - e)) else θ

/-- The bid `τ_j` of client `j` for facility `i` and the parameter `T`, capped at
`(1 - δ) D j`: for an inactive client it is `(1 - δ) D j`. -/
def mT (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) (T : ℚ) (j : Fin n) : ℚ :=
  min ((1 - P.δ) * D j) (gT P θ (d j i) T)

/-- The left side of (iii): facility `i` is paid for in the `(1 - δ/2)`-scaled metric. -/
def lhs3 (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) (T : ℚ) : ℚ :=
  ∑ j, bid (mT P d θ D i T j) ((1 - P.δ / 2) * d j i)

/-- The left side of (iv): the overbidding of `i₀` under the bids for `i`. -/
def lhs4 (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) (T : ℚ) (i₀ : Fin m) : ℚ :=
  ∑ j, bid (mT P d θ D i T j) (d j i₀)

/-- The value of client `j` in the definition of candidates: `(1 + ε²) θ` if active,
`(1 - δ) D j` if inactive. -/
def cval (θ : ℚ) (D : Fin n → ℚ) (j : Fin n) : ℚ :=
  if θ < (1 - P.δ) * D j then (1 + P.ε ^ 2) * θ else (1 - P.δ) * D j

/-- The left side of the definition of candidates. -/
def candSum (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : ℚ :=
  ∑ j, bid (cval P θ D j) ((1 - P.δ / 2) * d j i)

/-! ### Openability -/

/-- **`(1, η)`-openable** at time `θ` for the profile `D`. -/
def Open1 (f η θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Prop := f - n * η ≤ lhs1 P d θ D i

/-- **`(2, η)`-openable** (restricted to the bids `mT`) at time `θ` for the profile `D`. -/
def Open2 (f η θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Prop :=
  ∃ T, θ ≤ T ∧ T ≤ P.θplus θ ∧ f - n * η ≤ lhs3 P d θ D i T ∧ ∀ i₀, lhs4 P d θ D i T i₀ ≤ f

/-- Openability of type 1 (`b = true`) or 2 (`b = false`). -/
def OpenT (b : Bool) (f η θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Prop :=
  cond b (Open1 P d f η θ D i) (Open2 P d f η θ D i)

/-- **Payable** (restricted): (iii) holds with `η = 0` for some `T ∈ [θ, (1 + ε²) θ]`. -/
def Pay2 (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Prop :=
  ∃ T, θ ≤ T ∧ T ≤ P.θplus θ ∧ f ≤ lhs3 P d θ D i T

/-- **No overbidding** at time `θ` for the profile `D`. -/
def NoOver (f θ : ℚ) (D : Fin n → ℚ) : Prop := ∀ i₀, over P d θ D i₀ ≤ f

/-- **Candidate** at time `θ` for the profile `D`. -/
def Cand (f η θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Prop := f - n * η ≤ candSum P d θ D i

/-! ### The exact test of type 2 -/

/-- The active clients near `i`: `d(j, i) ≤ εθ` and `θ < (1 - δ) D j`. -/
def nearAct (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Finset (Fin n) :=
  univ.filter fun j ↦ d j i ≤ P.ε * θ ∧ θ < (1 - P.δ) * D j

/-- The largest bid of a near active client: `c_j = min ((1 - δ) D j, (1 + ε) θ - d(j, i))`. -/
def cnear (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) (j : Fin n) : ℚ :=
  min ((1 - P.δ) * D j) ((1 + P.ε) * θ - d j i)

/-- What the near active clients must pay in total for (iii) to hold with `η = 0`:
`∑_{j near} min (T, c_j) ≥ need` iff `f ≤ lhs3 θ D i T`, for `T ≥ θ`. -/
def need (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : ℚ :=
  f - (∑ j ∈ univ \ nearAct P d θ D i, bid (mval P θ D j) ((1 - P.δ / 2) * d j i)) +
    ∑ j ∈ nearAct P d θ D i, γ * ((1 - P.δ / 2) * d j i)

/-- The least `T` with `∑_j min (T, c_j) ≥ need` if it lies between the `c_j` below `c_{j₀}`
and `c_{j₀}`. -/
def candT (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) (j₀ : Fin n) : ℚ :=
  (need P d f θ D i - ∑ j ∈ (nearAct P d θ D i).filter
      (fun j ↦ cnear P d θ D i j < cnear P d θ D i j₀), cnear P d θ D i j) /
    ((nearAct P d θ D i).filter fun j ↦ cnear P d θ D i j₀ ≤ cnear P d θ D i j).card

/-- The least `T ≥ θ` with `f ≤ lhs3 θ D i T`, if there is one (`BCFGJPSSV26.Greedy.tstar_le`,
`BCFGJPSSV26.Greedy.le_lhs3_tstar`). -/
def tstar (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : ℚ :=
  (nearAct P d θ D i).fold max θ (candT P d f θ D i)

/-- The test of type 1: `f ≤ lhs1`. -/
def test1 (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Bool := decide (f ≤ lhs1 P d θ D i)

/-- The test of type 2: at `T = tstar`, `T ≤ (1 + ε²) θ`, (iii) and (iv) hold with `η = 0`. -/
def test2 (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Bool :=
  decide (tstar P d f θ D i ≤ P.θplus θ ∧ f ≤ lhs3 P d θ D i (tstar P d f θ D i) ∧
    ∀ i₀, lhs4 P d θ D i (tstar P d f θ D i) i₀ ≤ f)

/-- The test of type 1 (`b = true`) or 2 (`b = false`). -/
def testT (b : Bool) (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : Bool :=
  cond b (test1 P d f θ D i) (test2 P d f θ D i)

/-! ### Elementary properties of the bids -/

variable {P d}

private theorem min_le_min_add {a b x y t : ℚ} (ha : a ≤ b + t) (hx : x ≤ y + t) :
    min a x ≤ min b y + t := by
  rcases min_choice b y with h | h <;> rw [h]
  · exact (min_le_left _ _).trans ha
  · exact (min_le_right _ _).trans hx

private theorem max_le_max_add {a b x y t : ℚ} (ha : a ≤ b + t) (hx : x ≤ y + t) :
    max a x ≤ max b y + t :=
  max_le (ha.trans (by linarith [le_max_left b y])) (hx.trans (by linarith [le_max_right b y]))

/-- The bid `gT` is `1`-Lipschitz in `T`. -/
theorem gT_le_add {θ e T T' : ℚ} (h : T' ≤ T) : gT P θ e T ≤ gT P θ e T' + (T - T') := by
  unfold gT
  split_ifs
  · exact max_le_max_add (by linarith) (min_le_min_add (by linarith) (by linarith))
  · linarith

/-- The bid `gT` grows by at most `c` when the distance drops by at most `c`. -/
theorem gT_le_gT_add {θ e e' T c : ℚ} (hc : e' ≤ e + c) (hc0 : 0 ≤ c) :
    gT P θ e T ≤ gT P θ e' T + c := by
  unfold gT
  split_ifs with h1 h2 h2
  · exact max_le_max_add (by linarith) (min_le_min_add (by linarith) (by linarith))
  · push Not at h2
    exact max_le (by linarith) ((min_le_right _ _).trans (by linarith))
  · linarith [le_max_left θ (min T ((1 + P.ε) * θ - e'))]
  · linarith

theorem gT_ge (θ e T : ℚ) : θ ≤ gT P θ e T := by
  unfold gT
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem gT_le {θ e T : ℚ} (hT : θ ≤ T) : gT P θ e T ≤ T := by
  unfold gT
  split_ifs
  · exact max_le hT (min_le_left _ _)
  · exact hT

theorem mT_le_D (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) (T : ℚ) (j : Fin n) :
    mT P d θ D i T j ≤ (1 - P.δ) * D j := min_le_left _ _

theorem mT_le_T {θ T : ℚ} (hT : θ ≤ T) (D : Fin n → ℚ) (i : Fin m) (j : Fin n) :
    mT P d θ D i T j ≤ T := (min_le_right _ _).trans (gT_le hT)

/-- An active client bids at least `θ`. -/
theorem θ_le_mT {θ : ℚ} {D : Fin n → ℚ} {j : Fin n} (h : θ ≤ (1 - P.δ) * D j) (i : Fin m)
    (T : ℚ) : θ ≤ mT P d θ D i T j := le_min h (gT_ge _ _ _)

/-- An inactive client bids `(1 - δ) D j`. -/
theorem mT_of_inactive {θ : ℚ} {D : Fin n → ℚ} {j : Fin n} (h : (1 - P.δ) * D j ≤ θ)
    (i : Fin m) (T : ℚ) : mT P d θ D i T j = (1 - P.δ) * D j :=
  min_eq_left (h.trans (gT_ge _ _ _))

/-- At `T = θ`, the bids are the values. -/
theorem mT_at_θ (θ : ℚ) (D : Fin n → ℚ) (i : Fin m) (j : Fin n) :
    mT P d θ D i θ j = mval P θ D j := by
  have h : gT P θ (d j i) θ = θ := by
    unfold gT
    split_ifs
    · exact max_eq_left (min_le_left _ _)
    · rfl
  rw [mT, h, mval, min_comm]

theorem lhs4_at_θ (θ : ℚ) (D : Fin n → ℚ) (i i₀ : Fin m) :
    lhs4 P d θ D i θ i₀ = over P d θ D i₀ := by
  simp only [lhs4, over, mT_at_θ]

/-- An active client far from `i` bids `θ`. -/
theorem mT_of_far {θ T : ℚ} {D : Fin n → ℚ} {i : Fin m} {j : Fin n} (h : P.ε * θ < d j i)
    (hact : θ ≤ (1 - P.δ) * D j) : mT P d θ D i T j = θ := by
  have : gT P θ (d j i) T = θ := by
    unfold gT
    rw [if_neg (not_le.2 h)]
  rw [mT, this, min_eq_right hact]

/-- A client that bids more than `θ` is near `i`. -/
theorem le_of_θ_lt_mT {θ T : ℚ} {D : Fin n → ℚ} {i : Fin m} {j : Fin n}
    (h : θ < mT P d θ D i T j) : d j i ≤ P.ε * θ := by
  by_contra hc
  have : gT P θ (d j i) T = θ := by
    unfold gT
    rw [if_neg hc]
  unfold mT at h
  rw [this] at h
  exact absurd h (not_lt.2 (min_le_right _ _))

theorem mT_le_θplus {θ T : ℚ} (hθ : 0 ≤ θ) (hT : T ≤ P.θplus θ) (D : Fin n → ℚ) (i : Fin m)
    (j : Fin n) : mT P d θ D i T j ≤ P.θplus θ := by
  have hθp : θ ≤ P.θplus θ := by
    unfold Par.θplus
    nlinarith [sq_nonneg P.ε]
  refine (min_le_right _ _).trans ?_
  unfold gT
  split_ifs
  · exact max_le hθp ((min_le_left _ _).trans hT)
  · exact hθp

/-! ### Monotonicity and continuity -/

section Mono

variable {θ T T' f η : ℚ} {D D' : Fin n → ℚ} {i i₀ : Fin m}

theorem mval_mono (hP : P.Good n) (h : D' ≤ D) (j : Fin n) : mval P θ D' j ≤ mval P θ D j :=
  min_le_min le_rfl (mul_le_mul_of_nonneg_left (h j) hP.one_sub_δ_pos.le)

theorem mT_mono_D (hP : P.Good n) (h : D' ≤ D) (j : Fin n) :
    mT P d θ D' i T j ≤ mT P d θ D i T j :=
  min_le_min (mul_le_mul_of_nonneg_left (h j) hP.one_sub_δ_pos.le) le_rfl

theorem mT_mono_T (h : T ≤ T') (j : Fin n) : mT P d θ D i T j ≤ mT P d θ D i T' j := by
  unfold mT
  refine min_le_min le_rfl ?_
  unfold gT
  split_ifs
  · exact max_le_max le_rfl (min_le_min h le_rfl)
  · exact le_rfl

theorem cval_mono (hP : P.Good n) (hθ : 0 ≤ θ) (h : D' ≤ D) (j : Fin n) :
    cval P θ D' j ≤ cval P θ D j := by
  have hD : (1 - P.δ) * D' j ≤ (1 - P.δ) * D j :=
    mul_le_mul_of_nonneg_left (h j) hP.one_sub_δ_pos.le
  unfold cval
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans_le hD) h2
  · push Not at h1
    exact h1.trans (by nlinarith [sq_nonneg P.ε])
  · exact hD

theorem lhs1_mono (hP : P.Good n) (h : D' ≤ D) : lhs1 P d θ D' i ≤ lhs1 P d θ D i :=
  sum_le_sum fun j _ ↦ bid_mono_left (mval_mono hP h j) _

theorem over_mono (hP : P.Good n) (h : D' ≤ D) : over P d θ D' i₀ ≤ over P d θ D i₀ :=
  sum_le_sum fun j _ ↦ bid_mono_left (mval_mono hP h j) _

theorem lhs3_mono_D (hP : P.Good n) (h : D' ≤ D) : lhs3 P d θ D' i T ≤ lhs3 P d θ D i T :=
  sum_le_sum fun j _ ↦ bid_mono_left (mT_mono_D hP h j) _

theorem lhs4_mono_D (hP : P.Good n) (h : D' ≤ D) :
    lhs4 P d θ D' i T i₀ ≤ lhs4 P d θ D i T i₀ :=
  sum_le_sum fun j _ ↦ bid_mono_left (mT_mono_D hP h j) _

theorem lhs3_mono_T (h : T ≤ T') : lhs3 P d θ D i T ≤ lhs3 P d θ D i T' :=
  sum_le_sum fun j _ ↦ bid_mono_left (mT_mono_T h j) _

theorem lhs4_mono_T (h : T ≤ T') : lhs4 P d θ D i T i₀ ≤ lhs4 P d θ D i T' i₀ :=
  sum_le_sum fun j _ ↦ bid_mono_left (mT_mono_T h j) _

theorem candSum_mono (hP : P.Good n) (hθ : 0 ≤ θ) (h : D' ≤ D) :
    candSum P d θ D' i ≤ candSum P d θ D i :=
  sum_le_sum fun j _ ↦ bid_mono_left (cval_mono hP hθ h j) _

theorem NoOver.mono (hP : P.Good n) (hno : NoOver P d f θ D) (h : D' ≤ D) : NoOver P d f θ D' :=
  fun i₀ ↦ (over_mono hP h).trans (hno i₀)

theorem Cand.mono (hP : P.Good n) (hθ : 0 ≤ θ) (hc : Cand P d f η θ D' i) (h : D' ≤ D) :
    Cand P d f η θ D i := hc.trans (candSum_mono hP hθ h)

/-- If `D - c ≤ D'` pointwise, the bids drop by at most `c`. -/
theorem mT_sub_le (hP : P.Good n) {c : ℚ} (hc : 0 ≤ c) (h : ∀ j, D j - c ≤ D' j) (j : Fin n) :
    mT P d θ D i T j - c ≤ mT P d θ D' i T j := by
  have hδ := hP.one_sub_δ_pos
  have hδ' := hP.δ_pos
  have h1 := h j
  unfold mT
  refine le_min ?_ (by linarith [min_le_right ((1 - P.δ) * D j) (gT P θ (d j i) T)])
  have := min_le_left ((1 - P.δ) * D j) (gT P θ (d j i) T)
  nlinarith

theorem mval_sub_le (hP : P.Good n) {c : ℚ} (hc : 0 ≤ c) (h : ∀ j, D j - c ≤ D' j)
    (j : Fin n) : mval P θ D j - c ≤ mval P θ D' j := by
  have hδ := hP.one_sub_δ_pos
  have hδ' := hP.δ_pos
  have h1 := h j
  unfold mval
  refine le_min (by linarith [min_le_left θ ((1 - P.δ) * D j)]) ?_
  have := min_le_right θ ((1 - P.δ) * D j)
  nlinarith

/-- If `D - c ≤ D'` pointwise, (iii) drops by at most `n c`. -/
theorem lhs3_sub_le (hP : P.Good n) {c : ℚ} (hc : 0 ≤ c) (h : ∀ j, D j - c ≤ D' j) :
    lhs3 P d θ D i T - n * c ≤ lhs3 P d θ D' i T := by
  have hterm : ∀ j, bid (mT P d θ D i T j) ((1 - P.δ / 2) * d j i) - c ≤
      bid (mT P d θ D' i T j) ((1 - P.δ / 2) * d j i) := fun j ↦ by
    have h1 := bid_sub_bid_le (mT P d θ D i T j) (mT P d θ D' i T j) ((1 - P.δ / 2) * d j i)
    have h2 : max (mT P d θ D i T j - mT P d θ D' i T j) 0 ≤ c :=
      max_le (by linarith [mT_sub_le hP hc h j (i := i) (T := T) (θ := θ) (d := d)]) hc
    linarith
  have := sum_le_sum fun j (_ : j ∈ univ) ↦ hterm j
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact this

/-- If `D - c ≤ D'` pointwise, the left side of type 1 drops by at most `n c`. -/
theorem lhs1_sub_le (hP : P.Good n) {c : ℚ} (hc : 0 ≤ c) (h : ∀ j, D j - c ≤ D' j) :
    lhs1 P d θ D i - n * c ≤ lhs1 P d θ D' i := by
  have hterm : ∀ j, bid (mval P θ D j) ((1 - P.δ) * d j i) - c ≤
      bid (mval P θ D' j) ((1 - P.δ) * d j i) := fun j ↦ by
    have h1 := bid_sub_bid_le (mval P θ D j) (mval P θ D' j) ((1 - P.δ) * d j i)
    have h2 : max (mval P θ D j - mval P θ D' j) 0 ≤ c :=
      max_le (by linarith [mval_sub_le hP hc h j (θ := θ)]) hc
    linarith
  have := sum_le_sum fun j (_ : j ∈ univ) ↦ hterm j
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact this

/-- (iv) is `n`-Lipschitz in `T`. -/
theorem lhs4_sub_le (h : T' ≤ T) :
    lhs4 P d θ D i T i₀ - n * (T - T') ≤ lhs4 P d θ D i T' i₀ := by
  have hterm : ∀ j, bid (mT P d θ D i T j) (d j i₀) - (T - T') ≤
      bid (mT P d θ D i T' j) (d j i₀) := fun j ↦ by
    have h1 := bid_sub_bid_le (mT P d θ D i T j) (mT P d θ D i T' j) (d j i₀)
    have h2 : mT P d θ D i T j ≤ mT P d θ D i T' j + (T - T') :=
      min_le_min_add (by linarith) (gT_le_add h)
    have h3 : max (mT P d θ D i T j - mT P d θ D i T' j) 0 ≤ T - T' :=
      max_le (by linarith) (by linarith)
    linarith
  have := sum_le_sum fun j (_ : j ∈ univ) ↦ hterm j
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact this

end Mono

/-! ### Triangle inequality (v) and open facilities -/

/-- **(v)** for the bids `mT`, between active clients of a profile. -/
theorem mT_triangle (hP : P.Good n) (X : Space n m) (S : Finset (Fin m × ℚ)) {θ T : ℚ}
    (_hθ : 0 ≤ θ) (_hT : θ ≤ T) (i : Fin m) {j k : Fin n}
    (_hj : θ < (1 - P.δ) * profF P.K X.d S j) (_hk : θ < (1 - P.δ) * profF P.K X.d S k) :
    mT P X.d θ (profF P.K X.d S) i T j ≤ mT P X.d θ (profF P.K X.d S) i T k + X.dC j k := by
  have hC : 0 ≤ X.dC j k := X.nonneg _ _
  have hδ := hP.one_sub_δ_pos
  have hδ' := hP.δ_pos
  have hD := profF_lipschitz P.K X S j k
  have hdk : X.d k i ≤ X.d j i + X.dC j k := by
    have := X.d_le_dC_add k j i
    rw [X.dC_comm k j] at this
    linarith
  refine min_le_min_add ?_ (gT_le_gT_add hdk hC)
  nlinarith

/-- A facility at distance at least the profile from every client collects nothing (type 1). -/
theorem lhs1_eq_zero (hP : P.Good n) {θ : ℚ} {D : Fin n → ℚ} {i : Fin m}
    (hd : ∀ j, 0 ≤ d j i) (h : ∀ j, D j ≤ d j i) : lhs1 P d θ D i = 0 := by
  have hδ := hP.one_sub_δ_pos
  refine sum_eq_zero fun j _ ↦ bid_eq_zero_of_le ?_ (by nlinarith [hd j])
  exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (h j) hδ.le)

/-- A facility at distance at least the profile from every client collects nothing (type 2). -/
theorem lhs3_eq_zero (hP : P.Good n) {θ T : ℚ} {D : Fin n → ℚ} {i : Fin m}
    (hd : ∀ j, 0 ≤ d j i) (h : ∀ j, D j ≤ d j i) : lhs3 P d θ D i T = 0 := by
  have hδ := hP.one_sub_δ_pos
  have hδ' := hP.δ_pos
  refine sum_eq_zero fun j _ ↦ bid_eq_zero_of_le ?_ (by nlinarith [hd j])
  refine (mT_le_D θ D i T j).trans ?_
  have := mul_le_mul_of_nonneg_left (h j) hδ.le
  nlinarith [hd j]

/-! ### The key lemma and the exact test -/

/-- The key lemma, for one client: what `i₀` collects from `j` with the bid `mT` in the
`(1 - δ/2)`-scaled metric is at least `β(min (T, (1 - δ) D j), d(j, i₀))`. -/
theorem bid_min_le_bid_mT (hP : P.Good n) {θ T : ℚ} {D : Fin n → ℚ} {i₀ : Fin m} {j : Fin n}
    (he : 0 ≤ d j i₀) (hθ : 0 < θ) (hT' : T ≤ P.θplus θ) :
    bid (min T ((1 - P.δ) * D j)) (d j i₀) ≤
      bid (mT P d θ D i₀ T j) ((1 - P.δ / 2) * d j i₀) := by
  have hδ := hP.δ_pos
  have hδ1 := hP.δ_le
  have hε := hP.ε_pos
  have hεγ := hP.ε_le_γδ
  have hγ := one_le_γ
  have hγδ : γ * P.δ / 2 ≤ 1 := by norm_num [γ]; linarith
  have hT'' : T ≤ (1 + P.ε ^ 2) * θ := hT'
  set e := d j i₀
  set x := min T ((1 - P.δ) * D j)
  have hxT : x ≤ T := min_le_left _ _
  have hxD : x ≤ (1 - P.δ) * D j := min_le_right _ _
  have hee : (1 - P.δ / 2) * e ≤ e := by nlinarith
  -- if `x` is at most the bid, the bound follows from `(1 - δ/2) e ≤ e`
  have hcase : x ≤ mT P d θ D i₀ T j →
      bid x e ≤ bid (mT P d θ D i₀ T j) ((1 - P.δ / 2) * e) := fun h ↦
    (bid_anti_right x hee).trans (bid_mono_left h _)
  -- otherwise it is enough that `y ≤ mT` with `x - γ e ≤ y - γ (1 - δ/2) e`
  have hcase' : ∀ y, y ≤ mT P d θ D i₀ T j → x - γ * e ≤ y - γ * ((1 - P.δ / 2) * e) →
      bid x e ≤ bid (mT P d θ D i₀ T j) ((1 - P.δ / 2) * e) := fun y hy hxy ↦
    (max_le_max hxy le_rfl).trans (bid_mono_left hy _)
  by_cases hnear : e ≤ P.ε * θ
  · have hg : gT P θ e T = max θ (min T ((1 + P.ε) * θ - e)) := by
      unfold gT; rw [if_pos hnear]
    rcases le_total x ((1 + P.ε) * θ - e) with hxc | hxc
    · refine hcase (le_min hxD ?_)
      change x ≤ gT P θ (d j i₀) T
      rw [hg]
      exact le_max_of_le_right (le_min hxT hxc)
    · refine hcase' ((1 + P.ε) * θ - e) (le_min (hxc.trans hxD) ?_) ?_
      · change (1 + P.ε) * θ - e ≤ gT P θ (d j i₀) T
        rw [hg]
        exact le_max_of_le_right (le_min (hxc.trans hxT) le_rfl)
      · have h1 : 0 ≤ (1 - γ * P.δ / 2) * (P.ε * θ - e) := mul_nonneg (by linarith) (by linarith)
        have h2 : 0 ≤ (γ * P.δ / 2 - P.ε) * (P.ε * θ) :=
          mul_nonneg (by linarith) (by positivity)
        nlinarith
  · push Not at hnear
    have hg : gT P θ e T = θ := by unfold gT; rw [if_neg (not_le.2 hnear)]
    by_cases hact : (1 - P.δ) * D j ≤ θ
    · refine hcase (le_min hxD ?_)
      change x ≤ gT P θ (d j i₀) T
      rw [hg]
      linarith
    · push Not at hact
      refine hcase' θ (le_min hact.le (by rw [show gT P θ (d j i₀) T = θ from hg])) ?_
      have h1 : 0 ≤ P.ε * (e - P.ε * θ) := mul_nonneg hε.le (by linarith)
      have h2 : 0 ≤ (γ * P.δ / 2 - P.ε) * e := mul_nonneg (by linarith) he
      nlinarith

theorem θ_le_tstar (f θ : ℚ) (D : Fin n → ℚ) (i : Fin m) : θ ≤ tstar P d f θ D i :=
  (le_fold_max _).2 (.inl le_rfl)

/-- A client that is not near and active bids its value, whatever `T`. -/
theorem mT_of_not_mem_nearAct {θ T : ℚ} {D : Fin n → ℚ} {i : Fin m} {j : Fin n}
    (hj : j ∉ nearAct P d θ D i) : mT P d θ D i T j = mval P θ D j := by
  by_cases hact : (1 - P.δ) * D j ≤ θ
  · rw [mT_of_inactive hact, mval, min_eq_right hact]
  · push Not at hact
    have hfar : P.ε * θ < d j i := by
      by_contra hc
      exact hj (mem_filter.2 ⟨mem_univ _, not_lt.1 hc, hact⟩)
    rw [mT_of_far hfar hact.le, mval, min_eq_left hact.le]

/-- A near active client bids `min (T, c_j)` and collects it minus `γ (1 - δ/2) d(j, i)`. -/
theorem bid_mT_of_mem_nearAct (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {θ T : ℚ}
    {D : Fin n → ℚ} {i : Fin m} {j : Fin n} (hθ : 0 < θ) (hT : θ ≤ T)
    (hj : j ∈ nearAct P d θ D i) :
    bid (mT P d θ D i T j) ((1 - P.δ / 2) * d j i) =
      min T (cnear P d θ D i j) - γ * ((1 - P.δ / 2) * d j i) := by
  obtain ⟨hnear, hact⟩ := (mem_filter.1 hj).2
  have hδ := hP.δ_pos
  have hγε := hP.γε_lt_one
  have hγ := one_le_γ
  have he := hd j i
  have hc : θ ≤ (1 + P.ε) * θ - d j i := by linarith
  have hmin : θ ≤ min T ((1 + P.ε) * θ - d j i) := le_min hT hc
  have hm : mT P d θ D i T j = min T (cnear P d θ D i j) := by
    rw [mT, gT, if_pos hnear, max_eq_right hmin, cnear, min_left_comm]
  rw [hm]
  refine bid_eq_of_le ?_
  have h1 : θ ≤ min T (cnear P d θ D i j) := le_min hT (le_min hact.le hc)
  have h2 : γ * ((1 - P.δ / 2) * d j i) ≤ γ * (P.ε * θ) := by
    have : (1 - P.δ / 2) * d j i ≤ P.ε * θ := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by linarith)
  nlinarith

/-- **(iii) is affine-concave in `T`**: on `T ≥ θ`, only the near active clients depend on `T`,
each through `min (T, c_j)`. -/
theorem lhs3_eq (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ T : ℚ} {D : Fin n → ℚ}
    {i : Fin m} (hθ : 0 < θ) (hT : θ ≤ T) :
    lhs3 P d θ D i T =
      f - need P d f θ D i + ∑ j ∈ nearAct P d θ D i, min T (cnear P d θ D i j) := by
  rw [lhs3, ← sum_sdiff (subset_univ (nearAct P d θ D i)),
    sum_congr rfl fun j hj ↦ by rw [mT_of_not_mem_nearAct (mem_sdiff.1 hj).2],
    sum_congr rfl fun j hj ↦ bid_mT_of_mem_nearAct hP hd hθ hT hj, sum_sub_distrib, need]
  ring

theorem le_lhs3_iff (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ T : ℚ} {D : Fin n → ℚ}
    {i : Fin m} (hθ : 0 < θ) (hT : θ ≤ T) :
    f ≤ lhs3 P d θ D i T ↔
      need P d f θ D i ≤ ∑ j ∈ nearAct P d θ D i, min T (cnear P d θ D i j) := by
  rw [lhs3_eq hP hd hθ hT (f := f)]
  constructor <;> intro h <;> linarith

/-- `tstar` is at most every `T ≥ θ` at which (iii) holds with `η = 0`. -/
theorem tstar_le (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ T : ℚ} {D : Fin n → ℚ}
    {i : Fin m} (hθ : 0 < θ) (hT : θ ≤ T) (h : f ≤ lhs3 P d θ D i T) : tstar P d f θ D i ≤ T := by
  rw [le_lhs3_iff hP hd hθ hT] at h
  set N := nearAct P d θ D i
  set c := cnear P d θ D i
  refine (fold_max_le _).2 ⟨hT, fun j₀ hj₀ ↦ ?_⟩
  have hpos' : 0 < (N.filter fun j ↦ c j₀ ≤ c j).card :=
    card_pos.2 ⟨j₀, mem_filter.2 ⟨hj₀, le_rfl⟩⟩
  have hpos : (0 : ℚ) < (N.filter fun j ↦ c j₀ ≤ c j).card := by exact_mod_cast hpos'
  rw [candT, div_le_iff₀ hpos]
  have hsplit := sum_filter_add_sum_filter_not N (fun j ↦ c j < c j₀) fun j ↦ min T (c j)
  have h1 : ∑ j ∈ N.filter (fun j ↦ c j < c j₀), min T (c j) ≤
      ∑ j ∈ N.filter (fun j ↦ c j < c j₀), c j := sum_le_sum fun j _ ↦ min_le_right _ _
  have h2 : ∑ j ∈ N.filter (fun j ↦ ¬ c j < c j₀), min T (c j) ≤
      (N.filter fun j ↦ c j₀ ≤ c j).card * T := by
    rw [filter_congr fun j _ ↦ not_lt]
    calc _ ≤ ∑ j ∈ N.filter (fun j ↦ c j₀ ≤ c j), T := sum_le_sum fun j _ ↦ min_le_left _ _
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  linarith

/-- (iii) holds with `η = 0` at `tstar` if it holds at some `T ≥ tstar`. -/
theorem le_lhs3_tstar (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ T : ℚ} {D : Fin n → ℚ}
    {i : Fin m} (hθ : 0 < θ) (hT : tstar P d f θ D i ≤ T) (h : f ≤ lhs3 P d θ D i T) :
    f ≤ lhs3 P d θ D i (tstar P d f θ D i) := by
  have hθt := θ_le_tstar (P := P) (d := d) f θ D i
  rw [le_lhs3_iff hP hd hθ (hθt.trans hT)] at h
  rw [le_lhs3_iff hP hd hθ hθt]
  set N := nearAct P d θ D i
  set c := cnear P d θ D i
  set t := tstar P d f θ D i
  rcases (N.filter fun j ↦ t ≤ c j).eq_empty_or_nonempty with hU | hU
  · -- all `c_j < t`: the sum is constant on `[t, T]`
    have hlt : ∀ j ∈ N, c j < t := fun j hj ↦ by
      by_contra hc
      have : j ∈ N.filter fun j ↦ t ≤ c j := mem_filter.2 ⟨hj, not_lt.1 hc⟩
      rw [hU] at this
      exact absurd this (notMem_empty _)
    have heq : ∑ j ∈ N, min T (c j) = ∑ j ∈ N, min t (c j) := sum_congr rfl fun j hj ↦ by
      rw [min_eq_right ((hlt j hj).le.trans hT), min_eq_right (hlt j hj).le]
    linarith
  · -- the least `c_{j₀} ≥ t` splits the clients as `candT j₀` does
    obtain ⟨j₀, hj₀U, hmin⟩ := (N.filter fun j ↦ t ≤ c j).exists_min_image c hU
    obtain ⟨hj₀, htj₀⟩ := mem_filter.1 hj₀U
    have hcand : candT P d f θ D i j₀ ≤ t := (le_fold_max _).2 (.inr ⟨j₀, hj₀, le_rfl⟩)
    have hpos' : 0 < (N.filter fun j ↦ c j₀ ≤ c j).card :=
      card_pos.2 ⟨j₀, mem_filter.2 ⟨hj₀, le_rfl⟩⟩
    have hpos : (0 : ℚ) < (N.filter fun j ↦ c j₀ ≤ c j).card := by exact_mod_cast hpos'
    rw [candT, div_le_iff₀ hpos] at hcand
    have hsplit := sum_filter_add_sum_filter_not N (fun j ↦ c j < c j₀) fun j ↦ min t (c j)
    have h1 : ∑ j ∈ N.filter (fun j ↦ c j < c j₀), min t (c j) =
        ∑ j ∈ N.filter (fun j ↦ c j < c j₀), c j := sum_congr rfl fun j hj ↦ by
      obtain ⟨hjN, hjc⟩ := mem_filter.1 hj
      refine min_eq_right (le_of_lt ?_)
      by_contra hc
      exact absurd (hmin j (mem_filter.2 ⟨hjN, not_lt.1 hc⟩)) (not_le.2 hjc)
    have h2 : ∑ j ∈ N.filter (fun j ↦ ¬ c j < c j₀), min t (c j) =
        (N.filter fun j ↦ c j₀ ≤ c j).card * t := by
      rw [filter_congr fun j _ ↦ not_lt]
      calc _ = ∑ j ∈ N.filter (fun j ↦ c j₀ ≤ c j), t := sum_congr rfl fun j hj ↦
            min_eq_left (htj₀.trans (mem_filter.1 hj).2)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    linarith

theorem test1_iff {f θ : ℚ} {D : Fin n → ℚ} {i : Fin m} :
    test1 P d f θ D i = true ↔ Open1 P d f 0 θ D i := by
  simp [test1, Open1]

/-! ### Pay to open, maximality, no overbidding -/

end BCFGJPSSV26.Greedy


