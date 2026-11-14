-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring
-- name    : BCFGJPSSV26_Stable_Alg_Coloring
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:10:01.650312+00:00
-- url     : https://prove2.me/theorems/c84fbc92-79ad-47ce-9d03-67d596ef78a9
-- title:
--   BCFGJPSSV26.Stable.Alg.Coloring — Color coding
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.Coloring` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The last `k` chunks of a trial color the kept centers `LS'` (a list), one fair bit per position:
--   red for `true` (`BCFGJPSSV26.Stable.colors`, `BCFGJPSSV26.Stable.redOf`,
--   `BCFGJPSSV26.Stable.blueOf`).
--
--   [BCFGJPSSV26b, Section 3.3] (`BCFGJPSSV26.Stable.Partition.card_colorEvent`): the
--   color event of a partition (the centers of `Z*` red, their nearest centers in `LS' \ Z*` blue)
--   constrains at most `2 z ≤ 2 s` positions, each satisfied by exactly half the chunks, so it holds
--   for at least `4^(-s) K^k` chunk vectors.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Partition.card_colorEvent` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Coloring.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.Coloring` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Color coding

The last `k` chunks of a trial color the kept centers `LS'` (a list), one fair bit per position:
red for `true` (`BCFGJPSSV26.Stable.colors`, `BCFGJPSSV26.Stable.redOf`,
`BCFGJPSSV26.Stable.blueOf`).

[BCFGJPSSV26b, Section 3.3] (`BCFGJPSSV26.Stable.Partition.card_colorEvent`): the
color event of a partition (the centers of `Z*` red, their nearest centers in `LS' \ Z*` blue)
constrains at most `2 z ≤ 2 s` positions, each satisfied by exactly half the chunks, so it holds
for at least `4^(-s) K^k` chunk vectors.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- One color bit for each position of `LS'`. -/
def colors (b : ℕ) (LS' : List ℕ) (ch : ℕ → ℕ) : List Bool :=
  (List.range LS'.length).map fun i ↦ cbit b (ch i)

/-- The red centers. -/
def redOf (LS' : List ℕ) (col : List Bool) : List ℕ :=
  (LS'.zip col).filterMap fun p ↦ if p.2 then some p.1 else none

/-- The blue centers. -/
def blueOf (LS' : List ℕ) (col : List Bool) : List ℕ :=
  (LS'.zip col).filterMap fun p ↦ if p.2 then none else some p.1

/-- Membership in a zip of two lists of the same length, by positions. -/
theorem mem_zip_iff_getElem {LS' : List ℕ} {col : List Bool} (hcol : col.length = LS'.length)
    {i : ℕ} {x : Bool} :
    (i, x) ∈ LS'.zip col ↔ ∃ p, ∃ h : p < LS'.length, LS'[p] = i ∧ col[p] = x := by
  rw [List.mem_iff_getElem]
  simp only [List.length_zip, List.getElem_zip, Prod.mk.injEq]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, by omega, h1, h2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, by omega, h1, h2⟩

theorem mem_redOf {LS' : List ℕ} {col : List Bool} {i : ℕ} :
    i ∈ redOf LS' col ↔ (i, true) ∈ LS'.zip col := by
  simp only [redOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, c⟩, ha, h⟩
    cases c
    · simp at h
    · simp only [ite_true, Option.some.injEq] at h
      exact h ▸ ha
  · intro h
    exact ⟨(i, true), h, by simp⟩

theorem mem_blueOf {LS' : List ℕ} {col : List Bool} {i : ℕ} :
    i ∈ blueOf LS' col ↔ (i, false) ∈ LS'.zip col := by
  simp only [blueOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, c⟩, ha, h⟩
    cases c
    · simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at h
      exact h ▸ ha
    · simp at h
  · intro h
    exact ⟨(i, false), h, by simp⟩

/-- Red and blue split a list of distinct centers. -/
theorem centers_red_blue {I : Instance} {LS' : List ℕ} (hnd : LS'.Nodup) {col : List Bool}
    (hcol : col.length = LS'.length) :
    I.centers (redOf LS' col) ⊆ I.centers LS' ∧
      I.centers (blueOf LS' col) = I.centers LS' \ I.centers (redOf LS' col) := by
  have huniq : ∀ i x y, (i, x) ∈ LS'.zip col → (i, y) ∈ LS'.zip col → x = y := by
    intro i x y hx hy
    obtain ⟨p, hp, h1, h2⟩ := (mem_zip_iff_getElem hcol).1 hx
    obtain ⟨p', hp', h1', h2'⟩ := (mem_zip_iff_getElem hcol).1 hy
    have : p = p' := hnd.getElem_inj_iff.1 (h1.trans h1'.symm)
    subst this
    rw [← h2, ← h2']
  have hex : ∀ i ∈ LS', ∃ x, (i, x) ∈ LS'.zip col := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hi
    exact ⟨col[p], (mem_zip_iff_getElem hcol).2 ⟨p, hp, rfl, rfl⟩⟩
  refine ⟨Instance.centers_mono fun i hi ↦ (List.of_mem_zip (mem_redOf.1 hi)).1, ?_⟩
  ext c
  rw [mem_sdiff, Instance.mem_centers, Instance.mem_centers, Instance.mem_centers, mem_blueOf,
    mem_redOf]
  constructor
  · intro h
    exact ⟨(List.of_mem_zip h).1, fun h' ↦ absurd (huniq _ _ _ h h') (by decide)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := hex _ h1
    cases x
    · exact hx
    · exact absurd hx h2

theorem length_colors (b : ℕ) (LS' : List ℕ) (ch : ℕ → ℕ) :
    (colors b LS' ch).length = LS'.length := by
  simp [colors]

/-- A position colored red gives a red center. -/
theorem mem_redOf_colors {b : ℕ} {LS' : List ℕ} {ch : ℕ → ℕ} {p : ℕ} (hp : p < LS'.length)
    (h : cbit b (ch p) = true) : LS'[p] ∈ redOf LS' (colors b LS' ch) := by
  rw [mem_redOf, mem_zip_iff_getElem (length_colors b LS' ch)]
  exact ⟨p, hp, rfl, by simp [colors, h]⟩

/-- A position colored blue gives a blue center. -/
theorem mem_blueOf_colors {b : ℕ} {LS' : List ℕ} {ch : ℕ → ℕ} {p : ℕ} (hp : p < LS'.length)
    (h : cbit b (ch p) = false) : LS'[p] ∈ blueOf LS' (colors b LS' ch) := by
  rw [mem_blueOf, mem_zip_iff_getElem (length_colors b LS' ch)]
  exact ⟨p, hp, rfl, by simp [colors, h]⟩

theorem toCh_of_lt {M K : ℕ} (u : Fin M → Fin K) {p : ℕ} (hp : p < M) : toCh u p = u ⟨p, hp⟩ := by
  simp [toCh, hp]

end BCFGJPSSV26.Stable


