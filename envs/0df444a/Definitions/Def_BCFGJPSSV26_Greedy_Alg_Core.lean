-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
-- name    : BCFGJPSSV26_Greedy_Alg_Core
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:02:53.902868+00:00
-- url     : https://prove2.me/theorems/231e7e0e-5e91-4af3-8973-882288e55124
-- title:
--   BCFGJPSSV26.Greedy.Alg.Core — The core theorem
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Alg.Core` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Theorem 5.16] on a core input (`BCFGJPSSV26.Greedy.core_spec`): for good constants
--   and a core input whose distances lie in `[1, M]` with `2 ≤ n` and `1 ≤ k < min (n, m)`, the core
--   outputs at most `k + 6R` distinct facilities, of cost at most `(ρ + 10δ) cost(O)` for every
--   nonempty set `O` of at most `k` facilities.
--
--   The proof: the merge ends with a good output (`BCFGJPSSV26.Greedy.Ctx.merge_spec`), to which the
--   robust LMP guarantee (`BCFGJPSSV26.Greedy.robust_lmp`) applies. With exactly `k` regular atoms
--   the opening costs cancel; with fewer (only at `f̂ = δ`) the extra `k δ ≤ δ cost(O)`, since every
--   distance is at least `1`. The slack `k n η ≤ δ² / 100` is at most `δ²/100 · cost(O)`. Replacing
--   free copies by their originals does not raise the cost.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.core_spec` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Core.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge
public import Definitions.Def_BCFGJPSSV26_Greedy_LMP
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDups

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Alg.Core` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The core theorem

[BCFGJPSSV26a, Theorem 5.16] on a core input (`BCFGJPSSV26.Greedy.core_spec`): for good constants
and a core input whose distances lie in `[1, M]` with `2 ≤ n` and `1 ≤ k < min (n, m)`, the core
outputs at most `k + 6R` distinct facilities, of cost at most `(ρ + 10δ) cost(O)` for every
nonempty set `O` of at most `k` facilities.

The proof: the merge ends with a good output (`BCFGJPSSV26.Greedy.Ctx.merge_spec`), to which the
robust LMP guarantee (`BCFGJPSSV26.Greedy.robust_lmp`) applies. With exactly `k` regular atoms
the opening costs cancel; with fewer (only at `f̂ = δ`) the extra `k δ ≤ δ cost(O)`, since every
distance is at least `1`. The slack `k n η ≤ δ² / 100` is at most `δ²/100 · cost(O)`. Replacing
free copies by their originals does not raise the cost.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Ctx

variable {C : Ctx} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

omit hX in
/-- The output of a good solution is a list of distinct facilities, nonempty, of length at most
the number of atoms. -/
theorem toCenters_spec (_hX : C.Hyp X) {H : List (List AAtom)} (hok : C.SolOK H)
    (hreg : 1 ≤ nRegA H) :
    toCenters H ≠ [] ∧ (toCenters H).Nodup ∧ (∀ i ∈ toCenters H, i < C.ip.m) ∧
      (toCenters H).length ≤ H.flatten.length := by
  have hmem : ∀ i, i ∈ toCenters H ↔ ∃ a ∈ H.flatten, a.1 = i := by
    intro i
    simp only [toCenters, List.mem_eraseDups, List.mem_map]
  refine ⟨fun h ↦ ?_, List.nodup_eraseDups _, fun i hi ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, a ∈ H.flatten := by
      unfold nRegA at hreg
      obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos hreg
      exact ⟨a, List.mem_of_mem_filter ha⟩
    have := (hmem a.1).2 ⟨a, ha, rfl⟩
    rw [h] at this
    exact List.not_mem_nil this
  · obtain ⟨a, ha, rfl⟩ := (hmem i).1 hi
    exact (hok a ha).1
  · refine (List.eraseDups_sublist _).length_le.trans ?_
    rw [List.length_map]

omit hX in
/-- A solution with at most three free atoms per sequence has at most `nReg + 6R` atoms. -/
theorem flatten_length_le (_hX : C.Hyp X) {H : List (List AAtom)}
    (hlen : H.length = 2 * C.ip.R) (hfree : ∀ q, nFreeSeqA (H.getD q []) ≤ 3) :
    H.flatten.length ≤ nRegA H + 6 * C.ip.R := by
  have hfree' : ∀ S ∈ H, nFreeSeqA S ≤ 3 := by
    intro S hS
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hS
    have := hfree q
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some] at this
  have key : ∀ H' : List (List AAtom), (∀ S ∈ H', nFreeSeqA S ≤ 3) →
      (H'.flatten.filter fun a ↦ !(a.2 == 0)).length ≤ 3 * H'.length := by
    intro H' h
    induction H' with
    | nil => simp
    | cons S H' ih =>
      rw [List.flatten_cons, List.filter_append, List.length_append, List.length_cons]
      have h1 := h S List.mem_cons_self
      have h2 := ih fun S' hS' ↦ h S' (List.mem_cons_of_mem _ hS')
      unfold nFreeSeqA at h1
      have e : (S.filter fun a ↦ !(a.2 == 0)) = S.filter fun a ↦ a.2 != 0 := rfl
      rw [e]
      omega
  have h1 := List.length_eq_length_filter_add (l := H.flatten) fun a ↦ a.2 == 0
  have h2 := key H hfree'
  unfold nRegA
  omega

/-- **Free copies replaced by their originals**: the cost of the output is at most the
connection cost of the solution. -/
theorem coreCost_toCenters_le {f η : ℚ} {H : List (List AAtom)}
    (hH : Sol C.par X.d f η (decH hX H)) (hok : C.SolOK H) :
    coreCost (C.ip.n, C.ip.m, C.ip.k, C.tab) (toCenters H) ≤ connCost C.par X.d (decH hX H) := by
  unfold coreCost connCost
  rw [list_sum_map_range, Finset.sum_range]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hlt := Sol.profL_lt_K hX.good hH j
  obtain ⟨p, hp, hpeq⟩ := exists_profF_eq C.par.K X.d hlt
  rw [decH_flatten] at hp hpeq
  simp only [pairs, decS, List.map_map, List.mem_toFinset, List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  have ham := (hok a ha).1
  have hpeq' : profL C.par.K X.d (decH hX H).flatten j = X.d j ⟨a.1, ham⟩ + C.aoff a := by
    rw [decH_flatten]
    simpa [profL, Function.comp_apply, decA_pair hX ham] using hpeq
  rw [hpeq']
  have hK := hX.K_pos
  have h0 := aoff_nonneg hK.le a
  have hin : C.dist j a.1 ∈ (toCenters H).map fun i ↦ (C.tab.getD j []).getD i 0 := by
    refine List.mem_map.2 ⟨a.1, ?_, rfl⟩
    simp only [toCenters, List.mem_eraseDups, List.mem_map]
    exact ⟨a, ha, rfl⟩
  have hmin := (Combine.minQ_spec (List.ne_nil_of_mem hin)).2 _ hin
  have hd : C.dist j a.1 = X.d j ⟨a.1, ham⟩ := hX.dist_eq j ⟨a.1, ham⟩
  change Combine.minQ ((toCenters H).map fun i ↦ (C.tab.getD j []).getD i 0) ≤ _
  linarith

omit hX in
/-- Every set of facilities costs at least `n` when all distances are at least `1`. -/
theorem costF_ge {X : Space C.ip.n C.ip.m} (hd1 : ∀ j i, 1 ≤ X.d j i) {O : Finset (Fin C.ip.m)}
    (hO : O.Nonempty) : (C.ip.n : ℚ) ≤ costF X.d O := by
  unfold costF
  simp only [hO, dite_true]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦
    (Finset.le_inf' hO (X.d j) fun i _ ↦ hd1 j i : (1 : ℚ) ≤ O.inf' hO (X.d j))
  simpa using h

end Ctx

/-- The slack: `s n η ≤ δ² / 100` for `η = δ² / (100 n²)` and `s ≤ n`. -/
theorem eta_bound {n s δ : ℚ} (hn : 0 < n) (hs : s ≤ n) :
    s * n * (δ ^ 2 / (100 * n ^ 2)) ≤ δ ^ 2 / 100 := by
  have h : s * n * (δ ^ 2 / (100 * n ^ 2)) = s / n * (δ ^ 2 / 100) := by
    field_simp
  rw [h]
  have : s / n ≤ 1 := by rw [div_le_one hn]; exact hs
  have : 0 ≤ δ ^ 2 / 100 := by positivity
  nlinarith

/-- The arithmetic of the core theorem: from the robust LMP guarantee with `s` regular atoms,
`|O| = o` and opening cost `f`, the connection cost `A` is at most `(ρ + 10 δ) B`. -/
theorem core_ineq {δ A B s k n η f o : ℚ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 100) (hB : n ≤ B)
    (hn1 : 1 ≤ n) (hkn : k ≤ n) (hs : s ≤ k) (hs0 : 0 ≤ s) (hη : s * n * η ≤ δ ^ 2 / 100)
    (hopen : o * f ≤ s * f + k * δ)
    (hlmp : (1 - δ) * A + s * f ≤ (ρ + 6 * δ) * B + o * f + s * n * η) :
    A ≤ (ρ + 10 * δ) * B := by
  have hρ := one_le_ρ
  have hρ' : ρ ≤ 2 := by rw [ρ_eq]; norm_num
  have hn0 : 0 ≤ n := hs0.trans (hs.trans hkn)
  have hB1 : 0 ≤ B := hn0.trans hB
  have h1 : k * δ ≤ δ * B := by nlinarith
  have hn1 : 1 ≤ n ∨ n < 1 := le_or_gt 1 n
  have h2 : (1 - δ) * A ≤ (ρ + 7 * δ) * B + δ ^ 2 / 100 := by nlinarith
  have h3 : δ ^ 2 / 100 ≤ δ ^ 2 / 100 * B := by nlinarith [sq_nonneg δ]
  have h4 : (ρ + 7 * δ) * B + δ ^ 2 / 100 * B ≤ (1 - δ) * ((ρ + 10 * δ) * B) := by
    have : ρ + 7 * δ + δ ^ 2 / 100 ≤ (1 - δ) * (ρ + 10 * δ) := by nlinarith
    nlinarith
  have h5 : (1 - δ) * A ≤ (1 - δ) * ((ρ + 10 * δ) * B) := by linarith
  exact le_of_mul_le_mul_left h5 (by linarith)

end BCFGJPSSV26.Greedy


