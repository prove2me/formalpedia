-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Defs
-- name    : BCFGJPSSV26_Stable_LocalSearch_Defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:46.64639+00:00
-- url     : https://prove2.me/theorems/ee1c072b-df83-4365-a171-6eb7f79d76af
-- title:
--   BCFGJPSSV26.Stable.LocalSearch.Defs — Approximate local optima
-- statement:
--   This is module `BCFGJPSSV26.Stable.LocalSearch.Defs` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   A set `S` of exactly `k` facilities is an **approximate local optimum** for swaps of size `p` and
--   improvement threshold `δ` (`BCFGJPSSV26.Stable.IsALO`) if no nonempty set `T` of at most `k`
--   facilities with `|S \ T| ≤ p` costs less than `(1 - δ) cost(S)`. The local search of
--   `BCFGJPSSV26/Stable/Alg/LocalSearch.lean` stops at one, with `p = 24 N` and `δ = 1/(N k)`.
--   It checks only the sets `T` of exactly `k` facilities, which suffices
--   (`BCFGJPSSV26.Stable.isALO_of_card_eq`): adding facilities of `S \ T` to a smaller
--   `T` lowers its cost and keeps `|S \ T| ≤ p`.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Defs`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/Defs.lean

module

public import Definitions.Def_BCFGJPSSV26_Basic_Metric

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.LocalSearch.Defs` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Approximate local optima

A set `S` of exactly `k` facilities is an **approximate local optimum** for swaps of size `p` and
improvement threshold `δ` (`BCFGJPSSV26.Stable.IsALO`) if no nonempty set `T` of at most `k`
facilities with `|S \ T| ≤ p` costs less than `(1 - δ) cost(S)`. The local search of
`BCFGJPSSV26/Stable/Alg/LocalSearch.lean` stops at one, with `p = 24 N` and `δ = 1/(N k)`.
It checks only the sets `T` of exactly `k` facilities, which suffices
(`BCFGJPSSV26.Stable.isALO_of_card_eq`): adding facilities of `S \ T` to a smaller
`T` lowers its cost and keeps `|S \ T| ≤ p`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

variable (I) in
/-- **Approximate local optimality**: `|S| = k`, and every nonempty `T` with `|T| ≤ k` and
`|S \ T| ≤ p` costs at least `(1 - δ) cost(S)`. -/
def IsALO (p : ℕ) (δ : ℝ) (S : Finset (Fin I.m)) : Prop :=
  S.card = I.k ∧ ∀ T : Finset (Fin I.m), T.Nonempty → T.card ≤ I.k → (S \ T).card ≤ p →
    (1 - δ) * I.costF S ≤ I.costF T

/-- **Swaps to sets of exactly `k` facilities suffice.** -/
theorem isALO_of_card_eq (hv : I.Valid) {p : ℕ} {δ : ℝ} {S : Finset (Fin I.m)}
    (hS : S.card = I.k)
    (h : ∀ T : Finset (Fin I.m), T.card = I.k → (S \ T).card ≤ p →
      (1 - δ) * I.costF S ≤ I.costF T) : IsALO I p δ S := by
  classical
  refine ⟨hS, fun T hT hTk hST ↦ ?_⟩
  have hcard : I.k ≤ (T ∪ S).card := hS ▸ card_le_card subset_union_right
  obtain ⟨T', hTT', hT'S, hT'⟩ := exists_subsuperset_card_eq subset_union_left hTk hcard
  have hST' : (S \ T').card ≤ p :=
    (card_le_card (sdiff_subset_sdiff (subset_refl S) hTT')).trans hST
  exact (h T' hT' hST').trans (Instance.costF_anti hv hTT')

end BCFGJPSSV26.Stable


