-- Prove2me | Definitions.Def_MultitaskContracts_Instance_tStar
-- name    : MultitaskContracts_Instance_tStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:19.273856+00:00
-- url     : https://prove2.me/theorems/4ccdff8e-8ae7-48bb-af83-77e1c3ed1467
-- title:
--   Largest incentive price $t^\star=\max_{S\subsetneq K}\theta(S)$, eq. (10)
-- statement:
--   For a nonempty task set $K$, the **deviations** are the strategies $S\subsetneq K$, and
--   $$t^\star=\max_{S\subsetneq K}\theta(S)$$
--   is the largest incentive price. By eq. (10), $t^\star$ is the optimal payment for success on all tasks of an AoN contract and $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}=P_K(K)\,t^\star$.
--
--   **Formalization Note** `deviations K` is the finite set of `S ≠ Finset.univ`; it contains $\emptyset$ when $K$ is nonempty (the helper `deviations_nonempty`), and the maximum is `Finset.sup'` over it, so `tStar` requires `[Nonempty K]`.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), eq. (10), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_Instance_incentivePrice

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- The deviations `{S : S ⊊ K}`, the strategies other than full effort. -/
def deviations (K : Type*) [Fintype K] [DecidableEq K] : Finset (Finset K) :=
  (Finset.univ : Finset (Finset K)).erase Finset.univ

/-- With `K` nonempty, `∅` is a deviation, so the set of deviations is nonempty. -/
theorem deviations_nonempty (K : Type*) [Fintype K] [DecidableEq K] [Nonempty K] :
    (deviations K).Nonempty :=
  ⟨∅, Finset.mem_erase.2 ⟨Finset.univ_nonempty.ne_empty.symm, Finset.mem_univ _⟩⟩

/-- `t⋆ := max_{S ⊊ K} θ(S)` (eq. (10), §4.1.2, p.13, PDF 15), the largest incentive price.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), eq. (10), p.13.

**Formalization Note.** The maximum is `Finset.sup'` over the finite nonempty set of deviations
`S ≠ univ`; it needs `K` nonempty (otherwise `K` has no deviation). -/
noncomputable def Instance.tStar {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    (I : Instance K) : ℝ :=
  (deviations K).sup' (deviations_nonempty K) I.incentivePrice

end MultitaskContracts


