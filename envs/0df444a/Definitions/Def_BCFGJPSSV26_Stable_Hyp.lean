-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Hyp
-- name    : BCFGJPSSV26_Stable_Hyp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:58:33.082642+00:00
-- url     : https://prove2.me/theorems/c2f3ced7-e0b9-419f-a822-32681b15c6f0
-- title:
--   BCFGJPSSV26.Stable.Hyp — The setting of the analysis
-- statement:
--   This is module `BCFGJPSSV26.Stable.Hyp` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The analysis of [BCFGJPSSV26b] is about one instance `I`, one accuracy `1/N`, one stability
--   parameter `β` with `L ≥ 1/β`, one optimal set `O` of exactly `k` facilities and the local-search
--   set `S` (`BCFGJPSSV26.Stable.Ctx`). The standing hypotheses (H) are bundled once
--   (`BCFGJPSSV26.Stable.Hyp`): a valid instance with `2 ≤ k ≤ m`, `opt > 0`, a `β`-stable instance,
--   `O` optimal and `S` an approximate local optimum. (The cases `k = 1` and `opt = 0` are handled by
--   the local search alone, in `BCFGJPSSV26/Stable/Final/Combine.lean`.)
--
--   The objects of the analysis are functions of the context: for a center `c* ∈ O`, its cluster
--   `C*` (`BCFGJPSSV26.Stable.Ctx.C`), its cost `cost_OPT(C*)` (`BCFGJPSSV26.Stable.Ctx.costO`), its
--   percentile, averages, cores and `κ`; for `c ∈ S` the local-search cluster
--   (`BCFGJPSSV26.Stable.Ctx.CS`).
--
--   **Contents.** The module is published as a whole: 29 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Hyp`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Hyp.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Params
public import Definitions.Def_BCFGJPSSV26_Stable_Percentile
public import Definitions.Def_BCFGJPSSV26_Stable_Kappa
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Defs

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Hyp` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The setting of the analysis

The analysis of [BCFGJPSSV26b] is about one instance `I`, one accuracy `1/N`, one stability
parameter `β` with `L ≥ 1/β`, one optimal set `O` of exactly `k` facilities and the local-search
set `S` (`BCFGJPSSV26.Stable.Ctx`). The standing hypotheses (H) are bundled once
(`BCFGJPSSV26.Stable.Hyp`): a valid instance with `2 ≤ k ≤ m`, `opt > 0`, a `β`-stable instance,
`O` optimal and `S` an approximate local optimum. (The cases `k = 1` and `opt = 0` are handled by
the local search alone, in `BCFGJPSSV26/Stable/Final/Combine.lean`.)

The objects of the analysis are functions of the context: for a center `c* ∈ O`, its cluster
`C*` (`BCFGJPSSV26.Stable.Ctx.C`), its cost `cost_OPT(C*)` (`BCFGJPSSV26.Stable.Ctx.costO`), its
percentile, averages, cores and `κ`; for `c ∈ S` the local-search cluster
(`BCFGJPSSV26.Stable.Ctx.CS`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- The **context** of the analysis. -/
structure Ctx where
  /-- The accuracy. -/
  P : Prm
  /-- The instance. -/
  I : Instance
  /-- The stability parameter. -/
  β : ℝ
  /-- The number `L ≥ 1/β` given to the algorithm. -/
  L : ℕ
  /-- An optimal set of exactly `k` facilities. -/
  O : Finset (Fin I.m)
  /-- The local-search set. -/
  S : Finset (Fin I.m)

namespace Ctx

variable (X : Ctx)

/-- `ε = 1/N`. -/
noncomputable def ε : ℝ := X.P.eps

/-- The bound `s = 632 N L` on the special clusters. -/
abbrev s : ℕ := Par.s X.P.N X.L

/-- The optimum `opt k`. -/
noncomputable def opt : ℝ := X.I.opt X.I.k

/-- The distance from client `j` to facility `i`. -/
noncomputable def dist (j : Fin X.I.n) (i : Fin X.I.m) : ℝ := X.I.dd (.inl j) (.inr i)

/-- The distance between facilities. -/
noncomputable def dF (i i' : Fin X.I.m) : ℝ := X.I.dd (.inr i) (.inr i')

/-- The optimal cluster `C*` of `c* ∈ O`. -/
noncomputable def C (c : Fin X.I.m) : Finset (Fin X.I.n) := X.I.cluster X.O c

/-- The local-search cluster of `c ∈ S`. -/
noncomputable def CS (c : Fin X.I.m) : Finset (Fin X.I.n) := X.I.cluster X.S c

/-- `cost_OPT(C*) = ∑_{j ∈ C*} d(j, c*)`. -/
noncomputable def costO (c : Fin X.I.m) : ℝ := costAt X.I c (X.C c)

/-- `cost_OPT(D) = ∑_{j ∈ D} d(j, O)`, on any set of clients. -/
noncomputable def costOD (D : Finset (Fin X.I.n)) : ℝ := X.I.costOn X.O D

/-- `cost_S(D) = ∑_{j ∈ D} d(j, S)`. -/
noncomputable def costS (D : Finset (Fin X.I.n)) : ℝ := X.I.costOn X.S D

/-- The percentile `per(C*)`. -/
noncomputable def per (c : Fin X.I.m) : ℝ := Stable.per X.I X.ε (X.C c) c

/-- `avg_OPT(C*)`. -/
noncomputable def avgO (c : Fin X.I.m) : ℝ := X.costO c / (X.C c).card

/-- `avg_S(C*)`: the average distance of `C*` to `S`. -/
noncomputable def avgS (c : Fin X.I.m) : ℝ := X.costS (X.C c) / (X.C c).card

/-- `core_γ(C*)`. -/
noncomputable def core (γ : ℝ) (c : Fin X.I.m) : Finset (Fin X.I.n) :=
  Stable.core X.I X.ε γ (X.C c) c

/-- `x(C*) = per/avg_OPT`. -/
noncomputable def xr (c : Fin X.I.m) : ℝ := xRatio (X.per c) (X.avgO c)

/-- `κ(C*)`. -/
noncomputable def kap (c : Fin X.I.m) : ℝ := kappa (X.xr c)

/-- `d(c*, S)`. -/
noncomputable def dOS (c : Fin X.I.m) : ℝ := X.I.dSet (.inr c) X.S

/-- The number `b = |enc I| + 7 N` of bits per chunk of coins. -/
abbrev b : ℕ := Par.bits X.P.N (encInstance X.I).length

/-- The clients of the clusters of a set of centers: `D_A = ⋃_{c* ∈ A} C*`. -/
noncomputable def DOf (A : Finset (Fin X.I.m)) : Finset (Fin X.I.n) := A.biUnion X.C

end Ctx

/-- **The standing hypotheses (H)** of [BCFGJPSSV26b, Sections 3–6]. -/
structure Hyp (X : Ctx) : Prop where
  valid : X.I.Valid
  k_le_m : X.I.k ≤ X.I.m
  two_le_k : 2 ≤ X.I.k
  opt_pos : 0 < X.I.opt X.I.k
  β_pos : 0 < X.β
  stable : X.I.IsStable X.β
  L_ge : 1 / X.β ≤ X.L
  isOpt : X.I.IsOpt X.O
  alo : IsALO X.I (Par.p X.P.N) (1 / (X.P.N * X.I.k)) X.S

namespace Hyp

variable {X : Ctx}

theorem eps_pos (_ : Hyp X) : 0 < X.ε := X.P.eps_pos

theorem eps_lt (_ : Hyp X) : X.ε < 1 / 200 := X.P.eps_lt

variable (H : Hyp X)
include H

theorem O_nonempty : X.O.Nonempty := H.isOpt.nonempty H.valid

theorem S_nonempty : X.S.Nonempty := by
  rw [← card_pos, H.alo.1]
  have := H.two_le_k
  omega

theorem one_le_L : 1 ≤ X.L := Prm.one_le_L H.β_pos H.L_ge

/-- `s ≥ 632/(εβ)`. -/
theorem s_ge : 632 / (X.ε * X.β) ≤ X.s := X.P.s_ge H.β_pos H.L_ge

/-- There is a client, since `opt > 0`. -/
theorem one_le_n : 1 ≤ X.I.n := by
  by_contra h
  have : IsEmpty (Fin X.I.n) := ⟨fun j ↦ by have := j.2; omega⟩
  have h0 : X.I.costF X.O = 0 := by
    unfold Instance.costF
    rw [univ_eq_empty, sum_empty]
  have := H.opt_pos
  rw [← H.isOpt.cost, h0] at this
  exact lt_irrefl _ this

/-- The optimal cost is the sum of the costs of the optimal clusters. -/
theorem opt_eq_sum : X.opt = ∑ c ∈ X.O, X.costO c := by
  rw [Ctx.opt, ← H.isOpt.cost, Instance.costF_eq_sum_clusters H.O_nonempty]
  rfl

end Hyp

end BCFGJPSSV26.Stable


