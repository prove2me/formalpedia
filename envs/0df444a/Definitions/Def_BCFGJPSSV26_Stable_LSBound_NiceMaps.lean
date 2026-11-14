-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
-- name    : BCFGJPSSV26_Stable_LSBound_NiceMaps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:10:28.150309+00:00
-- url     : https://prove2.me/theorems/5f58ebb9-ee1e-4141-8109-dca29a61f0e0
-- title:
--   BCFGJPSSV26.Stable.LSBound.NiceMaps — The nuanced local-search bound
-- statement:
--   This is module `BCFGJPSSV26.Stable.LSBound.NiceMaps` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Theorem 3.8] (`BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS`):
--   `cost(S) ≤ Ψ_LS + 150 ε opt`, where `Ψ_LS` is the sum over the optimal clusters of their
--   local-search rows (`BCFGJPSSV26.Stable.Partition.PsiLS`):
--
--   * `(1 + η) cost_OPT(C*)` on `O_S`, `3 cost_OPT(C*)` on `O_Λᵉ`;
--   * `cost_OPT(C*) + |C*| per` on `O_Λˡ ∪ O_P`;
--   * `cost_OPT(core_κ) + 2 cost_OPT(C* \ core_κ) + |C* \ core_κ| per` on `O_R`.
--
--   Proof: [BCFGJPSSV26b, Lemma 3.7, with Claim A.1 and Lemmas A.2 and A.3] give assignments `μA`,
--   `μB` with `B = O_Λᵉ ∪ O_R` and `D₀ = D_Λᵉ ∪ D_R`, cross-free with respect to
--   `D₀`, with `cost_μB(D₀) + cost(μA) - cost_S(D₀) ≤ Ψ_LS + 39 ε opt`
--   (`BCFGJPSSV26.Stable.Partition.exists_nice_maps`; `μB` uses `near(O, ·)` rather than
--   `near(B, ·)` to avoid ties); then apply the refined bound `BCFGJPSSV26.Stable.refined_ls`.
--
--   The maps (`BCFGJPSSV26.Stable.Partition.nmA`, `BCFGJPSSV26.Stable.Partition.nmBm`): with `h` the
--   reverse map of the satellites (`h(σ(c*)) = c*`), the clients `D_Γ` of `D₀` in satellite clusters
--   of `O_R` keep their local-search center under `μA` and go to `h` of it under `μB`; the other
--   clients of `D₀` go to `π_OPT` under `μB` and, under `μA`, to the nearest non-satellite center of
--   their optimal center (on `O_Λᵉ`) or to its satellite `σ(c*)` (on `O_R`); outside `D₀`, `μA` uses
--   `σ₀` on `O_S` and `π_LS(c*)` on `O_P ∪ O_Λˡ`. The constants come out as
--   `cost_μB(D₀) ≤ cost_OPT(D₀) + 4 ε opt` (`BCFGJPSSV26.Stable.Partition.costMap_nmBm_le`, with
--   `d(j, h(c)) - d(j, O) ≤ 3 d(j, S) + 3 ε d(j, O)` from the witness client of the satellite and
--   the farness of `c*`) and `cost(μA) ≤ Ψ_LS + cost_S(D₀) - cost_OPT(D₀) + 32 ε opt`
--   (`BCFGJPSSV26.Stable.Partition.costMap_nmA_le`: `30 ε` from `O_S`, `(201/200) ε` from the
--   `ε |C*| per` slack of the satellites, `O(ε⁴)` from the hidden cores), so `39 ε` holds with room.
--   If `O_Λᵉ ∪ O_R = ∅`, then `D₀ = ∅` would force `μB` into an empty `B`; there `B = O`, `D₀ = D`
--   and `μB = π_OPT` are used instead, with `opt ≤ cost(S)`. Helper declarations of this file carry
--   the prefixes `nm`/`nm_`.
--
--   **Contents.** The module is published as a whole: 61 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LSBound/NiceMaps.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.LSBound.NiceMaps` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The nuanced local-search bound

[BCFGJPSSV26b, Theorem 3.8] (`BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS`):
`cost(S) ≤ Ψ_LS + 150 ε opt`, where `Ψ_LS` is the sum over the optimal clusters of their
local-search rows (`BCFGJPSSV26.Stable.Partition.PsiLS`):

* `(1 + η) cost_OPT(C*)` on `O_S`, `3 cost_OPT(C*)` on `O_Λᵉ`;
* `cost_OPT(C*) + |C*| per` on `O_Λˡ ∪ O_P`;
* `cost_OPT(core_κ) + 2 cost_OPT(C* \ core_κ) + |C* \ core_κ| per` on `O_R`.

Proof: [BCFGJPSSV26b, Lemma 3.7, with Claim A.1 and Lemmas A.2 and A.3] give assignments `μA`,
`μB` with `B = O_Λᵉ ∪ O_R` and `D₀ = D_Λᵉ ∪ D_R`, cross-free with respect to
`D₀`, with `cost_μB(D₀) + cost(μA) - cost_S(D₀) ≤ Ψ_LS + 39 ε opt`
(`BCFGJPSSV26.Stable.Partition.exists_nice_maps`; `μB` uses `near(O, ·)` rather than
`near(B, ·)` to avoid ties); then apply the refined bound `BCFGJPSSV26.Stable.refined_ls`.

The maps (`BCFGJPSSV26.Stable.Partition.nmA`, `BCFGJPSSV26.Stable.Partition.nmBm`): with `h` the
reverse map of the satellites (`h(σ(c*)) = c*`), the clients `D_Γ` of `D₀` in satellite clusters
of `O_R` keep their local-search center under `μA` and go to `h` of it under `μB`; the other
clients of `D₀` go to `π_OPT` under `μB` and, under `μA`, to the nearest non-satellite center of
their optimal center (on `O_Λᵉ`) or to its satellite `σ(c*)` (on `O_R`); outside `D₀`, `μA` uses
`σ₀` on `O_S` and `π_LS(c*)` on `O_P ∪ O_Λˡ`. The constants come out as
`cost_μB(D₀) ≤ cost_OPT(D₀) + 4 ε opt` (`BCFGJPSSV26.Stable.Partition.costMap_nmBm_le`, with
`d(j, h(c)) - d(j, O) ≤ 3 d(j, S) + 3 ε d(j, O)` from the witness client of the satellite and
the farness of `c*`) and `cost(μA) ≤ Ψ_LS + cost_S(D₀) - cost_OPT(D₀) + 32 ε opt`
(`BCFGJPSSV26.Stable.Partition.costMap_nmA_le`: `30 ε` from `O_S`, `(201/200) ε` from the
`ε |C*| per` slack of the satellites, `O(ε⁴)` from the hidden cores), so `39 ε` holds with room.
If `O_Λᵉ ∪ O_R = ∅`, then `D₀ = ∅` would force `μB` into an empty `B`; there `B = O`, `D₀ = D`
and `μB = π_OPT` are used instead, with `opt ≤ cost(S)`. Helper declarations of this file carry
the prefixes `nm`/`nm_`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

open Classical in
/-- The **local-search row** of an optimal cluster. -/
noncomputable def rowLS (c : Fin X.I.m) : ℝ :=
  if c ∈ X.OSall w₁.OL then (1 + eta) * X.costO c
  else if c ∈ w₁.OLe then 3 * X.costO c
  else if c ∈ Q.OLam ∪ Q.OP then X.costO c + (X.C c).card * X.per c
  else costAt X.I c (X.core (X.kap c) c) + 2 * (X.costO c - costAt X.I c (X.core (X.kap c) c)) +
    ((X.C c).card - (X.core (X.kap c) c).card) * X.per c

/-- `Ψ_LS`: the sum of the local-search rows. -/
noncomputable def PsiLS : ℝ := ∑ c ∈ X.O, Q.rowLS c

/-! ### The maps `μA`, `μB` -/

section Maps

variable (H : Hyp X)

/-- The nearest optimal center `π_OPT(j)` of a client. -/
noncomputable def nmO (j : Fin X.I.n) : Fin X.I.m := X.I.near X.O H.O_nonempty (.inl j)

/-- The nearest local-search center `π_LS(j)` of a client. -/
noncomputable def nmS (j : Fin X.I.n) : Fin X.I.m := X.I.near X.S H.S_nonempty (.inl j)

/-- `j ∈ D_Γ`: the client is in `D₀ = D_Λᵉ ∪ D_R` and its local-search center is a satellite of
`O_R`. -/
def nmInΓ (j : Fin X.I.n) : Prop :=
  nmO H j ∈ w₁.OLe ∪ Q.OR ∧ nmS H j ∈ X.GamOf Q.OR

open Classical in
/-- The set `D₀ = D_Λᵉ ∪ D_R`. -/
noncomputable def nmD0 : Finset (Fin X.I.n) := univ.filter fun j ↦ nmO H j ∈ w₁.OLe ∪ Q.OR

open Classical in
/-- The reverse map `h : Γ(O_R) → O_R`: `h(σ(c*)) = c*`, else some `c*` with `c ∈ Γ(c*)`. -/
noncomputable def nmh (c : Fin X.I.m) : Fin X.I.m :=
  if h : ∃ c' ∈ Q.OR, Q.σR c' = c then Classical.choose h
  else if h' : ∃ c' ∈ Q.OR, c ∈ X.Gam c' then Classical.choose h' else c

open Classical in
/-- The nearest non-satellite local-search center `π_{LS \ Γ(O_R)}(c*)`. -/
noncomputable def nmE (c : Fin X.I.m) : Fin X.I.m :=
  if h : (X.S \ X.GamOf Q.OR).Nonempty then X.I.near (X.S \ X.GamOf Q.OR) h (.inr c)
  else X.σcl c

open Classical in
/-- The center of `S` to which `μA` sends the clients of `C*` outside `D_Γ`. -/
noncomputable def nmSub (c : Fin X.I.m) : Fin X.I.m :=
  if c ∈ w₁.OLe then Q.nmE c else if c ∈ Q.OR then Q.σR c
  else if c ∈ X.OSall w₁.OL then X.σ₀ c else X.σcl c

open Classical in
/-- **The map `μA`** (A1)–(A4). -/
noncomputable def nmA (j : Fin X.I.n) : Fin X.I.m :=
  if Q.nmInΓ H j then nmS H j else Q.nmSub (nmO H j)

open Classical in
/-- **The map `μB`** (B1)–(B3). -/
noncomputable def nmBm (j : Fin X.I.n) : Fin X.I.m :=
  if Q.nmInΓ H j then Q.nmh (nmS H j)
  else if nmO H j ∈ w₁.OLe ∪ Q.OR then nmO H j
  else if h : (w₁.OLe ∪ Q.OR).Nonempty then (w₁.OLe ∪ Q.OR).min' h else nmO H j

/-! #### Basic facts -/

omit Q in
theorem nmO_mem (j : Fin X.I.n) : nmO H j ∈ X.O := Instance.near_mem _ _

omit Q in
theorem nmS_mem (j : Fin X.I.n) : nmS H j ∈ X.S := Instance.near_mem _ _

omit Q in
theorem dd_nmO (j : Fin X.I.n) : X.I.dd (.inl j) (.inr (nmO H j)) = X.I.dSet (.inl j) X.O :=
  Instance.dd_near _ _

omit Q in
theorem dd_nmS (j : Fin X.I.n) : X.I.dd (.inl j) (.inr (nmS H j)) = X.I.dSet (.inl j) X.S :=
  Instance.dd_near _ _

omit Q in
theorem nm_mem_C_iff {c : Fin X.I.m} {j : Fin X.I.n} : j ∈ X.C c ↔ nmO H j = c :=
  Instance.mem_cluster H.O_nonempty

theorem mem_nmD0 {j : Fin X.I.n} : j ∈ Q.nmD0 H ↔ nmO H j ∈ w₁.OLe ∪ Q.OR := by
  classical
  unfold nmD0
  simp

theorem nmh_σR {c : Fin X.I.m} (hc : c ∈ Q.OR) : Q.nmh (Q.σR c) = c := by
  unfold nmh
  have h : ∃ c' ∈ Q.OR, Q.σR c' = Q.σR c := ⟨c, hc, rfl⟩
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  exact Q.σR_inj h1 hc h2

theorem nmh_spec {c : Fin X.I.m} (hc : c ∈ X.GamOf Q.OR) :
    Q.nmh c ∈ Q.OR ∧ c ∈ X.Gam (Q.nmh c) := by
  unfold nmh
  by_cases h : ∃ c' ∈ Q.OR, Q.σR c' = c
  · rw [dif_pos h]
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    refine ⟨h1, ?_⟩
    have := (Q.σR_gam _ h1).1
    rwa [h2] at this
  · rw [dif_neg h]
    have h' : ∃ c' ∈ Q.OR, c ∈ X.Gam c' := by
      obtain ⟨c', hc', hm⟩ := mem_biUnion.1 hc
      exact ⟨c', hc', hm⟩
    rw [dif_pos h']
    exact Classical.choose_spec h'

theorem nm_σR_mem_S {c : Fin X.I.m} (hc : c ∈ Q.OR) : Q.σR c ∈ X.S :=
  X.Gam_subset_S c (Q.σR_gam c hc).1

theorem nm_σR_mem_GamOf {c : Fin X.I.m} (hc : c ∈ Q.OR) : Q.σR c ∈ X.GamOf Q.OR :=
  mem_biUnion.2 ⟨c, hc, (Q.σR_gam c hc).1⟩

include H in
theorem nmE_mem (c : Fin X.I.m) : Q.nmE c ∈ X.S := by
  unfold nmE
  split_ifs with h
  · exact (mem_sdiff.1 (Instance.near_mem h _)).1
  · exact H.σcl_mem c

theorem nmE_mem_sdiff (h : (X.S \ X.GamOf Q.OR).Nonempty) (c : Fin X.I.m) :
    Q.nmE c ∈ X.S \ X.GamOf Q.OR := by
  unfold nmE
  rw [dif_pos h]
  exact Instance.near_mem h _

include H in
theorem nmSub_mem (c : Fin X.I.m) : Q.nmSub c ∈ X.S := by
  unfold nmSub
  split_ifs with h1 h2 h3
  · exact Q.nmE_mem H c
  · exact Q.nm_σR_mem_S h2
  · exact H.σ₀_mem c
  · exact H.σcl_mem c

theorem nmA_mem (j : Fin X.I.n) : Q.nmA H j ∈ X.S := by
  unfold nmA
  split_ifs
  · exact nmS_mem H j
  · exact Q.nmSub_mem H _

theorem nmA_of_inΓ {j : Fin X.I.n} (hΓ : Q.nmInΓ H j) : Q.nmA H j = nmS H j := by
  unfold nmA
  rw [if_pos hΓ]

theorem nmA_of_not {j : Fin X.I.n} (hΓ : ¬ Q.nmInΓ H j) : Q.nmA H j = Q.nmSub (nmO H j) := by
  unfold nmA
  rw [if_neg hΓ]

theorem nmBm_of_inΓ {j : Fin X.I.n} (hΓ : Q.nmInΓ H j) : Q.nmBm H j = Q.nmh (nmS H j) := by
  unfold nmBm
  rw [if_pos hΓ]

theorem nmBm_of_not {j : Fin X.I.n} (hΓ : ¬ Q.nmInΓ H j) (hB : nmO H j ∈ w₁.OLe ∪ Q.OR) :
    Q.nmBm H j = nmO H j := by
  unfold nmBm
  rw [if_neg hΓ, if_pos hB]

/-! #### The parts of `O` -/

theorem nm_cover : X.OSall w₁.OL ∪ (w₁.OL ∪ w₂.OL2) ∪ Q.OP ∪ Q.OR = X.O ∧
    Disjoint (X.OSall w₁.OL) (w₁.OL ∪ w₂.OL2) ∧
    Disjoint (X.OSall w₁.OL ∪ (w₁.OL ∪ w₂.OL2)) Q.OP ∧
    Disjoint (X.OSall w₁.OL ∪ (w₁.OL ∪ w₂.OL2) ∪ Q.OP) Q.OR :=
  Ctx.pt_cover_of w₁ w₂ Q.union_eq Q.disjoint

theorem nm_facts_OSall {c : Fin X.I.m} (hc : c ∈ X.OSall w₁.OL) :
    c ∈ X.O ∧ c ∉ w₁.OLe ∧ c ∉ Q.OR := by
  obtain ⟨h1, h2, -, h4⟩ := Q.nm_cover
  refine ⟨h1 ▸ ?_, fun h ↦ disjoint_left.1 h2 hc (mem_union_left _ (w₁.OLe_sub h)),
    fun h ↦ disjoint_right.1 h4 h ?_⟩
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hc))
  · exact mem_union_left _ (mem_union_left _ hc)

theorem nm_facts_OLe {c : Fin X.I.m} (hc : c ∈ w₁.OLe) :
    c ∈ X.O ∧ c ∉ X.OSall w₁.OL ∧ c ∉ Q.OR := by
  obtain ⟨h1, h2, -, h4⟩ := Q.nm_cover
  have hc' : c ∈ w₁.OL ∪ w₂.OL2 := mem_union_left _ (w₁.OLe_sub hc)
  refine ⟨h1 ▸ ?_, fun h ↦ disjoint_left.1 h2 h hc', fun h ↦ disjoint_right.1 h4 h ?_⟩
  · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hc'))
  · exact mem_union_left _ (mem_union_right _ hc')

theorem nm_facts_OPL {c : Fin X.I.m} (hc : c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)) :
    c ∈ X.O ∧ c ∉ X.OSall w₁.OL ∧ c ∉ w₁.OLe ∧ c ∉ Q.OR ∧ c ∈ Q.OLam ∪ Q.OP := by
  obtain ⟨h1, h2, h3, h4⟩ := Q.nm_cover
  have hm : c ∈ X.OSall w₁.OL ∪ (w₁.OL ∪ w₂.OL2) ∪ Q.OP := by
    rcases mem_union.1 hc with h | h
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.1 h).1)
  refine ⟨h1 ▸ mem_union_left _ hm, ?_, ?_, fun h ↦ disjoint_right.1 h4 h hm, ?_⟩
  · intro hS
    rcases mem_union.1 hc with h | h
    · exact disjoint_right.1 h3 h (mem_union_left _ hS)
    · exact disjoint_left.1 h2 hS (mem_sdiff.1 h).1
  · intro hE
    rcases mem_union.1 hc with h | h
    · exact disjoint_right.1 h3 h (mem_union_right _ (mem_union_left _ (w₁.OLe_sub hE)))
    · exact (mem_sdiff.1 h).2 hE
  · change c ∈ (w₁.OL ∪ w₂.OL2) ∪ Q.OP
    rcases mem_union.1 hc with h | h
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.1 h).1

theorem nm_facts_OR {c : Fin X.I.m} (hc : c ∈ Q.OR) :
    c ∈ X.O ∧ c ∉ X.OSall w₁.OL ∧ c ∉ w₁.OLe ∧ c ∉ Q.OLam ∪ Q.OP := by
  obtain ⟨h1, -, -, h4⟩ := Q.nm_cover
  refine ⟨h1 ▸ mem_union_right _ hc, fun h ↦ disjoint_right.1 h4 hc ?_,
    fun h ↦ disjoint_right.1 h4 hc ?_, fun h ↦ disjoint_right.1 h4 hc ?_⟩
  · exact mem_union_left _ (mem_union_left _ h)
  · exact mem_union_left _ (mem_union_right _ (mem_union_left _ (w₁.OLe_sub h)))
  · have h' : c ∈ (w₁.OL ∪ w₂.OL2) ∪ Q.OP := h
    rcases mem_union.1 h' with h | h
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h

theorem nm_mem_OPL_of {c : Fin X.I.m} (hO : c ∈ X.O) (hS : c ∉ X.OSall w₁.OL) (hE : c ∉ w₁.OLe)
    (hR : c ∉ Q.OR) : c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe) := by
  obtain ⟨h1, -, -, -⟩ := Q.nm_cover
  rw [← h1] at hO
  rcases mem_union.1 hO with h | h
  · rcases mem_union.1 h with h | h
    · rcases mem_union.1 h with h | h
      · exact absurd h hS
      · exact mem_union_right _ (mem_sdiff.2 ⟨h, hE⟩)
    · exact mem_union_left _ h
  · exact absurd h hR

theorem nm_disj_OLe_OR : Disjoint w₁.OLe Q.OR :=
  disjoint_left.2 fun _ hc ↦ (Q.nm_facts_OLe hc).2.2

/-- The sum over `O` split over `O_S`, `O_Λᵉ`, `O_P ∪ O_Λˡ` and `O_R`. -/
theorem nm_sum_split (F : Fin X.I.m → ℝ) :
    ∑ c ∈ X.O, F c = ∑ c ∈ X.OSall w₁.OL, F c + ∑ c ∈ w₁.OLe, F c +
      ∑ c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe), F c + ∑ c ∈ Q.OR, F c := by
  obtain ⟨h1, h2, h3, h4⟩ := Q.nm_cover
  rw [← h1, sum_union h4, sum_union h3, sum_union h2,
    ← sum_sdiff (f := F) (w₁.OLe_sub.trans subset_union_left)]
  have hd : Disjoint Q.OP ((w₁.OL ∪ w₂.OL2) \ w₁.OLe) :=
    disjoint_left.2 fun c hc hc' ↦
      disjoint_right.1 h3 hc (mem_union_right _ (mem_sdiff.1 hc').1)
  rw [sum_union hd]
  ring

/-! #### The rows -/

theorem nm_rowLS_OSall {c : Fin X.I.m} (hc : c ∈ X.OSall w₁.OL) :
    Q.rowLS c = (1 + eta) * X.costO c := by
  unfold rowLS
  rw [if_pos hc]

theorem nm_rowLS_OLe {c : Fin X.I.m} (hc : c ∈ w₁.OLe) : Q.rowLS c = 3 * X.costO c := by
  unfold rowLS
  rw [if_neg (Q.nm_facts_OLe hc).2.1, if_pos hc]

theorem nm_rowLS_OPL {c : Fin X.I.m} (hc : c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)) :
    Q.rowLS c = X.costO c + (X.C c).card * X.per c := by
  obtain ⟨-, h1, h2, -, h4⟩ := Q.nm_facts_OPL hc
  unfold rowLS
  rw [if_neg h1, if_neg h2, if_pos h4]

theorem nm_rowLS_OR {c : Fin X.I.m} (hc : c ∈ Q.OR) :
    Q.rowLS c = costAt X.I c (X.core (X.kap c) c) +
      2 * (X.costO c - costAt X.I c (X.core (X.kap c) c)) +
      ((X.C c).card - (X.core (X.kap c) c).card) * X.per c := by
  obtain ⟨-, h1, h2, h3⟩ := Q.nm_facts_OR hc
  unfold rowLS
  rw [if_neg h1, if_neg h2, if_neg h3]

omit Q in
include H in
/-- `|C*| per ≤ (201/200) cost_OPT(C*)`. -/
theorem nm_card_mul_per_le {c : Fin X.I.m} (hc : c ∈ X.O) :
    ((X.C c).card : ℝ) * X.per c ≤ 201 / 200 * X.costO c := by
  have hv := H.valid
  have hε := H.eps_pos
  have hε' : X.ε ≤ 1 / 201 := X.P.eps_le
  have h := per_mul_le_costAt hv hε (by linarith) (H.cluster_nonempty hc) c
  have hp : 0 ≤ X.per c := per_nonneg hv _ _ _
  have hcp : 0 ≤ ((X.C c).card : ℝ) * X.per c := by positivity
  have : (200 / 201) * (((X.C c).card : ℝ) * X.per c) ≤ X.costO c := by
    calc (200 / 201) * (((X.C c).card : ℝ) * X.per c)
        ≤ (1 - X.ε) * ((X.C c).card * X.per c) := mul_le_mul_of_nonneg_right (by linarith) hcp
      _ = (1 - X.ε) * (X.C c).card * X.per c := by ring
      _ ≤ X.costO c := h
  linarith

include H in
theorem nm_rowLS_le {c : Fin X.I.m} (hc : c ∈ X.O) : Q.rowLS c ≤ 4 * X.costO c := by
  have hv := H.valid
  have h0 := X.pt_costO_nonneg hv c
  have h1 := nm_card_mul_per_le H hc
  have hp : 0 ≤ X.per c := per_nonneg hv _ _ _
  have hK0 : 0 ≤ costAt X.I c (X.core (X.kap c) c) :=
    sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have hKp : 0 ≤ ((X.core (X.kap c) c).card : ℝ) * X.per c := mul_nonneg (Nat.cast_nonneg _) hp
  unfold rowLS
  split_ifs
  · unfold eta
    linarith
  · linarith
  · linarith
  · linarith

include H in
/-- `Ψ_LS ≤ 4 opt`. -/
theorem nm_PsiLS_le : Q.PsiLS ≤ 4 * X.opt := by
  rw [PsiLS, H.opt_eq_sum, mul_sum]
  exact sum_le_sum fun c hc ↦ Q.nm_rowLS_le H hc

/-! #### The cost of `μA` ([BCFGJPSSV26b, Lemma A.3]) -/

/-- (A3) The clusters of `O_S` go to their substitutes. -/
theorem sum_OSall_nmA_le :
    ∑ c ∈ X.OSall w₁.OL, ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      ∑ c ∈ X.OSall w₁.OL, Q.rowLS c + 30 * X.ε * X.opt := by
  have h1 : ∀ c ∈ X.OSall w₁.OL, ∀ j ∈ X.C c, Q.nmA H j = X.σ₀ c := by
    intro c hc j hj
    obtain ⟨-, hE, hR⟩ := Q.nm_facts_OSall hc
    have hj' : nmO H j = c := (nm_mem_C_iff H).1 hj
    have hΓ : ¬ Q.nmInΓ H j := fun h ↦ by
      have := h.1
      rw [hj'] at this
      rcases mem_union.1 this with h' | h'
      exacts [hE h', hR h']
    rw [Q.nmA_of_not H hΓ, hj']
    unfold nmSub
    rw [if_neg hE, if_neg hR, if_pos hc]
  calc ∑ c ∈ X.OSall w₁.OL, ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j))
      = ∑ c ∈ X.OSall w₁.OL, ∑ j ∈ X.C c, X.dist j (X.σ₀ c) :=
        sum_congr rfl fun c hc ↦ sum_congr rfl fun j hj ↦ by rw [h1 c hc j hj]; rfl
    _ ≤ (1 + eta) * ∑ c ∈ X.OSall w₁.OL, X.costO c + 30 * X.ε * X.opt := Q.cost_OS
    _ = ∑ c ∈ X.OSall w₁.OL, Q.rowLS c + 30 * X.ε * X.opt := by
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun c hc ↦ (Q.nm_rowLS_OSall hc).symm

/-- (A1) An early cluster: `d(j, μA j) ≤ 2 d(j, c*) + d(j, S)`. -/
theorem sum_C_nmA_le_OLe {c : Fin X.I.m} (hc : c ∈ w₁.OLe) :
    ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤ X.costS (X.C c) + 2 * X.costO c := by
  have hv := H.valid
  have hB : c ∈ w₁.OLe ∪ Q.OR := mem_union_left _ hc
  have hcost : X.costS (X.C c) + 2 * X.costO c =
      ∑ j ∈ X.C c, (X.I.dSet (.inl j) X.S + 2 * X.I.dd (.inl j) (.inr c)) := by
    rw [sum_add_distrib, ← mul_sum]
    rfl
  rw [hcost]
  refine sum_le_sum fun j hj ↦ ?_
  have hj' : nmO H j = c := (nm_mem_C_iff H).1 hj
  have hdj : 0 ≤ X.I.dd (.inl j) (.inr c) := Instance.dd_nonneg hv _ _
  by_cases hΓ : Q.nmInΓ H j
  · rw [Q.nmA_of_inΓ H hΓ, dd_nmS]
    linarith
  · rw [Q.nmA_of_not H hΓ, hj']
    unfold nmSub
    rw [if_pos hc]
    have hnS : nmS H j ∉ X.GamOf Q.OR := fun h ↦ hΓ ⟨hj' ▸ hB, h⟩
    have hne : nmS H j ∈ X.S \ X.GamOf Q.OR := mem_sdiff.2 ⟨nmS_mem H j, hnS⟩
    unfold nmE
    rw [dif_pos ⟨_, hne⟩]
    have h1 := Instance.dd_triangle hv (.inl j) (.inr c)
      (.inr (X.I.near (X.S \ X.GamOf Q.OR) ⟨_, hne⟩ (.inr c)))
    have h1' := Instance.dd_near (I := X.I) ⟨_, hne⟩ (.inr c)
    have h2 := Instance.dSet_le hne (.inr c)
    have h3 := Instance.dd_triangle hv (.inr c) (.inl j) (.inr (nmS H j))
    rw [Instance.dd_comm hv (.inr c) (.inl j), dd_nmS] at h3
    linarith

/-- (A4) A cluster of `O_P ∪ O_Λˡ` goes to the nearest local-search center of its center. -/
theorem sum_C_nmA_le_OPL {c : Fin X.I.m} (hc : c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)) :
    ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      X.costO c + (X.C c).card * X.per c + 1 / X.ε * X.costS (X.core (6 * X.ε) c) := by
  have hv := H.valid
  obtain ⟨hO, hS, hE, hR, -⟩ := Q.nm_facts_OPL hc
  have hμ : ∀ j ∈ X.C c, Q.nmA H j = X.σcl c := by
    intro j hj
    have hj' : nmO H j = c := (nm_mem_C_iff H).1 hj
    have hΓ : ¬ Q.nmInΓ H j := fun h ↦ by
      have := h.1
      rw [hj'] at this
      rcases mem_union.1 this with h' | h'
      exacts [hE h', hR h']
    rw [Q.nmA_of_not H hΓ, hj']
    unfold nmSub
    rw [if_neg hE, if_neg hR, if_neg hS]
  have hne := H.cluster_nonempty hO
  have hε := H.eps_pos
  have hε1 : X.ε ≤ 1 := by linarith [H.eps_lt]
  have hB6 : X.dOS c ≤ X.per c + X.costS (X.core 0 c) / (X.ε * (X.C c).card) :=
    dSet_center_le_per hv hε hε1 hne c X.S
  have hcard : (0 : ℝ) < (X.C c).card := by exact_mod_cast hne.card_pos
  have hsub : X.costS (X.core 0 c) ≤ X.costS (X.core (6 * X.ε) c) :=
    sum_le_sum_of_subset_of_nonneg (core_mono (by linarith) hv _ _)
      fun j _ _ ↦ Instance.dSet_nonneg hv _ _
  calc ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j))
      ≤ ∑ j ∈ X.C c, (X.I.dd (.inl j) (.inr c) + X.dOS c) := by
        refine sum_le_sum fun j hj ↦ ?_
        rw [hμ j hj, ← H.dF_σcl c]
        exact Instance.dd_triangle hv _ _ _
    _ = X.costO c + (X.C c).card * X.dOS c := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        rfl
    _ ≤ X.costO c + (X.C c).card * X.per c + 1 / X.ε * X.costS (X.core (6 * X.ε) c) := by
        have h1 : ((X.C c).card : ℝ) * X.dOS c ≤
            (X.C c).card * X.per c + 1 / X.ε * X.costS (X.core 0 c) := by
          calc ((X.C c).card : ℝ) * X.dOS c
              ≤ (X.C c).card * (X.per c + X.costS (X.core 0 c) / (X.ε * (X.C c).card)) :=
                mul_le_mul_of_nonneg_left hB6 hcard.le
            _ = (X.C c).card * X.per c + 1 / X.ε * X.costS (X.core 0 c) := by
                field_simp
        have h2 : 1 / X.ε * X.costS (X.core 0 c) ≤ 1 / X.ε * X.costS (X.core (6 * X.ε) c) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
        linarith

/-- (A2) A cluster of `O_R`: its `D_Γ` clients stay, the others go to the satellite `σ(c*)`;
the core clients outside `D_Γ` are far from `S`. -/
theorem sum_C_nmA_le_OR {c : Fin X.I.m} (hc : c ∈ Q.OR) :
    ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      X.costS (X.C c) + (X.costO c - costAt X.I c (X.core (X.kap c) c)) +
        ((X.C c).card - (X.core (X.kap c) c).card) * X.per c +
        X.ε * ((X.C c).card * X.per c) + 3 / X.ε * X.costS (X.core (X.kap c) c) := by
  have hv := H.valid
  obtain ⟨-, -, hE, -⟩ := Q.nm_facts_OR hc
  have hB : c ∈ w₁.OLe ∪ Q.OR := mem_union_right _ hc
  have hgam := Q.σR_gam c hc
  have hp : 0 ≤ X.per c := per_nonneg hv _ _ _
  have hκ := kappa_mem (X.xr c)
  have hε := H.eps_pos
  have hε' : X.ε ≤ 1 / 201 := X.P.eps_le
  have hκ' : X.kap c ≤ 23 / 65 := hκ.2
  have hκ0 : 0 ≤ X.kap c := le_trans (by norm_num) hκ.1
  have hKC : X.core (X.kap c) c ⊆ X.C c := core_subset _ _ _ _
  have hnot : ∀ j ∈ X.C c, ¬ Q.nmInΓ H j → X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      X.I.dd (.inl j) (.inr c) + (1 + X.ε) * X.per c := by
    intro j hj hΓ
    have hj' : nmO H j = c := (nm_mem_C_iff H).1 hj
    rw [Q.nmA_of_not H hΓ, hj']
    unfold nmSub
    rw [if_neg hE, if_pos hc]
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr (Q.σR c))
    have h2 : X.I.dd (.inr c) (.inr (Q.σR c)) ≤ (1 + X.ε) * X.per c := hgam.2
    linarith
  have hfar : ∀ j ∈ X.core (X.kap c) c, ¬ Q.nmInΓ H j →
      X.ε * X.per c < X.I.dSet (.inl j) X.S := by
    intro j hjK hΓ
    have hj := hKC hjK
    have hj' : nmO H j = c := (nm_mem_C_iff H).1 hj
    have hjc : X.I.dd (.inl j) (.inr c) ≤ (1 + X.kap c) * X.per c := (mem_filter.1 hjK).2
    by_contra hle
    push Not at hle
    apply hΓ
    refine ⟨hj' ▸ hB, mem_biUnion.2 ⟨c, hc, mem_filter.2 ⟨nmS_mem H j, ?_, j, hj, ?_⟩⟩⟩
    · have h1 := Instance.dd_triangle hv (.inr (nmS H j)) (.inl j) (.inr c)
      rw [Instance.dd_comm hv (.inr (nmS H j)) (.inl j), dd_nmS] at h1
      change X.I.dd (.inr (nmS H j)) (.inr c) ≤ _
      nlinarith
    · change X.I.dd (.inl j) (.inr (nmS H j)) ≤ _
      rw [dd_nmS]
      exact hle
  have hin : ∀ j ∈ X.core (X.kap c) c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      X.I.dSet (.inl j) X.S + 3 / X.ε * X.I.dSet (.inl j) X.S := by
    intro j hjK
    have hdS := Instance.dSet_nonneg hv (.inl j) X.S
    by_cases hΓ : Q.nmInΓ H j
    · rw [Q.nmA_of_inΓ H hΓ, dd_nmS]
      have : 0 ≤ 3 / X.ε * X.I.dSet (.inl j) X.S := by positivity
      linarith
    · have h1 := hnot j (hKC hjK) hΓ
      have h2 := hfar j hjK hΓ
      have hjc : X.I.dd (.inl j) (.inr c) ≤ (1 + X.kap c) * X.per c := (mem_filter.1 hjK).2
      have h3 : 3 * X.per c ≤ 3 / X.ε * X.I.dSet (.inl j) X.S := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]
        linarith
      nlinarith
  have hout : ∀ j ∈ X.C c \ X.core (X.kap c) c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      X.I.dSet (.inl j) X.S + (X.I.dd (.inl j) (.inr c) + (1 + X.ε) * X.per c) := by
    intro j hj
    have hj1 := (mem_sdiff.1 hj).1
    have hdS := Instance.dSet_nonneg hv (.inl j) X.S
    by_cases hΓ : Q.nmInΓ H j
    · rw [Q.nmA_of_inΓ H hΓ, dd_nmS]
      have := Instance.dd_nonneg hv (.inl j) (.inr c)
      nlinarith
    · have := hnot j hj1 hΓ
      linarith
  have hcsd : ((X.C c \ X.core (X.kap c) c).card : ℝ) =
      (X.C c).card - (X.core (X.kap c) c).card := by
    rw [card_sdiff_of_subset hKC, Nat.cast_sub (card_le_card hKC)]
  have hcardK : ((X.core (X.kap c) c).card : ℝ) ≤ (X.C c).card := by
    exact_mod_cast card_le_card hKC
  rw [← sum_sdiff hKC]
  have e1 := sum_le_sum hout
  have e2 := sum_le_sum hin
  rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, hcsd] at e1
  rw [sum_add_distrib, ← mul_sum] at e2
  have hS : X.costS (X.C c) = ∑ j ∈ X.C c \ X.core (X.kap c) c, X.I.dSet (.inl j) X.S +
      ∑ j ∈ X.core (X.kap c) c, X.I.dSet (.inl j) X.S := (sum_sdiff hKC).symm
  have hO' : X.costO c - costAt X.I c (X.core (X.kap c) c) =
      ∑ j ∈ X.C c \ X.core (X.kap c) c, X.I.dd (.inl j) (.inr c) := by
    have := sum_sdiff (f := fun j ↦ X.I.dd (.inl j) (.inr c)) hKC
    unfold Ctx.costO costAt
    linarith
  have hKS : X.costS (X.core (X.kap c) c) =
      ∑ j ∈ X.core (X.kap c) c, X.I.dSet (.inl j) X.S := rfl
  have hεp : X.ε * (((X.C c).card - (X.core (X.kap c) c).card) * X.per c) ≤
      X.ε * ((X.C c).card * X.per c) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    have := mul_nonneg (Nat.cast_nonneg (X.core (X.kap c) c).card) hp
    linarith
  rw [hS, hO', hKS]
  linarith

omit Q in
/-- `t < ε⁵ opt ⇒ t/ε ≤ ε⁴ opt`. -/
theorem nm_div_le_of_lt_pow {e t o : ℝ} (he : 0 < e) (h : t < e ^ 5 * o) :
    1 / e * t ≤ e ^ 4 * o := by
  rw [one_div, inv_mul_le_iff₀ he]
  have : e * (e ^ 4 * o) = e ^ 5 * o := by ring
  linarith

include H in
/-- **The cost of `μA`** ([BCFGJPSSV26b, Lemma A.3]):
`cost(μA) ≤ Ψ_LS + (cost_S(D₀) - cost_OPT(D₀)) + 32 ε opt`. -/
theorem costMap_nmA_le :
    X.I.costMap (Q.nmA H) univ ≤
      Q.PsiLS + ∑ c ∈ w₁.OLe ∪ Q.OR, (X.costS (X.C c) - X.costO c) + 32 * X.ε * X.opt := by
  have hv := H.valid
  have hε := H.eps_pos
  have hε' : X.ε ≤ 1 / 201 := X.P.eps_le
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hcl : X.I.costMap (Q.nmA H) univ =
      ∑ c ∈ X.O, ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) :=
    Instance.sum_clusters H.O_nonempty _
  rw [hcl, Q.nm_sum_split, PsiLS, Q.nm_sum_split, sum_union Q.nm_disj_OLe_OR]
  have a1 := Q.sum_OSall_nmA_le H
  have a2 : ∑ c ∈ w₁.OLe, ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      ∑ c ∈ w₁.OLe, Q.rowLS c + ∑ c ∈ w₁.OLe, (X.costS (X.C c) - X.costO c) := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun c hc ↦ ?_
    rw [Q.nm_rowLS_OLe hc]
    linarith [Q.sum_C_nmA_le_OLe H hc]
  have a3 : ∑ c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe),
        ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      ∑ c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe), Q.rowLS c +
        1 / X.ε * ∑ c ∈ Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe), X.costS (X.core (6 * X.ε) c) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun c hc ↦ ?_
    rw [Q.nm_rowLS_OPL hc]
    linarith [Q.sum_C_nmA_le_OPL H hc]
  have a4 : ∑ c ∈ Q.OR, ∑ j ∈ X.C c, X.I.dd (.inl j) (.inr (Q.nmA H j)) ≤
      ∑ c ∈ Q.OR, Q.rowLS c + ∑ c ∈ Q.OR, (X.costS (X.C c) - X.costO c) +
        X.ε * ∑ c ∈ Q.OR, ((X.C c).card * X.per c) +
        3 / X.ε * ∑ c ∈ Q.OR, X.costS (X.core (X.kap c) c) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_le_sum fun c hc ↦ ?_
    rw [Q.nm_rowLS_OR hc]
    linarith [Q.sum_C_nmA_le_OR H hc]
  have e1 := nm_div_le_of_lt_pow hε Q.hidden_PL
  have e3 : 3 / X.ε * ∑ c ∈ Q.OR, X.costS (X.core (X.kap c) c) ≤ 3 * (X.ε ^ 4 * X.opt) := by
    have := nm_div_le_of_lt_pow hε Q.hidden_R
    have h3 : 3 / X.ε * ∑ c ∈ Q.OR, X.costS (X.core (X.kap c) c) =
        3 * (1 / X.ε * ∑ c ∈ Q.OR, X.costS (X.core (X.kap c) c)) := by ring
    rw [h3]
    linarith
  have e2 : X.ε * ∑ c ∈ Q.OR, ((X.C c).card * X.per c) ≤ X.ε * (201 / 200 * X.opt) := by
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    calc ∑ c ∈ Q.OR, ((X.C c).card * X.per c) ≤ ∑ c ∈ Q.OR, 201 / 200 * X.costO c :=
          sum_le_sum fun c hc ↦ nm_card_mul_per_le H (Q.nm_facts_OR hc).1
      _ = 201 / 200 * ∑ c ∈ Q.OR, X.costO c := by rw [mul_sum]
      _ ≤ 201 / 200 * X.opt := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [H.opt_eq_sum]
          exact sum_le_sum_of_subset_of_nonneg (fun c hc ↦ (Q.nm_facts_OR hc).1)
            fun c _ _ ↦ X.pt_costO_nonneg hv c
  have e4 : X.ε ^ 4 * X.opt ≤ X.ε * X.opt / 1000 := by
    have h3 : X.ε ^ 3 ≤ 1 / 1000 := by
      have := pow_le_pow_left₀ hε.le hε' 3
      calc X.ε ^ 3 ≤ (1 / 201) ^ 3 := this
        _ ≤ 1 / 1000 := by norm_num
    have : X.ε ^ 4 * X.opt = X.ε ^ 3 * (X.ε * X.opt) := by ring
    rw [this]
    have := mul_nonneg hε.le hopt
    nlinarith
  have := mul_nonneg hε.le hopt
  linarith

/-! #### `D₀` and the cost of `μB` ([BCFGJPSSV26b, Lemma A.2]) -/

theorem nmD0_eq : Q.nmD0 H = (w₁.OLe ∪ Q.OR).biUnion X.C := by
  ext j
  rw [Q.mem_nmD0 H, mem_biUnion]
  constructor
  · intro h
    exact ⟨_, h, (nm_mem_C_iff H).2 rfl⟩
  · rintro ⟨c, hc, hj⟩
    rw [(nm_mem_C_iff H).1 hj]
    exact hc

theorem sum_nmD0 (F : Fin X.I.n → ℝ) :
    ∑ j ∈ Q.nmD0 H, F j = ∑ c ∈ w₁.OLe ∪ Q.OR, ∑ j ∈ X.C c, F j := by
  rw [Q.nmD0_eq H, sum_biUnion]
  intro c _ c' _ hcc'
  exact Instance.disjoint_cluster _ hcc'

theorem costOn_sub_costOn_nmD0 :
    X.I.costOn X.S (Q.nmD0 H) - X.I.costOn X.O (Q.nmD0 H) =
      ∑ c ∈ w₁.OLe ∪ Q.OR, (X.costS (X.C c) - X.costO c) := by
  unfold Instance.costOn
  rw [Q.sum_nmD0 H, Q.sum_nmD0 H, ← sum_sub_distrib]
  refine sum_congr rfl fun c _ ↦ ?_
  congr 1
  exact sum_congr rfl fun j hj ↦ Instance.dSet_of_mem_cluster hj

/-- A client of `D_Γ` absorbed into `h(π_LS(j))` pays at most
`d(j, O) + 3 d(j, S) + 3 ε d(j, O)`: its satellite has a witness client of `C*` nearby, and `c*`
is far from `S`. -/
theorem dd_nmBm_le {j : Fin X.I.n} (hΓ : Q.nmInΓ H j) :
    X.I.dd (.inl j) (.inr (Q.nmBm H j)) ≤
      X.I.dSet (.inl j) X.O + 3 * X.I.dSet (.inl j) X.S + 3 * X.ε * X.I.dSet (.inl j) X.O := by
  have hv := H.valid
  rw [Q.nmBm_of_inΓ H hΓ]
  obtain ⟨hoR, hcG⟩ := Q.nmh_spec hΓ.2
  have hfar := Q.far_R _ hoR
  obtain ⟨hcS, -, q, hq, hqc⟩ := mem_filter.1 hcG
  have hqc' : X.I.dd (.inl q) (.inr (nmS H j)) ≤ X.ε * X.per (Q.nmh (nmS H j)) := hqc
  have hjc := dd_nmS H j
  have hqO : X.I.dd (.inl q) (.inr (Q.nmh (nmS H j))) = X.I.dSet (.inl q) X.O :=
    (Instance.dSet_of_mem_cluster hq).symm
  have t1 := Instance.dd_triangle hv (.inl j) (.inr (nmS H j)) (.inr (Q.nmh (nmS H j)))
  have t2 := Instance.dd_triangle hv (.inr (nmS H j)) (.inl q) (.inr (Q.nmh (nmS H j)))
  have t3 := Instance.dd_comm hv (.inr (nmS H j)) (.inl q)
  have t4 := Instance.dSet_triangle hv (.inl q) (.inl j) X.O
  have t5 := Instance.dd_triangle hv (.inl q) (.inr (nmS H j)) (.inl j)
  have t6 := Instance.dd_comm hv (.inr (nmS H j)) (.inl j)
  have hdO := Instance.dSet_le hcS (.inr (Q.nmh (nmS H j)))
  have t7 := Instance.dd_comm hv (.inr (Q.nmh (nmS H j))) (.inr (nmS H j))
  have hfar' := hfar.far
  have havg := hfar.avg_ge
  have hS0 : 0 ≤ X.avgS (Q.nmh (nmS H j)) :=
    div_nonneg (Instance.costOn_nonneg hv _ _) (Nat.cast_nonneg _)
  have hp := hfar.per_pos.le
  have he := H.eps_pos
  have he' : X.ε ≤ 1 / 201 := X.P.eps_le
  have hp99 : 99 / 100 * X.per (Q.nmh (nmS H j)) ≤
      X.per (Q.nmh (nmS H j)) / (1 + 2 * X.ε) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hep : X.ε * X.per (Q.nmh (nmS H j)) ≤ X.per (Q.nmh (nmS H j)) / 201 := by nlinarith
  have hdOS : X.dOS (Q.nmh (nmS H j)) = X.I.dSet (.inr (Q.nmh (nmS H j))) X.S := rfl
  have h1 : 89 / 100 * (99 / 100 * X.per (Q.nmh (nmS H j))) <
      X.I.dd (.inr (nmS H j)) (.inr (Q.nmh (nmS H j))) := by
    unfold eta at hfar'
    have := mul_nonneg he.le hS0
    linarith
  have hjO := Instance.dSet_nonneg hv (.inl j) X.O
  have hjS := Instance.dSet_nonneg hv (.inl j) X.S
  have ha : 87 / 100 * X.per (Q.nmh (nmS H j)) ≤
      X.I.dSet (.inl j) X.S + X.I.dSet (.inl j) X.O := by linarith
  have hea := mul_le_mul_of_nonneg_left ha he.le
  have hejS : X.ε * X.I.dSet (.inl j) X.S ≤ X.I.dSet (.inl j) X.S / 201 := by nlinarith
  have hejO := mul_nonneg he.le hjO
  linarith

/-- **The cost of `μB`** ([BCFGJPSSV26b, Lemma A.2]): `cost_μB(D₀) ≤ cost_OPT(D₀) + 4 ε opt`. -/
theorem costMap_nmBm_le :
    X.I.costMap (Q.nmBm H) (Q.nmD0 H) ≤ X.I.costOn X.O (Q.nmD0 H) + 4 * X.ε * X.opt := by
  classical
  have hv := H.valid
  have hle : ∀ j ∈ Q.nmD0 H, X.I.dd (.inl j) (.inr (Q.nmBm H j)) ≤
      X.I.dSet (.inl j) X.O + if Q.nmInΓ H j then
        3 * X.I.dSet (.inl j) X.S + 3 * X.ε * X.I.dSet (.inl j) X.O else 0 := by
    intro j hj
    split_ifs with hΓ
    · linarith [Q.dd_nmBm_le H hΓ]
    · rw [Q.nmBm_of_not H hΓ ((Q.mem_nmD0 H).1 hj), dd_nmO, add_zero]
  have hsum := sum_le_sum hle
  rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_add_distrib, ← mul_sum,
    ← mul_sum] at hsum
  have hΓS : ∑ j ∈ (Q.nmD0 H).filter (Q.nmInΓ H), X.I.dSet (.inl j) X.S <
      X.ε ^ 3 * X.opt := by
    refine lt_of_le_of_lt ?_ Q.gam_cost
    have hsub : (Q.nmD0 H).filter (Q.nmInΓ H) ⊆ (X.GamOf Q.OR).biUnion X.CS := by
      intro j hj
      have hΓ := (mem_filter.1 hj).2
      exact mem_biUnion.2 ⟨nmS H j, hΓ.2, Instance.mem_cluster_near H.S_nonempty j⟩
    calc ∑ j ∈ (Q.nmD0 H).filter (Q.nmInΓ H), X.I.dSet (.inl j) X.S
        ≤ ∑ j ∈ (X.GamOf Q.OR).biUnion X.CS, X.I.dSet (.inl j) X.S :=
          sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ Instance.dSet_nonneg hv _ _
      _ = ∑ c ∈ X.GamOf Q.OR, X.costS (X.CS c) := by
          rw [sum_biUnion]
          · rfl
          · intro c _ c' _ hcc'
            exact Instance.disjoint_cluster _ hcc'
  have hΓO : ∑ j ∈ (Q.nmD0 H).filter (Q.nmInΓ H), X.I.dSet (.inl j) X.O ≤ X.opt := by
    calc ∑ j ∈ (Q.nmD0 H).filter (Q.nmInΓ H), X.I.dSet (.inl j) X.O
        ≤ ∑ j, X.I.dSet (.inl j) X.O :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ Instance.dSet_nonneg hv _ _
      _ = X.opt := H.isOpt.cost
  have hε := H.eps_pos
  have hε' : X.ε ≤ 1 / 201 := X.P.eps_le
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hε3 : X.ε ^ 3 * X.opt ≤ X.ε * X.opt / 100 := by
    have : X.ε ^ 3 * X.opt = X.ε ^ 2 * (X.ε * X.opt) := by ring
    rw [this]
    have h2 : X.ε ^ 2 ≤ 1 / 100 := by nlinarith
    have := mul_nonneg hε.le hopt
    nlinarith
  have hεO := mul_le_mul_of_nonneg_left hΓO hε.le
  have hcm : X.I.costMap (Q.nmBm H) (Q.nmD0 H) =
      ∑ j ∈ Q.nmD0 H, X.I.dd (.inl j) (.inr (Q.nmBm H j)) := rfl
  have hco : X.I.costOn X.O (Q.nmD0 H) = ∑ j ∈ Q.nmD0 H, X.I.dSet (.inl j) X.O := rfl
  rw [hcm, hco]
  nlinarith

/-! #### Cross-freeness and size ([BCFGJPSSV26b, Claim A.1]) -/

include H in
theorem nmBm_mem (hB : (w₁.OLe ∪ Q.OR).Nonempty) (j : Fin X.I.n) :
    Q.nmBm H j ∈ w₁.OLe ∪ Q.OR := by
  by_cases h1 : Q.nmInΓ H j
  · rw [Q.nmBm_of_inΓ H h1]
    exact mem_union_right _ (Q.nmh_spec h1.2).1
  · by_cases h2 : nmO H j ∈ w₁.OLe ∪ Q.OR
    · rw [Q.nmBm_of_not H h1 h2]
      exact h2
    · unfold nmBm
      rw [if_neg h1, if_neg h2, dif_pos hB]
      exact min'_mem _ _

/-- On `D₀`, a client sent by `μA` to a satellite is sent by `μB` to `h` of it. -/
theorem nmBm_eq_nmh {j : Fin X.I.n} (hj : nmO H j ∈ w₁.OLe ∪ Q.OR)
    (hA : Q.nmA H j ∈ X.GamOf Q.OR) : Q.nmBm H j = Q.nmh (Q.nmA H j) := by
  by_cases hΓ : Q.nmInΓ H j
  · rw [Q.nmA_of_inΓ H hΓ, Q.nmBm_of_inΓ H hΓ]
  · rw [Q.nmBm_of_not H hΓ hj]
    rw [Q.nmA_of_not H hΓ] at hA ⊢
    rcases mem_union.1 hj with hE | hR
    · exfalso
      have hnS : nmS H j ∉ X.GamOf Q.OR := fun h ↦ hΓ ⟨hj, h⟩
      have hne : (X.S \ X.GamOf Q.OR).Nonempty := ⟨_, mem_sdiff.2 ⟨nmS_mem H j, hnS⟩⟩
      unfold nmSub at hA
      rw [if_pos hE] at hA
      exact (mem_sdiff.1 (Q.nmE_mem_sdiff hne _)).2 hA
    · unfold nmSub
      rw [if_neg (Q.nm_facts_OR hR).2.2.1, if_pos hR, Q.nmh_σR hR]

/-- On `D₀`, a client sent by `μA` outside the satellites is early, and both maps depend only
on its optimal center. -/
theorem nmA_not_Gam {j : Fin X.I.n} (hj : nmO H j ∈ w₁.OLe ∪ Q.OR)
    (hA : Q.nmA H j ∉ X.GamOf Q.OR) :
    nmO H j ∈ w₁.OLe ∧ Q.nmBm H j = nmO H j ∧ Q.nmA H j = Q.nmE (nmO H j) := by
  by_cases hΓ : Q.nmInΓ H j
  · exfalso
    rw [Q.nmA_of_inΓ H hΓ] at hA
    exact hA hΓ.2
  · rw [Q.nmBm_of_not H hΓ hj]
    rw [Q.nmA_of_not H hΓ] at hA ⊢
    rcases mem_union.1 hj with hE | hR
    · unfold nmSub
      rw [if_pos hE]
      exact ⟨hE, rfl, rfl⟩
    · exfalso
      unfold nmSub at hA
      rw [if_neg (Q.nm_facts_OR hR).2.2.1, if_pos hR] at hA
      exact hA (Q.nm_σR_mem_GamOf hR)

theorem nmA_not_Gam_of {j : Fin X.I.n} (hj : nmO H j ∈ w₁.OLe ∪ Q.OR)
    (hB : Q.nmBm H j ∈ w₁.OLe) : Q.nmA H j ∉ X.GamOf Q.OR := by
  intro hA
  rw [Q.nmBm_eq_nmh H hj hA] at hB
  exact (Q.nm_facts_OLe hB).2.2 (Q.nmh_spec hA).1

/-- **`(μA, μB)` is cross-free with respect to `D₀`.** -/
theorem nm_crossFree : CrossFreeWrt X.I X.S (Q.nmA H) (Q.nmBm H) (Q.nmD0 H) := by
  classical
  intro c hc c'
  have hcA : ∀ j, Q.nmA H j = c → j ∈ Q.nmD0 H := (mem_filter.1 hc).2
  by_cases hcΓ : c ∈ X.GamOf Q.OR
  · by_cases hc' : Q.nmh c = c'
    · right
      left
      intro j hj
      have hjc : Q.nmA H j = c := (mem_filter.1 hj).2
      have hjD := (Q.mem_nmD0 H).1 (hcA j hjc)
      refine mem_filter.2 ⟨mem_univ _, ?_, fun j' hj' ↦ hcA j' (hj'.trans hjc)⟩
      rw [Q.nmBm_eq_nmh H hjD (hjc ▸ hcΓ), hjc, hc']
    · left
      rw [disjoint_left]
      intro j hj hj'
      have hjc : Q.nmA H j = c := (mem_filter.1 hj).2
      have hjD := (Q.mem_nmD0 H).1 (hcA j hjc)
      have h1 := Q.nmBm_eq_nmh H hjD (hjc ▸ hcΓ)
      have h2 : Q.nmBm H j = c' := (mem_filter.1 hj').2.1
      exact hc' (by rw [← h2, h1, hjc])
  · by_cases hc' : c' ∈ w₁.OLe ∧ Q.nmE c' = c
    · right
      right
      intro j hj
      obtain ⟨hjB, hjall⟩ := (mem_filter.1 hj).2
      have hjD := (Q.mem_nmD0 H).1 (hjall j rfl)
      have hA := Q.nmA_not_Gam_of H hjD (hjB ▸ hc'.1)
      obtain ⟨-, h1, h2⟩ := Q.nmA_not_Gam H hjD hA
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [h2, ← h1, hjB, hc'.2]
    · left
      rw [disjoint_left]
      intro j hj hj'
      have hjc : Q.nmA H j = c := (mem_filter.1 hj).2
      have hjD := (Q.mem_nmD0 H).1 (hcA j hjc)
      obtain ⟨hE, h1, h2⟩ := Q.nmA_not_Gam H hjD (hjc ▸ hcΓ)
      have hjB : Q.nmBm H j = c' := (mem_filter.1 hj').2.1
      exact hc' ⟨by rw [← hjB, h1]; exact hE, by rw [← hjB, h1, ← h2, hjc]⟩

/-- **`|B| + |μA(D \ D₀)| ≤ k`**: outside `D₀`, `μA` takes the values `σ₀(O_S)` and
`π_LS(O_P ∪ O_Λˡ)`. -/
theorem nm_card_size :
    (w₁.OLe ∪ Q.OR).card + ((Q.nmD0 H)ᶜ.image (Q.nmA H)).card ≤ X.I.k := by
  classical
  have hsub : (Q.nmD0 H)ᶜ.image (Q.nmA H) ⊆ (X.OSall w₁.OL).image X.σ₀ ∪
      (Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)).image X.σcl := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    have hjB : nmO H j ∉ w₁.OLe ∪ Q.OR := fun h ↦ (mem_compl.1 hj) ((Q.mem_nmD0 H).2 h)
    have hΓ : ¬ Q.nmInΓ H j := fun h ↦ hjB h.1
    rw [Q.nmA_of_not H hΓ]
    have hcE : nmO H j ∉ w₁.OLe := fun h ↦ hjB (mem_union_left _ h)
    have hcR : nmO H j ∉ Q.OR := fun h ↦ hjB (mem_union_right _ h)
    unfold nmSub
    rw [if_neg hcE, if_neg hcR]
    by_cases hcS : nmO H j ∈ X.OSall w₁.OL
    · rw [if_pos hcS]
      exact mem_union_left _ (mem_image_of_mem _ hcS)
    · rw [if_neg hcS]
      exact mem_union_right _ (mem_image_of_mem _ (Q.nm_mem_OPL_of (nmO_mem H j) hcS hcE hcR))
  have hcount := Ctx.pt_card_cover_of w₁ w₂ Q.union_eq Q.disjoint H.isOpt.card
  have hsubLe : w₁.OLe ⊆ w₁.OL ∪ w₂.OL2 := fun c hc ↦ mem_union_left _ (w₁.OLe_sub hc)
  have h1 := card_le_card hsub
  have h2 := card_union_le ((X.OSall w₁.OL).image X.σ₀)
    ((Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)).image X.σcl)
  have h3 : ((X.OSall w₁.OL).image X.σ₀).card ≤ (X.OSall w₁.OL).card := card_image_le
  have h4 : ((Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)).image X.σcl).card ≤
      (Q.OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)).card := card_image_le
  have h5 := card_union_le Q.OP ((w₁.OL ∪ w₂.OL2) \ w₁.OLe)
  have h6 : ((w₁.OL ∪ w₂.OL2) \ w₁.OLe).card = (w₁.OL ∪ w₂.OL2).card - w₁.OLe.card :=
    card_sdiff_of_subset hsubLe
  have h7 : (w₁.OL ∪ w₂.OL2).card = w₁.OL.card + w₂.OL2.card :=
    card_union_of_disjoint (Ctx.pt_disjoint_OL_OL2 w₁ w₂)
  have h8 := card_union_le w₁.OLe Q.OR
  have h9 : w₁.OLe.card ≤ (w₁.OL ∪ w₂.OL2).card := card_le_card hsubLe
  omega

end Maps

end Partition

end BCFGJPSSV26.Stable


