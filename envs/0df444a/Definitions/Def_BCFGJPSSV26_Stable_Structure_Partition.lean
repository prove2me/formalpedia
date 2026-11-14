-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
-- name    : BCFGJPSSV26_Stable_Structure_Partition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:07:40.993237+00:00
-- url     : https://prove2.me/theorems/ac5954eb-7735-4988-bd81-a38ffd750dd7
-- title:
--   BCFGJPSSV26.Stable.Structure.Partition — The structural theorem
-- statement:
--   This is module `BCFGJPSSV26.Stable.Structure.Partition` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Theorems 3.1 and 3.2]: from good outcomes `w₁` of
--   the client sampling and `w₂` of the cluster sampling, the optimal centers split into
--
--   * `O_S = O_S0 ∪ O_S1`, with substitutes `σ₀` in `LS'` (`BCFGJPSSV26.Stable.Ctx.OSall`);
--   * `O_Λ = O_Λ1 ∪ O_Λ2`, each with its dummy in `Λ = Λ₁ ++ Λ₂`; the early ones `O_Λᵉ` are those of
--     the client sampling led from `core_{6ε}`;
--   * `O_P`, each within `(1 + κ + 4ε) per` of a substitute `ψ(c*)` of `LS_σ`;
--   * `O_R`, each with a satellite `σ(c*)`, distinct and outside `σ(O_S)`;
--
--   with the cost and size bounds of the theorems (`BCFGJPSSV26.Stable.Partition`). A set `Z*` of
--   `z = |LS'| + |Λ| + |O_P| - k` centers of `LS' \ LS_σ` is chosen for the color coding
--   (`BCFGJPSSV26.Stable.Partition.Zstar`).
--
--   The construction (`BCFGJPSSV26.Stable.Hyp.exists_partition`) replaces the paper's greedy pass over
--   `O_B` by a choice of representatives, with the same effect: every `c* ∈ O_B` picks a satellite
--   `σ(c*)` within `(1 + ε) per` (`BCFGJPSSV26.Stable.Ctx.IsFar.near_sat`); for every such satellite
--   outside `LS_X = σ₀(O_S)` (`BCFGJPSSV26.Stable.Ctx.pt_LSX_eq_image`), the least `c*` choosing it
--   goes to `O_R` (`BCFGJPSSV26.Stable.pt_exists_reps`); the other clusters of `O_B` go to `O_P` with
--   backup `ψ(c*) = σ(c*)`, which is in `LS_X` or the satellite of a cluster of `O_R`, and
--   `O_X ⊆ O_P` keeps `ψ_X`. The cost bound (d-i) on `O_S` is
--   `BCFGJPSSV26.Stable.Hyp.pt_cost_OSall` (`30 ε opt`, from [BCFGJPSSV26b, Propositions 4.3 and
--   4.4] and the client sampling, with `cost(S) ≤ 4 opt`).
--
--   Helper lemmas of this file carry the prefix `pt_`.
--
--   **Contents.** The module is published as a whole: 26 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Hyp.exists_partition` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Structure/Partition.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Structure.Partition` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The structural theorem

[BCFGJPSSV26b, Theorems 3.1 and 3.2]: from good outcomes `w₁` of
the client sampling and `w₂` of the cluster sampling, the optimal centers split into

* `O_S = O_S0 ∪ O_S1`, with substitutes `σ₀` in `LS'` (`BCFGJPSSV26.Stable.Ctx.OSall`);
* `O_Λ = O_Λ1 ∪ O_Λ2`, each with its dummy in `Λ = Λ₁ ++ Λ₂`; the early ones `O_Λᵉ` are those of
  the client sampling led from `core_{6ε}`;
* `O_P`, each within `(1 + κ + 4ε) per` of a substitute `ψ(c*)` of `LS_σ`;
* `O_R`, each with a satellite `σ(c*)`, distinct and outside `σ(O_S)`;

with the cost and size bounds of the theorems (`BCFGJPSSV26.Stable.Partition`). A set `Z*` of
`z = |LS'| + |Λ| + |O_P| - k` centers of `LS' \ LS_σ` is chosen for the color coding
(`BCFGJPSSV26.Stable.Partition.Zstar`).

The construction (`BCFGJPSSV26.Stable.Hyp.exists_partition`) replaces the paper's greedy pass over
`O_B` by a choice of representatives, with the same effect: every `c* ∈ O_B` picks a satellite
`σ(c*)` within `(1 + ε) per` (`BCFGJPSSV26.Stable.Ctx.IsFar.near_sat`); for every such satellite
outside `LS_X = σ₀(O_S)` (`BCFGJPSSV26.Stable.Ctx.pt_LSX_eq_image`), the least `c*` choosing it
goes to `O_R` (`BCFGJPSSV26.Stable.pt_exists_reps`); the other clusters of `O_B` go to `O_P` with
backup `ψ(c*) = σ(c*)`, which is in `LS_X` or the satellite of a cluster of `O_R`, and
`O_X ⊆ O_P` keeps `ψ_X`. The cost bound (d-i) on `O_S` is
`BCFGJPSSV26.Stable.Hyp.pt_cost_OSall` (`30 ε opt`, from [BCFGJPSSV26b, Propositions 4.3 and
4.4] and the client sampling, with `cost(S) ≤ 4 opt`).

Helper lemmas of this file carry the prefix `pt_`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

/-- `O_S = O_S0 ∪ O_S1`. -/
noncomputable def OSall (OL : Finset (Fin X.I.m)) : Finset (Fin X.I.m) := X.OS0 ∪ X.OS1 OL

end Ctx

variable {X : Ctx}

theorem Ctx.pt_OS0_subset : X.OS0 ⊆ X.O := by
  classical
  exact union_subset (filter_subset _ _) (filter_subset _ _)

theorem Ctx.pt_not_isSynced_of_mem_OS1 {OL : Finset (Fin X.I.m)} {c : Fin X.I.m}
    (hc : c ∈ X.OS1 OL) : ¬ X.IsSynced c := by
  classical
  intro h
  have h1 := (mem_sdiff.1 (mem_filter.1 hc).1).1
  obtain ⟨hO, h0⟩ := mem_sdiff.1 h1
  exact h0 (mem_union_left _ (mem_filter.2 ⟨hO, h⟩))

/-- `LS_X = σ₀(O_S)`. -/
theorem Ctx.pt_LSX_eq_image (OL : Finset (Fin X.I.m)) : X.LSX OL = (X.OSall OL).image X.σ₀ := by
  classical
  rw [Ctx.LSX, Ctx.OSall, image_union]
  congr 1
  refine image_congr fun c hc ↦ ?_
  simp only [Ctx.σ₀]
  rw [if_neg (X.pt_not_isSynced_of_mem_OS1 hc)]

theorem Ctx.pt_costO_nonneg (hv : X.I.Valid) (c : Fin X.I.m) : 0 ≤ X.costO c :=
  sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _

/-- The local-search costs of distinct optimal clusters add up to at most `cost(S)`. -/
theorem Hyp.pt_sum_costS_C_le (H : Hyp X) {A : Finset (Fin X.I.m)} (hA : A ⊆ X.O) :
    ∑ c ∈ A, X.costS (X.C c) ≤ X.I.costF X.S := by
  unfold Instance.costF
  rw [Instance.sum_clusters H.O_nonempty]
  refine sum_le_sum_of_subset_of_nonneg hA fun c _ _ ↦ ?_
  exact sum_nonneg fun j _ ↦ Instance.dSet_nonneg H.valid _ _

/-- The partition of `O` in abstract form. -/
theorem pt_cover_abstract {α : Type*} [DecidableEq α] {O OS0 OL OS1 OX OL2 OP OR : Finset α}
    (h0 : OS0 ⊆ O) (hL : OL ⊆ O \ OS0) (h1 : OS1 ⊆ (O \ OS0) \ OL)
    (hX : OX ⊆ ((O \ OS0) \ OL) \ OS1) (hL2 : OL2 ⊆ (((O \ OS0) \ OL) \ OS1) \ OX)
    (hu : OP ∪ OR = OX ∪ (((((O \ OS0) \ OL) \ OS1) \ OX) \ OL2)) (hd : Disjoint OP OR) :
    OS0 ∪ OS1 ∪ (OL ∪ OL2) ∪ OP ∪ OR = O ∧ Disjoint (OS0 ∪ OS1) (OL ∪ OL2) ∧
      Disjoint (OS0 ∪ OS1 ∪ (OL ∪ OL2)) OP ∧ Disjoint (OS0 ∪ OS1 ∪ (OL ∪ OL2) ∪ OP) OR := by
  have hPR : ∀ x, x ∈ OP ∨ x ∈ OR → x ∈ OX ∨ ((((x ∈ O ∧ x ∉ OS0) ∧ x ∉ OL) ∧ x ∉ OS1) ∧
      x ∉ OX) ∧ x ∉ OL2 := by
    intro x hx
    have : x ∈ OP ∪ OR := mem_union.2 hx
    rw [hu] at this
    simpa only [mem_union, mem_sdiff] using this
  have hPR' : ∀ x, x ∈ OX ∨ ((((x ∈ O ∧ x ∉ OS0) ∧ x ∉ OL) ∧ x ∉ OS1) ∧
      x ∉ OX) ∧ x ∉ OL2 → x ∈ OP ∨ x ∈ OR := by
    intro x hx
    have : x ∈ OX ∪ (((((O \ OS0) \ OL) \ OS1) \ OX) \ OL2) := by
      simpa only [mem_union, mem_sdiff] using hx
    rw [← hu] at this
    exact mem_union.1 this
  simp only [subset_iff, mem_sdiff] at h0 hL h1 hX hL2
  -- every element of a part is in `O` and in no earlier part
  have pL : ∀ x, x ∈ OL → x ∈ O ∧ x ∉ OS0 := fun x hx ↦ hL hx
  have p1 : ∀ x, x ∈ OS1 → (x ∈ O ∧ x ∉ OS0) ∧ x ∉ OL := fun x hx ↦ h1 hx
  have pX : ∀ x, x ∈ OX → ((x ∈ O ∧ x ∉ OS0) ∧ x ∉ OL) ∧ x ∉ OS1 := fun x hx ↦ hX hx
  have pL2 : ∀ x, x ∈ OL2 → (((x ∈ O ∧ x ∉ OS0) ∧ x ∉ OL) ∧ x ∉ OS1) ∧ x ∉ OX :=
    fun x hx ↦ hL2 hx
  have pPR : ∀ x, x ∈ OP ∨ x ∈ OR → (((x ∈ O ∧ x ∉ OS0) ∧ x ∉ OL) ∧ x ∉ OS1) ∧ x ∉ OL2 := by
    intro x hx
    rcases hPR x hx with h | h
    · refine ⟨pX x h, fun h' ↦ (pL2 x h').2 h⟩
    · exact ⟨h.1.1, h.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_union]
    constructor
    · rintro ((((h | h) | h | h) | h) | h)
      · exact h0 h
      · exact (p1 x h).1.1
      · exact (pL x h).1
      · exact (pL2 x h).1.1.1.1
      · exact (pPR x (Or.inl h)).1.1.1.1
      · exact (pPR x (Or.inr h)).1.1.1.1
    · intro hO
      by_cases a0 : x ∈ OS0
      · exact Or.inl (Or.inl (Or.inl (Or.inl a0)))
      by_cases aL : x ∈ OL
      · exact Or.inl (Or.inl (Or.inr (Or.inl aL)))
      by_cases a1 : x ∈ OS1
      · exact Or.inl (Or.inl (Or.inl (Or.inr a1)))
      by_cases aL2 : x ∈ OL2
      · exact Or.inl (Or.inl (Or.inr (Or.inr aL2)))
      have hXB : x ∈ OX ∨ ((((x ∈ O ∧ x ∉ OS0) ∧ x ∉ OL) ∧ x ∉ OS1) ∧ x ∉ OX) ∧ x ∉ OL2 := by
        by_cases aX : x ∈ OX
        · exact Or.inl aX
        · exact Or.inr ⟨⟨⟨⟨⟨hO, a0⟩, aL⟩, a1⟩, aX⟩, aL2⟩
      rcases hPR' x hXB with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · rw [disjoint_left]
    simp only [mem_union]
    rintro x (h | h) (h' | h')
    · exact (pL x h').2 h
    · exact (pL2 x h').1.1.1.2 h
    · exact (p1 x h).2 h'
    · exact (pL2 x h').1.2 h
  · rw [disjoint_left]
    simp only [mem_union]
    intro x h h'
    have := pPR x (Or.inl h')
    rcases h with (h | h) | h | h
    · exact this.1.1.1.2 h
    · exact this.1.2 h
    · exact this.1.1.2 h
    · exact this.2 h
  · rw [disjoint_left]
    simp only [mem_union]
    intro x h h'
    have := pPR x (Or.inr h')
    rcases h with ((h | h) | h | h) | h
    · exact this.1.1.1.2 h
    · exact this.1.2 h
    · exact this.1.1.2 h
    · exact this.2 h
    · exact disjoint_left.1 hd h h'

/-- `O_Λ1` and `O_Λ2` are disjoint. -/
theorem Ctx.pt_disjoint_OL_OL2 {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁)
    {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} (w₂ : ClusterWitness w₁ LS' Λ₂) :
    Disjoint w₁.OL w₂.OL2 := by
  rw [disjoint_left]
  intro c h1 h2
  exact (mem_sdiff.1 (mem_sdiff.1 (mem_sdiff.1 (w₂.OL2_sub h2)).1).1).2 h1

/-- **The parts cover `O`**, for any split `O_P ∪ O_R = O_X ∪ O_B`. -/
theorem Ctx.pt_cover_of {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁)
    {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} (w₂ : ClusterWitness w₁ LS' Λ₂)
    {OP OR : Finset (Fin X.I.m)} (hu : OP ∪ OR = X.OX w₁.OL ∪ X.OB w₁.OL w₂.OL2)
    (hd : Disjoint OP OR) :
    X.OSall w₁.OL ∪ (w₁.OL ∪ w₂.OL2) ∪ OP ∪ OR = X.O ∧
      Disjoint (X.OSall w₁.OL) (w₁.OL ∪ w₂.OL2) ∧
      Disjoint (X.OSall w₁.OL ∪ (w₁.OL ∪ w₂.OL2)) OP ∧
      Disjoint (X.OSall w₁.OL ∪ (w₁.OL ∪ w₂.OL2) ∪ OP) OR := by
  classical
  exact pt_cover_abstract (O := X.O) (OS0 := X.OS0) (OL := w₁.OL) (OS1 := X.OS1 w₁.OL)
    (OX := X.OX w₁.OL) (OL2 := w₂.OL2) X.pt_OS0_subset w₁.OL_sub (filter_subset _ _)
    (filter_subset _ _) w₂.OL2_sub hu hd

/-- The sizes of the parts add up to `k`. -/
theorem Ctx.pt_card_cover_of {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁)
    {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} (w₂ : ClusterWitness w₁ LS' Λ₂)
    {OP OR : Finset (Fin X.I.m)} (hu : OP ∪ OR = X.OX w₁.OL ∪ X.OB w₁.OL w₂.OL2)
    (hd : Disjoint OP OR) (hO : X.O.card = X.I.k) :
    (X.OSall w₁.OL).card + (w₁.OL.card + w₂.OL2.card) + OP.card + OR.card = X.I.k := by
  obtain ⟨h1, h2, h3, h4⟩ := Ctx.pt_cover_of w₁ w₂ hu hd
  rw [← hO, ← h1, card_union_of_disjoint h4, card_union_of_disjoint h3,
    card_union_of_disjoint h2, card_union_of_disjoint (Ctx.pt_disjoint_OL_OL2 w₁ w₂)]

/-- The dummies of a witness are those of its clusters. -/
theorem pt_exists_eq_of_length_eq_card {Λ : List (Dummy X.I)} {A : Finset (Fin X.I.m)}
    {φ : Fin X.I.m → Dummy X.I} (hlen : Λ.length = A.card) (hmem : ∀ c ∈ A, φ c ∈ Λ)
    (hinj : Set.InjOn φ A) {l : Dummy X.I} (hl : l ∈ Λ) : ∃ c ∈ A, φ c = l := by
  classical
  have hsub : A.image φ ⊆ Λ.toFinset := fun x hx ↦ by
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    exact List.mem_toFinset.2 (hmem c hc)
  have hcard : Λ.toFinset.card ≤ (A.image φ).card := by
    rw [card_image_of_injOn hinj, ← hlen]
    exact List.toFinset_card_le Λ
  have heq := eq_of_subset_of_card_le hsub hcard
  have hl' : l ∈ A.image φ := heq ▸ List.mem_toFinset.2 hl
  exact mem_image.1 hl'

/-- The radii of the dummies of both witnesses are nonnegative. -/
theorem Hyp.pt_radius_nonneg_of_witness (H : Hyp X) {Λ₁ : List (Dummy X.I)}
    (w₁ : ClientWitness X Λ₁) {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)}
    (w₂ : ClusterWitness w₁ LS' Λ₂) : ∀ l ∈ Λ₁ ++ Λ₂, 0 ≤ l.radius := by
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨c, hc, rfl⟩ := pt_exists_eq_of_length_eq_card w₁.length_eq w₁.φ_mem w₁.φ_inj hl
    exact (Instance.dd_nonneg H.valid _ _).trans (w₁.radius_ge c hc)
  · obtain ⟨c, hc, rfl⟩ := pt_exists_eq_of_length_eq_card w₂.length_eq w₂.φ_mem w₂.φ_inj hl
    exact (Instance.dd_nonneg H.valid _ _).trans (w₂.radius_ge c hc)

/-- **The structural partition** ([BCFGJPSSV26b, Theorems 3.1 and 3.2]). -/
structure Partition {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
    {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} (w₂ : ClusterWitness w₁ LS' Λ₂) where
  /-- The clusters with a substitute within `(1 + κ + 4ε) per`. -/
  OP : Finset (Fin X.I.m)
  /-- The clusters with a satellite. -/
  OR : Finset (Fin X.I.m)
  /-- The substitutes of `O_P`. -/
  ψ : Fin X.I.m → Fin X.I.m
  /-- The satellites of `O_R`. -/
  σR : Fin X.I.m → Fin X.I.m
  /-- The centers to be closed, for the color coding. -/
  Zstar : Finset (Fin X.I.m)
  union_eq : OP ∪ OR = X.OX w₁.OL ∪ X.OB w₁.OL w₂.OL2
  OX_sub : X.OX w₁.OL ⊆ OP
  disjoint : Disjoint OP OR
  card_le : w₁.OL.card + w₂.OL2.card + OP.card + OR.card ≤ X.s
  ψ_mem : ∀ c ∈ OP, ψ c ∈ (X.OSall w₁.OL).image X.σ₀ ∪ OR.image σR
  ψ_dist : ∀ c ∈ OP, X.dF c (ψ c) ≤ (1 + X.kap c + 4 * X.ε) * X.per c
  σR_gam : ∀ c ∈ OR, σR c ∈ X.Gam c ∧ X.dF c (σR c) ≤ (1 + X.ε) * X.per c
  σR_inj : Set.InjOn σR OR
  σR_disj : ∀ c ∈ OR, σR c ∉ (X.OSall w₁.OL).image X.σ₀
  σ₀_sub : (X.OSall w₁.OL).image X.σ₀ ⊆ LS'
  Gam_sub : X.GamOf OR ⊆ LS'
  cost_OS : ∑ c ∈ X.OSall w₁.OL, ∑ j ∈ X.C c, X.dist j (X.σ₀ c) ≤
    (1 + eta) * ∑ c ∈ X.OSall w₁.OL, X.costO c + 30 * X.ε * X.opt
  cost_mix : ∑ c ∈ X.GamOf OR ∪ (LS' \ ((X.OSall w₁.OL).image X.σ₀ ∪ OR.image σR)),
    costMixOn X.I LS' (Λ₁ ++ Λ₂) (clusterMix X.I LS' (Λ₁ ++ Λ₂) c) < X.ε ^ 3 * X.opt
  hidden_PL : ∑ c ∈ OP ∪ ((w₁.OL ∪ w₂.OL2) \ w₁.OLe), X.costS (X.core (6 * X.ε) c) <
    X.ε ^ 5 * X.opt
  hidden_R : ∑ c ∈ OR, X.costS (X.core (X.kap c) c) < X.ε ^ 5 * X.opt
  gam_cost : ∑ c ∈ X.GamOf OR, X.costS (X.CS c) < X.ε ^ 3 * X.opt
  far_R : ∀ c ∈ OR, X.IsFar c
  per_pos_P : ∀ c ∈ OP, 0 < X.per c
  Zstar_sub : Zstar ⊆ LS' \ ((X.OSall w₁.OL).image X.σ₀ ∪ OR.image σR)
  Zstar_card : Zstar.card = (LS'.card + (Λ₁.length + Λ₂.length + OP.card)) - X.I.k

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

/-- `O_Λ = O_Λ1 ∪ O_Λ2`. -/
noncomputable def OLam (_ : Partition w₂) : Finset (Fin X.I.m) := w₁.OL ∪ w₂.OL2

/-- The substitutes `LS_σ = σ(O_S ∪ O_R)`. -/
noncomputable def LSσ : Finset (Fin X.I.m) := (X.OSall w₁.OL).image X.σ₀ ∪ Q.OR.image Q.σR

open Classical in
/-- The dummy of a cluster of `O_Λ`. -/
noncomputable def φ (_ : Partition w₂) (c : Fin X.I.m) : Dummy X.I :=
  if c ∈ w₁.OL then w₁.φ c else w₂.φ c

/-- The number `z = |LS'| + |Λ| + |O_P| - k` of centers to close. -/
def z : ℕ := (LS'.card + (Λ₁.length + Λ₂.length + Q.OP.card)) - X.I.k

/-- **The color-coding event**: the centers of `Z*` are red, and the nearest center of
`LS' \ Z*` to each of them is blue. -/
def ColorEvent (red blue : Finset (Fin X.I.m)) : Prop :=
  Q.Zstar ⊆ red ∧ ∀ c ∈ Q.Zstar, ∀ h : (LS' \ Q.Zstar).Nonempty,
    X.I.near (LS' \ Q.Zstar) h (.inr c) ∈ blue

/-- **The parts cover `O`**: every optimal center is in exactly one of `O_S`, `O_Λ`, `O_P`,
`O_R`. -/
theorem cover (H : Hyp X) :
    X.OSall w₁.OL ∪ Q.OLam ∪ Q.OP ∪ Q.OR = X.O ∧ Disjoint (X.OSall w₁.OL) Q.OLam ∧
      Disjoint (X.OSall w₁.OL ∪ Q.OLam) Q.OP ∧ Disjoint (X.OSall w₁.OL ∪ Q.OLam ∪ Q.OP) Q.OR := by
  have _h := H
  exact Ctx.pt_cover_of w₁ w₂ Q.union_eq Q.disjoint

/-- The dummies of `Λ` are those of the clusters of `O_Λ`, one each, with
`d(c*, ℓ) ≤ r ≤ (1 + κ 1[late] + 8ε) per + ε avg_S`. -/
theorem φ_spec (H : Hyp X) :
    (∀ c ∈ Q.OLam, Q.φ c ∈ Λ₁ ++ Λ₂) ∧ Set.InjOn Q.φ Q.OLam ∧
      (Λ₁ ++ Λ₂).length = Q.OLam.card ∧
      ∀ c ∈ Q.OLam, X.I.dd (.inr c) (Q.φ c).leader ≤ (Q.φ c).radius ∧
        (Q.φ c).radius ≤ (1 + (if c ∈ w₁.OLe then 0 else X.kap c) + 8 * X.ε) * X.per c +
          X.ε * X.avgS c := by
  classical
  have hdisj := Ctx.pt_disjoint_OL_OL2 w₁ w₂
  have hφ1 : ∀ c ∈ w₁.OL, Q.φ c = w₁.φ c := fun c hc ↦ by
    unfold φ
    rw [if_pos hc]
  have hφ2 : ∀ c ∈ w₂.OL2, Q.φ c = w₂.φ c := fun c hc ↦ by
    unfold φ
    rw [if_neg (disjoint_right.1 hdisj hc)]
  have hlead : ∀ c₁ ∈ w₁.OL, ∀ c₂ ∈ w₂.OL2, w₁.φ c₁ ≠ w₂.φ c₂ := by
    intro c₁ h₁ c₂ h₂ heq
    obtain ⟨j, -, hj⟩ := w₁.leader c₁ h₁
    obtain ⟨i, -, hi⟩ := w₂.leader c₂ h₂
    have := congrArg Dummy.leader heq
    rw [hj, hi] at this
    exact Sum.inl_ne_inr this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases mem_union.1 hc with h | h
    · rw [hφ1 c h]
      exact List.mem_append_left _ (w₁.φ_mem c h)
    · rw [hφ2 c h]
      exact List.mem_append_right _ (w₂.φ_mem c h)
  · intro c₁ h₁ c₂ h₂ heq
    rcases mem_union.1 h₁ with h₁ | h₁ <;> rcases mem_union.1 h₂ with h₂ | h₂
    · rw [hφ1 c₁ h₁, hφ1 c₂ h₂] at heq
      exact w₁.φ_inj h₁ h₂ heq
    · rw [hφ1 c₁ h₁, hφ2 c₂ h₂] at heq
      exact absurd heq (hlead c₁ h₁ c₂ h₂)
    · rw [hφ2 c₁ h₁, hφ1 c₂ h₂] at heq
      exact absurd heq.symm (hlead c₂ h₂ c₁ h₁)
    · rw [hφ2 c₁ h₁, hφ2 c₂ h₂] at heq
      exact w₂.φ_inj h₁ h₂ heq
  · rw [List.length_append, w₁.length_eq, w₂.length_eq, OLam, card_union_of_disjoint hdisj]
  · intro c hc
    rcases mem_union.1 hc with h | h
    · rw [hφ1 c h]
      exact ⟨w₁.radius_ge c h, w₁.radius_le c h⟩
    · rw [hφ2 c h]
      have hle : c ∉ w₁.OLe := fun h' ↦ disjoint_right.1 hdisj h (w₁.OLe_sub h')
      rw [if_neg hle]
      refine ⟨w₂.radius_ge c h, (w₂.radius_le c h).trans ?_⟩
      have hp : 0 ≤ X.per c := per_nonneg H.valid _ _ _
      have ha : 0 ≤ X.avgS c := div_nonneg (Instance.costOn_nonneg H.valid _ _) (Nat.cast_nonneg _)
      have hε := H.eps_pos
      nlinarith

/-- The radii of the dummies are nonnegative. -/
theorem radius_nonneg (_ : Partition w₂) (H : Hyp X) : ∀ l ∈ Λ₁ ++ Λ₂, 0 ≤ l.radius :=
  H.pt_radius_nonneg_of_witness w₁ w₂

/-- `|O_Λ| + |O_P| ≤ s`. -/
theorem card_OLam_add_OP_le (H : Hyp X) : (Λ₁ ++ Λ₂).length + Q.OP.card ≤ X.s := by
  have _h := H
  have := Q.card_le
  rw [List.length_append, w₁.length_eq, w₂.length_eq]
  omega

end Partition

/-- **Representatives**: a subset `R ⊆ T` on which `f` is injective and misses `L`, such that
every other element of `T` has its image in `L` or in `f(R)` (take the least preimage of every
value outside `L`). -/
theorem pt_exists_reps {α β : Type*} [LinearOrder α] (T : Finset α) (f : α → β)
    (L : Finset β) :
    ∃ R ⊆ T, Set.InjOn f R ∧ (∀ c ∈ R, f c ∉ L) ∧
      ∀ c ∈ T, c ∉ R → f c ∈ L ∨ ∃ c' ∈ R, f c' = f c := by
  classical
  refine ⟨T.filter fun c ↦ f c ∉ L ∧ ∀ c'' ∈ T, f c'' = f c → c ≤ c'', filter_subset _ _, ?_,
    fun c hc ↦ (mem_filter.1 hc).2.1, ?_⟩
  · intro a ha b hb hab
    have ha' := mem_filter.1 (mem_coe.1 ha)
    have hb' := mem_filter.1 (mem_coe.1 hb)
    exact le_antisymm (ha'.2.2 b hb'.1 hab.symm) (hb'.2.2 a ha'.1 hab)
  · intro c hc _
    by_cases hL : f c ∈ L
    · exact Or.inl hL
    · right
      have hne : (T.filter fun c'' ↦ f c'' = f c).Nonempty := ⟨c, mem_filter.2 ⟨hc, rfl⟩⟩
      have hc₀ := mem_filter.1 (min'_mem _ hne)
      refine ⟨_, mem_filter.2 ⟨hc₀.1, by rw [hc₀.2]; exact hL, fun c'' hc'' h ↦
        min'_le _ _ (mem_filter.2 ⟨hc'', h.trans hc₀.2⟩)⟩, hc₀.2⟩

open Classical in
/-- A satellite of `c*` within `(1 + ε) per` of it (`c*` itself if there is none). -/
noncomputable def Ctx.pt_sat (X : Ctx) (c : Fin X.I.m) : Fin X.I.m :=
  if h : ∃ c' ∈ X.Gam c, X.dF c c' ≤ (1 + X.ε) * X.per c then Classical.choose h else c

theorem Ctx.pt_sat_spec {X : Ctx} {c : Fin X.I.m}
    (h : ∃ c' ∈ X.Gam c, X.dF c c' ≤ (1 + X.ε) * X.per c) :
    X.pt_sat c ∈ X.Gam c ∧ X.dF c (X.pt_sat c) ≤ (1 + X.ε) * X.per c := by
  unfold Ctx.pt_sat
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem Ctx.pt_ψX_spec {X : Ctx} {OL : Finset (Fin X.I.m)} {c : Fin X.I.m} (hc : c ∈ X.OX OL) :
    X.ψX OL c ∈ X.LSX OL ∧ X.dF c (X.ψX OL c) ≤ (1 + X.kap c + 4 * X.ε) * X.per c := by
  classical
  have h := (mem_filter.1 hc).2
  unfold Ctx.ψX
  rw [dif_pos h]
  exact Classical.choose_spec h

end BCFGJPSSV26.Stable


