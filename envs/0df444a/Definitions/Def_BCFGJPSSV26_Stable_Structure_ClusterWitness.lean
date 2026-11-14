-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
-- name    : BCFGJPSSV26_Stable_Structure_ClusterWitness
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:05:40.919601+00:00
-- url     : https://prove2.me/theorems/2f6c7aa8-30e1-47bd-8079-2e50dc6fae34
-- title:
--   BCFGJPSSV26.Stable.Structure.ClusterWitness — The outcome of the cluster sampling
-- statement:
--   This is module `BCFGJPSSV26.Stable.Structure.ClusterWitness` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Given a good outcome `w₁` of the client sampling, the substitutes found so far are
--   `LS_X = σ₀(O_S0) ∪ σ₁(O_S1)` (`BCFGJPSSV26.Stable.Ctx.LSX`), and `O_X` are the clusters of `O₂`
--   with a center within `(1 + κ + 4ε) per` of one of them (`BCFGJPSSV26.Stable.Ctx.OX`).
--
--   The cluster-sampling theorem of [BCFGJPSSV26b, Section 4.4]: a pair `(LS', Λ₂)` is a good
--   outcome of the cluster sampling (`BCFGJPSSV26.Stable.ClusterWitness`) if `LS_X ⊆ LS' ⊆ S` with
--   `|S \ LS'| ≤ s`, the dummies of `Λ₂` match distinct clusters `O_Λ2` of `O₂ \ O_X`, with radii
--   between the distance to the center and `(1 + κ + 6ε) per`, the remaining clusters
--   `O_B = (O₂ \ O_X) \ O_Λ2` keep all their satellites in `LS'`, and two sums are below `ε³ opt`:
--   the local-search costs of the satellite clusters of `O_B` (`costcond₀`), and the costs in the
--   mixed set `(LS', Λ₁ ++ Λ₂)` of the clusters of those satellites and of the centers of
--   `LS' \ LS_X` (`costcond₁`).
--
--   Also (used by the cluster-sampling analysis):
--
--   * the cost bound for the clusters outside `O₂` of [BCFGJPSSV26b, Section 4.7]
--     (`BCFGJPSSV26.Stable.Hyp.cost_exceptional_le`): the clusters outside `O₂` cost at most
--     `5 cost_OPT + 37 ε opt` in `(LS_X, Λ₁)`;
--   * the claim on the intermediate cost of [BCFGJPSSV26b, Section 4.7]
--     (`BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`): every intermediate mixed set of the cluster
--     sampling costs less than `6 opt`.
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Hyp.card_S_sdiff_LSX_le`, `BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Structure/ClusterWitness.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Structure.ClusterWitness` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The outcome of the cluster sampling

Given a good outcome `w₁` of the client sampling, the substitutes found so far are
`LS_X = σ₀(O_S0) ∪ σ₁(O_S1)` (`BCFGJPSSV26.Stable.Ctx.LSX`), and `O_X` are the clusters of `O₂`
with a center within `(1 + κ + 4ε) per` of one of them (`BCFGJPSSV26.Stable.Ctx.OX`).

The cluster-sampling theorem of [BCFGJPSSV26b, Section 4.4]: a pair `(LS', Λ₂)` is a good
outcome of the cluster sampling (`BCFGJPSSV26.Stable.ClusterWitness`) if `LS_X ⊆ LS' ⊆ S` with
`|S \ LS'| ≤ s`, the dummies of `Λ₂` match distinct clusters `O_Λ2` of `O₂ \ O_X`, with radii
between the distance to the center and `(1 + κ + 6ε) per`, the remaining clusters
`O_B = (O₂ \ O_X) \ O_Λ2` keep all their satellites in `LS'`, and two sums are below `ε³ opt`:
the local-search costs of the satellite clusters of `O_B` (`costcond₀`), and the costs in the
mixed set `(LS', Λ₁ ++ Λ₂)` of the clusters of those satellites and of the centers of
`LS' \ LS_X` (`costcond₁`).

Also (used by the cluster-sampling analysis):

* the cost bound for the clusters outside `O₂` of [BCFGJPSSV26b, Section 4.7]
  (`BCFGJPSSV26.Stable.Hyp.cost_exceptional_le`): the clusters outside `O₂` cost at most
  `5 cost_OPT + 37 ε opt` in `(LS_X, Λ₁)`;
* the claim on the intermediate cost of [BCFGJPSSV26b, Section 4.7]
  (`BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`): every intermediate mixed set of the cluster
  sampling costs less than `6 opt`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

/-- `LS_X = σ₀(O_S0) ∪ σ₁(O_S1)`. -/
noncomputable def LSX (OL : Finset (Fin X.I.m)) : Finset (Fin X.I.m) :=
  X.OS0.image X.σ₀ ∪ (X.OS1 OL).image X.σcl

open Classical in
/-- `O_X`: the clusters of `O₂` with a center within `(1 + κ + 4ε) per` of `LS_X`. -/
noncomputable def OX (OL : Finset (Fin X.I.m)) : Finset (Fin X.I.m) :=
  (X.O2 OL).filter fun c ↦ ∃ c' ∈ X.LSX OL, X.dF c c' ≤ (1 + X.kap c + 4 * X.ε) * X.per c

open Classical in
/-- The substitute `ψ_X` of a cluster of `O_X` (`c` itself otherwise). -/
noncomputable def ψX (OL : Finset (Fin X.I.m)) (c : Fin X.I.m) : Fin X.I.m :=
  if h : ∃ c' ∈ X.LSX OL, X.dF c c' ≤ (1 + X.kap c + 4 * X.ε) * X.per c then Classical.choose h
  else c

/-- `O_B = (O₂ \ O_X) \ O_Λ2`. -/
noncomputable def OB (OL OL2 : Finset (Fin X.I.m)) : Finset (Fin X.I.m) :=
  (X.O2 OL \ X.OX OL) \ OL2

end Ctx

/-- **A good outcome of the cluster sampling** (the cluster-sampling theorem of [BCFGJPSSV26b,
Section 4.4]). -/
structure ClusterWitness {X : Ctx} {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁)
    (LS' : Finset (Fin X.I.m)) (Λ₂ : List (Dummy X.I)) where
  /-- The clusters matched with the dummies of `Λ₂`. -/
  OL2 : Finset (Fin X.I.m)
  /-- The dummy of each matched cluster. -/
  φ : Fin X.I.m → Dummy X.I
  LS'_sub : LS' ⊆ X.S
  LSX_sub : X.LSX w₁.OL ⊆ LS'
  card_del : (X.S \ LS').card ≤ X.s
  OL2_sub : OL2 ⊆ X.O2 w₁.OL \ X.OX w₁.OL
  length_eq : Λ₂.length = OL2.card
  φ_mem : ∀ c ∈ OL2, φ c ∈ Λ₂
  φ_inj : Set.InjOn φ OL2
  leader : ∀ c ∈ OL2, ∃ i ∈ X.S, (φ c).leader = .inr i
  radius_ge : ∀ c ∈ OL2, X.I.dd (.inr c) (φ c).leader ≤ (φ c).radius
  radius_le : ∀ c ∈ OL2, (φ c).radius ≤ (1 + X.kap c + 6 * X.ε) * X.per c
  Gam_sub : X.GamOf (X.OB w₁.OL OL2) ⊆ LS'
  cost₀ : ∑ c ∈ X.GamOf (X.OB w₁.OL OL2), X.costS (X.CS c) < X.ε ^ 3 * X.opt
  cost₁ : ∑ c ∈ X.GamOf (X.OB w₁.OL OL2) ∪ (LS' \ X.LSX w₁.OL),
    costMixOn X.I LS' (Λ₁ ++ Λ₂) (clusterMix X.I LS' (Λ₁ ++ Λ₂) c) < X.ε ^ 3 * X.opt

/-- The distance to a list of dummies is at most `dMax`. -/
private theorem dDums_le_dMax {I : Instance} (a : I.Pt) (Λ : List (Dummy I)) :
    dDums I a Λ ≤ I.dMax := by
  induction Λ with
  | nil => exact le_rfl
  | cons l Λ ih =>
    unfold dDums at ih ⊢
    rw [List.foldr_cons]
    exact (min_le_right _ _).trans ih

/-- The dummies of a longer list are nearer. -/
private theorem dDums_append_le {I : Instance} (a : I.Pt) (Λ₁ Λ₂ : List (Dummy I)) :
    dDums I a (Λ₁ ++ Λ₂) ≤ dDums I a Λ₁ := by
  induction Λ₁ with
  | nil => exact dDums_le_dMax a Λ₂
  | cons l Λ ih =>
    unfold dDums at ih ⊢
    rw [List.cons_append, List.foldr_cons, List.foldr_cons]
    exact min_le_min_left _ ih

/-- **Monotonicity of mixed sets**: more facilities and more dummies are nearer. -/
private theorem dMix_mono {I : Instance} (hv : I.Valid) {F F' : Finset (Fin I.m)} (hF : F ⊆ F')
    (a : I.Pt) (Λ₁ Λ₂ : List (Dummy I)) : dMix I a F' (Λ₁ ++ Λ₂) ≤ dMix I a F Λ₁ :=
  min_le_min (Instance.dSet_anti hv hF a) (dDums_append_le a Λ₁ Λ₂)

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

/-- **`Γ_ε(O₂ \ O_X)` misses `LS_X`.** -/
theorem GamE_disjoint_LSX {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁) :
    Disjoint (X.GamEOf (X.O2 w₁.OL \ X.OX w₁.OL)) (X.LSX w₁.OL) := by
  rw [disjoint_left]
  intro c'' h1 h2
  obtain ⟨c, hc, hc''⟩ := mem_biUnion.1 h1
  obtain ⟨hcO2, hcX⟩ := mem_sdiff.1 hc
  apply hcX
  simp only [Ctx.GamE, mem_filter] at hc''
  refine mem_filter.2 ⟨hcO2, c'', h2, ?_⟩
  have hp : 0 ≤ X.per c := per_nonneg H.valid X.ε (X.C c) c
  have he := H.eps_pos
  rw [Ctx.dF, Instance.dd_comm H.valid]
  exact hc''.2.1.trans (by nlinarith)

theorem LSX_subset {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁) : X.LSX w₁.OL ⊆ X.S := by
  intro c hc
  simp only [Ctx.LSX, mem_union, mem_image] at hc
  rcases hc with ⟨c', -, rfl⟩ | ⟨c', -, rfl⟩
  · exact H.σ₀_mem c'
  · exact H.σcl_mem c'

omit H in
/-- A client pays in a mixed set at most its distance to any facility of it. -/
private theorem costMixOn_le_of_mem {F : Finset (Fin X.I.m)} {Λ : List (Dummy X.I)}
    {i : Fin X.I.m} (hi : i ∈ F) (D : Finset (Fin X.I.n)) :
    costMixOn X.I F Λ D ≤ ∑ j ∈ D, X.dist j i :=
  sum_le_sum fun _ _ ↦ (dMix_le_dSet _ _ _).trans (Instance.dSet_le hi _)

omit H in
/-- `|C*| avg_S(C*) = cost_S(C*)`. -/
private theorem card_mul_avgS (c : Fin X.I.m) : (X.C c).card * X.avgS c = X.costS (X.C c) := by
  rcases (X.C c).eq_empty_or_nonempty with h | h
  · simp [Ctx.costS, Instance.costOn, h]
  · have : ((X.C c).card : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
    unfold Ctx.avgS
    field_simp

/-- `|C*| per(C*) ≤ (1 + 2ε) cost_OPT(C*)`. -/
private theorem card_mul_per_le (c : Fin X.I.m) :
    (X.C c).card * X.per c ≤ (1 + 2 * X.ε) * X.costO c := by
  rcases (X.C c).eq_empty_or_nonempty with h | h
  · have : X.costO c = 0 := by simp [Ctx.costO, costAt, h]
    simp [h, this]
  · have hcard : (0 : ℝ) < (X.C c).card := by exact_mod_cast h.card_pos
    have := per_le_avg H.valid H.eps_pos (by linarith [H.eps_lt]) h c
    calc ((X.C c).card : ℝ) * X.per c ≤
          (X.C c).card * ((1 + 2 * X.ε) * (costAt X.I c (X.C c) / (X.C c).card)) :=
          mul_le_mul_of_nonneg_left this hcard.le
      _ = (1 + 2 * X.ε) * X.costO c := by
          unfold Ctx.costO
          field_simp

/-- The local-search costs of some optimal clusters add up to at most `cost(S)`. -/
private theorem sum_costS_le {T : Finset (Fin X.I.m)} (hT : T ⊆ X.O) :
    ∑ c ∈ T, X.costS (X.C c) ≤ X.I.costF X.S := by
  have hv := H.valid
  calc ∑ c ∈ T, X.costS (X.C c) ≤ ∑ c ∈ X.O, X.costS (X.C c) :=
        sum_le_sum_of_subset_of_nonneg hT fun _ _ _ ↦ Instance.costOn_nonneg hv _ _
    _ = X.I.costF X.S := (Instance.sum_clusters H.O_nonempty _).symm

/-- A hit cluster in the mixed set: `d(j, φ₁ c*) ≤ d(j, c*) + 2 r`. -/
private theorem costMixOn_OL_le {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁) {c : Fin X.I.m}
    (hc : c ∈ w₁.OL) (F : Finset (Fin X.I.m)) :
    costMixOn X.I F Λ₁ (X.C c) ≤ 4 * X.costO c + 2 * X.ε * X.costS (X.C c) := by
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  have hκ : 12 / 65 ≤ X.kap c ∧ X.kap c ≤ 23 / 65 := kappa_mem _
  have hO0 : 0 ≤ X.costO c := sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have hr := w₁.radius_le c hc
  have hite : (if c ∈ w₁.OLe then 0 else X.kap c) ≤ X.kap c := by
    split_ifs
    · exact (kappa_pos _).le
    · exact le_rfl
  have hr' : (w₁.φ c).radius ≤ (1 + X.kap c + 8 * X.ε) * X.per c + X.ε * X.avgS c := by
    have := per_nonneg hv X.ε (X.C c) c
    refine hr.trans ?_
    have : (if c ∈ w₁.OLe then 0 else X.kap c) * X.per c ≤ X.kap c * X.per c :=
      mul_le_mul_of_nonneg_right hite this
    nlinarith
  have h1 : costMixOn X.I F Λ₁ (X.C c) ≤ X.costO c + (X.C c).card * (2 * (w₁.φ c).radius) := by
    rw [← nsmul_eq_mul, ← sum_const, Ctx.costO, costAt, ← sum_add_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    refine (dMix_le_dist (w₁.φ_mem c hc) _ F).trans ?_
    have := (w₁.φ c).dist_le hv (.inl j) (.inr c)
    have := w₁.radius_ge c hc
    linarith
  have hcard : (0 : ℝ) ≤ (X.C c).card := Nat.cast_nonneg _
  have h2 : ((X.C c).card : ℝ) * (2 * (w₁.φ c).radius) ≤
      2 * ((1 + X.kap c + 8 * X.ε) * ((X.C c).card * X.per c)) +
        2 * X.ε * ((X.C c).card * X.avgS c) := by
    have := mul_le_mul_of_nonneg_left hr' hcard
    nlinarith
  have h3 : (1 + X.kap c + 8 * X.ε) * ((X.C c).card * X.per c) ≤
      (1 + X.kap c + 8 * X.ε) * ((1 + 2 * X.ε) * X.costO c) :=
    mul_le_mul_of_nonneg_left (H.card_mul_per_le c) (by linarith)
  have h4 : (1 + X.kap c + 8 * X.ε) * (1 + 2 * X.ε) ≤ 3 / 2 := by nlinarith
  have h5 : (1 + X.kap c + 8 * X.ε) * (1 + 2 * X.ε) * X.costO c ≤ 3 / 2 * X.costO c :=
    mul_le_mul_of_nonneg_right h4 hO0
  rw [card_mul_avgS] at h2
  nlinarith

/-- One client of a cluster of `O₂`: it is within `d(j, c*) + 2 (1 + κ + 6ε) per` of the
intermediate mixed set. -/
private theorem dMix_O2_le {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁)
    {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {M : Finset (Fin X.I.m)}
    {φ : Fin X.I.m → Dummy X.I} (hX : X.LSX w₁.OL ⊆ LS') (hΓ : X.GamOf (X.OB w₁.OL M) ⊆ LS')
    (hφ : ∀ c ∈ M, φ c ∈ Λ₂ ∧ X.I.dd (.inr c) (φ c).leader ≤ (φ c).radius ∧
      (φ c).radius ≤ (1 + X.kap c + 6 * X.ε) * X.per c)
    {c : Fin X.I.m} (hc : c ∈ X.O2 w₁.OL) (j : Fin X.I.n) :
    dMix X.I (.inl j) LS' (Λ₁ ++ Λ₂) ≤
      X.I.dd (.inl j) (.inr c) + 2 * ((1 + X.kap c + 6 * X.ε) * X.per c) := by
  classical
  have hv := H.valid
  have he := H.eps_pos
  have hP : 0 ≤ X.per c := per_nonneg hv _ _ _
  have hκ : 0 ≤ X.kap c := (kappa_pos _).le
  have hr0 : 0 ≤ (1 + X.kap c + 6 * X.ε) * X.per c := by positivity
  have hfac : ∀ c' ∈ LS', X.dF c c' ≤ (1 + X.kap c + 6 * X.ε) * X.per c →
      dMix X.I (.inl j) LS' (Λ₁ ++ Λ₂) ≤
        X.I.dd (.inl j) (.inr c) + 2 * ((1 + X.kap c + 6 * X.ε) * X.per c) := by
    intro c' hc' hd
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr c')
    have := (dMix_le_dSet (.inl j) LS' (Λ₁ ++ Λ₂)).trans (Instance.dSet_le hc' _)
    unfold Ctx.dF at hd
    linarith
  by_cases hX' : c ∈ X.OX w₁.OL
  · obtain ⟨c', hc', hd⟩ := (mem_filter.1 hX').2
    refine hfac c' (hX hc') (hd.trans ?_)
    nlinarith
  by_cases hMc : c ∈ M
  · obtain ⟨hmem, hge, hle⟩ := hφ c hMc
    have := dMix_le_dist (List.mem_append_right Λ₁ hmem) (.inl j) LS'
    have := (φ c).dist_le hv (.inl j) (.inr c)
    linarith
  · have hB : c ∈ X.OB w₁.OL M := mem_sdiff.2 ⟨mem_sdiff.2 ⟨hc, hX'⟩, hMc⟩
    obtain ⟨c', hc', hd, -⟩ := (w₁.isFar H hc).near_sat
    refine hfac c' (hΓ (mem_biUnion.2 ⟨c, hB, hc'⟩)) (hd.trans ?_)
    nlinarith

end Hyp

end BCFGJPSSV26.Stable


