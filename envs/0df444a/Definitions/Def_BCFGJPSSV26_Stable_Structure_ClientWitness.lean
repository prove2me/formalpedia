-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness
-- name    : BCFGJPSSV26_Stable_Structure_ClientWitness
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:03:32.037685+00:00
-- url     : https://prove2.me/theorems/0f3033aa-afba-4afe-b3c8-5c7991eab157
-- title:
--   BCFGJPSSV26.Stable.Structure.ClientWitness — The outcome of the client sampling
-- statement:
--   This is module `BCFGJPSSV26.Stable.Structure.ClientWitness` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The client-sampling theorem of [BCFGJPSSV26b, Section 4.2]: a list `Λ₁` of dummies is a good
--   outcome of the client sampling (`BCFGJPSSV26.Stable.ClientWitness`) if its dummies are led by
--   clients of the cores of distinct clusters `O_Λ ⊆ O₁` (the hit clusters), one dummy per cluster,
--   with radii between the distance to the optimal center and
--   `(1 + κ 1[late] + 8ε) per + ε avg_S`, where the early clusters `O_Λᵉ` are those led from
--   `core_{6ε}`; and if the clusters it misses have cheap cores in `S`: the `core_{6ε}` of the
--   non-early clusters of `O₁` and the `core_κ` of the missed ones cost less than `ε⁵ opt` in `S`.
--
--   The missed clusters split into `O_S1`, whose `core_κ` costs at least `ε³ cost_OPT` in `S`
--   (`BCFGJPSSV26.Stable.Ctx.OS1`), sent to their nearest local-search center at total cost at most
--   `ε opt` (`BCFGJPSSV26.Stable.ClientWitness.sum_OS1_le`), and the rest `O₂`
--   (`BCFGJPSSV26.Stable.Ctx.O2`), which are far in the sense of `BCFGJPSSV26.Stable.Ctx.IsFar`
--   (`BCFGJPSSV26.Stable.ClientWitness.isFar`).
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Structure/ClientWitness.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Satellites
public import Definitions.Def_BCFGJPSSV26_Stable_Dummy

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Structure.ClientWitness` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The outcome of the client sampling

The client-sampling theorem of [BCFGJPSSV26b, Section 4.2]: a list `Λ₁` of dummies is a good
outcome of the client sampling (`BCFGJPSSV26.Stable.ClientWitness`) if its dummies are led by
clients of the cores of distinct clusters `O_Λ ⊆ O₁` (the hit clusters), one dummy per cluster,
with radii between the distance to the optimal center and
`(1 + κ 1[late] + 8ε) per + ε avg_S`, where the early clusters `O_Λᵉ` are those led from
`core_{6ε}`; and if the clusters it misses have cheap cores in `S`: the `core_{6ε}` of the
non-early clusters of `O₁` and the `core_κ` of the missed ones cost less than `ε⁵ opt` in `S`.

The missed clusters split into `O_S1`, whose `core_κ` costs at least `ε³ cost_OPT` in `S`
(`BCFGJPSSV26.Stable.Ctx.OS1`), sent to their nearest local-search center at total cost at most
`ε opt` (`BCFGJPSSV26.Stable.ClientWitness.sum_OS1_le`), and the rest `O₂`
(`BCFGJPSSV26.Stable.Ctx.O2`), which are far in the sense of `BCFGJPSSV26.Stable.Ctx.IsFar`
(`BCFGJPSSV26.Stable.ClientWitness.isFar`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

open Classical in
/-- `O_S1`: the missed clusters of `O₁` whose `core_κ` costs at least `ε³ cost_OPT` in `S`. -/
noncomputable def OS1 (OL : Finset (Fin X.I.m)) : Finset (Fin X.I.m) :=
  (X.O1 \ OL).filter fun c ↦ X.ε ^ 3 * X.costO c ≤ X.costS (X.core (X.kap c) c)

/-- `O₂`: the other missed clusters of `O₁`. -/
noncomputable def O2 (OL : Finset (Fin X.I.m)) : Finset (Fin X.I.m) := (X.O1 \ OL) \ X.OS1 OL

end Ctx

/-- **A good outcome of the client sampling** (the client-sampling theorem of [BCFGJPSSV26b,
Section 4.2]). -/
structure ClientWitness (X : Ctx) (Λ₁ : List (Dummy X.I)) where
  /-- The hit clusters `O_Λ`. -/
  OL : Finset (Fin X.I.m)
  /-- The early clusters `O_Λᵉ`. -/
  OLe : Finset (Fin X.I.m)
  /-- The dummy of each hit cluster. -/
  φ : Fin X.I.m → Dummy X.I
  OL_sub : OL ⊆ X.O1
  OLe_sub : OLe ⊆ OL
  length_eq : Λ₁.length = OL.card
  φ_mem : ∀ c ∈ OL, φ c ∈ Λ₁
  φ_inj : Set.InjOn φ OL
  leader : ∀ c ∈ OL, ∃ j ∈ X.core (X.kap c) c, (φ c).leader = .inl j
  leader_early : ∀ c ∈ OLe, ∃ j ∈ X.core (6 * X.ε) c, (φ c).leader = .inl j
  radius_ge : ∀ c ∈ OL, X.I.dd (.inr c) (φ c).leader ≤ (φ c).radius
  radius_le : ∀ c ∈ OL, (φ c).radius ≤
    (1 + (if c ∈ OLe then 0 else X.kap c) + 8 * X.ε) * X.per c + X.ε * X.avgS c
  hidden_early : ∑ c ∈ X.O1 \ OLe, X.costS (X.core (6 * X.ε) c) < X.ε ^ 5 * X.opt
  hidden_hit : ∑ c ∈ X.O1 \ OL, X.costS (X.core (X.kap c) c) < X.ε ^ 5 * X.opt

namespace ClientWitness

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} (w : ClientWitness X Λ₁)

/-- One cluster sent to the nearest local-search center of its center:
`∑_{j ∈ C*} d(j, σ_cl c*) ≤ (2 + 2ε) cost_OPT + cost_S(core_κ)/ε`. -/
private theorem sum_σcl_le (H : Hyp X) (c : Fin X.I.m) :
    ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤
      (2 + 2 * X.ε) * X.costO c + X.costS (X.core (X.kap c) c) / X.ε := by
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  have hcore0 : 0 ≤ X.costS (X.core (X.kap c) c) := Instance.costOn_nonneg hv _ _
  have hO0 : 0 ≤ X.costO c := sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have h1 : ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤ X.costO c + (X.C c).card * X.dOS c := by
    rw [← nsmul_eq_mul, ← sum_const, Ctx.costO, costAt, ← sum_add_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr (X.σcl c))
    have h2 := H.dF_σcl c
    unfold Ctx.dF at h2
    unfold Ctx.dist
    linarith
  rcases (X.C c).eq_empty_or_nonempty with hC | hC
  · rw [hC, sum_empty]
    have : 0 ≤ X.costS (X.core (X.kap c) c) / X.ε := div_nonneg hcore0 he.le
    nlinarith
  have hcard : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
  have hper : (X.C c).card * X.per c ≤ (1 + 2 * X.ε) * X.costO c := by
    have := per_le_avg hv he (by linarith) hC c
    have h : (X.C c).card * ((1 + 2 * X.ε) * (costAt X.I c (X.C c) / (X.C c).card)) =
        (1 + 2 * X.ε) * X.costO c := by
      unfold Ctx.costO
      field_simp
    calc (X.C c).card * X.per c ≤
          (X.C c).card * ((1 + 2 * X.ε) * (costAt X.I c (X.C c) / (X.C c).card)) :=
          mul_le_mul_of_nonneg_left this hcard.le
      _ = _ := h
  have hB6 : X.dOS c ≤
      X.per c + X.costS (Stable.core X.I X.ε 0 (X.C c) c) / (X.ε * (X.C c).card) :=
    dSet_center_le_per hv he (by linarith) hC c X.S
  have hcs : X.costS (Stable.core X.I X.ε 0 (X.C c) c) ≤ X.costS (X.core (X.kap c) c) :=
    sum_le_sum_of_subset_of_nonneg (core_mono (kappa_pos _).le hv _ _)
      fun _ _ _ ↦ Instance.dSet_nonneg hv _ _
  have h3 : (X.C c).card * X.dOS c ≤
      (X.C c).card * X.per c + X.costS (X.core (X.kap c) c) / X.ε := by
    have h4 : (X.C c).card * (X.costS (Stable.core X.I X.ε 0 (X.C c) c) /
        (X.ε * (X.C c).card)) = X.costS (Stable.core X.I X.ε 0 (X.C c) c) / X.ε := by
      field_simp
    have h5 : X.costS (Stable.core X.I X.ε 0 (X.C c) c) / X.ε ≤
        X.costS (X.core (X.kap c) c) / X.ε := div_le_div_of_nonneg_right hcs he.le
    nlinarith
  linarith

/-- **(b)** The clusters of `O_S1`, sent to the nearest local-search center of their centers, cost
at most `ε opt`: `d(c*, S) ≤ per + cost_S(core_0)/(ε |C*|)`
(`BCFGJPSSV26.Stable.dSet_center_le_per`), and the cores are cheap. -/
theorem sum_OS1_le (H : Hyp X) :
    ∑ c ∈ X.OS1 w.OL, ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤ X.ε * X.opt := by
  classical
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  set A : ℝ := (2 + 2 * X.ε) / X.ε ^ 3 + 1 / X.ε with hA
  have hA0 : 0 ≤ A := by positivity
  have h1 : ∀ c ∈ X.OS1 w.OL, ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤
      A * X.costS (X.core (X.kap c) c) := by
    intro c hc
    have hc' := (mem_filter.1 hc).2
    refine (sum_σcl_le H c).trans ?_
    have : X.costO c ≤ X.costS (X.core (X.kap c) c) / X.ε ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h3 : (2 + 2 * X.ε) * X.costO c ≤
        (2 + 2 * X.ε) * (X.costS (X.core (X.kap c) c) / X.ε ^ 3) :=
      mul_le_mul_of_nonneg_left this (by linarith)
    calc (2 + 2 * X.ε) * X.costO c + X.costS (X.core (X.kap c) c) / X.ε
        ≤ (2 + 2 * X.ε) * (X.costS (X.core (X.kap c) c) / X.ε ^ 3) +
          X.costS (X.core (X.kap c) c) / X.ε := by linarith
      _ = A * X.costS (X.core (X.kap c) c) := by rw [hA]; ring
  have h2 : ∑ c ∈ X.OS1 w.OL, X.costS (X.core (X.kap c) c) < X.ε ^ 5 * X.opt := by
    refine lt_of_le_of_lt ?_ w.hidden_hit
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun _ _ _ ↦ Instance.costOn_nonneg hv _ _
  calc ∑ c ∈ X.OS1 w.OL, ∑ j ∈ X.C c, X.dist j (X.σcl c)
      ≤ ∑ c ∈ X.OS1 w.OL, A * X.costS (X.core (X.kap c) c) := sum_le_sum h1
    _ = A * ∑ c ∈ X.OS1 w.OL, X.costS (X.core (X.kap c) c) := by rw [mul_sum]
    _ ≤ A * (X.ε ^ 5 * X.opt) := mul_le_mul_of_nonneg_left h2.le hA0
    _ = ((2 + 2 * X.ε) * X.ε ^ 2 + X.ε ^ 4) * X.opt := by
        rw [hA]
        field_simp
    _ ≤ X.ε * X.opt := by
        refine mul_le_mul_of_nonneg_right ?_ hopt
        have h3 : 2 * X.ε + 2 * X.ε ^ 2 + X.ε ^ 3 ≤ 1 := by nlinarith
        have h4 : X.ε * (2 * X.ε + 2 * X.ε ^ 2 + X.ε ^ 3) ≤ X.ε * 1 :=
          mul_le_mul_of_nonneg_left h3 he.le
        linarith

/-- **(c-iii)–(c-v)** The clusters of `O₂` are far. -/
theorem isFar (H : Hyp X) {c : Fin X.I.m} (hc : c ∈ X.O2 w.OL) : X.IsFar c := by
  classical
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  have hc0 := hc
  simp only [Ctx.O2, Ctx.OS1, mem_sdiff, mem_filter, not_and, not_le] at hc0
  obtain ⟨⟨hc1, hc2⟩, hcheap⟩ := hc0
  have hcheap := hcheap ⟨hc1, hc2⟩
  have hcO : c ∈ X.O := (mem_sdiff.1 hc1).1
  have hnS0 : c ∉ X.OS0 := (mem_sdiff.1 hc1).2
  simp only [Ctx.OS0, Ctx.Osync, Ctx.Ocl, mem_union, mem_filter, not_or, not_and] at hnS0
  have hns : ¬ X.IsSynced c := hnS0.1 hcO
  have hfar : eta * X.avgO c + 2 * X.ε * X.avgS c < X.dOS c := by
    by_contra h
    exact hnS0.2 hcO ⟨hns, not_lt.1 h⟩
  have hcore0 : 0 ≤ X.costS (X.core (X.kap c) c) := Instance.costOn_nonneg hv _ _
  have hpos : 0 < X.costO c := by
    by_contra h
    have : X.ε ^ 3 * X.costO c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 h)
    linarith
  have hC : (X.C c).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [Ctx.costO, costAt, h] at hpos
  have hcard : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
  have hper0 : 0 ≤ X.per c := per_nonneg hv _ _ _
  have havg_ge : X.per c ≤ (1 + 2 * X.ε) * X.avgO c :=
    per_le_avg hv he (by linarith) hC c
  have hB6 : X.dOS c ≤
      X.per c + X.costS (Stable.core X.I X.ε 0 (X.C c) c) / (X.ε * (X.C c).card) :=
    dSet_center_le_per hv he (by linarith) hC c X.S
  have hsub : Stable.core X.I X.ε 0 (X.C c) c ⊆ X.core (X.kap c) c :=
    core_mono (kappa_pos _).le hv _ _
  have hcs : X.costS (Stable.core X.I X.ε 0 (X.C c) c) ≤ X.costS (X.core (X.kap c) c) :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Instance.dSet_nonneg hv _ _
  -- `cost_S(core_0)/(ε|C|) < ε² avg_OPT`
  have hsmall : X.costS (Stable.core X.I X.ε 0 (X.C c) c) / (X.ε * (X.C c).card) <
      X.ε ^ 2 * X.avgO c := by
    rw [div_lt_iff₀ (by positivity), Ctx.avgO]
    rw [show X.ε ^ 2 * (X.costO c / (X.C c).card) * (X.ε * (X.C c).card) = X.ε ^ 3 * X.costO c by
      field_simp]
    linarith
  have havgS : 0 ≤ X.avgS c := div_nonneg (Instance.costOn_nonneg hv _ _) hcard.le
  have heta : eta = 89 / 100 := rfl
  have havgO : 0 < X.avgO c := div_pos hpos hcard
  -- `(η - ε²) avg_OPT < per`
  have hlt : (eta - X.ε ^ 2) * X.avgO c < X.per c := by nlinarith
  have havg_le : X.avgO c ≤ (1 + X.ε) * X.per c / eta := by
    rw [le_div_iff₀ (by rw [heta]; norm_num)]
    have : eta ≤ (1 + X.ε) * (eta - X.ε ^ 2) := by rw [heta]; nlinarith
    nlinarith
  have hper : 0 < X.per c := by
    by_contra h
    have : X.per c = 0 := le_antisymm (not_lt.1 h) hper0
    rw [this] at havg_le
    simp at havg_le
    linarith
  refine ⟨hcO, hfar, hcheap, ?_, havg_le, hpos, hper, ?_⟩
  · rw [div_le_iff₀ (by linarith)]
    linarith
  · -- a client `q ∈ core_0` nearest to `S`
    set K := Stable.core X.I X.ε 0 (X.C c) c with hK
    have hKne : K.Nonempty := by
      have := card_core_ge hv (ε := X.ε) (by linarith) le_rfl hC c
      rw [← hK] at this
      have : (0 : ℝ) < K.card := lt_of_lt_of_le (by positivity) this
      exact card_pos.1 (by exact_mod_cast this)
    obtain ⟨q, hqK, hqmin⟩ := K.exists_min_image (fun j ↦ X.I.dSet (.inl j) X.S) hKne
    have hKcard : X.ε * (X.C c).card ≤ K.card := card_core_ge hv (by linarith) le_rfl hC c
    have hqS : K.card * X.I.dSet (.inl q) X.S ≤ X.costS K := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum hqmin
    have hq : X.I.dSet (.inl q) X.S ≤ X.ε * X.per c := by
      have h1 : X.ε * (X.C c).card * X.I.dSet (.inl q) X.S ≤ X.costS K :=
        (mul_le_mul_of_nonneg_right hKcard (Instance.dSet_nonneg hv _ _)).trans hqS
      have h2 : X.I.dSet (.inl q) X.S ≤ X.costS K / (X.ε * (X.C c).card) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h3 : X.ε ^ 2 * X.avgO c ≤ X.ε * X.per c := by
        have : X.ε * X.avgO c ≤ X.per c := by nlinarith
        nlinarith
      linarith
    have hqC : q ∈ X.C c := core_subset _ _ _ _ hqK
    have hqc : X.I.dd (.inl q) (.inr c) ≤ X.per c := by
      have := (mem_filter.1 hqK).2
      rw [add_zero, one_mul] at this
      exact this
    obtain ⟨c', hc'S, hc'q⟩ := Instance.exists_dSet_eq H.S_nonempty (.inl q)
    have hcc' : X.dF c c' ≤ (1 + X.ε) * X.per c := by
      have := Instance.dd_triangle hv (.inr c) (.inl q) (.inr c')
      rw [Instance.dd_comm hv (.inr c) (.inl q)] at this
      unfold Ctx.dF
      nlinarith
    have hκ := kappa_pos (X.xr c)
    refine ⟨c', ?_, hcc', q, hqC, ?_⟩
    · simp only [Ctx.Gam, mem_filter]
      refine ⟨hc'S, ?_, q, hqC, ?_⟩
      · rw [Ctx.dF, Instance.dd_comm hv]
        unfold Ctx.kap
        unfold Ctx.dF at hcc'
        nlinarith
      · unfold Ctx.dist
        linarith
    · unfold Ctx.dist
      linarith

theorem O2_subset : X.O2 w.OL ⊆ X.O1 := fun _ hc ↦ (mem_sdiff.1 (mem_sdiff.1 hc).1).1

end ClientWitness

end BCFGJPSSV26.Stable


