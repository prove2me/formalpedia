-- Prove2me | Definitions.Def_AutomorphicForm_AdelicMaximalCompact
-- name    : AutomorphicForm_AdelicMaximalCompact
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/dcc0c913-b4d3-5b2a-9ed0-dd6bd4c2db47
-- title:
--   Adelic maximal compact subgroup of GL₂ and its Haar measures
-- statement:
--   Throughout, $K$ is a number field and $\mathrm{GL}_2(\mathbb{A}_K)$ denotes `AdelicGL2 (𝓞 K) K`, the general linear group of degree $2$ over the adele ring $\mathbb{A}_K = \mathbb{A}_{K,\infty} \times \mathbb{A}_K^{f}$. The subgroup `adelicMaximalCompact K` consists of those $k$ whose finite part $\mathrm{glFin}(k)$ lies in `finiteIntegralGL2`, i.e. in `finiteLevelZero` at the unit ideal — all entries of $k_f$ and of $k_f^{-1}$ are integral at every finite place — and whose component at each infinite place $w$, obtained by applying `glArch` and then `archComponent K w`, satisfies the project predicate `IsRowIsometry`: the determinant has norm $1$ and the map $(x,y)\mapsto (x,y)\cdot k_w$ preserves $\lVert x\rVert^2+\lVert y\rVert^2$ on $K_w^2$. Membership is literally this pair of conditions, equivalently the second condition read as membership in `rowIsometrySubgroup`. Supporting lemmas record that for $k$ in this subgroup the local entries at each finite place $v$, and those of the inverse, have valuation at most $1$, and that the determinant of the $v$-component has valuation exactly $1$; that row isometries have all entries of norm at most $1$; and that the set of row isometries is closed in $\mathrm{GL}_2(L)$ for a normed field $L$. From compactness of the closed unit balls in the completions $K_w$ and of the integral finite adeles, the subgroup is shown closed and compact, the subtype is given a `CompactSpace` instance, and `maximalCompactHaar K` is defined as its Haar measure normalised to total mass $1$ (with `IsHaarMeasure` and `IsProbabilityMeasure` instances); the inclusion into $\mathrm{GL}_2(\mathbb{A}_K)$ is measurable for the Borel structure `glBorel`. For a finite set $S$ of finite places, `maximalCompactAt K S` is the intersection of the above subgroup with the kernels of $k\mapsto k_v$ for all $v \notin S$, and `maximalCompactAway K S` its intersection with the kernel of `glArch` and with the kernels of $k \mapsto k_v$ for $v \in S$; both are closed, compact, and carry Haar probability measures `maximalCompactAtHaar`, `maximalCompactAwayHaar`.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the completions at infinite places, `GL (Fin 2)` and Haar measure on a compact group; the adelic maximal compact subgroup of $\mathrm{GL}_2$ and its factors at and away from a finite set of places are the project's own, phrased through the project notions `IsRowIsometry` and `finiteIntegralGL2`.
--
--   **Where it is used.** This compact subgroup is the group by which adelic automorphic forms on $\mathrm{GL}_2$ over a number field are taken invariant, and its Haar probability measure is what normalises averaging over it; the factors at and away from a finite set of finite places separate the archimedean and the $S$-part of that averaging.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel MeasureTheory IsDedekindDomain
open AutomorphicForm.WindowedSiegel

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]

def adelicMaximalCompact : Subgroup (AdelicGL2 (𝓞 K) K) where
  carrier := {k | glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
    ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨?_, fun w => ?_⟩
    · rw [map_mul]; exact (finiteIntegralGL2 (𝓞 K) K).mul_mem ha.1 hb.1
    · rw [map_mul, map_mul]; exact (ha.2 w).mul (hb.2 w)
  one_mem' := by
    refine ⟨?_, fun w => ?_⟩
    · rw [map_one]; exact (finiteIntegralGL2 (𝓞 K) K).one_mem
    · rw [map_one, map_one]; exact isRowIsometry_one
  inv_mem' := fun {a} ha => by
    refine ⟨?_, fun w => ?_⟩
    · rw [map_inv]; exact (finiteIntegralGL2 (𝓞 K) K).inv_mem ha.1
    · rw [map_inv, map_inv]; exact (ha.2 w).inv

variable {K}

theorem mem_adelicMaximalCompact_iff {k : AdelicGL2 (𝓞 K) K} :
    k ∈ adelicMaximalCompact K ↔
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
        ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k)) :=
  Iff.rfl

theorem mem_adelicMaximalCompact_iff' {k : AdelicGL2 (𝓞 K) K} :
    k ∈ adelicMaximalCompact K ↔
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
        ∀ w : InfinitePlace K, archComponent K w (glArch (𝓞 K) K k) ∈ rowIsometrySubgroup w.Completion :=
  Iff.rfl

theorem glFin_mem_finiteIntegralGL2 {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K := hk.1

theorem isRowIsometry_archComponent {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (w : InfinitePlace K) : IsRowIsometry (archComponent K w (glArch (𝓞 K) K k)) := hk.2 w

theorem archComponent_mem_rowIsometrySubgroup {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (w : InfinitePlace K) : archComponent K w (glArch (𝓞 K) K k) ∈ rowIsometrySubgroup w.Completion := hk.2 w

theorem valued_finComponent_apply_le_one {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    Valued.v ((finComponent (𝓞 K) K v (glFin (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 ∧
      Valued.v ((((finComponent (𝓞 K) K v (glFin (𝓞 K) K k))⁻¹ : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 := by
  have h := mem_finiteIntegralGL2_iff.1 hk.1
  refine ⟨?_, ?_⟩
  · rw [finComponent_apply]; exact valued_apply_le_one (h.1 i j) v
  · rw [← map_inv, finComponent_apply]; exact valued_apply_le_one (h.2 i j) v

theorem valued_det_finComponent_eq_one {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (finComponent (𝓞 K) K v (glFin (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 := by
  set g := finComponent (𝓞 K) K v (glFin (𝓞 K) K k) with hg
  have hle : ∀ (m : GL (Fin 2) (v.adicCompletion K)),
      (∀ i j, Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1) →
      Valued.v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
    · exact mul_le_one' (hm 0 0) (hm 1 1)
    · exact mul_le_one' (hm 0 1) (hm 1 0)
  have h1 : Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≤ 1 :=
    hle g fun i j => (valued_finComponent_apply_le_one hk v i j).1
  have h2 : Valued.v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≤ 1 :=
    hle g⁻¹ fun i j => (valued_finComponent_apply_le_one hk v i j).2
  have hprod : Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det *
      Valued.v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 := by
    rw [← Valuation.map_mul, ← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.det_one, Valuation.map_one]
  exact le_antisymm h1 (by
    calc (1 : _) = _ * _ := hprod.symm
      _ ≤ Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det * 1 :=
          mul_le_mul' le_rfl h2
      _ = _ := mul_one _)

variable (K)

theorem isClosed_setOf_isRowIsometry (L : Type*) [NormedField L] :
    IsClosed {k : GL (Fin 2) L | IsRowIsometry k} := by
  have hval : Continuous fun k : GL (Fin 2) L => (k : Matrix (Fin 2) (Fin 2) L) :=
    Units.continuous_val
  have hent : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) L => (k : Matrix (Fin 2) (Fin 2) L) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hval)
  have h1 : IsClosed {k : GL (Fin 2) L | ‖(k : Matrix (Fin 2) (Fin 2) L).det‖ = 1} := by
    refine isClosed_eq ?_ continuous_const
    exact continuous_norm.comp ((continuous_id.matrix_det).comp hval)
  have h2 : IsClosed {k : GL (Fin 2) L | ∀ x y : L,
      ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2
        + ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
    fun_prop
  simpa only [IsRowIsometry, Set.setOf_and] using h1.inter h2

theorem isClosed_adelicMaximalCompact :
    IsClosed (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) := by
  have h : (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) =
      (glFin (𝓞 K) K) ⁻¹' (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∩
        ⋂ w : InfinitePlace K, (fun k => archComponent K w (glArch (𝓞 K) K k)) ⁻¹'
          {k : GL (Fin 2) w.Completion | IsRowIsometry k} := by
    ext k
    simp only [SetLike.mem_coe, mem_adelicMaximalCompact_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  refine IsClosed.inter ((isClosed_finiteLevelZero (𝓞 K) K ⊤).preimage (continuous_glFin (𝓞 K) K)) ?_
  exact isClosed_iInter fun w => (isClosed_setOf_isRowIsometry w.Completion).preimage
    ((continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K))

variable {K} in

theorem WindowedSiegel.IsRowIsometry.norm_apply_le_one {L : Type*} [NormedField L]
    {k : GL (Fin 2) L} (hk : IsRowIsometry k) (i j : Fin 2) :
    ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 := by
  have h0 := hk.2 1 0
  have h1 := hk.2 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero, one_pow,
    zero_pow (two_ne_zero)] at h0 h1
  have hn := fun i j => sq_nonneg ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖
  have hsq : ∀ i j : Fin 2, ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ ^ 2 ≤ 1 := by
    rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
    exact ⟨⟨by linarith [hn 0 1], by linarith [hn 0 0]⟩, ⟨by linarith [hn 1 1], by linarith [hn 1 0]⟩⟩
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp (hsq i j)

omit [NumberField K] in

theorem isCompact_setOf_norm_le_one_completion (w : InfinitePlace K) :
    IsCompact {x : w.Completion | ‖x‖ ≤ 1} := by
  have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hce : Topology.IsClosedEmbedding (NumberField.InfinitePlace.Completion.extensionEmbedding w) :=
    hiso.isClosedEmbedding
  have hnorm : ∀ x : w.Completion,
      ‖NumberField.InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
    hiso.norm_map_of_map_zero (map_zero _)
  have heq : {x : w.Completion | ‖x‖ ≤ 1} =
      (NumberField.InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, hnorm]
  rw [heq]
  exact hce.isCompact_preimage (isCompact_closedBall 0 1)

theorem isCompact_setOf_integral_and_norm_le_one :
    IsCompact {a : AdeleRing (𝓞 K) K |
      a.2 ∈ integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ 1} := by
  have h : {a : AdeleRing (𝓞 K) K | a.2 ∈ integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ 1}
      = (Set.pi Set.univ fun w : InfinitePlace K => {x : w.Completion | ‖x‖ ≤ 1}) ×ˢ
          integralFiniteAdeles (𝓞 K) K := by
    ext a
    constructor
    · rintro ⟨h2, h1⟩
      exact ⟨Set.mem_univ_pi.mpr h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Set.mem_univ_pi.mp h1⟩
  rw [h]
  exact (isCompact_univ_pi fun w => isCompact_setOf_norm_le_one_completion K w).prod
    (isCompact_integralFiniteAdeles (𝓞 K) K)

theorem isCompact_adelicMaximalCompact :
    IsCompact (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) := by
  set A : Set (AdeleRing (𝓞 K) K) :=
    {a | a.2 ∈ integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ 1} with hA_def
  set C : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := {m | ∀ i j, m i j ∈ A} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_setOf_integral_and_norm_le_one K
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_adelicMaximalCompact K) ?_

  have hmemA : ∀ k : AdelicGL2 (𝓞 K) K, k ∈ adelicMaximalCompact K →
      ∀ i j, (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ A := by
    intro k hk i j
    rw [mem_adelicMaximalCompact_iff] at hk
    refine ⟨?_, fun w => ?_⟩
    · exact (mem_finiteIntegralGL2_iff.1 hk.1).1 i j
    · exact (hk.2 w).norm_apply_le_one i j
  intro k hk
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  refine ⟨hmemA k hk, _, hmemA k⁻¹ ((adelicMaximalCompact K).inv_mem hk), rfl⟩

instance compactSpace_adelicMaximalCompact : CompactSpace (adelicMaximalCompact K) :=
  isCompact_iff_compactSpace.mp (isCompact_adelicMaximalCompact K)

def maximalCompactHaar : Measure (adelicMaximalCompact K) := Measure.haarMeasure ⊤

instance isHaarMeasure_maximalCompactHaar : (maximalCompactHaar K).IsHaarMeasure := by
  rw [maximalCompactHaar]; infer_instance

instance isProbabilityMeasure_maximalCompactHaar : IsProbabilityMeasure (maximalCompactHaar K) :=
  ⟨by rw [maximalCompactHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

theorem measurable_subtype_val_adelicMaximalCompact :
    @Measurable (adelicMaximalCompact K) (AdelicGL2 (𝓞 K) K) _ (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K)
      (fun k => (k : AdelicGL2 (𝓞 K) K)) := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  exact continuous_subtype_val.measurable

section Factors

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def maximalCompactAt : Subgroup (AdelicGL2 (𝓞 K) K) :=
  adelicMaximalCompact K ⊓
    ⨅ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ, ((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker

def maximalCompactAway : Subgroup (AdelicGL2 (𝓞 K) K) :=
  adelicMaximalCompact K ⊓ (glArch (𝓞 K) K).ker ⊓
    ⨅ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K))), ((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker

variable {K S} in
theorem mem_maximalCompactAt_iff {k : AdelicGL2 (𝓞 K) K} :
    k ∈ maximalCompactAt K S ↔
      k ∈ adelicMaximalCompact K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1 := by
  simp only [maximalCompactAt, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.coe_comp, Function.comp_apply, Set.mem_compl_iff, Finset.mem_coe]

variable {K S} in
theorem mem_maximalCompactAway_iff {k : AdelicGL2 (𝓞 K) K} :
    k ∈ maximalCompactAway K S ↔
      k ∈ adelicMaximalCompact K ∧ glArch (𝓞 K) K k = 1 ∧
        ∀ v ∈ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1 := by
  simp only [maximalCompactAway, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.coe_comp, Function.comp_apply, Finset.mem_coe, and_assoc]

theorem maximalCompactAt_le : maximalCompactAt K S ≤ adelicMaximalCompact K := inf_le_left

theorem maximalCompactAway_le : maximalCompactAway K S ≤ adelicMaximalCompact K :=
  inf_le_left.trans inf_le_left

private theorem isClosed_ker_finComponent_comp_glFin (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
      Set (AdelicGL2 (𝓞 K) K)) := by
  have : ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
      Set (AdelicGL2 (𝓞 K) K)) = (fun k => finComponent (𝓞 K) K v (glFin (𝓞 K) K k)) ⁻¹' {1} := by
    ext k; simp [MonoidHom.mem_ker]
  rw [this]
  exact (isClosed_singleton).preimage
    ((continuous_finComponent (𝓞 K) K v).comp (continuous_glFin (𝓞 K) K))

theorem isClosed_maximalCompactAt : IsClosed (maximalCompactAt K S : Set (AdelicGL2 (𝓞 K) K)) := by
  have h : (maximalCompactAt K S : Set (AdelicGL2 (𝓞 K) K)) =
      (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) ∩
        ⋂ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ,
          ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
            Set (AdelicGL2 (𝓞 K) K)) := by
    simp only [maximalCompactAt, Subgroup.coe_inf, Subgroup.coe_iInf]
  rw [h]
  exact (isClosed_adelicMaximalCompact K).inter
    (isClosed_biInter fun v _ => isClosed_ker_finComponent_comp_glFin K v)

theorem isClosed_maximalCompactAway :
    IsClosed (maximalCompactAway K S : Set (AdelicGL2 (𝓞 K) K)) := by
  have hker : IsClosed (((glArch (𝓞 K) K).ker : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by
    have : (((glArch (𝓞 K) K).ker : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) =
        (glArch (𝓞 K) K) ⁻¹' {1} := by
      ext k; simp [MonoidHom.mem_ker]
    rw [this]
    exact (isClosed_singleton).preimage (continuous_glArch (𝓞 K) K)
  have h : (maximalCompactAway K S : Set (AdelicGL2 (𝓞 K) K)) =
      ((adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) ∩
          (((glArch (𝓞 K) K).ker : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K))) ∩
        ⋂ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K))),
          ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
            Set (AdelicGL2 (𝓞 K) K)) := by
    simp only [maximalCompactAway, Subgroup.coe_inf, Subgroup.coe_iInf]
  rw [h]
  exact ((isClosed_adelicMaximalCompact K).inter hker).inter
    (isClosed_biInter fun v _ => isClosed_ker_finComponent_comp_glFin K v)

theorem isCompact_maximalCompactAt : IsCompact (maximalCompactAt K S : Set (AdelicGL2 (𝓞 K) K)) :=
  (isCompact_adelicMaximalCompact K).of_isClosed_subset (isClosed_maximalCompactAt K S)
    (maximalCompactAt_le K S)

theorem isCompact_maximalCompactAway : IsCompact (maximalCompactAway K S : Set (AdelicGL2 (𝓞 K) K)) :=
  (isCompact_adelicMaximalCompact K).of_isClosed_subset (isClosed_maximalCompactAway K S)
    (maximalCompactAway_le K S)

instance compactSpace_maximalCompactAt : CompactSpace (maximalCompactAt K S) :=
  isCompact_iff_compactSpace.mp (isCompact_maximalCompactAt K S)

instance compactSpace_maximalCompactAway : CompactSpace (maximalCompactAway K S) :=
  isCompact_iff_compactSpace.mp (isCompact_maximalCompactAway K S)

def maximalCompactAtHaar : Measure (maximalCompactAt K S) := Measure.haarMeasure ⊤

def maximalCompactAwayHaar : Measure (maximalCompactAway K S) := Measure.haarMeasure ⊤

instance isHaarMeasure_maximalCompactAtHaar : (maximalCompactAtHaar K S).IsHaarMeasure := by
  rw [maximalCompactAtHaar]; infer_instance

instance isProbabilityMeasure_maximalCompactAtHaar : IsProbabilityMeasure (maximalCompactAtHaar K S) :=
  ⟨by rw [maximalCompactAtHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

instance isHaarMeasure_maximalCompactAwayHaar : (maximalCompactAwayHaar K S).IsHaarMeasure := by
  rw [maximalCompactAwayHaar]; infer_instance

instance isProbabilityMeasure_maximalCompactAwayHaar :
    IsProbabilityMeasure (maximalCompactAwayHaar K S) :=
  ⟨by rw [maximalCompactAwayHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

end Factors

end AutomorphicForm

end


