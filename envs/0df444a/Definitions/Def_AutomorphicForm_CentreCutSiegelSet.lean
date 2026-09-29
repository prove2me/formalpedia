-- Prove2me | Definitions.Def_AutomorphicForm_CentreCutSiegelSet
-- name    : AutomorphicForm_CentreCutSiegelSet
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/7b0e5ad7-7307-5a86-8999-1e7c01ce0d7a
-- title:
--   Centre-cut Siegel sets and capped compact blocks for adelic GL(2)
-- statement:
--   Fix a number field $F$ and work in the project's adelic group `AdelicGL2 (𝓞 F) F` of invertible $2\times 2$ matrices over the adele ring of $F$, with its finite and archimedean projections `glFin`, `glArch` and, for each infinite place $w$, the component map `archComponent F w` landing in $\mathrm{GL}_2(F_w)$. The module defines, for real parameters $c,u,d_1,d_2$, the set `centreCutSiegelSet F c u d₁ d₂` of all $g$ such that (i) the finite part of $g$ lies in the subgroup `finiteIntegralGL2` (integral matrices, integral inverse), and, for every infinite place $w$, (ii) `localHeight` of $g_w$ is $\ge c$, (iii) `xWindowSq` of $g_w$ is $\le u^2$, (iv) `archDetNorm w g` lies in the closed interval $[d_1,d_2]$. The three archimedean quantities are defined in the imported modules; the proofs here use the identities $\texttt{localHeight}(g)=\lVert\det g\rVert/\texttt{rowNormSq}(g)$ and $\texttt{topNormSq}(g)=\texttt{rowNormSq}(g)\,(\texttt{xWindowSq}(g)+\texttt{localHeight}(g)^2)$, with `rowNormSq`, `topNormSq` the squared norms of the second, respectively first, row, and `archDetNorm w g` $=\lVert\det g_w\rVert$. Note that the determinant window is imposed separately at each infinite place. The second definition, `cappedSiegelBlock F c u d₁ d₂`, intersects the above with the ceiling condition $\texttt{localHeight}(g_w)\le 4c$ at every infinite place.
--
--   The accompanying lemmas give: the membership unfolding; membership of $1$ under $c\le 1$, $d_1\le 1\le d_2$; failure of stability under the centre (for $d_2<4$ there is a central element, a scalar $2$ at one infinite place, moving $1$ out of the set); containment in `integralWindowedSiegelSet F (c ^ ∑ w, w.mult) u`; measurability and closedness; continuity of the local height and of the $x$-window at a fixed place; membership of $1$ in the interior under the strict margins $c<1$, $u\ne 0$, $d_1<1<d_2$, hence a nonempty open subset. A generic section bounds, over any normed field $K$, the entries of $g$ and of $g^{-1}$ in terms of $c,u,d_1,d_2$ under the clauses $c\le\texttt{localHeight}(g)\le 4c$, $\texttt{xWindowSq}(g)\le u^2$, $\lVert\det g\rVert\in[d_1,d_2]$, and deduces compactness of that block of $\mathrm{GL}_2(K)$ when $K$ is proper and $c,d_1>0$; `properSpace_completion` supplies properness of $F_w$, and `isCompact_cappedSiegelBlock` transfers the argument to the adelic capped block. No covering statement and no Haar-measure statement is made here.
--
--   **Relation to Mathlib.** Mathlib has no Siegel sets for adelic $\mathrm{GL}_2$; the sets and the height/window functions are the project's own (the latter from the imported modules). `properSpace_completion` proves a `ProperSpace` instance for `InfinitePlace.Completion` used locally rather than taken from Mathlib; the compactness arguments otherwise run through Mathlib's `Units.embedProduct` and product-of-closed-balls machinery.
--
--   **Where it is used.** These sets provide the measure-theoretic domain on $\mathrm{GL}_2(\mathbb{A}_F)$ used in the project's adelic volume computations for automorphic forms on $\mathrm{GL}_2$: the determinant windows remove the central directions along which a pure product-height Siegel set has zero or infinite Haar measure, and the capped blocks supply the compact pieces out of which finiteness and positivity of the volume are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CentreCutSiegelSet.lean

import Definitions.Def_NumberField_AdelicVolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set IsDedekindDomain NumberField Metric

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre

variable (F : Type) [Field F] [NumberField F]

def centreCutSiegelSet (c u d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F ∧
    (∀ w : InfinitePlace F,
      c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))) ∧
    (∀ w : InfinitePlace F,
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2) ∧
    (∀ w : InfinitePlace F, archDetNorm w g ∈ Icc d₁ d₂)}

variable {F}

theorem mem_centreCutSiegelSet_iff {c u d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 F) F} :
    g ∈ centreCutSiegelSet F c u d₁ d₂ ↔
      glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F ∧
      (∀ w : InfinitePlace F,
        c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))) ∧
      (∀ w : InfinitePlace F,
        xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2) ∧
      (∀ w : InfinitePlace F, archDetNorm w g ∈ Icc d₁ d₂) :=
  Iff.rfl

theorem one_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : c ≤ 1) (hd₁ : d₁ ≤ 1)
    (hd₂ : 1 ≤ d₂) : (1 : AdelicGL2 (𝓞 F) F) ∈ centreCutSiegelSet F c u d₁ d₂ := by
  refine ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · rw [map_one, map_one, localHeight_one]
    exact hc
  · rw [map_one, map_one, xWindowSq_one]
    positivity
  · unfold archDetNorm
    rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one]
    exact ⟨hd₁, hd₂⟩

theorem not_centrally_stable_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : c ≤ 1)
    (hd₁ : d₁ ≤ 1) (hd₂ : 1 ≤ d₂) (hd₂4 : d₂ < 4) :
    ∃ z g, g ∈ centreCutSiegelSet F c u d₁ d₂ ∧
      z * g ∉ centreCutSiegelSet F c u d₁ d₂ ∧
      z ∈ Subgroup.center (AdelicGL2 (𝓞 F) F) := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha₀ : ‖(2 : v₀.Completion)‖ = 2 := norm_two_completion v₀
  have ha0 : (2 : v₀.Completion) ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha₀
    norm_num at ha₀
  refine ⟨centralScalar (𝓞 F) F (archCentralUnit F v₀ (Units.mk0 2 ha0)), 1,
    one_mem_centreCutSiegelSet hc hd₁ hd₂, fun hmem => ?_, ?_⟩
  case refine_2 =>
    rw [center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have h4 := (mem_centreCutSiegelSet_iff.mp hmem).2.2.2 v₀
  rw [archDetNorm_centralScalar_mul] at h4
  unfold archDetNorm at h4
  rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one, mul_one, Units.val_mk0,
    ha₀] at h4
  have : (2 : ℝ) * 2 ≤ d₂ := h4.2
  linarith

theorem centreCutSiegelSet_subset_integralWindowedSiegelSet {c u d₁ d₂ : ℝ}
    (hc : 0 ≤ c) :
    centreCutSiegelSet F c u d₁ d₂ ⊆
      integralWindowedSiegelSet F (c ^ (∑ w : InfinitePlace F, w.mult)) u := by
  rintro g ⟨hK, hfloor, hwin, -⟩
  refine ⟨hK, ?_, hwin⟩
  unfold archHeight
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg hc _)
    (fun w _ => pow_le_pow_left₀ hc (hfloor w) _)

theorem measurableSet_centreCutSiegelSet {mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)}
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (c u d₁ d₂ : ℝ) :
    MeasurableSet (centreCutSiegelSet F c u d₁ d₂) := by
  have hK : IsOpen {g : AdelicGL2 (𝓞 F) F |
      glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F} :=
    (isOpen_finiteLevelZero (R := 𝓞 F) (K := F) (N := ⊤) (by simp)).preimage
      (continuous_glFin (𝓞 F) F)
  have hfloor : ∀ w : InfinitePlace F, IsClosed {g : AdelicGL2 (𝓞 F) F |
      c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))} := fun w =>
    isClosed_le continuous_const ((continuous_localHeight).comp
      ((continuous_archComponent F w).comp (continuous_glArch (𝓞 F) F)))
  have hwin : ∀ w : InfinitePlace F, IsClosed {g : AdelicGL2 (𝓞 F) F |
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2} := fun w =>
    isClosed_le ((continuous_xWindowSq).comp
      ((continuous_archComponent F w).comp (continuous_glArch (𝓞 F) F))) continuous_const
  have hdet : ∀ w : InfinitePlace F, IsClosed {g : AdelicGL2 (𝓞 F) F |
      archDetNorm w g ∈ Icc d₁ d₂} := fun w =>
    isClosed_Icc.preimage (continuous_archDetNorm w)
  have : centreCutSiegelSet F c u d₁ d₂ =
      {g | glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F} ∩
      ((⋂ w : InfinitePlace F, {g | c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))}) ∩
       ((⋂ w : InfinitePlace F, {g | xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2}) ∩
        (⋂ w : InfinitePlace F, {g | archDetNorm w g ∈ Icc d₁ d₂}))) := by
    ext g
    simp only [mem_centreCutSiegelSet_iff, mem_inter_iff, mem_setOf_eq, mem_iInter]
  rw [this]
  exact hK.measurableSet.inter
    (((isClosed_iInter hfloor).measurableSet).inter
      (((isClosed_iInter hwin).measurableSet).inter
        ((isClosed_iInter hdet).measurableSet)))

theorem continuous_localHeight_place (w : InfinitePlace F) :
    Continuous fun g : AdelicGL2 (𝓞 F) F =>
      localHeight (archComponent F w (glArch (𝓞 F) F g)) :=
  continuous_localHeight.comp ((continuous_archComponent F w).comp
    (continuous_glArch (𝓞 F) F))

theorem continuous_xWindowSq_place (w : InfinitePlace F) :
    Continuous fun g : AdelicGL2 (𝓞 F) F =>
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) :=
  continuous_xWindowSq.comp ((continuous_archComponent F w).comp
    (continuous_glArch (𝓞 F) F))

theorem one_mem_interior_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : c < 1) (hu : u ≠ 0)
    (hd₁ : d₁ < 1) (hd₂ : 1 < d₂) :
    (1 : AdelicGL2 (𝓞 F) F) ∈ interior (centreCutSiegelSet F c u d₁ d₂) := by
  have hK : IsOpen {g : AdelicGL2 (𝓞 F) F |
      glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F} :=
    (isOpen_finiteLevelZero (R := 𝓞 F) (K := F) (N := ⊤) (by simp)).preimage
      (continuous_glFin (𝓞 F) F)
  have hfloor : IsOpen {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      c < localHeight (archComponent F w (glArch (𝓞 F) F g))} := by
    have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
        c < localHeight (archComponent F w (glArch (𝓞 F) F g))}
        = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            c < localHeight (archComponent F w (glArch (𝓞 F) F g))} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt continuous_const (continuous_localHeight_place w)
  have hwin : IsOpen {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) < u ^ 2} := by
    have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
        xWindowSq (archComponent F w (glArch (𝓞 F) F g)) < u ^ 2}
        = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            xWindowSq (archComponent F w (glArch (𝓞 F) F g)) < u ^ 2} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (continuous_xWindowSq_place w) continuous_const
  have hdet : IsOpen {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      archDetNorm w g ∈ Ioo d₁ d₂} := by
    have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
        archDetNorm w g ∈ Ioo d₁ d₂}
        = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            archDetNorm w g ∈ Ioo d₁ d₂} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact isOpen_iInter_of_finite fun w => isOpen_Ioo.preimage (continuous_archDetNorm w)
  rw [mem_interior]
  refine ⟨{g : AdelicGL2 (𝓞 F) F |
        glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F}
      ∩ ({g | ∀ w : InfinitePlace F,
            c < localHeight (archComponent F w (glArch (𝓞 F) F g))}
      ∩ ({g | ∀ w : InfinitePlace F,
            xWindowSq (archComponent F w (glArch (𝓞 F) F g)) < u ^ 2}
      ∩ {g | ∀ w : InfinitePlace F, archDetNorm w g ∈ Ioo d₁ d₂})),
    fun g hg => ⟨hg.1, fun w => (hg.2.1 w).le, fun w => (hg.2.2.1 w).le,
      fun w => ⟨(hg.2.2.2 w).1.le, (hg.2.2.2 w).2.le⟩⟩,
    hK.inter (hfloor.inter (hwin.inter hdet)), ?_, ?_, ?_, ?_⟩
  · show glFin (𝓞 F) F 1 ∈ finiteIntegralGL2 (𝓞 F) F
    rw [map_one]
    exact Subgroup.one_mem _
  · intro w
    show c < localHeight (archComponent F w (glArch (𝓞 F) F 1))
    rw [map_one, map_one, localHeight_one]
    exact hc
  · intro w
    show xWindowSq (archComponent F w (glArch (𝓞 F) F 1)) < u ^ 2
    rw [map_one, map_one, xWindowSq_one]
    positivity
  · intro w
    show archDetNorm w 1 ∈ Ioo d₁ d₂
    unfold archDetNorm
    rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one]
    exact ⟨hd₁, hd₂⟩

theorem exists_isOpen_subset_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : c < 1)
    (hu : u ≠ 0) (hd₁ : d₁ < 1) (hd₂ : 1 < d₂) :
    ∃ U : Set (AdelicGL2 (𝓞 F) F), IsOpen U ∧ U.Nonempty ∧
      U ⊆ centreCutSiegelSet F c u d₁ d₂ :=
  ⟨interior (centreCutSiegelSet F c u d₁ d₂), isOpen_interior,
    ⟨1, one_mem_interior_centreCutSiegelSet hc hu hd₁ hd₂⟩, interior_subset⟩
section GenericBlock

variable {K : Type*} [NormedField K]

theorem rowNormSq_le_of_clauses {g : GL (Fin 2) K} {c d₂ : ℝ} (hc : 0 < c)
    (hlh : c ≤ localHeight g)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ≤ d₂) :
    rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ d₂ / c := by
  have hrow := rowNormSq_pos g
  have h1 : c * rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ := by
    have h2 : c ≤ ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖
        / rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := hlh
    rw [le_div_iff₀ hrow] at h2
    linarith
  rw [le_div_iff₀ hc]
  nlinarith

theorem topNormSq_le_of_clauses {g : GL (Fin 2) K} {c u d₂ : ℝ} (hc : 0 < c)
    (hlh : c ≤ localHeight g) (hlh4 : localHeight g ≤ 4 * c)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ≤ d₂) :
    topNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ d₂ / c * (u ^ 2 + (4 * c) ^ 2) := by
  have hrow := rowNormSq_pos g
  have hrowle := rowNormSq_le_of_clauses hc hlh hdet

  have htop : topNormSq (g : Matrix (Fin 2) (Fin 2) K)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) K) * (xWindowSq g + localHeight g ^ 2) := by
    unfold xWindowSq
    field_simp
    ring
  rw [htop]
  have hlh0 : 0 ≤ localHeight g := le_trans hc.le hlh
  have hxlh : xWindowSq g + localHeight g ^ 2 ≤ u ^ 2 + (4 * c) ^ 2 := by
    have : localHeight g ^ 2 ≤ (4 * c) ^ 2 := by nlinarith
    linarith
  have hxlh0 : 0 ≤ xWindowSq g + localHeight g ^ 2 := by
    have h1 : 0 ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
      unfold topNormSq; positivity
    nlinarith [htop, hrow]
  have hd20 : 0 ≤ d₂ / c := hrow.le.trans hrowle
  exact mul_le_mul hrowle hxlh hxlh0 hd20

theorem entry_norm_le_of_clauses {g : GL (Fin 2) K} {c u d₁ d₂ : ℝ} (hc : 0 < c)
    (hlh : c ≤ localHeight g) (hlh4 : localHeight g ≤ 4 * c)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂) (i j : Fin 2) :
    ‖(g : Matrix (Fin 2) (Fin 2) K) i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)) := by
  have hrowle := rowNormSq_le_of_clauses hc hlh hdet.2
  have htople := topNormSq_le_of_clauses hc hlh hlh4 hxw hdet.2
  have hd₂0 : 0 ≤ d₂ / c := div_nonneg (le_trans (norm_nonneg _) hdet.2) hc.le
  have h00 : ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖ ^ 2
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold topNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 1‖]
  have h01 : ‖(g : Matrix (Fin 2) (Fin 2) K) 0 1‖ ^ 2
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold topNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖]
  have h10 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖]
  have h11 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖]
  have hsplit : d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)
      = d₂ / c + d₂ / c * (u ^ 2 + (4 * c) ^ 2) := by ring
  have hterm : 0 ≤ d₂ / c * (u ^ 2 + (4 * c) ^ 2) :=
    mul_nonneg hd₂0 (by positivity)
  have hRtop : topNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2) := by
    rw [hsplit]
    linarith
  have hRrow : rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2) := by
    rw [hsplit]
    linarith
  refine Real.le_sqrt_of_sq_le ?_
  fin_cases i <;> fin_cases j
  · exact h00.trans hRtop
  · exact h01.trans hRtop
  · exact h10.trans hRrow
  · exact h11.trans hRrow

theorem inv_entry_norm_le_of_clauses {g : GL (Fin 2) K} {c u d₁ d₂ : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) (hlh : c ≤ localHeight g) (hlh4 : localHeight g ≤ 4 * c)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂) (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)) / d₁ := by
  have hB := entry_norm_le_of_clauses hc hlh hlh4 hxw hdet
  have hdet0 : ((g : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact absurd hdet.1 (not_le.mpr hd₁)

  have hcoe : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((g : Matrix (Fin 2) (Fin 2) K))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, norm_smul, norm_inv]
  have hadj : ‖((g : Matrix (Fin 2) (Fin 2) K)).adjugate i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)) := by
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · show ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ _
      exact hB 1 1
    · show ‖-(g : Matrix (Fin 2) (Fin 2) K) 0 1‖ ≤ _
      rw [norm_neg]; exact hB 0 1
    · show ‖-(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ _
      rw [norm_neg]; exact hB 1 0
    · show ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖ ≤ _
      exact hB 0 0
  have hdinv : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ ≤ d₁⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hd₁ hdet.1
  have h0 : (0 : ℝ) ≤ ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ := by positivity
  calc ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ * ‖((g : Matrix (Fin 2) (Fin 2) K)).adjugate i j‖
      ≤ d₁⁻¹ * Real.sqrt (d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)) := by
        exact mul_le_mul hdinv hadj (norm_nonneg _) (by positivity)
    _ = Real.sqrt (d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)) / d₁ := by
        ring

theorem isCompact_glBlock [ProperSpace K] {c u d₁ d₂ : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) :
    IsCompact {g : GL (Fin 2) K |
      (c ≤ localHeight g ∧ localHeight g ≤ 4 * c) ∧ xWindowSq g ≤ u ^ 2 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂} := by
  set B := Real.sqrt (d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)) with hB_def
  set C : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      closedBall (0 : K) B with hC_def
  set C' : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      closedBall (0 : K) (B / d₁) with hC'_def
  have hC : IsCompact C :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hC' : IsCompact C' :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) K)) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C'))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC'.image MulOpposite.continuous_op))
  have hclosed : IsClosed {g : GL (Fin 2) K |
      (c ≤ localHeight g ∧ localHeight g ≤ 4 * c) ∧ xWindowSq g ≤ u ^ 2 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂} := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ ?_)
    · exact isClosed_le continuous_const continuous_localHeight
    · exact isClosed_le continuous_localHeight continuous_const
    · exact isClosed_le continuous_xWindowSq continuous_const
    · exact (isClosed_Icc).preimage continuous_det_gl.norm
  refine hK.of_isClosed_subset hclosed ?_
  rintro g ⟨⟨hlh, hlh4⟩, hxw, hdet⟩
  have hent := entry_norm_le_of_clauses hc hlh hlh4 hxw hdet
  have hinv := inv_entry_norm_le_of_clauses hc hd₁ hlh hlh4 hxw hdet
  refine ⟨fun i _ => fun j _ => ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact hent i j
  · refine ⟨((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), fun i _ => fun j _ => ?_, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hinv i j

end GenericBlock

section PerPlace

omit [NumberField F] in

theorem properSpace_completion (w : InfinitePlace F) : ProperSpace w.Completion := by
  obtain ⟨r, rpos, hr⟩ := exists_isCompact_closedBall (0 : w.Completion)
  have h2 : ‖(2 : w.Completion)‖ = 2 := norm_two_completion w
  have h20 : (2 : w.Completion) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    norm_num at h2
  have hC : ∀ n : ℕ, IsCompact (Metric.closedBall (0 : w.Completion) (2 ^ n * r)) := by
    intro n
    have h2n : (2 : w.Completion) ^ n ≠ 0 := pow_ne_zero _ h20
    have hs := hr.smul ((2 : w.Completion) ^ n)
    rw [_root_.smul_closedBall' h2n, smul_zero, norm_pow, h2] at hs
    exact hs
  have hTop : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n * r) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const rpos
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  exact ProperSpace.of_seq_closedBall hTop (Filter.Eventually.of_forall hC)

omit [NumberField F] in

theorem isCompact_archBlock (w : InfinitePlace F) {c u d₁ d₂ : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) :
    IsCompact {g : GL (Fin 2) w.Completion |
      (c ≤ localHeight g ∧ localHeight g ≤ 4 * c) ∧ xWindowSq g ≤ u ^ 2 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) w.Completion)).det‖ ∈ Icc d₁ d₂} := by
  haveI := properSpace_completion w
  exact isCompact_glBlock hc hd₁

end PerPlace

variable (F)

def cappedSiegelBlock (c u d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  centreCutSiegelSet F c u d₁ d₂ ∩
    {g | ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ 4 * c}

variable {F}

theorem mem_cappedSiegelBlock_iff {c u d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 F) F} :
    g ∈ cappedSiegelBlock F c u d₁ d₂ ↔
      g ∈ centreCutSiegelSet F c u d₁ d₂ ∧
      ∀ w : InfinitePlace F,
        localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ 4 * c := Iff.rfl

theorem isClosed_centreCutSiegelSet (c u d₁ d₂ : ℝ) :
    IsClosed (centreCutSiegelSet F c u d₁ d₂) := by
  have hK : IsClosed {g : AdelicGL2 (𝓞 F) F |
      glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F} :=
    ((finiteIntegralGL2 (𝓞 F) F).isClosed_of_isOpen
      (isOpen_finiteLevelZero (R := 𝓞 F) (K := F) (N := ⊤) (by simp))).preimage
      (continuous_glFin (𝓞 F) F)
  have hfloor : IsClosed {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))} := by
    have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
        c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))}
        = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter fun w =>
      isClosed_le continuous_const (continuous_localHeight_place w)
  have hwin : IsClosed {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2} := by
    have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
        xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2}
        = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter fun w =>
      isClosed_le (continuous_xWindowSq_place w) continuous_const
  have hdet : IsClosed {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      archDetNorm w g ∈ Icc d₁ d₂} := by
    have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
        archDetNorm w g ∈ Icc d₁ d₂}
        = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
            archDetNorm w g ∈ Icc d₁ d₂} := by
      ext g
      simp [Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter fun w => isClosed_Icc.preimage (continuous_archDetNorm w)
  have hdecomp : centreCutSiegelSet F c u d₁ d₂ =
      {g : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F} ∩
      ({g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
          c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))} ∩
       ({g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
          xWindowSq (archComponent F w (glArch (𝓞 F) F g)) ≤ u ^ 2} ∩
        {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
          archDetNorm w g ∈ Icc d₁ d₂})) := by
    ext g
    simp only [mem_centreCutSiegelSet_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [hdecomp]
  exact hK.inter (hfloor.inter (hwin.inter hdet))

theorem isClosed_cappedSiegelBlock (c u d₁ d₂ : ℝ) :
    IsClosed (cappedSiegelBlock F c u d₁ d₂) := by
  refine (isClosed_centreCutSiegelSet c u d₁ d₂).inter ?_
  have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ 4 * c}
      = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
          localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ 4 * c} := by
    ext g
    simp [Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun w =>
    isClosed_le (continuous_localHeight_place w) continuous_const

theorem isCompact_cappedSiegelBlock {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (cappedSiegelBlock F c u d₁ d₂) := by
  classical
  set B := Real.sqrt (d₂ / c * (1 + u ^ 2 + (4 * c) ^ 2)) with hB_def
  set A : Set (AdeleRing (𝓞 F) F) :=
    (Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) B) ×ˢ
      integralFiniteAdeles (𝓞 F) F with hA_def
  set A' : Set (AdeleRing (𝓞 F) F) :=
    (Set.pi Set.univ fun w : InfinitePlace F =>
      Metric.closedBall (0 : w.Completion) (B / d₁)) ×ˢ
      integralFiniteAdeles (𝓞 F) F with hA'_def
  have hApi : IsCompact A := by
    refine IsCompact.prod (isCompact_univ_pi fun w => ?_)
      (isCompact_integralFiniteAdeles (𝓞 F) F)
    haveI := properSpace_completion (F := F) w
    exact isCompact_closedBall _ _
  have hA'pi : IsCompact A' := by
    refine IsCompact.prod (isCompact_univ_pi fun w => ?_)
      (isCompact_integralFiniteAdeles (𝓞 F) F)
    haveI := properSpace_completion (F := F) w
    exact isCompact_closedBall _ _
  set C : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A with hC_def
  set C' : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A' with hC'_def
  have hC : IsCompact C := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hApi
  have hC' : IsCompact C' := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hA'pi
  have hK : IsCompact ((Units.embedProduct
      (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C'))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC'.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_cappedSiegelBlock c u d₁ d₂) ?_
  rintro g ⟨⟨hKf, hfloor, hwin, hdet⟩, hcap⟩
  have hKf2 := mem_finiteIntegralGL2_iff.mp hKf

  have harch : ∀ (w : InfinitePlace F) (i j : Fin 2),
      ‖(archComponent F w (glArch (𝓞 F) F g) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ B := fun w i j =>
    entry_norm_le_of_clauses hc (hfloor w) (hcap w) (hwin w) (hdet w) i j
  have harch' : ∀ (w : InfinitePlace F) (i j : Fin 2),
      ‖(((archComponent F w (glArch (𝓞 F) F g))⁻¹ : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ B / d₁ := fun w i j =>
    inv_entry_norm_le_of_clauses hc hd₁ (hfloor w) (hcap w) (hwin w) (hdet w) i j
  constructor
  ·
    intro i _ j _
    constructor
    · intro w _
      rw [mem_closedBall_zero_iff]
      show ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w‖ ≤ B
      have hbridge : ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
          = (archComponent F w (glArch (𝓞 F) F g) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
      rw [hbridge]
      exact harch w i j
    · exact hKf2.1 i j
  ·
    refine ⟨((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)),
      ?_, rfl⟩
    intro i _ j _
    constructor
    · intro w _
      rw [mem_closedBall_zero_iff]
      show ‖(((g⁻¹ : AdelicGL2 (𝓞 F) F) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w‖ ≤ B / d₁
      have hbridge : (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
          = (((archComponent F w (glArch (𝓞 F) F g))⁻¹ : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j := by
        have h1 : (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
            = (archComponent F w (glArch (𝓞 F) F (g⁻¹ : AdelicGL2 (𝓞 F) F)) :
                Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
        rw [h1, map_inv (glArch (𝓞 F) F), map_inv (archComponent F w)]
      rw [hbridge]
      exact harch' w i j
    · exact hKf2.2 i j

end WindowedSiegel

end AutomorphicForm

end


