-- Prove2me | Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
-- name    : AutomorphicForm_CentreCutSiegelSetAmple
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/27bbe38e-12cf-522d-a15e-238dae8001a6
-- title:
--   Ample centre-cut Siegel sets in adelic GL2​
-- statement:
--   Throughout, $F$ is a number field and $\mathrm{GL}_2$ of the adele ring of $F$ is written `AdelicGL2 (𝓞 F) F`. The module defines, for real parameters $c,u,d_1,d_2,\kappa$, the set `centreCutSiegelSetAmple F c u d₁ d₂ κ` consisting of those $g$ lying in the centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂` — that is, whose finite part lies in `finiteIntegralGL2 (𝓞 F) F`, whose local height at each infinite place $w$ is at least $c$, whose $x$-window quantity `xWindowSq` at each $w$ is at most $u^2$, and whose archimedean determinant norm at each $w$ lies in $[d_1,d_2]$ — and which in addition satisfy the comparability clause
--   $$\mathrm{localHeight}\bigl(g_w\bigr)\ \le\ \kappa\,\mathrm{localHeight}\bigl(g_{w'}\bigr)\qquad\text{for all infinite places }w,w',$$
--   where $g_w$ denotes the component of the archimedean part of $g$ at $w$. Thus the new clause confines the vector of local heights to a tube of bounded ratio around the diagonal, the rest of the defining conditions being unchanged.
--
--   The accompanying lemmas record: the membership criterion, which is definitional; the inclusion of the ample set in `centreCutSiegelSet F c u d₁ d₂`; monotonicity in $\kappa$, using positivity of local heights; equality with the centre-cut Siegel set when $F$ has at most one infinite place and $1\le\kappa$; the auxiliary inequality $\mathrm{localHeight}\le\kappa\,\mathrm{localHeight}$ for $1\le\kappa$; membership of the identity under $c\le 1$, $d_1\le 1$, $1\le d_2$, $1\le\kappa$; closedness of each set $\{g:\mathrm{localHeight}(g_w)\le\kappa\,\mathrm{localHeight}(g_{w'})\}$, by continuity of the height and of the archimedean-component maps; the description of the ample set as the centre-cut Siegel set intersected with the double intersection of these closed sets, whence its measurability for the Borel structure; and finiteness of $\mu$ on it, for any left-invariant measure $\mu$ that is finite on compacta, when $0<c$ and $0<d_1$, by inclusion in the centre-cut Siegel set.
--
--   **Relation to Mathlib.** Mathlib has no notion of Siegel set for adelic groups; the centre-cut Siegel set, its ample variant and the associated height and window functions are the project's own, built on Mathlib's adele ring, `Matrix.GeneralLinearGroup` and Haar-measure machinery.
--
--   **Where it is used.** These sets serve as the regions of integration in the adelic $L^2$-theory of automorphic forms on $\mathrm{GL}_2$ used in the modularity part of the argument: the comparability clause keeps the height vector in a bounded tube around the diagonal ray, and the inclusion in the centre-cut Siegel set transfers measurability and finiteness of Haar volume.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CentreCutSiegelSetAmple.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_SiegelVolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set IsDedekindDomain NumberField Metric

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre NumberField.SiegelVolume

variable (F : Type) [Field F] [NumberField F]

def centreCutSiegelSetAmple (c u d₁ d₂ κ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | g ∈ centreCutSiegelSet F c u d₁ d₂ ∧
    ∀ w w' : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
        κ * localHeight (archComponent F w' (glArch (𝓞 F) F g))}

variable {F}

theorem mem_centreCutSiegelSetAmple_iff {c u d₁ d₂ κ : ℝ} {g : AdelicGL2 (𝓞 F) F} :
    g ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ ↔
      g ∈ centreCutSiegelSet F c u d₁ d₂ ∧
        ∀ w w' : InfinitePlace F,
          localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
            κ * localHeight (archComponent F w' (glArch (𝓞 F) F g)) :=
  Iff.rfl

theorem centreCutSiegelSetAmple_subset (c u d₁ d₂ κ : ℝ) :
    centreCutSiegelSetAmple F c u d₁ d₂ κ ⊆ centreCutSiegelSet F c u d₁ d₂ :=
  fun _ hg => hg.1

theorem centreCutSiegelSetAmple_mono {c u d₁ d₂ κ κ' : ℝ} (h : κ ≤ κ') :
    centreCutSiegelSetAmple F c u d₁ d₂ κ ⊆ centreCutSiegelSetAmple F c u d₁ d₂ κ' :=
  fun _ hg => ⟨hg.1, fun w w' => (hg.2 w w').trans
    (mul_le_mul_of_nonneg_right h (localHeight_pos _).le)⟩

theorem centreCutSiegelSetAmple_eq_of_subsingleton [Subsingleton (InfinitePlace F)] {c u d₁ d₂ κ : ℝ}
    (hκ : 1 ≤ κ) : centreCutSiegelSetAmple F c u d₁ d₂ κ = centreCutSiegelSet F c u d₁ d₂ := by
  refine Subset.antisymm (centreCutSiegelSetAmple_subset c u d₁ d₂ κ) fun g hg => ⟨hg, fun w w' => ?_⟩
  rw [Subsingleton.elim w' w]
  exact le_mul_of_one_le_left (localHeight_pos _).le hκ

theorem localHeight_le_mul_self {κ : ℝ} (hκ : 1 ≤ κ) (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
      κ * localHeight (archComponent F w (glArch (𝓞 F) F g)) :=
  le_mul_of_one_le_left (localHeight_pos _).le hκ

theorem one_mem_centreCutSiegelSetAmple {c u d₁ d₂ κ : ℝ} (hc : c ≤ 1) (hd₁ : d₁ ≤ 1) (hd₂ : 1 ≤ d₂)
    (hκ : 1 ≤ κ) : (1 : AdelicGL2 (𝓞 F) F) ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ := by
  refine ⟨one_mem_centreCutSiegelSet hc hd₁ hd₂, fun w w' => ?_⟩
  rw [map_one, map_one, map_one, localHeight_one, localHeight_one, mul_one]
  exact hκ

theorem isClosed_setOf_localHeight_le_mul (κ : ℝ) (w w' : InfinitePlace F) :
    IsClosed {g : AdelicGL2 (𝓞 F) F |
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
        κ * localHeight (archComponent F w' (glArch (𝓞 F) F g))} :=
  isClosed_le ((continuous_localHeight).comp
      ((continuous_archComponent F w).comp (continuous_glArch (𝓞 F) F)))
    (continuous_const.mul ((continuous_localHeight).comp
      ((continuous_archComponent F w').comp (continuous_glArch (𝓞 F) F))))

theorem centreCutSiegelSetAmple_eq_inter (c u d₁ d₂ κ : ℝ) :
    centreCutSiegelSetAmple F c u d₁ d₂ κ =
      centreCutSiegelSet F c u d₁ d₂ ∩
        ⋂ w : InfinitePlace F, ⋂ w' : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
          localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤
            κ * localHeight (archComponent F w' (glArch (𝓞 F) F g))} := by
  ext g
  simp only [mem_centreCutSiegelSetAmple_iff, mem_inter_iff, mem_iInter, mem_setOf_eq]

theorem measurableSet_centreCutSiegelSetAmple {mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)}
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (c u d₁ d₂ κ : ℝ) :
    MeasurableSet (centreCutSiegelSetAmple F c u d₁ d₂ κ) := by
  rw [centreCutSiegelSetAmple_eq_inter]
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).inter
    (MeasurableSet.iInter fun w => MeasurableSet.iInter fun w' =>
      (isClosed_setOf_localHeight_le_mul κ w w').measurableSet)

theorem measure_centreCutSiegelSetAmple_lt_top [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ κ : ℝ) :
    μ (centreCutSiegelSetAmple F c u d₁ d₂ κ) < ⊤ :=
  (measure_mono (centreCutSiegelSetAmple_subset c u d₁ d₂ κ)).trans_lt
    (measure_centreCutSiegelSet_lt_top μ hc u hd₁ d₂)

end WindowedSiegel

end AutomorphicForm

end


