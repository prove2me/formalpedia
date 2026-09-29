-- Prove2me | Definitions.Def_NumberField_SiegelVolume
-- name    : NumberField_SiegelVolume
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/e2894cd0-8170-5c66-8fb6-00c6eb68dd09
-- title:
--   One-place contractions and capped centre-cut Siegel sets
-- statement:
--   For a field $F$ with an infinite place $v_0$, `archPiMat F v₀ g` sends a $2\times 2$ matrix $g$ over the completion $F_{v_0}$ to the matrix over $\mathrm{InfiniteAdeleRing}\,F$ whose $(i,j)$ entry is the family $w\mapsto 1_{ij}$ updated at $w=v_0$ to $g_{ij}$: the matrix with component $g$ at $v_0$ and the identity at every other infinite place. For a number field $F$, `infMat F M` pairs an archimedean matrix $M$ with the identity finite-adelic matrix, giving a matrix over $\mathrm{AdeleRing}\,(\mathcal O_F)\,F$ with archimedean part $M$ and finite part $1$. Composing these, `archEmbed F v₀` is a monoid homomorphism $\mathrm{GL}_2(F_{v_0})\to$ `AdelicGL2`, with inverse built from $g^{-1}$; the accompanying lemmas compute its archimedean component at $v_0$ (it is $g$), at other places (it is $1$), its finite component (it is $1$), and the effect on the project's `archDetNorm` (multiplication by $\|\det g\|$ at $v_0$, no change elsewhere). `contraction w b` is the image under `archEmbed F w` of the project's `upperUnit` element $\begin{pmatrix}1/2 & b\\ 0 & 2\end{pmatrix}$; it has determinant $1$, divides the local height at $w$ by $4$, and acts on `xAt w g` — the `xCoord` of the $w$-component pushed entrywise into $\mathbb C$ along `InfinitePlace.Completion.extensionEmbedding` — by $x\mapsto x/4+\varphi_w(b)/2$. Finally `capAt c P D` is $D$ intersected with the set of $g$ whose local height at every $w\in P$ is $<4c$; it is shown measurable and, for $P$ everything, contained in the project's `cappedSiegelBlock`.
--
--   The module's theorems then state, for the project's `centreCutSiegelSet F c u d₁ d₂`: finiteness of its measure for every left-invariant Borel measure finite on compacts when $c>0$ and $d_1>0$ (no condition on $u$ or $d_2$), obtained from a $2^{\#\{w\mid\infty\}}$ bound by the capped set; positivity for every measure positive on nonempty open sets when $c<1$, $u\neq 0$, $d_1<1<d_2$; and the conjunction for Haar measures, in particular for `adelicGLHaar`. No covering or fundamental-domain property and no volume formula is asserted.
--
--   **Relation to Mathlib.** Mathlib supplies the adele rings, infinite places and their completions, `Matrix.GeneralLinearGroup`, and the measure classes used (`IsMulLeftInvariant`, `IsOpenPosMeasure`, `IsFiniteMeasureOnCompacts`, `IsHaarMeasure`); the one-place embeddings, the contractions, the height/window coordinates and the capped Siegel sets are the project's own, Mathlib having no adelic Siegel sets.
--
--   **Where it is used.** These finiteness and positivity statements support the project's adelic framework for automorphic forms on $\mathrm{GL}_2$ over a number field, where a region of finite positive Haar measure is needed before integrating over the adelic group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_SiegelVolume.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_MeasureTheory_ContractionDecay
import Definitions.Def_AutomorphicForm_SiegelCoordinates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set IsDedekindDomain NumberField Matrix
open scoped ENNReal

noncomputable section

namespace NumberField

namespace SiegelVolume

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates
  NumberField.AdelicLevel NumberField.AdelicVolume

variable (F : Type) [Field F]

section ArchEmbed

open scoped Classical in

def archPiMat (v₀ : InfinitePlace F) (g : Matrix (Fin 2) (Fin 2) v₀.Completion) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  Matrix.of fun i j =>
    (Function.update ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) v₀ (g i j) :
      InfiniteAdeleRing F)

theorem matrix_eq_of_forall_archEval {M N : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, (archEval F w).mapMatrix M = (archEval F w).mapMatrix N) :
    M = N := by
  refine Matrix.ext fun i j => funext fun w => ?_
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, archEval_apply] using hw

open scoped Classical in
theorem archEval_mapMatrix_archPiMat_self (v₀ : InfinitePlace F)
    (g : Matrix (Fin 2) (Fin 2) v₀.Completion) :
    (archEval F v₀).mapMatrix (archPiMat F v₀ g) = g := by
  ext i j
  simp [archPiMat, archEval_apply]

open scoped Classical in
theorem archEval_mapMatrix_archPiMat_of_ne (v₀ : InfinitePlace F)
    (g : Matrix (Fin 2) (Fin 2) v₀.Completion) {w : InfinitePlace F} (hw : w ≠ v₀) :
    (archEval F w).mapMatrix (archPiMat F v₀ g) = 1 := by
  ext i j
  simp only [archPiMat, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, archEval_apply,
    Function.update_of_ne hw]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]
    rfl

theorem archPiMat_one (v₀ : InfinitePlace F) : archPiMat F v₀ 1 = 1 :=
  matrix_eq_of_forall_archEval F fun w => by
    by_cases hw : w = v₀
    · subst hw
      rw [archEval_mapMatrix_archPiMat_self, map_one]
    · rw [archEval_mapMatrix_archPiMat_of_ne F _ _ hw, map_one]

theorem archPiMat_mul (v₀ : InfinitePlace F) (g h : Matrix (Fin 2) (Fin 2) v₀.Completion) :
    archPiMat F v₀ (g * h) = archPiMat F v₀ g * archPiMat F v₀ h :=
  matrix_eq_of_forall_archEval F fun w => by
    by_cases hw : w = v₀
    · subst hw
      rw [map_mul, archEval_mapMatrix_archPiMat_self, archEval_mapMatrix_archPiMat_self,
        archEval_mapMatrix_archPiMat_self]
    · rw [map_mul, archEval_mapMatrix_archPiMat_of_ne F _ _ hw,
        archEval_mapMatrix_archPiMat_of_ne F _ _ hw,
        archEval_mapMatrix_archPiMat_of_ne F _ _ hw, mul_one]

end ArchEmbed

variable [NumberField F]

section AdelicEmbed

def infMat (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((M i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
    AdeleRing (𝓞 F) F)

theorem matrix_eq_of_arch_fin {M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)}
    (h₁ : (adeleArch (𝓞 F) F).mapMatrix M = (adeleArch (𝓞 F) F).mapMatrix N)
    (h₂ : (adeleFin (𝓞 F) F).mapMatrix M = (adeleFin (𝓞 F) F).mapMatrix N) : M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

theorem adeleArch_mapMatrix_infMat (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (adeleArch (𝓞 F) F).mapMatrix (infMat F M) = M := by
  ext i j
  simp [infMat, adeleArch_apply]

theorem adeleFin_mapMatrix_infMat (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (adeleFin (𝓞 F) F).mapMatrix (infMat F M) = 1 := by
  ext i j
  simp [infMat, adeleFin_apply]

theorem infMat_one : infMat F 1 = 1 :=
  matrix_eq_of_arch_fin F (by rw [adeleArch_mapMatrix_infMat, map_one])
    (by rw [adeleFin_mapMatrix_infMat, map_one])

theorem infMat_mul (M N : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    infMat F (M * N) = infMat F M * infMat F N :=
  matrix_eq_of_arch_fin F
    (by rw [map_mul, adeleArch_mapMatrix_infMat, adeleArch_mapMatrix_infMat,
      adeleArch_mapMatrix_infMat])
    (by rw [map_mul, adeleFin_mapMatrix_infMat, adeleFin_mapMatrix_infMat,
      adeleFin_mapMatrix_infMat,
      mul_one])

def archEmbed (v₀ : InfinitePlace F) : GL (Fin 2) v₀.Completion →* AdelicGL2 (𝓞 F) F where
  toFun g :=
    { val := infMat F (archPiMat F v₀ g)
      inv := infMat F (archPiMat F v₀ ((g⁻¹ : GL (Fin 2) v₀.Completion) : Matrix _ _ _))
      val_inv := by rw [← infMat_mul, ← archPiMat_mul, Units.mul_inv, archPiMat_one, infMat_one]
      inv_val := by rw [← infMat_mul, ← archPiMat_mul, Units.inv_mul, archPiMat_one, infMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; rw [archPiMat_one, infMat_one])
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; rw [archPiMat_mul, infMat_mul])

variable {F}

theorem glFin_archEmbed (v₀ : InfinitePlace F) (g : GL (Fin 2) v₀.Completion) :
    glFin (𝓞 F) F (archEmbed F v₀ g) = 1 :=
  Units.ext (by
    show (adeleFin (𝓞 F) F).mapMatrix (infMat F (archPiMat F v₀ g)) = 1
    exact adeleFin_mapMatrix_infMat F _)

theorem archComponent_glArch_archEmbed_self (v₀ : InfinitePlace F) (g : GL (Fin 2) v₀.Completion) :
    archComponent F v₀ (glArch (𝓞 F) F (archEmbed F v₀ g)) = g :=
  Units.ext (by
    show (archEval F v₀).mapMatrix ((adeleArch (𝓞 F) F).mapMatrix (infMat F (archPiMat F v₀ g))) = g
    rw [adeleArch_mapMatrix_infMat, archEval_mapMatrix_archPiMat_self])

theorem archComponent_glArch_archEmbed_of_ne (v₀ : InfinitePlace F) (g : GL (Fin 2) v₀.Completion)
    {w : InfinitePlace F} (hw : w ≠ v₀) :
    archComponent F w (glArch (𝓞 F) F (archEmbed F v₀ g)) = 1 :=
  Units.ext (by
    show (archEval F w).mapMatrix ((adeleArch (𝓞 F) F).mapMatrix (infMat F (archPiMat F v₀ g))) = 1
    rw [adeleArch_mapMatrix_infMat, archEval_mapMatrix_archPiMat_of_ne F _ _ hw])

theorem archComponent_glArch_archEmbed_mul_self (w : InfinitePlace F) (s : GL (Fin 2) w.Completion)
    (g : AdelicGL2 (𝓞 F) F) :
    archComponent F w (glArch (𝓞 F) F (archEmbed F w s * g))
      = s * archComponent F w (glArch (𝓞 F) F g) := by
  rw [map_mul, map_mul, archComponent_glArch_archEmbed_self]

theorem archComponent_glArch_archEmbed_mul_of_ne {w v₀ : InfinitePlace F} (hw : w ≠ v₀)
    (s : GL (Fin 2) v₀.Completion) (g : AdelicGL2 (𝓞 F) F) :
    archComponent F w (glArch (𝓞 F) F (archEmbed F v₀ s * g))
      = archComponent F w (glArch (𝓞 F) F g) := by
  rw [map_mul, map_mul, archComponent_glArch_archEmbed_of_ne _ _ hw, one_mul]

theorem glFin_archEmbed_mul (v₀ : InfinitePlace F) (s : GL (Fin 2) v₀.Completion)
    (g : AdelicGL2 (𝓞 F) F) : glFin (𝓞 F) F (archEmbed F v₀ s * g) = glFin (𝓞 F) F g := by
  rw [map_mul, glFin_archEmbed, one_mul]

theorem archDetNorm_archEmbed_mul_of_ne {w v₀ : InfinitePlace F} (hw : w ≠ v₀)
    (s : GL (Fin 2) v₀.Completion) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (archEmbed F v₀ s * g) = archDetNorm w g := by
  unfold archDetNorm
  rw [archComponent_glArch_archEmbed_mul_of_ne hw]

theorem archDetNorm_archEmbed_mul_self (w : InfinitePlace F) (s : GL (Fin 2) w.Completion)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (archEmbed F w s * g)
      = ‖(s : Matrix (Fin 2) (Fin 2) w.Completion).det‖ * archDetNorm w g := by
  unfold archDetNorm
  rw [archComponent_glArch_archEmbed_mul_self]
  show ‖((s : Matrix (Fin 2) (Fin 2) w.Completion) *
      (archComponent F w (glArch (𝓞 F) F g) : Matrix (Fin 2) (Fin 2) w.Completion)).det‖ = _
  rw [Matrix.det_mul, norm_mul]

end AdelicEmbed

section Contraction

variable {F}

omit [NumberField F] in
theorem two_ne_zero_completion (w : InfinitePlace F) : (2 : w.Completion) ≠ 0 :=
  norm_pos_iff.mp (by rw [norm_two_completion]; norm_num)

def contraction (w : InfinitePlace F) (b : w.Completion) : AdelicGL2 (𝓞 F) F :=
  archEmbed F w (upperUnit (2⁻¹ : w.Completion) b 2 (inv_ne_zero (two_ne_zero_completion w))
    (two_ne_zero_completion w))

theorem localHeight_contraction_mul (w : InfinitePlace F) (b : w.Completion)
    (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w (glArch (𝓞 F) F (contraction w b * g)))
      = localHeight (archComponent F w (glArch (𝓞 F) F g)) / 4 := by
  unfold contraction
  rw [archComponent_glArch_archEmbed_mul_self,
    localHeight_upper_entries_mul (a := (2⁻¹ : w.Completion)) (t := (2 : w.Completion))
      (two_ne_zero_completion w) rfl rfl rfl, norm_inv,
    norm_two_completion]
  ring

theorem archDetNorm_contraction_mul_self (w : InfinitePlace F) (b : w.Completion)
    (g : AdelicGL2 (𝓞 F) F) : archDetNorm w (contraction w b * g) = archDetNorm w g := by
  unfold contraction
  rw [archDetNorm_archEmbed_mul_self]
  have hdet : ((upperUnit (2⁻¹ : w.Completion) b 2 (inv_ne_zero (two_ne_zero_completion w))
      (two_ne_zero_completion w) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
    rw [show ((upperUnit (2⁻¹ : w.Completion) b 2 (inv_ne_zero (two_ne_zero_completion w))
      (two_ne_zero_completion w) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = !![(2⁻¹ : w.Completion), b; 0, 2] from rfl, Matrix.det_fin_two_of]
    rw [inv_mul_cancel₀ (two_ne_zero_completion w)]
    ring
  rw [hdet, norm_one, one_mul]

def xAt (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  xCoord (((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) w.Completion).map (InfinitePlace.Completion.extensionEmbedding w))

theorem xWindowSq_eq_norm_xAt_sq (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    xWindowSq (archComponent F w (glArch (𝓞 F) F g)) = ‖xAt w g‖ ^ 2 :=
  xWindowSq_eq_norm_xCoord_map_sq _ (norm_extensionEmbedding w) _

theorem xAt_contraction_mul (w : InfinitePlace F) (b : w.Completion) (g : AdelicGL2 (𝓞 F) F) :
    xAt w (contraction w b * g)
      = xAt w g / 4 + InfinitePlace.Completion.extensionEmbedding w b / 2 := by
  set φ := InfinitePlace.Completion.extensionEmbedding w with hφ
  set s : GL (Fin 2) w.Completion := upperUnit (2⁻¹ : w.Completion) b 2
    (inv_ne_zero (two_ne_zero_completion w)) (two_ne_zero_completion w) with hs
  set h : GL (Fin 2) w.Completion := archComponent F w (glArch (𝓞 F) F g) with hh
  have hmap : ∀ k : GL (Fin 2) w.Completion, ((k : Matrix (Fin 2) (Fin 2) w.Completion).map φ)
      = ((Matrix.GeneralLinearGroup.map φ k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    fun k => rfl
  have h2 : φ 2 = 2 := map_ofNat φ 2
  have hlaw := xCoord_upper_entries_mul (s := Matrix.GeneralLinearGroup.map φ s) (a := 2⁻¹)
    (b := φ b) (t := 2) two_ne_zero
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_zero_zero, map_inv₀, h2])
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_zero_one])
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_one_zero, map_zero])
    (by rw [Matrix.GeneralLinearGroup.map_apply, upperUnit_apply_one_one, h2])
    (Matrix.GeneralLinearGroup.map φ h)
  unfold xAt
  rw [contraction, ← hs, archComponent_glArch_archEmbed_mul_self, ← hh, hmap, hmap, map_mul, hlaw]
  ring

end Contraction

section Capping

variable {F}

def capAt (c : ℝ) (P : Finset (InfinitePlace F)) (D : Set (AdelicGL2 (𝓞 F) F)) :
    Set (AdelicGL2 (𝓞 F) F) :=
  D ∩ {g | ∀ w ∈ P, localHeight (archComponent F w (glArch (𝓞 F) F g)) < 4 * c}

theorem capAt_empty (c : ℝ) (D : Set (AdelicGL2 (𝓞 F) F)) : capAt c ∅ D = D := by
  ext g; simp [capAt]

open scoped Classical in
theorem capAt_insert (c : ℝ) (P : Finset (InfinitePlace F)) (w : InfinitePlace F)
    (D : Set (AdelicGL2 (𝓞 F) F)) :
    capAt c (insert w P) D
      = capAt c P D ∩
          (fun g => localHeight (archComponent F w (glArch (𝓞 F) F g))) ⁻¹' Iio (4 * c) := by
  ext g
  simp only [capAt, Finset.forall_mem_insert, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_Iio]
  tauto

theorem measurableSet_capAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)] [BorelSpace (AdelicGL2 (𝓞 F) F)]
    (c : ℝ) (P : Finset (InfinitePlace F)) {D : Set (AdelicGL2 (𝓞 F) F)} (hD : MeasurableSet D) :
    MeasurableSet (capAt c P D) := by
  classical
  induction P using Finset.induction_on with
  | empty => rwa [capAt_empty]
  | insert w P hw ih =>
    rw [capAt_insert]
    exact ih.inter ((continuous_localHeight_place w).measurable measurableSet_Iio)

theorem norm_xAt_le {c u d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ centreCutSiegelSet F c u d₁ d₂) (w : InfinitePlace F) : ‖xAt w g‖ ≤ |u| := by
  have h := hg.2.2.1 w
  rw [xWindowSq_eq_norm_xAt_sq, ← sq_abs u] at h
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg u)).mp h

theorem contraction_mul_mem {c u d₁ d₂ : ℝ} {q : ℚ} (hq : |(q : ℝ)| ≤ 3 * |u| / 2)
    (w : InfinitePlace F) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (h4 : 4 * c ≤ localHeight (archComponent F w (glArch (𝓞 F) F g))) :
    contraction w (q : w.Completion) * g ∈ centreCutSiegelSet F c u d₁ d₂ := by
  obtain ⟨hK, hfl, hwin, hdet⟩ := hg
  refine ⟨?_, fun w' => ?_, fun w' => ?_, fun w' => ?_⟩
  · rw [contraction, glFin_archEmbed_mul]
    exact hK
  · by_cases hw : w' = w
    · subst hw
      rw [localHeight_contraction_mul]
      linarith
    · rw [contraction, archComponent_glArch_archEmbed_mul_of_ne hw]
      exact hfl w'
  · by_cases hw : w' = w
    · subst hw
      rw [xWindowSq_eq_norm_xAt_sq, xAt_contraction_mul, map_ratCast, ← sq_abs u]
      refine (sq_le_sq₀ (norm_nonneg _) (abs_nonneg u)).mpr ?_
      have hx := norm_xAt_le ⟨hK, hfl, hwin, hdet⟩ w'
      calc ‖xAt w' g / 4 + (q : ℂ) / 2‖ ≤ ‖xAt w' g / 4‖ + ‖(q : ℂ) / 2‖ := norm_add_le _ _
        _ = ‖xAt w' g‖ / 4 + |(q : ℝ)| / 2 := by
            rw [norm_div, norm_div, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
            norm_num
        _ ≤ |u| / 4 + (3 * |u| / 2) / 2 := by gcongr
        _ = |u| := by ring
    · rw [contraction, archComponent_glArch_archEmbed_mul_of_ne hw]
      exact hwin w'
  · by_cases hw : w' = w
    · subst hw
      rw [archDetNorm_contraction_mul_self]
      exact hdet w'
    · rw [contraction, archDetNorm_archEmbed_mul_of_ne hw]
      exact hdet w'

theorem contraction_mul_ne {c u d₁ d₂ : ℝ} {q : ℚ} (hq : |u| / 2 < (q : ℝ)) (w : InfinitePlace F)
    {g g' : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (hg' : g' ∈ centreCutSiegelSet F c u d₁ d₂) :
    contraction w (q : w.Completion) * g ≠ contraction w ((-q : ℚ) : w.Completion) * g' := by
  intro he
  have hx : xAt w (contraction w (q : w.Completion) * g)
      = xAt w (contraction w ((-q : ℚ) : w.Completion) * g') := by rw [he]
  rw [xAt_contraction_mul, xAt_contraction_mul, map_ratCast, map_ratCast] at hx
  have hq' : ((q : ℚ) : ℂ) = (xAt w g' - xAt w g) / 4 := by
    have : ((-q : ℚ) : ℂ) = -(q : ℂ) := by push_cast; ring
    rw [this] at hx
    linear_combination hx
  have hnorm : (q : ℝ) ≤ |u| / 2 := by
    have h1 : ‖((q : ℚ) : ℂ)‖ = (q : ℝ) := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_of_nonneg]
      exact le_trans (by positivity) hq.le
    rw [← h1, hq', norm_div]
    have h2 : ‖xAt w g' - xAt w g‖ ≤ |u| + |u| :=
      (norm_sub_le _ _).trans (add_le_add (norm_xAt_le hg' w) (norm_xAt_le hg w))
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    linarith
  linarith

open scoped Classical in

theorem measure_capAt_le_two_mul [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    {c u d₁ d₂ : ℝ} (hc : 0 < c) (hu : u ≠ 0)
    (hD : MeasurableSet (centreCutSiegelSet F c u d₁ d₂)) {P : Finset (InfinitePlace F)}
    {w : InfinitePlace F} (hwP : w ∉ P) :
    μ (capAt c P (centreCutSiegelSet F c u d₁ d₂))
      ≤ 2 * μ (capAt c (insert w P) (centreCutSiegelSet F c u d₁ d₂)) := by
  set D := centreCutSiegelSet F c u d₁ d₂ with hD_def
  have hu' : 0 < |u| := abs_pos.2 hu
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show |u| / 2 < 3 * |u| / 2 by linarith)
  have hq0 : 0 ≤ (q : ℝ) := le_trans (by positivity) hq1.le
  have hqabs : |(q : ℝ)| ≤ 3 * |u| / 2 := by rw [abs_of_nonneg hq0]; exact hq2.le
  have hqabs' : |((-q : ℚ) : ℝ)| ≤ 3 * |u| / 2 := by rw [Rat.cast_neg, abs_neg]; exact hqabs
  rw [capAt_insert]
  refine ContractionDecay.measure_le_two_mul_measure_inter μ (measurableSet_capAt c P hD)
    (continuous_localHeight_place w).measurable hc (by norm_num : (1 : ℝ) < 4)
    (fun g hg => hg.1.2.1 w) (p := contraction w (q : w.Completion))
    (q := contraction w ((-q : ℚ) : w.Completion)) ?_ ?_ ?_
  · rintro g ⟨hgD, hgP⟩ h4
    refine ⟨⟨contraction_mul_mem hqabs w hgD h4, fun w' hw' => ?_⟩,
      localHeight_contraction_mul w _ g⟩
    have hne : w' ≠ w := fun h => hwP (h ▸ hw')
    rw [contraction, archComponent_glArch_archEmbed_mul_of_ne hne]
    exact hgP w' hw'
  · rintro g ⟨hgD, hgP⟩ h4
    refine ⟨⟨contraction_mul_mem hqabs' w hgD h4, fun w' hw' => ?_⟩,
      localHeight_contraction_mul w _ g⟩
    have hne : w' ≠ w := fun h => hwP (h ▸ hw')
    rw [contraction, archComponent_glArch_archEmbed_mul_of_ne hne]
    exact hgP w' hw'
  · rintro g ⟨hgD, -⟩ g' ⟨hg'D, -⟩ - -
    exact contraction_mul_ne hq1 w hgD hg'D

open scoped Classical in

theorem measure_le_two_pow_mul_measure_capAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    {c u d₁ d₂ : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hD : MeasurableSet (centreCutSiegelSet F c u d₁ d₂))
    (P : Finset (InfinitePlace F)) :
    μ (centreCutSiegelSet F c u d₁ d₂)
      ≤ 2 ^ P.card * μ (capAt c P (centreCutSiegelSet F c u d₁ d₂)) := by
  induction P using Finset.induction_on with
  | empty => rw [capAt_empty]; simp
  | insert w P hw ih =>
    rw [Finset.card_insert_of_notMem hw, pow_succ, mul_assoc]
    calc μ (centreCutSiegelSet F c u d₁ d₂)
        ≤ 2 ^ P.card * μ (capAt c P (centreCutSiegelSet F c u d₁ d₂)) := ih
      _ ≤ 2 ^ P.card * (2 * μ (capAt c (insert w P) (centreCutSiegelSet F c u d₁ d₂))) := by
        gcongr
        exact measure_capAt_le_two_mul μ hc hu hD hw

theorem capAt_univ_subset_cappedSiegelBlock (c u d₁ d₂ : ℝ) :
    capAt c Finset.univ (centreCutSiegelSet F c u d₁ d₂) ⊆ cappedSiegelBlock F c u d₁ d₂ := by
  rintro g ⟨hgD, hg⟩
  exact ⟨hgD, fun w => (hg w (Finset.mem_univ w)).le⟩

theorem measure_centreCutSiegelSet_lt_top_of_ne_zero [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] {c u d₁ d₂ : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hd₁ : 0 < d₁) :
    μ (centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
  refine (measure_le_two_pow_mul_measure_capAt μ hc hu (measurableSet_centreCutSiegelSet c u d₁ d₂)
    Finset.univ).trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) ?_)
  exact (measure_mono (capAt_univ_subset_cappedSiegelBlock c u d₁ d₂)).trans_lt
    (isCompact_cappedSiegelBlock hc hd₁).measure_lt_top

theorem centreCutSiegelSet_mono_window {c u u' d₁ d₂ : ℝ} (h : u ^ 2 ≤ u' ^ 2) :
    centreCutSiegelSet F c u d₁ d₂ ⊆ centreCutSiegelSet F c u' d₁ d₂ :=
  fun _ hg => ⟨hg.1, hg.2.1, fun w => (hg.2.2.1 w).trans h, hg.2.2.2⟩

theorem measure_centreCutSiegelSet_lt_top [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] {c : ℝ} (hc : 0 < c) (u : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ) :
    μ (centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
  have hu : |u| + 1 ≠ 0 := by positivity
  refine (measure_mono (centreCutSiegelSet_mono_window (u' := |u| + 1) ?_)).trans_lt
    (measure_centreCutSiegelSet_lt_top_of_ne_zero μ hc hu hd₁)
  rw [← sq_abs u]
  gcongr
  linarith [abs_nonneg u]

theorem measure_centreCutSiegelSet_pos [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsOpenPosMeasure] {c u d₁ d₂ : ℝ} (hc : c < 1) (hu : u ≠ 0)
    (hd₁ : d₁ < 1) (hd₂ : 1 < d₂) : 0 < μ (centreCutSiegelSet F c u d₁ d₂) := by
  obtain ⟨U, hU, hne, hsub⟩ := exists_isOpen_subset_centreCutSiegelSet (F := F) hc hu hd₁ hd₂
  exact (hU.measure_pos μ hne).trans_le (measure_mono hsub)

theorem isHaarMeasure_centreCutSiegelSet_pos_lt_top [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsHaarMeasure]
    {c u d₁ d₂ : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) (hu : u ≠ 0) (hd₀ : 0 < d₁) (hd₁ : d₁ < 1)
    (hd₂ : 1 < d₂) :
    0 < μ (centreCutSiegelSet F c u d₁ d₂) ∧ μ (centreCutSiegelSet F c u d₁ d₂) < ⊤ :=
  ⟨measure_centreCutSiegelSet_pos μ hc₁ hu hd₁ hd₂,
    measure_centreCutSiegelSet_lt_top μ hc₀ u hd₀ d₂⟩

theorem adelicGLHaar_centreCutSiegelSet_pos_lt_top {c u d₁ d₂ : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1)
    (hu : u ≠ 0) (hd₀ : 0 < d₁) (hd₁ : d₁ < 1) (hd₂ : 1 < d₂) :
    (letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F;
      0 < NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F (centreCutSiegelSet F c u d₁ d₂) ∧
        NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F (centreCutSiegelSet F c u d₁ d₂)
          < ⊤) := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  exact isHaarMeasure_centreCutSiegelSet_pos_lt_top _ hc₀ hc₁ hu hd₀ hd₁ hd₂

end Capping

end SiegelVolume

end NumberField


