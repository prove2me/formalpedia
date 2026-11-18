-- Prove2me | Definitions.Def_ArtinKPB005
-- name    : ArtinKPB005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:14:39.679718+00:00
-- url     : https://prove2.me/theorems/0a1bdcf3-e075-4f43-942c-eb5c79aaaad7
-- title:
--   Definitions bundle ArtinKPB005 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 84 declarations of that development: 27 definitions, 4 instances and 53 theorems. The definitions and types are `ArtinKP.X.Coord`, `ArtinKP.X.E1`, `ArtinKP.X.Ginf`, `ArtinKP.X.H3`, `ArtinKP.X.H3.box`, `ArtinKP.X.H3.kQ`, `ArtinKP.X.H3.mk`, `ArtinKP.X.H3.q`, `ArtinKP.X.H3.rowDen`, `ArtinKP.X.H3.rowNum`, `ArtinKP.X.H3.toQ`, `ArtinKP.X.H3.v`, `ArtinKP.X.H3.x`, `ArtinKP.X.X`, `ArtinKP.X.X.box`, `ArtinKP.X.X.mk`, `ArtinKP.X.X.torus`, `ArtinKP.X.X.trans`, `ArtinKP.X.X.v`, `ArtinKP.X.X.x`, `ArtinKP.X.chart`, `ArtinKP.X.chart1`, `ArtinKP.X.den`, `ArtinKP.X.intSL`, `ArtinKP.X.mob`, `ArtinKP.X.sigma`, `ArtinKP.X.wMat`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X2_Chart`, `KP.X_Discrete`, `KP.X_H3`, `KP.X_Meas`, `KP.X_Space`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB006`; the statement `ArtinKP.X.X.summable_comp_smul_of_hasCompactSupport`; the proof of `ArtinKP.X.X.summable_comp_smul_of_hasCompactSupport`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib

section
-- module Solutions.Artin.KP.X_H3
/-! # WP-X, file 1: one factor — hyperbolic 3-space and the action of `SL(2,ℂ)`

`H3 = {(x, v) : ℂ × ℝ | 0 < v}` with the quaternionic Möbius action
`g • (x, v) = (((a x + b) conj(c x + d) + a conj(c) v²) / D, v / D)`,
`D = |c x + d|² + |c|² v²`.  The action axioms are proved through the quaternion `x + v j`:
`a P + b = (g • P) (c P + d)` in `ℍ[ℝ]`.
-/

open scoped MatrixGroups Quaternion ComplexConjugate

namespace ArtinKP.X

noncomputable section

/-- Hyperbolic 3-space, upper half space model. -/
def H3 : Type := {p : ℂ × ℝ // 0 < p.2}

namespace H3

instance instTopologicalSpace : TopologicalSpace H3 := inferInstanceAs (TopologicalSpace {p : ℂ × ℝ // 0 < p.2})

/-- The horizontal coordinate. -/
def x (P : H3) : ℂ := P.1.1
/-- The height coordinate. -/
def v (P : H3) : ℝ := P.1.2

/-- The point with coordinates `(x, v)`. -/
def mk (x : ℂ) (v : ℝ) (hv : 0 < v) : H3 := ⟨(x, v), hv⟩

@[simp] lemma x_mk (x : ℂ) (v : ℝ) (hv : 0 < v) : (mk x v hv).x = x := rfl
@[simp] lemma v_mk (x : ℂ) (v : ℝ) (hv : 0 < v) : (mk x v hv).v = v := rfl
lemma v_pos (P : H3) : 0 < P.v := P.2

@[ext] lemma ext {P Q : H3} (hx : P.x = Q.x) (hv : P.v = Q.v) : P = Q :=
  Subtype.ext (Prod.ext hx hv)

lemma continuous_x : Continuous x := continuous_fst.comp continuous_subtype_val
lemma continuous_v : Continuous v := continuous_snd.comp continuous_subtype_val

/-- The denominator of a row `(c, d)` at a point: `|c x + d|² + |c|² v²`. -/
def rowDen (c d : ℂ) (P : H3) : ℝ := Complex.normSq (c * P.x + d) + Complex.normSq c * P.v ^ 2

lemma rowDen_pos {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) (P : H3) : 0 < rowDen c d P := by
  unfold rowDen
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by simpa using h
    simpa using Complex.normSq_pos.mpr hd
  · have : 0 < Complex.normSq c * P.v ^ 2 :=
      mul_pos (Complex.normSq_pos.mpr hc) (pow_pos P.v_pos 2)
    have := Complex.normSq_nonneg (c * P.x + d)
    linarith

/-- The numerator of the horizontal coordinate of `g • P`. -/
def rowNum (a b c d : ℂ) (P : H3) : ℂ :=
  (a * P.x + b) * conj (c * P.x + d) + a * conj c * (P.v : ℂ) ^ 2

/-- The quaternion `x + v j` of a point. -/
def toQ (x : ℂ) (v : ℝ) : ℍ[ℝ] := ⟨x.re, x.im, v, 0⟩

@[simp] lemma toQ_re (x : ℂ) (v : ℝ) : (toQ x v).re = x.re := rfl
@[simp] lemma toQ_imI (x : ℂ) (v : ℝ) : (toQ x v).imI = x.im := rfl
@[simp] lemma toQ_imJ (x : ℂ) (v : ℝ) : (toQ x v).imJ = v := rfl
@[simp] lemma toQ_imK (x : ℂ) (v : ℝ) : (toQ x v).imK = 0 := rfl

/-- The quaternion `t k`. -/
def kQ (t : ℝ) : ℍ[ℝ] := ⟨0, 0, 0, t⟩

@[simp] lemma kQ_re (t : ℝ) : (kQ t).re = 0 := rfl
@[simp] lemma kQ_imI (t : ℝ) : (kQ t).imI = 0 := rfl
@[simp] lemma kQ_imJ (t : ℝ) : (kQ t).imJ = 0 := rfl
@[simp] lemma kQ_imK (t : ℝ) : (kQ t).imK = t := rfl

/-- The quaternion of a point of `H3`. -/
def q (P : H3) : ℍ[ℝ] := toQ P.x P.v

lemma q_injective : Function.Injective q := by
  intro P Q h
  have h1 := congrArg QuaternionAlgebra.re h
  have h2 := congrArg QuaternionAlgebra.imI h
  have h3 := congrArg QuaternionAlgebra.imJ h
  simp only [q, toQ_re, toQ_imI, toQ_imJ] at h1 h2 h3
  exact H3.ext (Complex.ext h1 h2) h3

lemma normSq_row (c d : ℂ) (P : H3) :
    Quaternion.normSq ((c : ℍ[ℝ]) * q P + (d : ℍ[ℝ])) = rowDen c d P := by
  rw [Quaternion.normSq_def']
  simp [q, rowDen, Complex.normSq_apply]
  ring

/-- The basic quaternion identity (no determinant condition). -/
lemma row_mul_star (a b c d : ℂ) (x : ℂ) (v : ℝ) :
    ((a : ℍ[ℝ]) * toQ x v + (b : ℍ[ℝ])) * star ((c : ℍ[ℝ]) * toQ x v + (d : ℍ[ℝ])) =
      toQ ((a * x + b) * conj (c * x + d) + a * conj c * (v : ℂ) ^ 2) (v * (a * d - b * c).re)
        + kQ (v * (a * d - b * c).im) := by
  ext <;> simp [pow_two] <;> ring

lemma row_mul_star_of_det {a b c d : ℂ} (hdet : a * d - b * c = 1) (x : ℂ) (v : ℝ) :
    ((a : ℍ[ℝ]) * toQ x v + (b : ℍ[ℝ])) * star ((c : ℍ[ℝ]) * toQ x v + (d : ℍ[ℝ])) =
      toQ ((a * x + b) * conj (c * x + d) + a * conj c * (v : ℂ) ^ 2) v := by
  rw [row_mul_star, hdet]
  ext <;> simp

lemma row_ne_zero {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) (P : H3) :
    (c : ℍ[ℝ]) * q P + (d : ℍ[ℝ]) ≠ 0 := by
  intro h0
  have := normSq_row c d P
  rw [h0, map_zero] at this
  exact (rowDen_pos h P).ne this

lemma toQ_smul (t : ℝ) (x : ℂ) (v : ℝ) : toQ ((t : ℂ) * x) (t * v) = (t : ℍ[ℝ]) * toQ x v := by
  ext <;> simp

end H3

open H3

lemma bottom_ne_zero (g : SL(2, ℂ)) : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
  by_contra h
  push Not at h
  have := g.det_coe
  rw [Matrix.det_fin_two, h.1, h.2] at this
  simp at this

lemma det_eq (g : SL(2, ℂ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.det_coe
  rwa [Matrix.det_fin_two] at this

/-- The automorphy denominator `|c x + d|² + |c|² v²` of `g` at `P`. -/
def den (g : SL(2, ℂ)) (P : H3) : ℝ := rowDen (g 1 0) (g 1 1) P

lemma den_pos (g : SL(2, ℂ)) (P : H3) : 0 < den g P := rowDen_pos (bottom_ne_zero g) P

/-- The Möbius action of `SL(2,ℂ)` on `H3`. -/
def mob (g : SL(2, ℂ)) (P : H3) : H3 :=
  H3.mk (rowNum (g 0 0) (g 0 1) (g 1 0) (g 1 1) P / (den g P : ℂ)) (P.v / den g P)
    (div_pos P.v_pos (den_pos g P))

/-- `a P + b = (g • P) (c P + d)` in the quaternions. -/
lemma q_mob (g : SL(2, ℂ)) (P : H3) :
    ((g 0 0 : ℂ) : ℍ[ℝ]) * q P + ((g 0 1 : ℂ) : ℍ[ℝ]) =
      q (mob g P) * (((g 1 0 : ℂ) : ℍ[ℝ]) * q P + ((g 1 1 : ℂ) : ℍ[ℝ])) := by
  set Q := ((g 1 0 : ℂ) : ℍ[ℝ]) * q P + ((g 1 1 : ℂ) : ℍ[ℝ]) with hQ
  have hD : star Q * Q = ((den g P : ℝ) : ℍ[ℝ]) := by
    rw [Quaternion.star_mul_self, hQ, normSq_row]; rfl
  have hD0 : ((den g P : ℝ) : ℍ[ℝ]) ≠ 0 := by
    intro h
    exact (den_pos g P).ne' (Quaternion.coe_injective (h.trans Quaternion.coe_zero.symm))
  have h1 := row_mul_star_of_det (det_eq g) P.x P.v
  have h2 : q (mob g P) = ((den g P : ℝ) : ℍ[ℝ])⁻¹ *
      toQ (rowNum (g 0 0) (g 0 1) (g 1 0) (g 1 1) P) P.v := by
    rw [← Quaternion.coe_inv, ← toQ_smul]
    simp only [q, mob, x_mk, v_mk]
    congr 1
    · push_cast; rw [div_eq_inv_mul]
    · rw [div_eq_inv_mul]
  rw [h2]
  change _ = _ * toQ (rowNum (g 0 0) (g 0 1) (g 1 0) (g 1 1) P) P.v * Q
  unfold rowNum
  rw [← h1]
  change ((g 0 0 : ℂ) : ℍ[ℝ]) * q P + ((g 0 1 : ℂ) : ℍ[ℝ]) =
    ((den g P : ℝ) : ℍ[ℝ])⁻¹ * ((((g 0 0 : ℂ) : ℍ[ℝ]) * q P + ((g 0 1 : ℂ) : ℍ[ℝ])) * star Q) * Q
  rw [mul_assoc, mul_assoc, hD]
  have hcomm : (((g 0 0 : ℂ) : ℍ[ℝ]) * q P + ((g 0 1 : ℂ) : ℍ[ℝ])) * ((den g P : ℝ) : ℍ[ℝ]) =
      ((den g P : ℝ) : ℍ[ℝ]) * (((g 0 0 : ℂ) : ℍ[ℝ]) * q P + ((g 0 1 : ℂ) : ℍ[ℝ])) :=
    (Quaternion.coe_commutes _ _).symm
  rw [hcomm, ← mul_assoc, inv_mul_cancel₀ hD0, one_mul]

lemma coe_entry_mul (g h : SL(2, ℂ)) (i j : Fin 2) :
    (((g * h) i j : ℂ) : ℍ[ℝ]) =
      ((g i 0 : ℂ) : ℍ[ℝ]) * ((h 0 j : ℂ) : ℍ[ℝ]) + ((g i 1 : ℂ) : ℍ[ℝ]) * ((h 1 j : ℂ) : ℍ[ℝ]) := by
  rw [← Quaternion.coeComplex_mul, ← Quaternion.coeComplex_mul, ← Quaternion.coeComplex_add]
  congr 1
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- The row of `g h` at `P` is the row of `g` at `h • P` times the bottom row of `h` at `P`. -/
lemma row_mul (g h : SL(2, ℂ)) (P : H3) (i : Fin 2) :
    (((g * h) i 0 : ℂ) : ℍ[ℝ]) * q P + (((g * h) i 1 : ℂ) : ℍ[ℝ]) =
      (((g i 0 : ℂ) : ℍ[ℝ]) * q (mob h P) + ((g i 1 : ℂ) : ℍ[ℝ])) *
        (((h 1 0 : ℂ) : ℍ[ℝ]) * q P + ((h 1 1 : ℂ) : ℍ[ℝ])) := by
  rw [add_mul, mul_assoc, ← q_mob h P, coe_entry_mul, coe_entry_mul]
  noncomm_ring

lemma mob_mul (g h : SL(2, ℂ)) (P : H3) : mob (g * h) P = mob g (mob h P) := by
  apply q_injective
  have hne := row_ne_zero (bottom_ne_zero (g * h)) P
  apply mul_right_cancel₀ hne
  rw [← q_mob (g * h) P, row_mul g h P 0]
  conv_rhs => rw [row_mul g h P 1, ← mul_assoc, ← q_mob g (mob h P)]

lemma mob_one (P : H3) : mob 1 P = P := by
  apply q_injective
  have h := q_mob 1 P
  simpa using h.symm

instance instMulActionSpecialLinearGroupFinOfNatNatComplexH3 : MulAction (SL(2, ℂ)) H3 where
  smul := mob
  one_smul := mob_one
  mul_smul := mob_mul

lemma smul_v (g : SL(2, ℂ)) (P : H3) : (g • P).v = P.v / den g P := rfl

/-- The cocycle identity for the automorphy denominator. -/
lemma den_mul (g h : SL(2, ℂ)) (P : H3) : den (g * h) P = den g (h • P) * den h P := by
  have := congrArg Quaternion.normSq (row_mul g h P 1)
  rw [map_mul, normSq_row, normSq_row, normSq_row] at this
  exact this

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Meas
/-! # WP-X, file 2: the invariant measure `dx dv / v³` on `H3`

`H3.vol` is the comap to `H3` of `(volume.restrict {v > 0}).withDensity v⁻³` on `ℂ × ℝ`.
Invariance under `SL(2,ℂ)` is proved on the generators `n(b)` and `w` (the Weyl element acts by
the Euclidean inversion followed by `x ↦ -conj x`), and `SL(2,ℂ)` is generated by them.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set

namespace ArtinKP.X

noncomputable section

/-! ### The Euclidean inversion -/

/-! ### The measure on `H3` -/

/-! ### Regularity of the action -/

/-! ### Generators -/

/-- The Weyl element. -/
def wMat : SL(2, ℂ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

lemma wMat_coe : (wMat : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0] := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Space
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The symmetric space `(H³)^r`, one factor per infinite place. -/
abbrev X : Type _ := InfinitePlace F → H3

/-- The archimedean group `SL(2,ℂ)^r`. -/
abbrev Ginf : Type _ := InfinitePlace F → SL(2, ℂ)

/-- The diagonal embedding `SL(2,F) → SL(2,ℂ)^r`. -/
def sigma : SL(2, F) →* Ginf F :=
  MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map w.embedding

instance instMulActionSpecialLinearGroupFinOfNatNatX : MulAction (SL(2, F)) (X F) := MulAction.compHom (X F) (sigma F)

variable {F}

namespace X

/-- Horizontal coordinates. -/
def x (P : X F) (w : InfinitePlace F) : ℂ := (P w).x
/-- Height coordinates. -/
def v (P : X F) (w : InfinitePlace F) : ℝ := (P w).v

lemma v_pos (P : X F) (w : InfinitePlace F) : 0 < P.v w := (P w).v_pos

@[ext] lemma ext' {P Q : X F} (hx : P.x = Q.x) (hv : P.v = Q.v) : P = Q :=
  funext fun w => H3.ext (congrFun hx w) (congrFun hv w)

/-- The point with given coordinates. -/
def mk (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) : X F :=
  fun w => H3.mk (x w) (v w) (hv w)

@[simp] lemma x_mk (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    (mk x v hv).x = x := rfl
@[simp] lemma v_mk (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    (mk x v hv).v = v := rfl

end X

/-! ### Topology and measure -/

lemma X.continuous_x (w : InfinitePlace F) : Continuous fun P : X F => P.x w :=
  H3.continuous_x.comp (continuous_apply w)

lemma X.continuous_v (w : InfinitePlace F) : Continuous fun P : X F => P.v w :=
  H3.continuous_v.comp (continuous_apply w)

/-! ### Upper triangular elements, translations and the torus -/

namespace X

/-- Translation `n(b)`, `b ∈ ℂ^r`. -/
def trans (b : InfinitePlace F → ℂ) (P : X F) : X F :=
  mk (fun w => P.x w + b w) P.v P.v_pos

/-- The torus `a(y)`, `y ∈ (ℂˣ)^r`: `(x, v) ↦ (y x, |y| v)`. -/
def torus (y : InfinitePlace F → ℂˣ) (P : X F) : X F :=
  mk (fun w => (y w : ℂ) * P.x w) (fun w => ‖(y w : ℂ)‖ * P.v w)
    (fun w => mul_pos (norm_pos_iff.mpr (y w).ne_zero) (P.v_pos w))

@[simp] lemma x_trans (b : InfinitePlace F → ℂ) (P : X F) : (trans b P).x = fun w => P.x w + b w :=
  rfl
@[simp] lemma v_trans (b : InfinitePlace F → ℂ) (P : X F) : (trans b P).v = P.v := rfl
@[simp] lemma x_torus (y : InfinitePlace F → ℂˣ) (P : X F) :
    (torus y P).x = fun w => (y w : ℂ) * P.x w := rfl
@[simp] lemma v_torus (y : InfinitePlace F → ℂˣ) (P : X F) :
    (torus y P).v = fun w => ‖(y w : ℂ)‖ * P.v w := rfl

end X

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Chart
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

/-! ### One factor -/

/-- The model of one factor: `(x, t)` with `v = exp t`. -/
abbrev E1 : Type := ℂ × ℝ

/-- The logarithmic chart of `H3`. -/
def chart1 : E1 ≃ₜ H3 where
  toFun p := H3.mk p.1 (Real.exp p.2) (Real.exp_pos _)
  invFun P := (P.x, Real.log P.v)
  left_inv p := by simp
  right_inv P := H3.ext rfl (Real.exp_log P.v_pos)
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := H3.continuous_x.prodMk
    (Real.continuousOn_log.comp_continuous H3.continuous_v fun P => P.v_pos.ne')

@[simp] lemma chart1_x (p : E1) : (chart1 p).x = p.1 := rfl
@[simp] lemma chart1_v (p : E1) : (chart1 p).v = Real.exp p.2 := rfl
@[simp] lemma chart1_symm_fst (P : H3) : (chart1.symm P).1 = P.x := rfl
@[simp] lemma chart1_symm_snd (P : H3) : (chart1.symm P).2 = Real.log P.v := rfl

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

/-- The coordinate space of the logarithmic chart of `X F`. -/
abbrev Coord : Type _ := InfinitePlace F → E1

/-- The logarithmic chart of `X F`. -/
def chart : Coord F ≃ₜ X F := Homeomorph.piCongrRight fun _ => chart1

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-- A box in `H3`: `|x| ≤ B`, `m ≤ v ≤ M`. -/
def H3.box (m M B : ℝ) : Set H3 := {Q | ‖Q.x‖ ≤ B ∧ m ≤ Q.v ∧ Q.v ≤ M}

lemma den_eq_div (g : SL(2, ℂ)) (Q : H3) : den g Q = Q.v / (g • Q).v := by
  rw [smul_v, div_div_cancel₀ Q.v_pos.ne']

lemma bottom_bounds (g : SL(2, ℂ)) (Q : H3) {K B m : ℝ} (hm : 0 < m) (hden : den g Q ≤ K)
    (hx : ‖Q.x‖ ≤ B) (hv : m ≤ Q.v) :
    ‖g 1 0‖ ≤ (K + 1) / m ∧ ‖g 1 1‖ ≤ (K + 1) + (K + 1) / m * B := by
  have hd : ‖g 1 0 * Q.x + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * Q.v ^ 2 ≤ K := by
    simpa [den, H3.rowDen, Complex.normSq_eq_norm_sq] using hden
  have hs := norm_nonneg (g 1 0 * Q.x + g 1 1)
  have hc := norm_nonneg (g 1 0)
  have hB : 0 ≤ B := (norm_nonneg _).trans hx
  have ht : ‖g 1 0‖ * Q.v ≤ K + 1 := by
    nlinarith [sq_nonneg (‖g 1 0‖ * Q.v - 1), sq_nonneg ‖g 1 0 * Q.x + g 1 1‖]
  have hs1 : ‖g 1 0 * Q.x + g 1 1‖ ≤ K + 1 := by
    nlinarith [sq_nonneg (‖g 1 0 * Q.x + g 1 1‖ - 1), sq_nonneg (‖g 1 0‖ * Q.v)]
  have hc1 : ‖g 1 0‖ ≤ (K + 1) / m := by
    rw [le_div_iff₀ hm]
    nlinarith
  have hK : 0 ≤ K := le_trans (by positivity) hd
  have hcm : 0 ≤ (K + 1) / m := by positivity
  refine ⟨hc1, ?_⟩
  have h1 : g 1 1 = (g 1 0 * Q.x + g 1 1) - g 1 0 * Q.x := by ring
  calc ‖g 1 1‖ = ‖(g 1 0 * Q.x + g 1 1) - g 1 0 * Q.x‖ := by rw [← h1]
    _ ≤ ‖g 1 0 * Q.x + g 1 1‖ + ‖g 1 0 * Q.x‖ := norm_sub_le _ _
    _ = ‖g 1 0 * Q.x + g 1 1‖ + ‖g 1 0‖ * ‖Q.x‖ := by rw [norm_mul]
    _ ≤ (K + 1) + (K + 1) / m * B := by gcongr

/-- If `Q` and `g • Q` lie in the same box, the entries of `g` are bounded. -/
theorem entries_bounded (m M B : ℝ) (hm : 0 < m) :
    ∃ C : ℝ, ∀ (g : SL(2, ℂ)) (Q : H3), Q ∈ H3.box m M B → g • Q ∈ H3.box m M B →
      ∀ i j : Fin 2, ‖g i j‖ ≤ C := by
  set K1 := M / m with hK1
  set K2 := (B ^ 2 + M ^ 2) * (M / m) with hK2
  set C1 := (K1 + 1) + (K1 + 1) / m * B with hC1
  set C2 := (K2 + 1) + (K2 + 1) / m * B with hC2
  refine ⟨(K1 + 1) / m + C1 + C2, ?_⟩
  intro g Q hQ hQ'
  obtain ⟨hx, hv1, hv2⟩ := hQ
  obtain ⟨hx', hv1', hv2'⟩ := hQ'
  have hM : 0 < M := hm.trans_le (hv1.trans hv2)
  have hB : 0 ≤ B := (norm_nonneg _).trans hx
  have hK1pos : 0 ≤ K1 := (div_pos hM hm).le
  have hK2pos : 0 ≤ K2 := mul_nonneg (by positivity) (div_pos hM hm).le
  have hC1pos : 0 ≤ C1 := by positivity
  have hC2pos : 0 ≤ C2 := by positivity
  have hcm : 0 ≤ (K1 + 1) / m := by positivity
  -- the bottom row
  have hden1 : den g Q ≤ K1 := by
    rw [den_eq_div]
    exact div_le_div₀ hM.le hv2 hm hv1'
  obtain ⟨hc, hd⟩ := bottom_bounds g Q hm hden1 hx hv1
  -- the entry `a`, from `g⁻¹` at `g • Q`
  have hden2 : den g⁻¹ (g • Q) ≤ K1 := by
    rw [den_eq_div, inv_smul_smul]
    exact div_le_div₀ hM.le hv2' hm hv1
  obtain ⟨-, ha⟩ := bottom_bounds g⁻¹ (g • Q) hm hden2 hx' hv1'
  have hinv11 : (g⁻¹ : SL(2, ℂ)) 1 1 = g 0 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; rfl
  rw [hinv11] at ha
  -- the entry `b`, from `w g` at `Q`
  have hdenw : den wMat (g • Q) ≤ B ^ 2 + M ^ 2 := by
    have : den wMat (g • Q) = ‖(g • Q).x‖ ^ 2 + (g • Q).v ^ 2 := by
      simp [den, H3.rowDen, wMat_coe, Complex.normSq_eq_norm_sq]
    rw [this]
    have h1 : ‖(g • Q).x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx' 2
    have h2 : (g • Q).v ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (g • Q).v_pos.le hv2' 2
    linarith
  have hden3 : den (wMat * g) Q ≤ K2 := by
    rw [den_mul]
    exact mul_le_mul hdenw hden1 (den_pos g Q).le (by positivity)
  obtain ⟨-, hb⟩ := bottom_bounds (wMat * g) Q hm hden3 hx hv1
  have hw11 : (wMat * g) 1 1 = g 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hw11] at hb
  intro i j
  fin_cases i <;> fin_cases j
  · change ‖g 0 0‖ ≤ _; linarith
  · change ‖g 0 1‖ ≤ _; linarith
  · change ‖g 1 0‖ ≤ _; linarith
  · change ‖g 1 1‖ ≤ _; linarith

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

variable (F) in
/-- `SL(2, 𝓞_F) → SL(2, F)`. -/
def intSL : SL(2, 𝓞 F) →* SL(2, F) := Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) F)

instance instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX : MulAction (SL(2, 𝓞 F)) (X F) := MulAction.compHom (X F) (intSL F)

lemma sigma_intSL_apply (γ : SL(2, 𝓞 F)) (w : InfinitePlace F) (i j : Fin 2) :
    (sigma F (intSL F γ) w) i j = w.embedding (algebraMap (𝓞 F) F (γ i j)) := rfl

/-- The exhausting boxes of `X`. -/
def X.box (n : ℕ) : Set (X F) := {P | ∀ w, P w ∈ H3.box (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) n}

/-- The algebraic integers with all embeddings bounded by `C` form a finite set. -/
lemma finite_integers_bounded (C : ℝ) :
    {a : 𝓞 F | ∀ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F a)‖ ≤ C}.Finite := by
  have h := NumberField.Embeddings.finite_of_norm_le F ℂ C
  refine (h.preimage (f := fun a : 𝓞 F => (a : F)) (Subtype.val_injective.injOn)).subset ?_
  intro a ha
  refine ⟨a.2, fun φ => ?_⟩
  have := ha (InfinitePlace.mk φ)
  rwa [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at this

/-- **Proper discontinuity**: a box meets only finitely many of its translates. -/
theorem finite_return_box (n : ℕ) :
    {γ : SL(2, 𝓞 F) | ∃ P ∈ (X.box n : Set (X F)), γ • P ∈ (X.box n : Set (X F))}.Finite := by
  obtain ⟨C, hC⟩ := entries_bounded (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) n (by positivity)
  have hS := finite_integers_bounded (F := F) C
  have hrow : {r : Fin 2 → 𝓞 F | ∀ j, r j ∈
      {a : 𝓞 F | ∀ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F a)‖ ≤ C}}.Finite :=
    Set.Finite.pi' fun _ => hS
  have hmat : {A : Matrix (Fin 2) (Fin 2) (𝓞 F) | ∀ i, A i ∈
      {r : Fin 2 → 𝓞 F | ∀ j, r j ∈
        {a : 𝓞 F | ∀ w : InfinitePlace F, ‖w.embedding (algebraMap (𝓞 F) F a)‖ ≤ C}}}.Finite :=
    Set.Finite.pi' fun _ => hrow
  refine (hmat.preimage (f := fun γ : SL(2, 𝓞 F) => (γ : Matrix (Fin 2) (Fin 2) (𝓞 F)))
    (Subtype.val_injective.injOn)).subset ?_
  rintro γ ⟨P, hP, hγP⟩ i j w
  have := hC (sigma F (intSL F γ) w) (P w) (hP w) (hγP w) i j
  rwa [sigma_intSL_apply] at this

/-- A compact subset of `X` lies in a box. -/
theorem X.exists_box_of_isCompact {K : Set (X F)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ X.box n := by
  have hcont : Continuous fun P : X F =>
      ∑ w : InfinitePlace F, (‖P.x w‖ + P.v w + 1 / P.v w) := by
    refine continuous_finsetSum _ fun w _ => ?_
    exact ((X.continuous_x w).norm.add (X.continuous_v w)).add
      (continuous_const.div (X.continuous_v w) fun P => (P.v_pos w).ne')
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_ge C
  refine ⟨n, fun P hP w => ?_⟩
  have hnn : ∀ w' ∈ (Finset.univ : Finset (InfinitePlace F)),
      0 ≤ ‖P.x w'‖ + P.v w' + 1 / P.v w' := fun w' _ => by
    have := P.v_pos w'
    positivity
  have h1 := Finset.single_le_sum hnn (Finset.mem_univ w)
  have h5 := (h1.trans ((le_abs_self _).trans (hC P hP))).trans hn
  have hv := P.v_pos w
  have h3 : 0 < 1 / P.v w := by positivity
  have h4 := norm_nonneg (P.x w)
  refine ⟨by change ‖P.x w‖ ≤ n; linarith, ?_, by change P.v w ≤ (n : ℝ) + 1; linarith⟩
  change 1 / ((n : ℝ) + 1) ≤ P.v w
  have h6 : 1 / P.v w ≤ n := by linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hv] at h6
  nlinarith

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end


