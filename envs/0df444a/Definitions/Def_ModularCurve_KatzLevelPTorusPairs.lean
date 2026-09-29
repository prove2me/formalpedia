-- Prove2me | Definitions.Def_ModularCurve_KatzLevelPTorusPairs
-- name    : ModularCurve_KatzLevelPTorusPairs
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/2ce6ec37-5a39-5d2c-8c01-2b62fbb81a77
-- title:
--   Universal rings of level-p torus pairs
-- statement:
--   Fix natural numbers $p, a, b$ and work over the universal basis ring `UnivBasisRing p`, carrying the universal Weierstrass curve `univCurveT p` and the level-$p$ datum `univData p`. The element `torusX p a` is $\Phi_a(x_P)$ multiplied by `Ring.inverse` of $\Psi_a^2(x_P)$, where $\Phi_a$, $\Psi_a^2$ are Mathlib's division-polynomial data of `univCurveT p` and $x_P$ is the first abscissa of `univData p`; `torusQuadratic p a` is the monic quadratic $X^2 + (a_1 t + a_3)X - (t^3 + a_2 t^2 + a_4 t + a_6)$ in $t =$ `torusX p a`, whose roots are the ordinates over that abscissa (`monic_torusQuadratic`, and `equation_map_of_torusQuadratic_eval₂`: any root of its image under a ring map $i$ gives an affine point with abscissa $i(t)$ on the base-changed curve). `TorusQRing p a b` adjoins such a root to the ring `BorelQRing p b`, and is equipped with `xP`, `yP` (the adjoined root), `xQ` (the image of `borelX p b`) and `yQ` (the image of `borelQY p b`), assembled into `torusQData'`; both resulting points lie on the base-changed curve `torusQCurve p a b`. Inverting `torusDenom p a b`, the product of the two elements $\mathrm{indepElt}(x_P,x_Q)$ and $\mathrm{indepElt}(x_Q,x_P)$ for this pair, yields `TorusRing p a b` as a localisation away from that element, with base-changed curve `torusCurve`, the transported universal datum `torusData` (a level-$p$ structure, with $\Delta$ and $p$ invertible) and the second datum `torusData'`.
--
--   The universal property is realised by `TorusRing.lift`: for a ring map $\varphi$ from `UnivBasisRing p` to $T$ and a level-$p$ structure $D'$ on the curve base-changed along $\varphi$ whose abscissae are $\varphi(\mathrm{torusX}\,p\,a)$ and $\varphi(\mathrm{borelX}\,p\,b)$, one obtains a ring map out of `TorusRing p a b` restricting to $\varphi$ and carrying `torusData'` to $D'$ (so also `torusCurve` and `torusData` to their base changes); `TorusRing.ringHom_ext` states that a ring map out of `TorusRing p a b` is determined by its restriction to `UnivBasisRing p` together with the image of `torusData'`.
--
--   **Relation to Mathlib.** The constructions use Mathlib's `AdjoinRoot`, `Localization.Away` and the division-polynomial data `Φ`, `ΨSq`, `preΨ` of `WeierstrassCurve`; the four-point datum `LevelPData`, the predicate `IsLevelPStructure` and the independence element `indepElt` are the project's own notions.
--
--   **Where it is used.** These rings are the universal carriers of a pair consisting of the universal level-$p$ structure and the second structure with abscissae $x([a]P)$, $x([b]Q)$, against which the torus (split Cartan) conditions on Katz level-$p$ modular forms — dependence only on the two lines spanned by $P$ and $Q$ — are formulated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_KatzLevelPTorusPairs.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section Torus

variable (p : ℕ) (a b : ℕ)

def torusX : UnivBasisRing p :=
  ((univCurveT p).Φ a).eval (univData p).xP * Ring.inverse (((univCurveT p).ΨSq a).eval (univData p).xP)

def torusQuadratic : Polynomial (UnivBasisRing p) :=
  X ^ 2 + C ((univCurveT p).a₁ * torusX p a + (univCurveT p).a₃) * X -
    C (torusX p a ^ 3 + (univCurveT p).a₂ * torusX p a ^ 2 + (univCurveT p).a₄ * torusX p a +
      (univCurveT p).a₆)

theorem monic_torusQuadratic : (torusQuadratic p a).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one 2 ?_ ?_
  · rw [torusQuadratic]
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact natDegree_X_pow_le 2
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans one_le_two)
    · exact (natDegree_C _).le.trans (Nat.zero_le _)
  · rw [torusQuadratic, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    norm_num

theorem equation_map_of_torusQuadratic_eval₂ {S : Type v} [CommRing S] (i : UnivBasisRing p →+* S)
    (y : S) (h : (torusQuadratic p a).eval₂ i y = 0) :
    ((univCurveT p).map i).toAffine.Equation (i (torusX p a)) y := by
  simp only [torusQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add,
    map_mul, map_pow] at h
  rw [WeierstrassCurve.Affine.equation_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  linear_combination h

abbrev TorusQRing : Type :=
  AdjoinRoot ((torusQuadratic p a).map (algebraMap (UnivBasisRing p) (BorelQRing p b)))

theorem monic_torusQuadratic_map :
    ((torusQuadratic p a).map (algebraMap (UnivBasisRing p) (BorelQRing p b))).Monic :=
  (monic_torusQuadratic p a).map _

def TorusQRing.ofUniv : UnivBasisRing p →+* TorusQRing p a b :=
  (AdjoinRoot.of _).comp (algebraMap (UnivBasisRing p) (BorelQRing p b))

theorem TorusQRing.algebraMap_eq :
    algebraMap (UnivBasisRing p) (TorusQRing p a b) = TorusQRing.ofUniv p a b := by
  refine RingHom.ext fun z => ?_
  rw [IsScalarTower.algebraMap_apply (UnivBasisRing p) (BorelQRing p b) (TorusQRing p a b) z,
    TorusQRing.ofUniv, RingHom.comp_apply]
  exact RingHom.congr_fun (AdjoinRoot.algebraMap_eq _) _

def TorusQRing.xP : TorusQRing p a b := TorusQRing.ofUniv p a b (torusX p a)

def TorusQRing.yP : TorusQRing p a b := AdjoinRoot.root _

def TorusQRing.xQ : TorusQRing p a b := TorusQRing.ofUniv p a b (borelX p b)

def TorusQRing.yQ : TorusQRing p a b := AdjoinRoot.of _ (borelQY p b)

def torusQCurve : WeierstrassCurve (TorusQRing p a b) := (univCurveT p).map (TorusQRing.ofUniv p a b)

def torusQData' : LevelPData (TorusQRing p a b) :=
  ⟨TorusQRing.xP p a b, TorusQRing.yP p a b, TorusQRing.xQ p a b, TorusQRing.yQ p a b⟩

theorem equation_torusQ_P :
    (torusQCurve p a b).toAffine.Equation (TorusQRing.xP p a b) (TorusQRing.yP p a b) := by
  refine equation_map_of_torusQuadratic_eval₂ p a _ _ ?_
  rw [TorusQRing.ofUniv, ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root _

theorem equation_torusQ_Q :
    (torusQCurve p a b).toAffine.Equation (TorusQRing.xQ p a b) (TorusQRing.yQ p a b) := by
  have h := equation_map (AdjoinRoot.of ((torusQuadratic p a).map (algebraMap _ (BorelQRing p b))))
    (equation_borelQ p b)
  rw [borelQCurve, WeierstrassCurve.map_map] at h
  exact h

def torusDenom : TorusQRing p a b :=
  indepElt (torusQCurve p a b) p (TorusQRing.xP p a b) (TorusQRing.xQ p a b) *
    indepElt (torusQCurve p a b) p (TorusQRing.xQ p a b) (TorusQRing.xP p a b)

def TorusRing : Type := Localization.Away (torusDenom p a b)

instance : CommRing (TorusRing p a b) := inferInstanceAs (CommRing (Localization.Away (torusDenom p a b)))

instance : Algebra (TorusQRing p a b) (TorusRing p a b) :=
  inferInstanceAs (Algebra (TorusQRing p a b) (Localization.Away (torusDenom p a b)))

instance : IsLocalization.Away (torusDenom p a b) (TorusRing p a b) :=
  inferInstanceAs (IsLocalization.Away (torusDenom p a b) (Localization.Away (torusDenom p a b)))

instance : Algebra (UnivBasisRing p) (TorusRing p a b) :=
  inferInstanceAs (Algebra (UnivBasisRing p) (Localization.Away (torusDenom p a b)))

instance : IsScalarTower (UnivBasisRing p) (TorusQRing p a b) (TorusRing p a b) :=
  inferInstanceAs (IsScalarTower (UnivBasisRing p) (TorusQRing p a b) (Localization.Away (torusDenom p a b)))

def TorusRing.ofUniv : UnivBasisRing p →+* TorusRing p a b := algebraMap (UnivBasisRing p) (TorusRing p a b)

theorem TorusRing.algebraMap_eq : algebraMap (UnivBasisRing p) (TorusRing p a b) = TorusRing.ofUniv p a b := rfl

theorem TorusRing.ofUniv_eq_comp : TorusRing.ofUniv p a b =
    (algebraMap (TorusQRing p a b) (TorusRing p a b)).comp (TorusQRing.ofUniv p a b) := by
  rw [TorusRing.ofUniv, IsScalarTower.algebraMap_eq (UnivBasisRing p) (TorusQRing p a b) (TorusRing p a b),
    TorusQRing.algebraMap_eq]

def torusCurve : WeierstrassCurve (TorusRing p a b) := (univCurveT p).map (TorusRing.ofUniv p a b)

theorem torusCurve_eq_map_torusQCurve :
    torusCurve p a b = (torusQCurve p a b).map (algebraMap (TorusQRing p a b) (TorusRing p a b)) := by
  rw [torusCurve, TorusRing.ofUniv_eq_comp, ← WeierstrassCurve.map_map, torusQCurve]

def torusData : LevelPData (TorusRing p a b) := (univData p).map (TorusRing.ofUniv p a b)

def torusData' : LevelPData (TorusRing p a b) :=
  (torusQData' p a b).map (algebraMap (TorusQRing p a b) (TorusRing p a b))

theorem torusData'_xP : (torusData' p a b).xP = TorusRing.ofUniv p a b (torusX p a) := by
  rw [TorusRing.ofUniv_eq_comp]; rfl

theorem torusData'_xQ : (torusData' p a b).xQ = TorusRing.ofUniv p a b (borelX p b) := by
  rw [TorusRing.ofUniv_eq_comp]; rfl

theorem isUnit_Δ_torusCurve : IsUnit (torusCurve p a b).Δ := by
  rw [torusCurve, WeierstrassCurve.map_Δ]; exact (isUnit_Δ_univCurveT p).map _

theorem isLevelPStructure_torusData : IsLevelPStructure (torusCurve p a b) p (torusData p a b) :=
  (isLevelPStructure_univData p).map _

theorem isUnit_natCast_torusRing : IsUnit (p : TorusRing p a b) := by
  simpa only [map_natCast] using (isUnit_natCast_univBasisRing p).map (TorusRing.ofUniv p a b)

theorem isUnit_algebraMap_torusDenom :
    IsUnit (algebraMap (TorusQRing p a b) (TorusRing p a b) (torusDenom p a b)) :=
  IsLocalization.Away.algebraMap_isUnit _

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
  (hD' : IsLevelPStructure ((univCurveT p).map φ) p D')
  (hxP : D'.xP = φ (torusX p a)) (hxQ : D'.xQ = φ (borelX p b))

include hD' hxP in
theorem torusQuadratic_eval₂_eq_zero : (torusQuadratic p a).eval₂ φ D'.yP = 0 := by
  have hyP := hD'.equation_P
  rw [WeierstrassCurve.Affine.equation_iff] at hyP
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, hxP] at hyP
  simp only [torusQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add,
    map_mul, map_pow]
  linear_combination hyP

def TorusQRing.lift : TorusQRing p a b →+* T :=
  AdjoinRoot.lift (BorelQRing.lift p b φ D' hD' hxQ) D'.yP (by
    rw [Polynomial.eval₂_map]
    have h : (BorelQRing.lift p b φ D' hD' hxQ).comp (algebraMap (UnivBasisRing p) (BorelQRing p b)) = φ := by
      rw [AdjoinRoot.algebraMap_eq]
      exact RingHom.ext (BorelQRing.lift_of p b φ D' hD' hxQ)
    rw [h]
    exact torusQuadratic_eval₂_eq_zero p a φ D' hD' hxP)

@[simp] theorem TorusQRing.lift_ofUniv (z : UnivBasisRing p) :
    TorusQRing.lift p a b φ D' hD' hxP hxQ (TorusQRing.ofUniv p a b z) = φ z := by
  rw [TorusQRing.ofUniv, RingHom.comp_apply, TorusQRing.lift, AdjoinRoot.lift_of, AdjoinRoot.algebraMap_eq,
    BorelQRing.lift_of]

theorem TorusQRing.lift_comp_ofUniv : (TorusQRing.lift p a b φ D' hD' hxP hxQ).comp (TorusQRing.ofUniv p a b) = φ :=
  RingHom.ext (TorusQRing.lift_ofUniv p a b φ D' hD' hxP hxQ)

@[simp] theorem TorusQRing.lift_xP : TorusQRing.lift p a b φ D' hD' hxP hxQ (TorusQRing.xP p a b) = D'.xP := by
  rw [TorusQRing.xP, TorusQRing.lift_ofUniv, hxP]

@[simp] theorem TorusQRing.lift_yP : TorusQRing.lift p a b φ D' hD' hxP hxQ (TorusQRing.yP p a b) = D'.yP :=
  AdjoinRoot.lift_root _

@[simp] theorem TorusQRing.lift_xQ : TorusQRing.lift p a b φ D' hD' hxP hxQ (TorusQRing.xQ p a b) = D'.xQ := by
  rw [TorusQRing.xQ, TorusQRing.lift_ofUniv, hxQ]

@[simp] theorem TorusQRing.lift_yQ : TorusQRing.lift p a b φ D' hD' hxP hxQ (TorusQRing.yQ p a b) = D'.yQ := by
  rw [TorusQRing.yQ, TorusQRing.lift, AdjoinRoot.lift_of, BorelQRing.lift_borelQY]

theorem torusQCurve_map_lift :
    (torusQCurve p a b).map (TorusQRing.lift p a b φ D' hD' hxP hxQ) = (univCurveT p).map φ := by
  rw [torusQCurve, WeierstrassCurve.map_map, TorusQRing.lift_comp_ofUniv]

theorem torusQData'_map_lift : (torusQData' p a b).map (TorusQRing.lift p a b φ D' hD' hxP hxQ) = D' :=
  LevelPData.ext (TorusQRing.lift_xP ..) (TorusQRing.lift_yP ..) (TorusQRing.lift_xQ ..) (TorusQRing.lift_yQ ..)

theorem TorusQRing.lift_torusDenom : TorusQRing.lift p a b φ D' hD' hxP hxQ (torusDenom p a b) =
    indepElt ((univCurveT p).map φ) p D'.xP D'.xQ * indepElt ((univCurveT p).map φ) p D'.xQ D'.xP := by
  rw [torusDenom, map_mul, ← indepElt_map, ← indepElt_map, torusQCurve_map_lift, TorusQRing.lift_xP,
    TorusQRing.lift_xQ]

def TorusRing.lift : TorusRing p a b →+* T :=
  IsLocalization.Away.lift (torusDenom p a b) (g := TorusQRing.lift p a b φ D' hD' hxP hxQ)
    (by rw [TorusQRing.lift_torusDenom]; exact hD'.isUnit_indepElt_PQ.mul hD'.isUnit_indepElt_QP)

@[simp] theorem TorusRing.lift_algebraMap (z : TorusQRing p a b) :
    TorusRing.lift p a b φ D' hD' hxP hxQ (algebraMap (TorusQRing p a b) (TorusRing p a b) z) =
      TorusQRing.lift p a b φ D' hD' hxP hxQ z :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem TorusRing.lift_ofUniv (z : UnivBasisRing p) :
    TorusRing.lift p a b φ D' hD' hxP hxQ (TorusRing.ofUniv p a b z) = φ z := by
  rw [TorusRing.ofUniv_eq_comp, RingHom.comp_apply, TorusRing.lift_algebraMap, TorusQRing.lift_ofUniv]

theorem TorusRing.lift_comp_ofUniv : (TorusRing.lift p a b φ D' hD' hxP hxQ).comp (TorusRing.ofUniv p a b) = φ :=
  RingHom.ext (TorusRing.lift_ofUniv p a b φ D' hD' hxP hxQ)

theorem torusCurve_map_lift :
    (torusCurve p a b).map (TorusRing.lift p a b φ D' hD' hxP hxQ) = (univCurveT p).map φ := by
  rw [torusCurve, WeierstrassCurve.map_map, TorusRing.lift_comp_ofUniv]

theorem torusData_map_lift :
    (torusData p a b).map (TorusRing.lift p a b φ D' hD' hxP hxQ) = (univData p).map φ := by
  rw [torusData, LevelPData.map_map, TorusRing.lift_comp_ofUniv]

theorem torusData'_map_lift : (torusData' p a b).map (TorusRing.lift p a b φ D' hD' hxP hxQ) = D' := by
  rw [torusData', LevelPData.map_map]
  have h : (TorusRing.lift p a b φ D' hD' hxP hxQ).comp (algebraMap (TorusQRing p a b) (TorusRing p a b)) =
      TorusQRing.lift p a b φ D' hD' hxP hxQ :=
    RingHom.ext (TorusRing.lift_algebraMap p a b φ D' hD' hxP hxQ)
  rw [h, torusQData'_map_lift]

theorem TorusRing.ringHom_ext {S : Type w} [CommRing S] {f g : TorusRing p a b →+* S}
    (h : f.comp (TorusRing.ofUniv p a b) = g.comp (TorusRing.ofUniv p a b))
    (hD : (torusData' p a b).map f = (torusData' p a b).map g) : f = g := by
  have h2 : f (algebraMap _ _ (TorusQRing.yP p a b)) = g (algebraMap _ _ (TorusQRing.yP p a b)) :=
    congrArg LevelPData.yP hD
  have h4 : f (algebraMap _ _ (TorusQRing.yQ p a b)) = g (algebraMap _ _ (TorusQRing.yQ p a b)) :=
    congrArg LevelPData.yQ hD
  refine IsLocalization.ringHom_ext (Submonoid.powers (torusDenom p a b)) ?_
  have h' : ((f.comp (algebraMap (TorusQRing p a b) (TorusRing p a b))).comp (AdjoinRoot.of _)).comp
      (algebraMap (UnivBasisRing p) (BorelQRing p b)) =
      ((g.comp (algebraMap (TorusQRing p a b) (TorusRing p a b))).comp (AdjoinRoot.of _)).comp
      (algebraMap (UnivBasisRing p) (BorelQRing p b)) := by
    have e : (algebraMap (TorusQRing p a b) (TorusRing p a b)).comp ((AdjoinRoot.of _).comp
        (algebraMap (UnivBasisRing p) (BorelQRing p b))) = TorusRing.ofUniv p a b :=
      (TorusRing.ofUniv_eq_comp p a b).symm
    simpa only [RingHom.comp_assoc, e] using h
  refine adjoinRoot_ringHom_ext (adjoinRoot_ringHom_ext ?_ ?_) h2
  · refine RingHom.ext fun z => ?_
    have hz := RingHom.congr_fun h' z
    simp only [RingHom.comp_apply] at hz ⊢
    rw [← RingHom.congr_fun (AdjoinRoot.algebraMap_eq (borelQuadratic p b)) z]
    exact hz
  · exact h4

end Torus

end LevelP

end ModularCurve

end


