-- Prove2me | Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
-- name    : ModularCurve_KatzLevelPClassifyingMaps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/261dc5c5-6eb6-51bb-b8e6-ddc7922eaa0e
-- title:
--   Classifying maps for the universal level-p rings
-- statement:
--   The first part of the module constructs the ring maps out of the level-$p$ tower attached to a Weierstrass curve $W$ over a commutative ring $B$. Given $\varphi\colon B\to T$ and $x,y\in T$ with $(\,(W\otimes_\varphi T)\,\tilde\psi_p)(x)=0$ and $(x,y)$ on the affine curve $W\otimes_\varphi T$, `PsiRoot.lift` and `TorsionPointRing.lift` are the maps out of the two successive root adjunctions sending the tautological $x$- and $y$-coordinates to $x$ and $y$ and restricting to $\varphi$ on $B$; the computation rules, the identity `torsionPtCurve` $\mapsto W\otimes_\varphi T$, and uniqueness (`TorsionPointRing.ringHom_ext`) are recorded. If instead a `LevelPData` $D$ over $T$ satisfies `IsLevelPStructure` for $W\otimes_\varphi T$ (both points on the curve, both $x$-coordinates roots of $\tilde\psi_p$, both `indepElt` products units), then `onePointLift`, `twoPointLift` and, after inverting `indepDenom`, `BasisRing.lift` carry the tautological basis to $D$, again uniquely. Next, `genericLift W` evaluates the five coordinate variables at $a_1,\dots,a_6$ of $W$, `UnivBase.lift p W hW` is the induced map on the localisation away from $p\Delta$ when $p\Delta(W)\in T^\times$, and `UnivBasisRing.classify p W hW D hD` is the resulting homomorphism $\mathcal T_p\to T$, characterised by pushing the universal curve to $W$ and the universal data to $D$ (`eq_classify`), being the identity on the universal object, and commuting with further ring maps.
--
--   Two further universal rings are built over $\mathcal T_p$. `VCRing p` is the polynomial ring in four variables localised at the first; it carries the variable change `univVC` whose $(u,r,s,t)$ are the four variables, and the base changes `vcCurve`, `vcData`, with `VCRing.lift` classifying a pair (map $\varphi$ out of $\mathcal T_p$, variable change $C$ over $T$). For $a\in\mathbb N$, `borelX p a` is $\Phi_a(x_Q)$ times the ring-theoretic inverse of $\Psi_a^2(x_Q)$; `borelQuadratic` is the monic Weierstrass quadratic in $y$ at that $x$; adjoining its root, then a further $p$-division point, then inverting the corresponding product `borelDenom` of `indepElt`s yields `BorelRing p a`, with the tautological data `borelData'` and the pushforward `borelData` of the universal data. Its lift classifies a map $\varphi$ together with a level-$p$ structure $D'$ on the pushed-forward universal curve subject to $x_{Q'}=\varphi(\mathrm{borelX})$, and is unique with these properties.
--
--   **Relation to Mathlib.** The lifts are built from Mathlib's `AdjoinRoot.lift` and `IsLocalization.Away.lift`, and the curves, division polynomials `preΨ`, `ΨSq`, `Φ` and admissible changes of coordinates `VariableChange` are Mathlib's; `LevelPData`, `IsLevelPStructure`, `indepElt` and the rings of the level-$p$ tower are the project's own.
--
--   **Where it is used.** These maps exhibit the level-$p$ tower as a representing object: a Weierstrass curve with $p\Delta$ invertible together with a level-$p$ structure over any ring is classified by a homomorphism out of `UnivBasisRing p`, and the variable-change and Borel variants classify the same data equipped with an admissible change of coordinates, respectively with a second level-$p$ structure whose second point has the $x$-coordinate of the $a$-th multiple of $Q$. They are the algebraic substrate for evaluating Katz level-$p$ and $\Gamma_0(p)$ forms on universal objects.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_KatzLevelPClassifyingMaps.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

theorem adjoinRoot_ringHom_ext {R : Type u} [CommRing R] {S : Type v} [Semiring S] {f : R[X]}
    {g₁ g₂ : AdjoinRoot f →+* S} (h₁ : g₁.comp (AdjoinRoot.of f) = g₂.comp (AdjoinRoot.of f))
    (h₂ : g₁ (AdjoinRoot.root f) = g₂ (AdjoinRoot.root f)) : g₁ = g₂ :=
  Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun a => RingHom.congr_fun h₁ a) h₂)

section TorsionPointLift

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) {T : Type v} [CommRing T]
  (φ : B →+* T) (x y : T)

theorem eval₂_preΨ_eq_zero (hx : ((W.map φ).preΨ p).eval x = 0) : (W.preΨ p).eval₂ φ x = 0 := by
  rwa [WeierstrassCurve.map_preΨ, Polynomial.eval_map] at hx

def PsiRoot.lift (hx : ((W.map φ).preΨ p).eval x = 0) : PsiRoot W p →+* T :=
  AdjoinRoot.lift φ x (eval₂_preΨ_eq_zero W p φ x hx)

@[simp] theorem PsiRoot.lift_ofBase (hx : ((W.map φ).preΨ p).eval x = 0) (b : B) :
    PsiRoot.lift W p φ x hx (PsiRoot.ofBase W p b) = φ b :=
  AdjoinRoot.lift_of _

@[simp] theorem PsiRoot.lift_psiRootX (hx : ((W.map φ).preΨ p).eval x = 0) :
    PsiRoot.lift W p φ x hx (psiRootX W p) = x :=
  AdjoinRoot.lift_root _

theorem torsionQuadratic_eval₂_eq_zero (hx : ((W.map φ).preΨ p).eval x = 0)
    (hy : (W.map φ).toAffine.Equation x y) :
    (torsionQuadratic W p).eval₂ (PsiRoot.lift W p φ x hx) y = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hy
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hy
  simp only [torsionQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    map_add, map_mul, map_pow, PsiRoot.lift_ofBase, PsiRoot.lift_psiRootX]
  linear_combination hy

def TorsionPointRing.lift (hx : ((W.map φ).preΨ p).eval x = 0)
    (hy : (W.map φ).toAffine.Equation x y) : TorsionPointRing W p →+* T :=
  AdjoinRoot.lift (PsiRoot.lift W p φ x hx) y (torsionQuadratic_eval₂_eq_zero W p φ x y hx hy)

variable (hx : ((W.map φ).preΨ p).eval x = 0) (hy : (W.map φ).toAffine.Equation x y)

@[simp] theorem TorsionPointRing.lift_ofPsiRoot (z : PsiRoot W p) :
    TorsionPointRing.lift W p φ x y hx hy (TorsionPointRing.ofPsiRoot W p z) =
      PsiRoot.lift W p φ x hx z :=
  AdjoinRoot.lift_of _

@[simp] theorem TorsionPointRing.lift_ofBase (b : B) :
    TorsionPointRing.lift W p φ x y hx hy (TorsionPointRing.ofBase W p b) = φ b := by
  rw [TorsionPointRing.ofBase, RingHom.comp_apply, TorsionPointRing.lift_ofPsiRoot,
    PsiRoot.lift_ofBase]

theorem TorsionPointRing.lift_comp_ofBase :
    (TorsionPointRing.lift W p φ x y hx hy).comp (TorsionPointRing.ofBase W p) = φ :=
  RingHom.ext (TorsionPointRing.lift_ofBase W p φ x y hx hy)

@[simp] theorem TorsionPointRing.lift_torsionPtX :
    TorsionPointRing.lift W p φ x y hx hy (torsionPtX W p) = x := by
  rw [torsionPtX, TorsionPointRing.lift_ofPsiRoot, PsiRoot.lift_psiRootX]

@[simp] theorem TorsionPointRing.lift_torsionPtY :
    TorsionPointRing.lift W p φ x y hx hy (torsionPtY W p) = y :=
  AdjoinRoot.lift_root _

theorem torsionPtCurve_map_lift :
    (torsionPtCurve W p).map (TorsionPointRing.lift W p φ x y hx hy) = W.map φ := by
  rw [torsionPtCurve, WeierstrassCurve.map_map, TorsionPointRing.lift_comp_ofBase]

theorem TorsionPointRing.ringHom_ext {S : Type w} [Semiring S] {f g : TorsionPointRing W p →+* S}
    (h : f.comp (TorsionPointRing.ofBase W p) = g.comp (TorsionPointRing.ofBase W p))
    (hX : f (torsionPtX W p) = g (torsionPtX W p)) (hY : f (torsionPtY W p) = g (torsionPtY W p)) :
    f = g := by
  refine adjoinRoot_ringHom_ext (adjoinRoot_ringHom_ext ?_ hX) hY
  ext b
  exact RingHom.congr_fun h b

end TorsionPointLift

section BasisRingLift

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) {T : Type v} [CommRing T]
  (φ : B →+* T) (D : LevelPData T) (hD : IsLevelPStructure (W.map φ) p D)

def onePointLift : TorsionPointRing W p →+* T :=
  TorsionPointRing.lift W p φ D.xP D.yP hD.preΨ_P hD.equation_P

theorem torsionPtCurve_map_onePointLift :
    (torsionPtCurve W p).map (onePointLift W p φ D hD) = W.map φ :=
  torsionPtCurve_map_lift W p φ _ _ _ _

def twoPointLift : TwoPointRing W p →+* T :=
  TorsionPointRing.lift (torsionPtCurve W p) p (onePointLift W p φ D hD) D.xQ D.yQ
    (by rw [torsionPtCurve_map_onePointLift]; exact hD.preΨ_Q)
    (by rw [torsionPtCurve_map_onePointLift]; exact hD.equation_Q)

theorem twoPointLift_comp_ofOnePoint :
    (twoPointLift W p φ D hD).comp (TwoPointRing.ofOnePoint W p) = onePointLift W p φ D hD :=
  TorsionPointRing.lift_comp_ofBase _ p _ _ _ _ _

theorem twoPointLift_comp_ofBase : (twoPointLift W p φ D hD).comp (TwoPointRing.ofBase W p) = φ := by
  rw [TwoPointRing.ofBase, ← RingHom.comp_assoc, twoPointLift_comp_ofOnePoint, onePointLift,
    TorsionPointRing.lift_comp_ofBase]

@[simp] theorem twoPointLift_ofBase (b : B) : twoPointLift W p φ D hD (TwoPointRing.ofBase W p b) = φ b :=
  RingHom.congr_fun (twoPointLift_comp_ofBase W p φ D hD) b

@[simp] theorem twoPointLift_xP : twoPointLift W p φ D hD (TwoPointRing.xP W p) = D.xP := by
  rw [TwoPointRing.xP, twoPointLift, TorsionPointRing.lift_ofBase, onePointLift,
    TorsionPointRing.lift_torsionPtX]

@[simp] theorem twoPointLift_yP : twoPointLift W p φ D hD (TwoPointRing.yP W p) = D.yP := by
  rw [TwoPointRing.yP, twoPointLift, TorsionPointRing.lift_ofBase, onePointLift,
    TorsionPointRing.lift_torsionPtY]

@[simp] theorem twoPointLift_xQ : twoPointLift W p φ D hD (TwoPointRing.xQ W p) = D.xQ :=
  TorsionPointRing.lift_torsionPtX _ p _ _ _ _ _

@[simp] theorem twoPointLift_yQ : twoPointLift W p φ D hD (TwoPointRing.yQ W p) = D.yQ :=
  TorsionPointRing.lift_torsionPtY _ p _ _ _ _ _

theorem twoPointCurve_map_twoPointLift :
    (twoPointCurve W p).map (twoPointLift W p φ D hD) = W.map φ := by
  show ((torsionPtCurve W p).map (TwoPointRing.ofOnePoint W p)).map (twoPointLift W p φ D hD) = W.map φ
  rw [WeierstrassCurve.map_map, twoPointLift_comp_ofOnePoint, torsionPtCurve_map_onePointLift]

theorem twoPointLift_indepDenom : twoPointLift W p φ D hD (indepDenom W p) =
    indepElt (W.map φ) p D.xP D.xQ * indepElt (W.map φ) p D.xQ D.xP := by
  rw [indepDenom, map_mul, ← indepElt_map, ← indepElt_map, twoPointCurve_map_twoPointLift,
    twoPointLift_xP, twoPointLift_xQ]

theorem isUnit_twoPointLift_indepDenom : IsUnit (twoPointLift W p φ D hD (indepDenom W p)) := by
  rw [twoPointLift_indepDenom]
  exact hD.isUnit_indepElt_PQ.mul hD.isUnit_indepElt_QP

def BasisRing.lift : BasisRing W p →+* T :=
  IsLocalization.Away.lift (indepDenom W p) (isUnit_twoPointLift_indepDenom W p φ D hD)

theorem BasisRing.lift_comp_ofTwoPoint :
    (BasisRing.lift W p φ D hD).comp (BasisRing.ofTwoPoint W p) = twoPointLift W p φ D hD :=
  IsLocalization.Away.lift_comp _ _

@[simp] theorem BasisRing.lift_ofTwoPoint (z : TwoPointRing W p) :
    BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p z) = twoPointLift W p φ D hD z :=
  RingHom.congr_fun (BasisRing.lift_comp_ofTwoPoint W p φ D hD) z

theorem BasisRing.lift_comp_ofBase : (BasisRing.lift W p φ D hD).comp (BasisRing.ofBase W p) = φ := by
  rw [BasisRing.ofBase, ← RingHom.comp_assoc, BasisRing.lift_comp_ofTwoPoint,
    twoPointLift_comp_ofBase]

@[simp] theorem BasisRing.lift_ofBase (b : B) : BasisRing.lift W p φ D hD (BasisRing.ofBase W p b) = φ b :=
  RingHom.congr_fun (BasisRing.lift_comp_ofBase W p φ D hD) b

theorem basisCurve_map_lift : (basisCurve W p).map (BasisRing.lift W p φ D hD) = W.map φ := by
  rw [basisCurve, WeierstrassCurve.map_map, BasisRing.lift_comp_ofBase]

theorem basisData_map_lift : (basisData W p).map (BasisRing.lift W p φ D hD) = D := by
  refine LevelPData.ext ?_ ?_ ?_ ?_
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)) = D.xP
    rw [BasisRing.lift_ofTwoPoint, twoPointLift_xP]
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.yP W p)) = D.yP
    rw [BasisRing.lift_ofTwoPoint, twoPointLift_yP]
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)) = D.xQ
    rw [BasisRing.lift_ofTwoPoint, twoPointLift_xQ]
  · show BasisRing.lift W p φ D hD (BasisRing.ofTwoPoint W p (TwoPointRing.yQ W p)) = D.yQ
    rw [BasisRing.lift_ofTwoPoint, twoPointLift_yQ]

theorem BasisRing.ringHom_ext {S : Type w} [CommRing S] {f g : BasisRing W p →+* S}
    (h : f.comp (BasisRing.ofBase W p) = g.comp (BasisRing.ofBase W p))
    (hD : (basisData W p).map f = (basisData W p).map g) : f = g := by
  have h1 : f (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)) = g (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)) :=
    congrArg LevelPData.xP hD
  have h2 : f (BasisRing.ofTwoPoint W p (TwoPointRing.yP W p)) = g (BasisRing.ofTwoPoint W p (TwoPointRing.yP W p)) :=
    congrArg LevelPData.yP hD
  have h3 : f (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)) = g (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)) :=
    congrArg LevelPData.xQ hD
  have h4 : f (BasisRing.ofTwoPoint W p (TwoPointRing.yQ W p)) = g (BasisRing.ofTwoPoint W p (TwoPointRing.yQ W p)) :=
    congrArg LevelPData.yQ hD
  refine IsLocalization.ringHom_ext (Submonoid.powers (indepDenom W p)) ?_
  change f.comp (BasisRing.ofTwoPoint W p) = g.comp (BasisRing.ofTwoPoint W p)
  refine TorsionPointRing.ringHom_ext _ p (TorsionPointRing.ringHom_ext W p ?_ ?_ ?_) ?_ ?_
  · simpa only [RingHom.comp_assoc, BasisRing.ofBase, TwoPointRing.ofBase] using h
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end BasisRingLift

section Univ

variable (p : ℕ) {T : Type v} [CommRing T]

def genericLift (W : WeierstrassCurve T) : MvPolynomial (Fin 5) ℤ →+* T :=
  MvPolynomial.eval₂Hom (Int.castRingHom T) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

@[simp] theorem genericLift_X (W : WeierstrassCurve T) (i : Fin 5) :
    genericLift W (MvPolynomial.X i) = ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆] i :=
  MvPolynomial.eval₂Hom_X' _ _ _

theorem genericCurve_map_genericLift (W : WeierstrassCurve T) :
    genericCurve.map (genericLift W) = W := by
  cases W
  simp only [genericCurve, WeierstrassCurve.map, genericLift_X]
  rfl

theorem isUnit_genericLift_pDelta (W : WeierstrassCurve T) (hW : IsUnit ((p : T) * W.Δ)) :
    IsUnit (genericLift W (pDelta p)) := by
  rwa [pDelta, map_mul, map_natCast, ← WeierstrassCurve.map_Δ, genericCurve_map_genericLift]

def UnivBase.lift (W : WeierstrassCurve T) (hW : IsUnit ((p : T) * W.Δ)) : UnivBase p →+* T :=
  IsLocalization.Away.lift (pDelta p) (isUnit_genericLift_pDelta p W hW)

variable (W : WeierstrassCurve T) (hW : IsUnit ((p : T) * W.Δ))

theorem UnivBase.lift_comp_algebraMap :
    (UnivBase.lift p W hW).comp (algebraMap (MvPolynomial (Fin 5) ℤ) (UnivBase p)) = genericLift W :=
  IsLocalization.Away.lift_comp _ _

theorem univCurve_map_lift : (univCurve p).map (UnivBase.lift p W hW) = W := by
  rw [univCurve, WeierstrassCurve.map_map, UnivBase.lift_comp_algebraMap,
    genericCurve_map_genericLift]

theorem UnivBase.ringHom_ext {S : Type w} [CommRing S] {f g : UnivBase p →+* S}
    (h : (univCurve p).map f = (univCurve p).map g) : f = g := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (pDelta p)) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_int
      ((f.comp (algebraMap (MvPolynomial (Fin 5) ℤ) (UnivBase p))).comp MvPolynomial.C)
      ((g.comp (algebraMap (MvPolynomial (Fin 5) ℤ) (UnivBase p))).comp MvPolynomial.C)) r
  · have h' := h
    simp only [univCurve, genericCurve, WeierstrassCurve.map, WeierstrassCurve.mk.injEq] at h'
    obtain ⟨h0, h1, h2, h3, h4⟩ := h'
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

variable (D : LevelPData T) (hD : IsLevelPStructure W p D)

include hD in
theorem isLevelPStructure_map_univBaseLift : IsLevelPStructure ((univCurve p).map (UnivBase.lift p W hW)) p D := by
  rwa [univCurve_map_lift]

def UnivBasisRing.classify (W : WeierstrassCurve T) (hW : IsUnit ((p : T) * W.Δ)) (D : LevelPData T)
    (hD : IsLevelPStructure W p D) : UnivBasisRing p →+* T :=
  BasisRing.lift (univCurve p) p (UnivBase.lift p W hW) D (isLevelPStructure_map_univBaseLift p W hW D hD)

theorem UnivBasisRing.classify_comp_ofBase :
    (UnivBasisRing.classify p W hW D hD).comp (UnivBasisRing.ofBase p) = UnivBase.lift p W hW :=
  BasisRing.lift_comp_ofBase _ p _ _ _

theorem univCurveT_map_classify : (univCurveT p).map (UnivBasisRing.classify p W hW D hD) = W := by
  rw [UnivBasisRing.classify, univCurveT, basisCurve_map_lift, univCurve_map_lift]

theorem univData_map_classify : (univData p).map (UnivBasisRing.classify p W hW D hD) = D :=
  basisData_map_lift _ p _ _ _

theorem UnivBasisRing.ringHom_ext {S : Type w} [CommRing S] {f g : UnivBasisRing p →+* S}
    (hW : (univCurveT p).map f = (univCurveT p).map g)
    (hD : (univData p).map f = (univData p).map g) : f = g := by
  refine BasisRing.ringHom_ext (univCurve p) p (UnivBase.ringHom_ext p ?_) hD
  simpa only [univCurveT, basisCurve, WeierstrassCurve.map_map] using hW

theorem UnivBasisRing.eq_classify {f : UnivBasisRing p →+* T} (hf : (univCurveT p).map f = W)
    (hf' : (univData p).map f = D) : f = UnivBasisRing.classify p W hW D hD :=
  UnivBasisRing.ringHom_ext p (by rw [hf, univCurveT_map_classify]) (by rw [hf', univData_map_classify])

theorem UnivBasisRing.classify_self :
    UnivBasisRing.classify p (univCurveT p)
      ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p)) (univData p)
      (isLevelPStructure_univData p) = RingHom.id _ :=
  (UnivBasisRing.eq_classify p _ _ _ _ (WeierstrassCurve.map_id _) (LevelPData.map_id _)).symm

theorem UnivBasisRing.comp_classify {T' : Type w} [CommRing T'] (ψ : T →+* T')
    (hW' : IsUnit ((p : T') * (W.map ψ).Δ)) (hD' : IsLevelPStructure (W.map ψ) p (D.map ψ)) :
    ψ.comp (UnivBasisRing.classify p W hW D hD) = UnivBasisRing.classify p (W.map ψ) hW' (D.map ψ) hD' :=
  UnivBasisRing.eq_classify p _ _ _ _
    (by rw [← WeierstrassCurve.map_map, univCurveT_map_classify])
    (by rw [← LevelPData.map_map, univData_map_classify])

end Univ

section VC

variable (p : ℕ)

abbrev VCPoly : Type := MvPolynomial (Fin 4) (UnivBasisRing p)

def VCRing : Type := Localization.Away (MvPolynomial.X 0 : VCPoly p)

instance : CommRing (VCRing p) := inferInstanceAs (CommRing (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : Algebra (VCPoly p) (VCRing p) :=
  inferInstanceAs (Algebra (VCPoly p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : IsLocalization.Away (MvPolynomial.X 0 : VCPoly p) (VCRing p) :=
  inferInstanceAs (IsLocalization.Away (MvPolynomial.X 0 : VCPoly p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : Algebra (UnivBasisRing p) (VCRing p) :=
  inferInstanceAs (Algebra (UnivBasisRing p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

instance : IsScalarTower (UnivBasisRing p) (VCPoly p) (VCRing p) :=
  inferInstanceAs (IsScalarTower (UnivBasisRing p) (VCPoly p) (Localization.Away (MvPolynomial.X 0 : VCPoly p)))

def VCRing.ofUniv : UnivBasisRing p →+* VCRing p := algebraMap (UnivBasisRing p) (VCRing p)

theorem VCRing.algebraMap_eq : algebraMap (UnivBasisRing p) (VCRing p) = VCRing.ofUniv p := rfl

theorem VCRing.ofUniv_eq_comp :
    VCRing.ofUniv p = (algebraMap (VCPoly p) (VCRing p)).comp MvPolynomial.C := by
  rw [VCRing.ofUniv, IsScalarTower.algebraMap_eq (UnivBasisRing p) (VCPoly p) (VCRing p),
    MvPolynomial.algebraMap_eq]

def vcVar (i : Fin 4) : VCRing p := algebraMap (VCPoly p) (VCRing p) (MvPolynomial.X i)

theorem isUnit_vcVar_zero : IsUnit (vcVar p 0) :=
  IsLocalization.Away.algebraMap_isUnit (S := VCRing p) (MvPolynomial.X 0 : VCPoly p)

def univVC : VariableChange (VCRing p) :=
  ⟨(isUnit_vcVar_zero p).unit, vcVar p 1, vcVar p 2, vcVar p 3⟩

@[simp] theorem univVC_u : ((univVC p).u : VCRing p) = vcVar p 0 := rfl
@[simp] theorem univVC_r : (univVC p).r = vcVar p 1 := rfl
@[simp] theorem univVC_s : (univVC p).s = vcVar p 2 := rfl
@[simp] theorem univVC_t : (univVC p).t = vcVar p 3 := rfl

def vcCurve : WeierstrassCurve (VCRing p) := (univCurveT p).map (VCRing.ofUniv p)

def vcData : LevelPData (VCRing p) := (univData p).map (VCRing.ofUniv p)

theorem isUnit_Δ_vcCurve : IsUnit (vcCurve p).Δ := by
  rw [vcCurve, WeierstrassCurve.map_Δ]; exact (isUnit_Δ_univCurveT p).map _

theorem isLevelPStructure_vcData : IsLevelPStructure (vcCurve p) p (vcData p) :=
  (isLevelPStructure_univData p).map _

theorem isUnit_natCast_vcRing : IsUnit (p : VCRing p) := by
  simpa only [map_natCast] using (isUnit_natCast_univBasisRing p).map (VCRing.ofUniv p)

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (C : VariableChange T)

def vcPolyLift : VCPoly p →+* T := MvPolynomial.eval₂Hom φ ![(C.u : T), C.r, C.s, C.t]

@[simp] theorem vcPolyLift_X (i : Fin 4) : vcPolyLift p φ C (MvPolynomial.X i) = ![(C.u : T), C.r, C.s, C.t] i :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[simp] theorem vcPolyLift_C (z : UnivBasisRing p) : vcPolyLift p φ C (MvPolynomial.C z) = φ z :=
  MvPolynomial.eval₂Hom_C _ _ _

def VCRing.lift : VCRing p →+* T :=
  IsLocalization.Away.lift (MvPolynomial.X 0 : VCPoly p) (g := vcPolyLift p φ C)
    (by rw [vcPolyLift_X]; exact Units.isUnit C.u)

@[simp] theorem VCRing.lift_algebraMap (z : VCPoly p) :
    VCRing.lift p φ C (algebraMap (VCPoly p) (VCRing p) z) = vcPolyLift p φ C z :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem VCRing.lift_vcVar (i : Fin 4) : VCRing.lift p φ C (vcVar p i) = ![(C.u : T), C.r, C.s, C.t] i := by
  rw [vcVar, VCRing.lift_algebraMap, vcPolyLift_X]

@[simp] theorem VCRing.lift_ofUniv (z : UnivBasisRing p) : VCRing.lift p φ C (VCRing.ofUniv p z) = φ z := by
  rw [VCRing.ofUniv_eq_comp, RingHom.comp_apply, VCRing.lift_algebraMap, vcPolyLift_C]

theorem VCRing.lift_comp_ofUniv : (VCRing.lift p φ C).comp (VCRing.ofUniv p) = φ :=
  RingHom.ext (VCRing.lift_ofUniv p φ C)

theorem univVC_map_lift : (univVC p).map (VCRing.lift p φ C) = C := by
  obtain ⟨cu, cr, cs, ct⟩ := C
  simp only [VariableChange.map, univVC, VariableChange.mk.injEq]
  refine ⟨Units.ext ?_, ?_, ?_, ?_⟩
  · show VCRing.lift p φ ⟨cu, cr, cs, ct⟩ (vcVar p 0) = cu
    rw [VCRing.lift_vcVar]; rfl
  · rw [VCRing.lift_vcVar]; rfl
  · rw [VCRing.lift_vcVar]; rfl
  · rw [VCRing.lift_vcVar]; rfl

theorem vcCurve_map_lift : (vcCurve p).map (VCRing.lift p φ C) = (univCurveT p).map φ := by
  rw [vcCurve, WeierstrassCurve.map_map, VCRing.lift_comp_ofUniv]

theorem vcData_map_lift : (vcData p).map (VCRing.lift p φ C) = (univData p).map φ := by
  rw [vcData, LevelPData.map_map, VCRing.lift_comp_ofUniv]

theorem VCRing.ringHom_ext {S : Type w} [CommRing S] {f g : VCRing p →+* S}
    (h : f.comp (VCRing.ofUniv p) = g.comp (VCRing.ofUniv p)) (hv : ∀ i, f (vcVar p i) = g (vcVar p i)) :
    f = g := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.X 0 : VCPoly p)) ?_
  refine MvPolynomial.ringHom_ext (fun z => ?_) (fun i => hv i)
  have := RingHom.congr_fun h z
  rwa [VCRing.ofUniv_eq_comp] at this

end VC

section Borel

variable (p : ℕ) (a : ℕ)

def borelX : UnivBasisRing p :=
  ((univCurveT p).Φ a).eval (univData p).xQ * Ring.inverse (((univCurveT p).ΨSq a).eval (univData p).xQ)

def borelQuadratic : Polynomial (UnivBasisRing p) :=
  X ^ 2 + C ((univCurveT p).a₁ * borelX p a + (univCurveT p).a₃) * X -
    C (borelX p a ^ 3 + (univCurveT p).a₂ * borelX p a ^ 2 + (univCurveT p).a₄ * borelX p a +
      (univCurveT p).a₆)

theorem monic_borelQuadratic : (borelQuadratic p a).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one 2 ?_ ?_
  · rw [borelQuadratic]
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact natDegree_X_pow_le 2
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans one_le_two)
    · exact (natDegree_C _).le.trans (Nat.zero_le _)
  · rw [borelQuadratic, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    norm_num

abbrev BorelQRing : Type := AdjoinRoot (borelQuadratic p a)

def borelQY : BorelQRing p a := AdjoinRoot.root (borelQuadratic p a)

def borelQCurve : WeierstrassCurve (BorelQRing p a) := (univCurveT p).map (AdjoinRoot.of (borelQuadratic p a))

theorem equation_map_of_borelQuadratic_eval₂ {S : Type v} [CommRing S] (i : UnivBasisRing p →+* S) (y : S)
    (h : (borelQuadratic p a).eval₂ i y = 0) :
    ((univCurveT p).map i).toAffine.Equation (i (borelX p a)) y := by
  simp only [borelQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add,
    map_mul, map_pow] at h
  rw [WeierstrassCurve.Affine.equation_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  linear_combination h

theorem equation_borelQ :
    (borelQCurve p a).toAffine.Equation (AdjoinRoot.of (borelQuadratic p a) (borelX p a)) (borelQY p a) :=
  equation_map_of_borelQuadratic_eval₂ p a _ _ (AdjoinRoot.eval₂_root _)

abbrev BorelPRing : Type := TorsionPointRing (borelQCurve p a) p

def BorelPRing.ofUniv : UnivBasisRing p →+* BorelPRing p a :=
  (TorsionPointRing.ofBase (borelQCurve p a) p).comp (AdjoinRoot.of (borelQuadratic p a))

instance : Algebra (UnivBasisRing p) (BorelPRing p a) := (BorelPRing.ofUniv p a).toAlgebra

theorem BorelPRing.algebraMap_eq : algebraMap (UnivBasisRing p) (BorelPRing p a) = BorelPRing.ofUniv p a := rfl

instance : IsScalarTower (UnivBasisRing p) (BorelQRing p a) (BorelPRing p a) :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [BorelPRing.algebraMap_eq, BorelPRing.ofUniv, TorsionPointRing.algebraMap_eq,
      AdjoinRoot.algebraMap_eq])

def BorelPRing.xP : BorelPRing p a := torsionPtX (borelQCurve p a) p

def BorelPRing.yP : BorelPRing p a := torsionPtY (borelQCurve p a) p

def BorelPRing.xQ : BorelPRing p a := BorelPRing.ofUniv p a (borelX p a)

def BorelPRing.yQ : BorelPRing p a := TorsionPointRing.ofBase (borelQCurve p a) p (borelQY p a)

abbrev borelPCurve : WeierstrassCurve (BorelPRing p a) := torsionPtCurve (borelQCurve p a) p

theorem borelPCurve_eq : borelPCurve p a = (univCurveT p).map (BorelPRing.ofUniv p a) :=
  WeierstrassCurve.map_map (univCurveT p) (AdjoinRoot.of (borelQuadratic p a))
    (TorsionPointRing.ofBase (borelQCurve p a) p)

def borelDenom : BorelPRing p a :=
  indepElt (borelPCurve p a) p (BorelPRing.xP p a) (BorelPRing.xQ p a) *
    indepElt (borelPCurve p a) p (BorelPRing.xQ p a) (BorelPRing.xP p a)

def BorelRing : Type := Localization.Away (borelDenom p a)

instance : CommRing (BorelRing p a) := inferInstanceAs (CommRing (Localization.Away (borelDenom p a)))

instance : Algebra (BorelPRing p a) (BorelRing p a) :=
  inferInstanceAs (Algebra (BorelPRing p a) (Localization.Away (borelDenom p a)))

instance : IsLocalization.Away (borelDenom p a) (BorelRing p a) :=
  inferInstanceAs (IsLocalization.Away (borelDenom p a) (Localization.Away (borelDenom p a)))

instance : Algebra (UnivBasisRing p) (BorelRing p a) :=
  inferInstanceAs (Algebra (UnivBasisRing p) (Localization.Away (borelDenom p a)))

instance : IsScalarTower (UnivBasisRing p) (BorelPRing p a) (BorelRing p a) :=
  inferInstanceAs (IsScalarTower (UnivBasisRing p) (BorelPRing p a) (Localization.Away (borelDenom p a)))

def BorelRing.ofUniv : UnivBasisRing p →+* BorelRing p a := algebraMap (UnivBasisRing p) (BorelRing p a)

theorem BorelRing.algebraMap_eq : algebraMap (UnivBasisRing p) (BorelRing p a) = BorelRing.ofUniv p a := rfl

theorem BorelRing.ofUniv_eq_comp : BorelRing.ofUniv p a =
    (algebraMap (BorelPRing p a) (BorelRing p a)).comp (BorelPRing.ofUniv p a) := by
  rw [BorelRing.ofUniv, IsScalarTower.algebraMap_eq (UnivBasisRing p) (BorelPRing p a) (BorelRing p a),
    BorelPRing.algebraMap_eq]

def borelCurve : WeierstrassCurve (BorelRing p a) := (univCurveT p).map (BorelRing.ofUniv p a)

theorem borelCurve_eq_map_borelPCurve :
    borelCurve p a = (borelPCurve p a).map (algebraMap (BorelPRing p a) (BorelRing p a)) := by
  rw [borelCurve, BorelRing.ofUniv_eq_comp, ← WeierstrassCurve.map_map, borelPCurve_eq]

def borelData : LevelPData (BorelRing p a) := (univData p).map (BorelRing.ofUniv p a)

def borelData' : LevelPData (BorelRing p a) :=
  ⟨algebraMap _ _ (BorelPRing.xP p a), algebraMap _ _ (BorelPRing.yP p a),
    algebraMap _ _ (BorelPRing.xQ p a), algebraMap _ _ (BorelPRing.yQ p a)⟩

theorem borelData'_eq_map : borelData' p a =
    (⟨BorelPRing.xP p a, BorelPRing.yP p a, BorelPRing.xQ p a, BorelPRing.yQ p a⟩ : LevelPData _).map
      (algebraMap (BorelPRing p a) (BorelRing p a)) := rfl

theorem borelData'_xQ : (borelData' p a).xQ = BorelRing.ofUniv p a (borelX p a) := by
  rw [BorelRing.ofUniv_eq_comp]; rfl

theorem isUnit_Δ_borelCurve : IsUnit (borelCurve p a).Δ := by
  rw [borelCurve, WeierstrassCurve.map_Δ]; exact (isUnit_Δ_univCurveT p).map _

theorem isLevelPStructure_borelData : IsLevelPStructure (borelCurve p a) p (borelData p a) :=
  (isLevelPStructure_univData p).map _

theorem isUnit_natCast_borelRing : IsUnit (p : BorelRing p a) := by
  simpa only [map_natCast] using (isUnit_natCast_univBasisRing p).map (BorelRing.ofUniv p a)

theorem isUnit_algebraMap_borelDenom : IsUnit (algebraMap (BorelPRing p a) (BorelRing p a) (borelDenom p a)) :=
  IsLocalization.Away.algebraMap_isUnit _

variable {T : Type v} [CommRing T] (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
  (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a))

include hD' hxQ in
theorem borelQuadratic_eval₂_eq_zero : (borelQuadratic p a).eval₂ φ D'.yQ = 0 := by
  have hyQ := hD'.equation_Q
  rw [WeierstrassCurve.Affine.equation_iff] at hyQ
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, hxQ] at hyQ
  simp only [borelQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add,
    map_mul, map_pow]
  linear_combination hyQ

def BorelQRing.lift (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
    (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a)) :
    BorelQRing p a →+* T :=
  AdjoinRoot.lift φ D'.yQ (borelQuadratic_eval₂_eq_zero p a φ D' hD' hxQ)

@[simp] theorem BorelQRing.lift_of (z : UnivBasisRing p) :
    BorelQRing.lift p a φ D' hD' hxQ (AdjoinRoot.of _ z) = φ z := AdjoinRoot.lift_of _

@[simp] theorem BorelQRing.lift_borelQY : BorelQRing.lift p a φ D' hD' hxQ (borelQY p a) = D'.yQ :=
  AdjoinRoot.lift_root _

theorem borelQCurve_map_lift : (borelQCurve p a).map (BorelQRing.lift p a φ D' hD' hxQ) = (univCurveT p).map φ := by
  rw [borelQCurve, WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext (BorelQRing.lift_of p a φ D' hD' hxQ)

def BorelPRing.lift (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
    (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a)) :
    BorelPRing p a →+* T :=
  TorsionPointRing.lift (borelQCurve p a) p (BorelQRing.lift p a φ D' hD' hxQ) D'.xP D'.yP
    (by rw [borelQCurve_map_lift]; exact hD'.preΨ_P) (by rw [borelQCurve_map_lift]; exact hD'.equation_P)

@[simp] theorem BorelPRing.lift_ofUniv (z : UnivBasisRing p) :
    BorelPRing.lift p a φ D' hD' hxQ (BorelPRing.ofUniv p a z) = φ z := by
  rw [BorelPRing.ofUniv, RingHom.comp_apply, BorelPRing.lift, TorsionPointRing.lift_ofBase,
    BorelQRing.lift_of]

theorem BorelPRing.lift_comp_ofUniv : (BorelPRing.lift p a φ D' hD' hxQ).comp (BorelPRing.ofUniv p a) = φ :=
  RingHom.ext (BorelPRing.lift_ofUniv p a φ D' hD' hxQ)

@[simp] theorem BorelPRing.lift_xP : BorelPRing.lift p a φ D' hD' hxQ (BorelPRing.xP p a) = D'.xP :=
  TorsionPointRing.lift_torsionPtX _ p _ _ _ _ _

@[simp] theorem BorelPRing.lift_yP : BorelPRing.lift p a φ D' hD' hxQ (BorelPRing.yP p a) = D'.yP :=
  TorsionPointRing.lift_torsionPtY _ p _ _ _ _ _

@[simp] theorem BorelPRing.lift_xQ : BorelPRing.lift p a φ D' hD' hxQ (BorelPRing.xQ p a) = D'.xQ := by
  rw [BorelPRing.xQ, BorelPRing.lift_ofUniv, hxQ]

@[simp] theorem BorelPRing.lift_yQ : BorelPRing.lift p a φ D' hD' hxQ (BorelPRing.yQ p a) = D'.yQ := by
  rw [BorelPRing.yQ, BorelPRing.lift, TorsionPointRing.lift_ofBase, BorelQRing.lift_borelQY]

theorem borelPCurve_map_lift :
    (borelPCurve p a).map (BorelPRing.lift p a φ D' hD' hxQ) = (univCurveT p).map φ := by
  rw [borelPCurve_eq, WeierstrassCurve.map_map, BorelPRing.lift_comp_ofUniv]

theorem BorelPRing.lift_borelDenom : BorelPRing.lift p a φ D' hD' hxQ (borelDenom p a) =
    indepElt ((univCurveT p).map φ) p D'.xP D'.xQ * indepElt ((univCurveT p).map φ) p D'.xQ D'.xP := by
  rw [borelDenom, map_mul, ← indepElt_map, ← indepElt_map, borelPCurve_map_lift, BorelPRing.lift_xP,
    BorelPRing.lift_xQ]

def BorelRing.lift (φ : UnivBasisRing p →+* T) (D' : LevelPData T)
    (hD' : IsLevelPStructure ((univCurveT p).map φ) p D') (hxQ : D'.xQ = φ (borelX p a)) :
    BorelRing p a →+* T :=
  IsLocalization.Away.lift (borelDenom p a) (g := BorelPRing.lift p a φ D' hD' hxQ)
    (by rw [BorelPRing.lift_borelDenom]; exact hD'.isUnit_indepElt_PQ.mul hD'.isUnit_indepElt_QP)

@[simp] theorem BorelRing.lift_algebraMap (z : BorelPRing p a) :
    BorelRing.lift p a φ D' hD' hxQ (algebraMap (BorelPRing p a) (BorelRing p a) z) =
      BorelPRing.lift p a φ D' hD' hxQ z :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem BorelRing.lift_ofUniv (z : UnivBasisRing p) :
    BorelRing.lift p a φ D' hD' hxQ (BorelRing.ofUniv p a z) = φ z := by
  rw [BorelRing.ofUniv_eq_comp, RingHom.comp_apply, BorelRing.lift_algebraMap, BorelPRing.lift_ofUniv]

theorem BorelRing.lift_comp_ofUniv : (BorelRing.lift p a φ D' hD' hxQ).comp (BorelRing.ofUniv p a) = φ :=
  RingHom.ext (BorelRing.lift_ofUniv p a φ D' hD' hxQ)

theorem borelCurve_map_lift :
    (borelCurve p a).map (BorelRing.lift p a φ D' hD' hxQ) = (univCurveT p).map φ := by
  rw [borelCurve, WeierstrassCurve.map_map, BorelRing.lift_comp_ofUniv]

theorem borelData_map_lift :
    (borelData p a).map (BorelRing.lift p a φ D' hD' hxQ) = (univData p).map φ := by
  rw [borelData, LevelPData.map_map, BorelRing.lift_comp_ofUniv]

theorem borelData'_map_lift : (borelData' p a).map (BorelRing.lift p a φ D' hD' hxQ) = D' := by
  refine LevelPData.ext ?_ ?_ ?_ ?_
  · show BorelRing.lift p a φ D' hD' hxQ (algebraMap _ _ (BorelPRing.xP p a)) = D'.xP
    rw [BorelRing.lift_algebraMap, BorelPRing.lift_xP]
  · show BorelRing.lift p a φ D' hD' hxQ (algebraMap _ _ (BorelPRing.yP p a)) = D'.yP
    rw [BorelRing.lift_algebraMap, BorelPRing.lift_yP]
  · show BorelRing.lift p a φ D' hD' hxQ (algebraMap _ _ (BorelPRing.xQ p a)) = D'.xQ
    rw [BorelRing.lift_algebraMap, BorelPRing.lift_xQ]
  · show BorelRing.lift p a φ D' hD' hxQ (algebraMap _ _ (BorelPRing.yQ p a)) = D'.yQ
    rw [BorelRing.lift_algebraMap, BorelPRing.lift_yQ]

theorem BorelRing.ringHom_ext {S : Type w} [CommRing S] {f g : BorelRing p a →+* S}
    (h : f.comp (BorelRing.ofUniv p a) = g.comp (BorelRing.ofUniv p a))
    (hD : (borelData' p a).map f = (borelData' p a).map g) : f = g := by
  have h1 : f (algebraMap _ _ (BorelPRing.xP p a)) = g (algebraMap _ _ (BorelPRing.xP p a)) :=
    congrArg LevelPData.xP hD
  have h2 : f (algebraMap _ _ (BorelPRing.yP p a)) = g (algebraMap _ _ (BorelPRing.yP p a)) :=
    congrArg LevelPData.yP hD
  have h4 : f (algebraMap _ _ (BorelPRing.yQ p a)) = g (algebraMap _ _ (BorelPRing.yQ p a)) :=
    congrArg LevelPData.yQ hD
  refine IsLocalization.ringHom_ext (Submonoid.powers (borelDenom p a)) ?_
  have h' : (f.comp (algebraMap (BorelPRing p a) (BorelRing p a))).comp (BorelPRing.ofUniv p a) =
      (g.comp (algebraMap (BorelPRing p a) (BorelRing p a))).comp (BorelPRing.ofUniv p a) := by
    simpa only [RingHom.comp_assoc, ← BorelRing.ofUniv_eq_comp] using h
  refine TorsionPointRing.ringHom_ext _ p (adjoinRoot_ringHom_ext ?_ ?_) h1 h2
  · simpa only [RingHom.comp_assoc, BorelPRing.ofUniv] using h'
  · exact h4

end Borel

end LevelP

end ModularCurve

end


