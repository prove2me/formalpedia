-- Prove2me | Definitions.Def_ModularCurve_KatzLevelPUniversal
-- name    : ModularCurve_KatzLevelPUniversal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/cab6abe5-e9fa-5f31-a235-d69e666ec704
-- title:
--   Universal level-p structure: division-point rings and basis ring
-- statement:
--   For a Weierstrass cubic $W$ over a commutative ring $B$ and a natural number $p$, the module builds, by successive adjunctions of roots, a ring carrying a tautological $p$-division point. First `PsiRoot W p` is $B[x]/(\psi_p)$, where $\psi_p$ is Mathlib's $p$-th polynomial `W.preΨ p`, with distinguished element `psiRootX` the class of $x$; then `torsionQuadratic W p` is the monic quadratic $Y^2+(a_1x+a_3)Y-(x^3+a_2x^2+a_4x+a_6)$ over that ring, and `TorsionPointRing W p` is the quotient by it, so that over `torsionPtCurve W p` (the base change of $W$) the pair `(torsionPtX, torsionPtY)` satisfies the affine Weierstrass equation and $\psi_p$ vanishes at its abscissa. Iterating the same construction one step gives `TwoPointRing W p` with two such points $P=(x_P,y_P)$, $Q=(x_Q,y_Q)$, both satisfying the equation and $\psi_p(x_P)=\psi_p(x_Q)=0$. Inverting `indepDenom W p`, the product of $\iota_p(x_P,x_Q)$ and $\iota_p(x_Q,x_P)$ where $\iota_p(x_0,x)=\prod_{1\le a\le (p-1)/2}\bigl(x\,\Psi^{\mathrm{sq}}_a(x_0)-\Phi_a(x_0)\bigr)$, yields `BasisRing W p`; over it the two points form `basisData W p`, and `isLevelPStructure_basisData` verifies the six clauses of `IsLevelPStructure` (the two equations, the two vanishings of $\psi_p$, and invertibility of $\iota_p$ in both orders). Invertibility of $\Delta$ is preserved under this base change.
--
--   The universal instance takes `genericCurve` over $\mathbb{Z}[a_1,a_2,a_3,a_4,a_6]=$ `MvPolynomial (Fin 5) ℤ`, localises away from `pDelta p` $=p\,\Delta$ to get `UnivBase p`, so that both $p$ and $\Delta$ become units, and applies the preceding construction to obtain `UnivBasisRing p`, the curve `univCurveT p` and the level-$p$ structure `univData p`, with $\Delta$ and $p$ again units. Finally, for a Katz level-$p$ form $F$ of weight $k$ over $R$, `evalUniv` is the value of $F$ at the base change of this universal curve and datum along $\mathbb{Z}$-linear inclusion of `UnivBasisRing p` into $R\otimes_{\mathbb{Z}}$ `UnivBasisRing p`; it is additive, compatible with negation and subtraction, and multiplicative for the product of forms of weights $k$ and $l$.
--
--   **Relation to Mathlib.** The division polynomials `preΨ`, `ΨSq`, `Φ`, Weierstrass curves and their base change, `AdjoinRoot` and `Localization.Away` are Mathlib's; `LevelPData`, `IsLevelPStructure`, `indepElt` and `KatzLevelPForm` are the project's own notions, and the universal rings constructed here have no Mathlib counterpart.
--
--   **Where it is used.** The universal basis ring provides a single ring over which a curve with an invertible discriminant carries a tautological level-$p$ structure, so that a Katz level-$p$ form of any weight has a universal value `evalUniv`; this is the algebraic substitute for the universal object over the modular curve used when level structures at $p$ are introduced in the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_KatzLevelPUniversal.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

theorem preΨ_eval_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S')
    (W : WeierstrassCurve S) (n : ℤ) (x : S) :
    ((W.map f).preΨ n).eval (f x) = f ((W.preΨ n).eval x) := by
  rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem equation_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S')
    {W : WeierstrassCurve S} {x y : S} (h : W.toAffine.Equation x y) :
    (W.map f).toAffine.Equation (f x) (f y) :=
  h.map f

section TorsionPoint

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)

def PsiRoot : Type u := AdjoinRoot (W.preΨ p)

instance : CommRing (PsiRoot W p) := inferInstanceAs (CommRing (AdjoinRoot (W.preΨ p)))

instance : Algebra B (PsiRoot W p) := inferInstanceAs (Algebra B (AdjoinRoot (W.preΨ p)))

def PsiRoot.ofBase : B →+* PsiRoot W p := AdjoinRoot.of (W.preΨ p)

theorem PsiRoot.algebraMap_eq : algebraMap B (PsiRoot W p) = PsiRoot.ofBase W p :=
  AdjoinRoot.algebraMap_eq _

def psiRootX : PsiRoot W p := AdjoinRoot.root (W.preΨ p)

theorem preΨ_eval₂_psiRootX : (W.preΨ p).eval₂ (PsiRoot.ofBase W p) (psiRootX W p) = 0 :=
  AdjoinRoot.eval₂_root (W.preΨ p)

def torsionQuadratic : Polynomial (PsiRoot W p) :=
  X ^ 2 + C (PsiRoot.ofBase W p W.a₁ * psiRootX W p + PsiRoot.ofBase W p W.a₃) * X -
    C (psiRootX W p ^ 3 + PsiRoot.ofBase W p W.a₂ * psiRootX W p ^ 2 +
      PsiRoot.ofBase W p W.a₄ * psiRootX W p + PsiRoot.ofBase W p W.a₆)

def TorsionPointRing : Type u := AdjoinRoot (torsionQuadratic W p)

instance : CommRing (TorsionPointRing W p) :=
  inferInstanceAs (CommRing (AdjoinRoot (torsionQuadratic W p)))

instance : Algebra (PsiRoot W p) (TorsionPointRing W p) :=
  inferInstanceAs (Algebra (PsiRoot W p) (AdjoinRoot (torsionQuadratic W p)))

instance : Algebra B (TorsionPointRing W p) :=
  inferInstanceAs (Algebra B (AdjoinRoot (torsionQuadratic W p)))

instance : IsScalarTower B (PsiRoot W p) (TorsionPointRing W p) :=
  inferInstanceAs (IsScalarTower B (PsiRoot W p) (AdjoinRoot (torsionQuadratic W p)))

def TorsionPointRing.ofPsiRoot : PsiRoot W p →+* TorsionPointRing W p :=
  AdjoinRoot.of (torsionQuadratic W p)

def TorsionPointRing.ofBase : B →+* TorsionPointRing W p :=
  (TorsionPointRing.ofPsiRoot W p).comp (PsiRoot.ofBase W p)

theorem TorsionPointRing.algebraMap_psiRoot_eq :
    algebraMap (PsiRoot W p) (TorsionPointRing W p) = TorsionPointRing.ofPsiRoot W p :=
  AdjoinRoot.algebraMap_eq _

theorem TorsionPointRing.algebraMap_eq :
    algebraMap B (TorsionPointRing W p) = TorsionPointRing.ofBase W p := by
  rw [IsScalarTower.algebraMap_eq B (PsiRoot W p) (TorsionPointRing W p),
    TorsionPointRing.algebraMap_psiRoot_eq, PsiRoot.algebraMap_eq, TorsionPointRing.ofBase]

def torsionPtX : TorsionPointRing W p := TorsionPointRing.ofPsiRoot W p (psiRootX W p)

def torsionPtY : TorsionPointRing W p := AdjoinRoot.root (torsionQuadratic W p)

def torsionPtCurve : WeierstrassCurve (TorsionPointRing W p) :=
  W.map (TorsionPointRing.ofBase W p)

theorem torsionQuadratic_eval₂_torsionPtY :
    (torsionQuadratic W p).eval₂ (TorsionPointRing.ofPsiRoot W p) (torsionPtY W p) = 0 :=
  AdjoinRoot.eval₂_root (torsionQuadratic W p)

theorem equation_torsionPt :
    (torsionPtCurve W p).toAffine.Equation (torsionPtX W p) (torsionPtY W p) := by
  have h := torsionQuadratic_eval₂_torsionPtY W p
  rw [torsionQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_C,
    map_add, map_mul, map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow] at h
  rw [WeierstrassCurve.Affine.equation_iff, torsionPtCurve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, TorsionPointRing.ofBase, RingHom.comp_apply, RingHom.comp_apply,
    RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, torsionPtX]
  linear_combination h

theorem preΨ_torsionPt : ((torsionPtCurve W p).preΨ p).eval (torsionPtX W p) = 0 := by
  rw [torsionPtCurve, TorsionPointRing.ofBase, ← WeierstrassCurve.map_map, torsionPtX,
    preΨ_eval_map, WeierstrassCurve.map_preΨ, Polynomial.eval_map, preΨ_eval₂_psiRootX, map_zero]

end TorsionPoint

section TwoPoints

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)

abbrev TwoPointRing : Type u := TorsionPointRing (torsionPtCurve W p) p

abbrev TwoPointRing.ofOnePoint : TorsionPointRing W p →+* TwoPointRing W p :=
  TorsionPointRing.ofBase (torsionPtCurve W p) p

def TwoPointRing.ofBase : B →+* TwoPointRing W p :=
  (TwoPointRing.ofOnePoint W p).comp (TorsionPointRing.ofBase W p)

abbrev twoPointCurve : WeierstrassCurve (TwoPointRing W p) := torsionPtCurve (torsionPtCurve W p) p

def TwoPointRing.xP : TwoPointRing W p := TwoPointRing.ofOnePoint W p (torsionPtX W p)

def TwoPointRing.yP : TwoPointRing W p := TwoPointRing.ofOnePoint W p (torsionPtY W p)

def TwoPointRing.xQ : TwoPointRing W p := torsionPtX (torsionPtCurve W p) p

def TwoPointRing.yQ : TwoPointRing W p := torsionPtY (torsionPtCurve W p) p

instance : Algebra B (TwoPointRing W p) := (TwoPointRing.ofBase W p).toAlgebra

theorem TwoPointRing.algebraMap_eq : algebraMap B (TwoPointRing W p) = TwoPointRing.ofBase W p :=
  rfl

theorem TwoPointRing.algebraMap_onePoint_eq :
    algebraMap (TorsionPointRing W p) (TwoPointRing W p) = TwoPointRing.ofOnePoint W p :=
  TorsionPointRing.algebraMap_eq _ _

instance : IsScalarTower B (TorsionPointRing W p) (TwoPointRing W p) :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [TwoPointRing.algebraMap_onePoint_eq W p, TorsionPointRing.algebraMap_eq W p]; rfl)

theorem equation_P_twoPointRing :
    (twoPointCurve W p).toAffine.Equation (TwoPointRing.xP W p) (TwoPointRing.yP W p) :=
  equation_map _ (equation_torsionPt W p)

theorem equation_Q_twoPointRing :
    (twoPointCurve W p).toAffine.Equation (TwoPointRing.xQ W p) (TwoPointRing.yQ W p) :=
  equation_torsionPt (torsionPtCurve W p) p

theorem preΨ_P_twoPointRing : ((twoPointCurve W p).preΨ p).eval (TwoPointRing.xP W p) = 0 := by
  have h := congrArg (TwoPointRing.ofOnePoint W p) (preΨ_torsionPt W p)
  rw [map_zero, ← preΨ_eval_map] at h
  exact h

theorem preΨ_Q_twoPointRing : ((twoPointCurve W p).preΨ p).eval (TwoPointRing.xQ W p) = 0 :=
  preΨ_torsionPt (torsionPtCurve W p) p

def indepDenom : TwoPointRing W p :=
  indepElt (twoPointCurve W p) p (TwoPointRing.xP W p) (TwoPointRing.xQ W p) *
    indepElt (twoPointCurve W p) p (TwoPointRing.xQ W p) (TwoPointRing.xP W p)

def BasisRing : Type u := Localization.Away (indepDenom W p)

instance : CommRing (BasisRing W p) := inferInstanceAs (CommRing (Localization.Away (indepDenom W p)))

instance : Algebra (TwoPointRing W p) (BasisRing W p) :=
  inferInstanceAs (Algebra (TwoPointRing W p) (Localization.Away (indepDenom W p)))

instance : IsLocalization.Away (indepDenom W p) (BasisRing W p) :=
  inferInstanceAs (IsLocalization.Away (indepDenom W p) (Localization.Away (indepDenom W p)))

def BasisRing.ofTwoPoint : TwoPointRing W p →+* BasisRing W p :=
  algebraMap (TwoPointRing W p) (BasisRing W p)

def BasisRing.ofBase : B →+* BasisRing W p :=
  (BasisRing.ofTwoPoint W p).comp (TwoPointRing.ofBase W p)

instance : Algebra B (BasisRing W p) := (BasisRing.ofBase W p).toAlgebra

theorem BasisRing.algebraMap_eq : algebraMap B (BasisRing W p) = BasisRing.ofBase W p := rfl

theorem BasisRing.algebraMap_twoPoint_eq :
    algebraMap (TwoPointRing W p) (BasisRing W p) = BasisRing.ofTwoPoint W p := rfl

instance : IsScalarTower B (TwoPointRing W p) (BasisRing W p) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem isUnit_indepDenom : IsUnit (BasisRing.ofTwoPoint W p (indepDenom W p)) :=
  IsLocalization.Away.algebraMap_isUnit (S := BasisRing W p) (indepDenom W p)

def basisCurve : WeierstrassCurve (BasisRing W p) := W.map (BasisRing.ofBase W p)

theorem basisCurve_eq_map_twoPointCurve :
    basisCurve W p = (twoPointCurve W p).map (BasisRing.ofTwoPoint W p) := by
  ext <;> rfl

theorem isUnit_Δ_basisCurve (hW : IsUnit W.Δ) : IsUnit (basisCurve W p).Δ := by
  rw [basisCurve, WeierstrassCurve.map_Δ]
  exact hW.map _

def basisData : LevelPData (BasisRing W p) where
  xP := BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)
  yP := BasisRing.ofTwoPoint W p (TwoPointRing.yP W p)
  xQ := BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)
  yQ := BasisRing.ofTwoPoint W p (TwoPointRing.yQ W p)

theorem isLevelPStructure_basisData : IsLevelPStructure (basisCurve W p) p (basisData W p) := by
  rw [basisCurve_eq_map_twoPointCurve]
  exact
  { equation_P := equation_map _ (equation_P_twoPointRing W p)
    equation_Q := equation_map _ (equation_Q_twoPointRing W p)
    preΨ_P := by
      show (((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)).preΨ p).eval
        (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)) = 0
      rw [preΨ_eval_map, preΨ_P_twoPointRing, map_zero]
    preΨ_Q := by
      show (((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)).preΨ p).eval
        (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)) = 0
      rw [preΨ_eval_map, preΨ_Q_twoPointRing, map_zero]
    isUnit_indepElt_PQ := by
      show IsUnit (indepElt ((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)) p
        (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p))
        (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)))
      rw [indepElt_map]
      have h := isUnit_indepDenom W p
      rw [indepDenom, map_mul] at h
      exact isUnit_of_mul_isUnit_left h
    isUnit_indepElt_QP := by
      show IsUnit (indepElt ((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)) p
        (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p))
        (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)))
      rw [indepElt_map]
      have h := isUnit_indepDenom W p
      rw [indepDenom, map_mul] at h
      exact isUnit_of_mul_isUnit_right h }

end TwoPoints

def genericCurve : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

variable (p : ℕ)

def pDelta : MvPolynomial (Fin 5) ℤ := (p : MvPolynomial (Fin 5) ℤ) * genericCurve.Δ

def UnivBase : Type := Localization.Away (pDelta p)

instance : CommRing (UnivBase p) := inferInstanceAs (CommRing (Localization.Away (pDelta p)))

instance : Algebra (MvPolynomial (Fin 5) ℤ) (UnivBase p) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin 5) ℤ) (Localization.Away (pDelta p)))

instance : IsLocalization.Away (pDelta p) (UnivBase p) :=
  inferInstanceAs (IsLocalization.Away (pDelta p) (Localization.Away (pDelta p)))

def univCurve : WeierstrassCurve (UnivBase p) :=
  genericCurve.map (algebraMap (MvPolynomial (Fin 5) ℤ) (UnivBase p))

theorem isUnit_natCast_mul_Δ_univCurve : IsUnit ((p : UnivBase p) * (univCurve p).Δ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := UnivBase p) (pDelta p)
  rwa [pDelta, map_mul, map_natCast, univCurve, WeierstrassCurve.map_Δ] at *

theorem isUnit_Δ_univCurve : IsUnit (univCurve p).Δ :=
  isUnit_of_mul_isUnit_right (isUnit_natCast_mul_Δ_univCurve p)

theorem isUnit_natCast_univBase : IsUnit (p : UnivBase p) :=
  isUnit_of_mul_isUnit_left (isUnit_natCast_mul_Δ_univCurve p)

abbrev UnivOnePoint : Type := TorsionPointRing (univCurve p) p

abbrev UnivTwoPoint : Type := TwoPointRing (univCurve p) p

abbrev UnivBasisRing : Type := BasisRing (univCurve p) p

abbrev UnivBasisRing.ofBase : UnivBase p →+* UnivBasisRing p := BasisRing.ofBase (univCurve p) p

abbrev univCurveT : WeierstrassCurve (UnivBasisRing p) := basisCurve (univCurve p) p

abbrev univData : LevelPData (UnivBasisRing p) := basisData (univCurve p) p

theorem isLevelPStructure_univData : IsLevelPStructure (univCurveT p) p (univData p) :=
  isLevelPStructure_basisData (univCurve p) p

theorem isUnit_Δ_univCurveT : IsUnit (univCurveT p).Δ :=
  isUnit_Δ_basisCurve (univCurve p) p (isUnit_Δ_univCurve p)

theorem isUnit_natCast_univBasisRing : IsUnit (p : UnivBasisRing p) := by
  have h := (isUnit_natCast_univBase p).map (UnivBasisRing.ofBase p)
  rwa [map_natCast] at h

end LevelP

namespace KatzLevelPForm

open scoped TensorProduct

variable {R : Type u} [CommRing R] {p : ℕ} {k : ℤ}

def univInclude (R : Type u) [CommRing R] (p : ℕ) :
    LevelP.UnivBasisRing p →+* R ⊗[ℤ] LevelP.UnivBasisRing p :=
  (Algebra.TensorProduct.includeRight :
    LevelP.UnivBasisRing p →ₐ[ℤ] R ⊗[ℤ] LevelP.UnivBasisRing p).toRingHom

def univCurveOver (R : Type u) [CommRing R] (p : ℕ) :
    WeierstrassCurve (R ⊗[ℤ] LevelP.UnivBasisRing p) :=
  (LevelP.univCurveT p).map (univInclude R p)

theorem isUnit_Δ_univCurveOver (R : Type u) [CommRing R] (p : ℕ) :
    IsUnit (univCurveOver R p).Δ := by
  rw [univCurveOver, WeierstrassCurve.map_Δ]
  exact (LevelP.isUnit_Δ_univCurveT p).map _

def univDataOver (R : Type u) [CommRing R] (p : ℕ) :
    LevelPData (R ⊗[ℤ] LevelP.UnivBasisRing p) :=
  (LevelP.univData p).map (univInclude R p)

theorem isLevelPStructure_univDataOver (R : Type u) [CommRing R] (p : ℕ) :
    IsLevelPStructure (univCurveOver R p) p (univDataOver R p) :=
  (LevelP.isLevelPStructure_univData p).map _

def evalUniv (F : KatzLevelPForm R p k) : R ⊗[ℤ] LevelP.UnivBasisRing p :=
  F.toFun (univCurveOver R p) (isUnit_Δ_univCurveOver R p) (univDataOver R p)
    (isLevelPStructure_univDataOver R p)

@[simp] theorem evalUniv_zero : (0 : KatzLevelPForm R p k).evalUniv = 0 := rfl

@[simp] theorem evalUniv_add (F G : KatzLevelPForm R p k) :
    (F + G).evalUniv = F.evalUniv + G.evalUniv := rfl

@[simp] theorem evalUniv_neg (F : KatzLevelPForm R p k) : (-F).evalUniv = -F.evalUniv := rfl

@[simp] theorem evalUniv_sub (F G : KatzLevelPForm R p k) :
    (F - G).evalUniv = F.evalUniv - G.evalUniv := rfl

@[simp] theorem evalUniv_mul {l : ℤ} (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) :
    (F.mul G).evalUniv = F.evalUniv * G.evalUniv := rfl

end KatzLevelPForm

end ModularCurve

end


