-- Prove2me | Definitions.Def_OAI_Combinatorics_SphericalRamsey_BasisDerivation
-- name    : OAI_Combinatorics_SphericalRamsey_BasisDerivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:07:52.532265+00:00
-- url     : https://prove2.me/theorems/972d322c-ca72-4ecb-be3d-16b0d5300597
-- title:
--   Partial derivatives on the rational function field via dual numbers
-- statement:
--   Let $\iota$ be an index set, $\mathbb{Q}[X_\iota]$ the polynomial ring in variables $X_j$ ($j\in\iota$), and $\mathbb{Q}(X_\iota)$ its fraction field. Fix $i\in\iota$ and let $\mathbb{Q}(X_\iota)[\varepsilon]$, $\varepsilon^2=0$, be the dual numbers over the fraction field.
--
--   1. **Tangent at $i$.** The ring homomorphism $T_i:\mathbb{Q}[X_\iota]\to\mathbb{Q}(X_\iota)[\varepsilon]$ sends $X_j\mapsto X_j+[j=i]\varepsilon$, so its first component is the inclusion of polynomials.
--   2. **Extension to fractions.** Since $T_i$ maps nonzero polynomials to units, it extends uniquely to $\widehat T_i:\mathbb{Q}(X_\iota)\to\mathbb{Q}(X_\iota)[\varepsilon]$, again with first component the identity.
--   3. **Partial derivative.** The $\varepsilon$-coefficient
--   $$
--   \partial_i(x)=\text{coefficient of }\varepsilon\text{ in }\widehat T_i(x)
--   $$
--      is a derivation of $\mathbb{Q}(X_\iota)$ over $\mathbb{Z}$.
--
--   This realizes $\partial/\partial X_i$ on rational functions without manipulating quotients by hand. Transported along an algebraic independence, it becomes a derivation of a subfield of $\mathbb{R}$ with $\partial_i(b_i)=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/BasisDerivation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/BasisDerivation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GrahamSpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction

namespace OAI

noncomputable section

namespace GrahamSpherical

 abbrev Poly (ι : Type*) := MvPolynomial ι ℚ
 abbrev RatFun (ι : Type*) := FractionRing (Poly ι)

 def tangentCoefficient {ι : Type*} :
    ℚ →+* TrivSqZeroExt (RatFun ι) (RatFun ι) :=
  (TrivSqZeroExt.inlHom _ _).comp (algebraMap ℚ (RatFun ι))

 def tangentVariable {ι : Type*} (i j : ι) :
    TrivSqZeroExt (RatFun ι) (RatFun ι) := by
  classical
  exact (algebraMap (Poly ι) (RatFun ι) (MvPolynomial.X j),
    if j = i then 1 else 0)

 def polynomialTangent {ι : Type*} (i : ι) :
    Poly ι →+* TrivSqZeroExt (RatFun ι) (RatFun ι) :=
  MvPolynomial.eval₂Hom tangentCoefficient (tangentVariable i)

 theorem polynomialTangent_X {ι : Type*} (i j : ι) :
    polynomialTangent i (MvPolynomial.X j) = tangentVariable i j :=
  MvPolynomial.eval₂Hom_X' tangentCoefficient (tangentVariable i) j

 theorem polynomialTangent_fst {ι : Type*} (i : ι) (p : Poly ι) :
    (polynomialTangent i p).fst = algebraMap (Poly ι) (RatFun ι) p := by
  classical
  have h : (TrivSqZeroExt.fstHom (RatFun ι) (RatFun ι) (RatFun ι)).toRingHom.comp
      (polynomialTangent i) = algebraMap (Poly ι) (RatFun ι) := by
    ext j
    · simp [polynomialTangent, tangentCoefficient, IsScalarTower.algebraMap_eq ℚ (Poly ι) (RatFun ι)]
    · exact congrArg TrivSqZeroExt.fst (polynomialTangent_X i j)
  exact RingHom.congr_fun h p

 theorem polynomialTangent_units {ι : Type*} (i : ι)
    (y : nonZeroDivisors (Poly ι)) : IsUnit (polynomialTangent i y) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, polynomialTangent_fst]
  exact IsFractionRing.isUnit_map_of_injective (IsFractionRing.injective (Poly ι) (RatFun ι)) y

 def fractionTangent {ι : Type*} (i : ι) :
    RatFun ι →+* TrivSqZeroExt (RatFun ι) (RatFun ι) :=
  IsLocalization.lift (polynomialTangent_units i)

 theorem fractionTangent_fst {ι : Type*} (i : ι) (x : RatFun ι) :
    (fractionTangent i x).fst = x := by
  have h : (TrivSqZeroExt.fstHom (RatFun ι) (RatFun ι) (RatFun ι)).toRingHom.comp
      (fractionTangent i) = RingHom.id (RatFun ι) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Poly ι))
    apply RingHom.ext
    intro p
    change (fractionTangent i (algebraMap (Poly ι) (RatFun ι) p)).fst =
      algebraMap (Poly ι) (RatFun ι) p
    rw [fractionTangent, IsLocalization.lift_eq, polynomialTangent_fst]
  exact RingHom.congr_fun h x

 def fractionDerivation {ι : Type*} (i : ι) :
    Derivation ℤ (RatFun ι) (RatFun ι) where
  toFun x := (fractionTangent i x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (fractionTangent i) x y)
  map_smul' n x := by
    simp only [RingHom.id_apply, OreLocalization.zsmul_eq_zsmul]
    exact congrArg TrivSqZeroExt.snd (map_zsmul (fractionTangent i) n x)
  map_one_eq_zero' := congrArg TrivSqZeroExt.snd (map_one (fractionTangent i))
  leibniz' x y := by
    change (fractionTangent i (x * y)).snd =
      x * (fractionTangent i y).snd + y * (fractionTangent i x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, fractionTangent_fst, fractionTangent_fst]
    change x * (fractionTangent i y).snd + (fractionTangent i x).snd * y =
      x * (fractionTangent i y).snd + y * (fractionTangent i x).snd
    rw [mul_comm (fractionTangent i x).snd y]

end GrahamSpherical

end

end OAI


