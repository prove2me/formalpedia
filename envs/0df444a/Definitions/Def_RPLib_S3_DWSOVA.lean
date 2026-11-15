-- Prove2me | Definitions.Def_RPLib_S3_DWSOVA
-- name    : RPLib_S3_DWSOVA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:23:23.10649+00:00
-- url     : https://prove2.me/theorems/4a4858c8-cf93-41fa-8414-c39ac8f473ba
-- title:
--   Weight-two Ramanujan-Petersson library: generic coordinates and changes of variables under base change (O1, VC2 tools)
-- statement:
--   Generic coordinates and changes of variables under base change (O1, VC2 tools).
--
--   * **`gen_indep`** : `1, x, x², x³, y, xy` (`x = gx`, `y = gy`) are `L`-linearly independent in `L(E)`.
--   * `vc_bc` : `C • W⁄K = W'⁄K ⇒ C^σ • W⁄K' = W'⁄K'` for `σ : K →ₐ[F] K'`; `ui_map`.
--   * **`ptMap_map`** : the point map of a change of variables commutes with `Point.map σ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOM
import Definitions.Def_RPLib_S3_DWSTateW

/-!
# S3-DWS-Ordinary, part VA: generic coordinates and changes of variables under base change (O1, VC2 tools)

* **`gen_indep`** : `1, x, x², x³, y, xy` (`x = gx`, `y = gy`) are `L`-linearly independent in `L(E)`.
* `vc_bc` : `C • W⁄K = W'⁄K ⇒ C^σ • W⁄K' = W'⁄K'` for `σ : K →ₐ[F] K'`; `ui_map`.
* **`ptMap_map`** : the point map of a change of variables commutes with `Point.map σ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF
open scoped Polynomial.Bivariate

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Indep

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- **The generic coordinates are independent**: `1, x, x², x³, y, xy` are `L`-linearly independent in `L(E)`. -/
theorem gen_indep {A₀ A₁ A₂ A₃ B₀ B₁ : L}
    (h : algebraMap L (FF W L) A₀ + algebraMap L (FF W L) A₁ * gx W L +
      algebraMap L (FF W L) A₂ * gx W L ^ 2 + algebraMap L (FF W L) A₃ * gx W L ^ 3 +
      (algebraMap L (FF W L) B₀ + algebraMap L (FF W L) B₁ * gx W L) * gy W L = 0) :
    A₀ = 0 ∧ A₁ = 0 ∧ A₂ = 0 ∧ A₃ = 0 ∧ B₀ = 0 ∧ B₁ = 0 := by
  have e1 : ∀ a : L, algebraMap (CR W L) (FF W L) (CoordinateRing.mk (W.baseChange L).toAffine (C (C a))) =
      algebraMap L (FF W L) a := fun a => alg_mk_CC W L a
  have e2 : algebraMap (CR W L) (FF W L) (CoordinateRing.mk (W.baseChange L).toAffine (C X)) = gx W L := rfl
  have e3 : algebraMap (CR W L) (FF W L) (CoordinateRing.mk (W.baseChange L).toAffine Y) = gy W L := rfl
  have key : (C A₀ + C A₁ * X + C A₂ * X ^ 2 + C A₃ * X ^ 3 : L[X]) • (1 : CR W L) +
      (C B₀ + C B₁ * X : L[X]) • CoordinateRing.mk (W.baseChange L).toAffine Y = 0 := by
    apply IsFractionRing.injective (CR W L) (FF W L)
    rw [map_zero, CoordinateRing.smul, CoordinateRing.smul, mul_one]
    refine Eq.trans ?_ h
    simp only [map_add, map_mul, map_pow, e1, e2, e3]
  obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero key
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg (fun p : L[X] => p.coeff 0) hp
  · simpa using congrArg (fun p : L[X] => p.coeff 1) hp
  · simpa using congrArg (fun p : L[X] => p.coeff 2) hp
  · simpa using congrArg (fun p : L[X] => p.coeff 3) hp
  · simpa using congrArg (fun p : L[X] => p.coeff 0) hq
  · simpa using congrArg (fun p : L[X] => p.coeff 1) hq

end Indep

section Nat

variable {F : Type*} [Field F] {W W' : WeierstrassCurve F}
  {K K' : Type*} [Field K] [Field K'] [Algebra F K] [Algebra F K'] [DecidableEq K] [DecidableEq K']

lemma ui_map (φ : K →+* K') (C : VariableChange K) : ui (C.map φ) = φ (ui C) := by
  simp [ui, VariableChange.map, map_inv₀]

/-- A change of variables between base changes stays one after a further base change. -/
lemma vc_bc (σ : K →ₐ[F] K') {C : VariableChange K} (h : C • W.baseChange K = W'.baseChange K) :
    C.map (σ : K →+* K') • W.baseChange K' = W'.baseChange K' := by
  rw [← WeierstrassCurve.map_baseChange W σ, ← WeierstrassCurve.map_baseChange W' σ, map_variableChange, h]

/-- **Naturality**: `σ ∘ ptMap C = ptMap C^σ ∘ σ` on points. -/
lemma ptMap_map (σ : K →ₐ[F] K') {C : VariableChange K} (h : C • W.baseChange K = W'.baseChange K)
    (P : (W.baseChange K).toAffine.Point) :
    Point.map (W' := W'.toAffine) σ (RPLib.TateNF.ptMap C h P) =
      RPLib.TateNF.ptMap (C.map (σ : K →+* K')) (vc_bc σ h) (Point.map (W' := W.toAffine) σ P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · rw [RPLib.TateNF.ptMap_some, Point.map_some, Point.map_some, RPLib.TateNF.ptMap_some, Point.some.injEq]
    constructor
    · simp only [vcX, ui_map, map_mul, map_pow, map_sub]
      rfl
    · simp only [vcY, ui_map, map_mul, map_pow, map_sub]
      rfl

end Nat

end RamanujanPetersson.S3.DWSO


