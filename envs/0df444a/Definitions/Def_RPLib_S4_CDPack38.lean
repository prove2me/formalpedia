-- Prove2me | Definitions.Def_RPLib_S4_CDPack38
-- name    : RPLib_S4_CDPack38
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:30:16.104603+00:00
-- url     : https://prove2.me/theorems/1bce4434-7e36-4bc8-a2ce-d36b232ea84c
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 38 of 71
-- statement:
--   Part 38 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_Syn`: The Jacobian (unit S4-JacComplete), part `Syn` (dictionary D2: the chart coordinate `1/(x - c)`)
--   * `Def_RP_JacComplete_RfinSyn`: The Jacobian (unit S4-JacComplete), part `RfinSyn`: chart rings are finite rings of the chart synonyms
--   * `Def_RP_JacDivisors_L`: S4-JacDivisors L (O13: pull-back of Weil divisors along dominant morphisms)
--   * `Def_RP_JacDivisors_M`: S4-JacDivisors M (O14, step E1: rational maps into proper targets are defined in codimension one)
--   * `Def_RP_JacDivisors_O`: S4-JacDivisors O (O14, steps E1' and E4-E5: where a rational map is undefined, a codimension-one divisor is)
--   * `Def_RP_ThetaSquare_CPull`: S4-ThetaSquare, file CPull: pulling Weil divisors back along non-dominant morphisms (T4a)
--   * `Def_RP_ThetaCube_Det`: S4-ThetaCube, file Det (D-B2, part 1): determinants of pulled-back rational functions
--   * `Def_RP_JacDivisors_N`: S4-JacDivisors N (O14, steps E6-E7: a prime divisor through `Δ x` meets any morphism in codimension one)
--   * `Def_RP_JacDivisors_P`: S4-JacDivisors P (O14, steps E2 and E8: the difference map `Φ(v, w) = φ(v) φ(w)⁻¹` is defined on the diagonal)
--   * `Def_RP_ThetaCube_Alg`: Unit S4-ThetaCube, file Alg: pure algebra for numerical classes (obligation T6, algebra part)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack17
import Definitions.Def_RPLib_S4_CDPack37

/-!
# Curve-duality library package, part 38 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_Syn`: The Jacobian (unit S4-JacComplete), part `Syn` (dictionary D2: the chart coordinate `1/(x - c)`)
* `Def_RP_JacComplete_RfinSyn`: The Jacobian (unit S4-JacComplete), part `RfinSyn`: chart rings are finite rings of the chart synonyms
* `Def_RP_JacDivisors_L`: S4-JacDivisors L (O13: pull-back of Weil divisors along dominant morphisms)
* `Def_RP_JacDivisors_M`: S4-JacDivisors M (O14, step E1: rational maps into proper targets are defined in codimension one)
* `Def_RP_JacDivisors_O`: S4-JacDivisors O (O14, steps E1' and E4-E5: where a rational map is undefined, a codimension-one divisor is)
* `Def_RP_ThetaSquare_CPull`: S4-ThetaSquare, file CPull: pulling Weil divisors back along non-dominant morphisms (T4a)
* `Def_RP_ThetaCube_Det`: S4-ThetaCube, file Det (D-B2, part 1): determinants of pulled-back rational functions
* `Def_RP_JacDivisors_N`: S4-JacDivisors N (O14, steps E6-E7: a prime divisor through `Δ x` meets any morphism in codimension one)
* `Def_RP_JacDivisors_P`: S4-JacDivisors P (O14, steps E2 and E8: the difference map `Φ(v, w) = φ(v) φ(w)⁻¹` is defined on the diagonal)
* `Def_RP_ThetaCube_Alg`: Unit S4-ThetaCube, file Alg: pure algebra for numerical classes (obligation T6, algebra part)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_Syn =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Syn` (dictionary D2: the chart coordinate `1/(x - c)`)

* `mobU K c = 1/(X - c)` and the Möbius automorphism `tau K c : K(X) →ₐ[K] K(X)`, `X ↦ 1/(X - c)`
  (`tau_algebraMap`, `tau_X`, `tau_surjective`, `tauEquiv`);
* `SynF K F c`: a type synonym of `F` carrying the function-field package whose coordinate is
  `x' = 1/(x - c)` (`synAlg_apply`, `synAlg_X`), with `FunctionField` and separability transported;
* `synEquiv K F c : F ≃ₐ[K] SynF K F c` and the induced bijection of places `synPlace` preserving `ord`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place)

section Mob

variable (K : Type*) [Field K]

/-- The Möbius coordinate `1/(X - c)` of `K(X)`. -/
noncomputable def mobU (c : K) : RatFunc K := JacSym.uc (RatFunc.X : RatFunc K) c

theorem transcendental_mobU (c : K) : Transcendental K (mobU K c) :=
  JacSym.transcendental_uc RatFunc.transcendental_X c

theorem le_comap_mobU (c : K) :
    nonZeroDivisors K[X] ≤ (nonZeroDivisors (RatFunc K)).comap (aeval (mobU K c) : K[X] →ₐ[K] RatFunc K) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.1 (transcendental_mobU K c))

/-- The `K`-algebra endomorphism `X ↦ 1/(X - c)` of `K(X)`. -/
noncomputable def tau (c : K) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (aeval (mobU K c)) (le_comap_mobU K c)

theorem tau_algebraMap (c : K) (p : K[X]) :
    tau K c (algebraMap K[X] (RatFunc K) p) = aeval (mobU K c) p := by
  have h := RatFunc.liftAlgHom_apply_div (aeval (mobU K c)) (le_comap_mobU K c) p 1
  simp only [map_one, div_one] at h
  exact h

theorem tau_X (c : K) : tau K c RatFunc.X = mobU K c := by
  rw [← RatFunc.algebraMap_X, tau_algebraMap, aeval_X]

theorem tau_X_inv (c : K) :
    tau K c ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) = RatFunc.X := by
  rw [map_add, map_inv₀, tau_X, AlgHom.commutes, mobU, JacSym.uc, inv_inv, sub_add_cancel]

theorem algebraMap_eq_aeval_X (p : K[X]) :
    algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
  rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]

theorem tau_surjective (c : K) : Function.Surjective (tau K c) := by
  intro f
  have hp : ∀ p : K[X], algebraMap K[X] (RatFunc K) p =
      tau K c (aeval ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) p) := fun p => by
    rw [← Polynomial.aeval_algHom_apply (tau K c), tau_X_inv, algebraMap_eq_aeval_X]
  refine ⟨aeval ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) f.num /
    aeval ((RatFunc.X : RatFunc K)⁻¹ + algebraMap K (RatFunc K) c) f.denom, ?_⟩
  rw [map_div₀, ← hp, ← hp, RatFunc.num_div_denom]

/-- `tau K c` as an automorphism. -/
noncomputable def tauEquiv (c : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  AlgEquiv.ofBijective (tau K c) ⟨(tau K c).toRingHom.injective, tau_surjective K c⟩

theorem tau_tauEquiv_symm (c : K) (r : RatFunc K) : tau K c ((tauEquiv K c).symm r) = r :=
  (tauEquiv K c).apply_symm_apply r

end Mob

section Syn

variable (K : Type*) [Field K] (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F]
  [Algebra (RatFunc K) F] [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] (c : K)

/-- The function field `F` with the coordinate `1/(x - c)` (a type synonym of `F`). -/
def SynF (K : Type*) [Field K] (F : Type*) (_c : K) : Type _ := F

noncomputable instance : Field (SynF K F c) := inferInstanceAs (Field F)

noncomputable instance : Algebra K (SynF K F c) := inferInstanceAs (Algebra K F)

/-- The new structure map `K(X) → F`, `X ↦ 1/(x - c)`. -/
noncomputable def synMap : RatFunc K →+* SynF K F c :=
  (algebraMap (RatFunc K) F).comp (tau K c).toRingHom

noncomputable instance : Algebra (RatFunc K) (SynF K F c) := (synMap K F c).toAlgebra

noncomputable instance : Algebra K[X] (SynF K F c) :=
  ((algebraMap (RatFunc K) (SynF K F c)).comp (algebraMap K[X] (RatFunc K))).toAlgebra

instance : IsScalarTower K[X] (RatFunc K) (SynF K F c) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The identification `F ≃ SynF K F c` (the identity map). -/
def synEquiv : F ≃ₐ[K] SynF K F c where
  toFun y := y
  invFun y := y
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem ratAlg_const (a : K) :
    algebraMap (RatFunc K) F (algebraMap K (RatFunc K) a) = algebraMap K F a := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F,
    ← IsScalarTower.algebraMap_apply K K[X] F]

theorem ratAlg_X : algebraMap (RatFunc K) F RatFunc.X = algebraMap K[X] F X := by
  rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply]

instance : IsScalarTower K K[X] (SynF K F c) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap K F a = algebraMap (RatFunc K) F (tau K c (algebraMap K[X] (RatFunc K) (algebraMap K K[X] a)))
    have h1 : tau K c (algebraMap K[X] (RatFunc K) (algebraMap K K[X] a)) =
        algebraMap K[X] (RatFunc K) (algebraMap K K[X] a) := by
      rw [← IsScalarTower.algebraMap_apply K K[X] (RatFunc K), AlgHom.commutes]
    rw [h1, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F, ← IsScalarTower.algebraMap_apply K K[X] F])

theorem ratAlg_mobU :
    algebraMap (RatFunc K) F (mobU K c) = JacSym.uc (algebraMap K[X] F X) c := by
  simp only [mobU, JacSym.uc, map_inv₀, map_sub, ratAlg_const, ratAlg_X]

/-- The new structure map on polynomials: `p ↦ p(1/(x - c))`. -/
theorem synAlg_apply (p : K[X]) :
    algebraMap K[X] (SynF K F c) p = synEquiv K F c (aeval (JacSym.uc (algebraMap K[X] F X) c) p) := by
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq (fun a => (ratAlg_const K F a).symm)
  show algebraMap (RatFunc K) F (tau K c (algebraMap K[X] (RatFunc K) p)) =
    aeval (JacSym.uc (algebraMap K[X] F X) c) p
  rw [tau_algebraMap, ← Polynomial.aeval_algebraMap_apply, ratAlg_mobU]

/-- The new coordinate is `x' = 1/(x - c)`. -/
theorem synAlg_X :
    algebraMap K[X] (SynF K F c) X = synEquiv K F c (JacSym.uc (algebraMap K[X] F X) c) := by
  rw [synAlg_apply, aeval_X]

instance [FunctionField K F] : FunctionField K (SynF K F c) := by
  have h1 : (algebraMap (RatFunc K) F).Finite := RingHom.finite_algebraMap.2 inferInstance
  have h2 : ((tau K c).toRingHom : RatFunc K →+* RatFunc K).Finite :=
    RingHom.Finite.of_surjective _ (tau_surjective K c)
  have h : (synMap K F c).Finite := h1.comp h2
  exact RingHom.finite_algebraMap.1 h

instance [Algebra.IsSeparable (RatFunc K) F] : Algebra.IsSeparable (RatFunc K) (SynF K F c) :=
  Algebra.IsSeparable.of_equiv_equiv (tauEquiv K c).symm.toRingEquiv (synEquiv K F c).toRingEquiv
    (RingHom.ext fun r => by
      show algebraMap (RatFunc K) F (tau K c ((tauEquiv K c).symm r)) = algebraMap (RatFunc K) F r
      rw [tau_tauEquiv_symm])

end Syn

section SynPlace

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The places of `F` and of the chart synonym `SynF K F c` agree. -/
noncomputable def synPlace (c : K) : Place K F ≃ Place K (SynF K F c) := placeEquiv (synEquiv K F c)

theorem ord_synPlace (c : K) (P : Place K F) (f : F) :
    (synPlace c P).ord (synEquiv K F c f) = P.ord f :=
  ord_placeEquiv _ P f

end SynPlace

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_RfinSyn =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `RfinSyn`: chart rings are finite rings of the chart synonyms

For `x = algebraMap K[X] F X` and `c : K`, the chart ring `chartRing x {c}` (the integral closure of `K[1/(x - c)]`)
is the ring of `x'`-integers of the synonym `SynF K F c` (coordinate `x' = 1/(x - c)`), as subsets of `F`:
* `ucPoly c : K[X] →ₐ[K] K[1/(x - c)]` (surjective), `synAlg_eq` (the structure map of `SynF` factors through it);
* **`mem_rfinSyn_iff`**, `chartRing_map_synEquiv`, `rfinSynEquiv : chartRing x {c} ≃ₐ[K] (x'-integers)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

section RfinSyn

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F]
  [Algebra (RatFunc K) F] [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] (c : K)

/-- `K[X] → K[1/(x - c)]`, `X ↦ 1/(x - c)`. -/
noncomputable def ucPoly : K[X] →ₐ[K] JacSym.polyA (algebraMap K[X] F X) {c} :=
  aeval (⟨JacSym.uc (algebraMap K[X] F X) c, JacSym.uc_mem_polyA _ (Finset.mem_singleton_self c)⟩ :
    JacSym.polyA (algebraMap K[X] F X) {c})

theorem ucPoly_coe (p : K[X]) :
    ((ucPoly (F := F) c p : JacSym.polyA (algebraMap K[X] F X) {c}) : F) =
      aeval (JacSym.uc (algebraMap K[X] F X) c) p :=
  (Polynomial.aeval_algHom_apply (JacSym.polyA (algebraMap K[X] F X) {c}).val _ p).symm

theorem ucPoly_surjective : Function.Surjective (ucPoly (F := F) c) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ Algebra.adjoin K {JacSym.uc (algebraMap K[X] F X) c} := by
    simpa [JacSym.polyA, Finset.coe_singleton, Set.image_singleton] using hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨p, rfl⟩ := hy'
  exact ⟨p, Subtype.ext (ucPoly_coe c p)⟩

/-- The structure map of `SynF K F c` is `K[X] → K[1/(x - c)] ⊆ F`. -/
theorem synAlg_eq :
    (algebraMap K[X] (SynF K F c) : K[X] →+* F) =
      (algebraMap (JacSym.polyA (algebraMap K[X] F X) {c}) F).comp (ucPoly (F := F) c).toRingHom :=
  RingHom.ext fun p => by
    show algebraMap K[X] (SynF K F c) p = ((ucPoly (F := F) c p : JacSym.polyA (algebraMap K[X] F X) {c}) : F)
    rw [synAlg_apply, ucPoly_coe]
    rfl

/-- **The chart ring `B_{c}` is the ring of `x'`-integers of `SynF K F c`.** -/
theorem mem_rfinSyn_iff (y : F) :
    synEquiv K F c y ∈ integralClosure K[X] (SynF K F c) ↔ y ∈ JacSym.chartRing (algebraMap K[X] F X) {c} := by
  rw [mem_integralClosure_iff, JacSym.mem_chartRing]
  constructor
  · intro h
    exact h.map_of_comp_eq (ucPoly (F := F) c).toRingHom (synEquiv K F c).symm.toRingEquiv.toRingHom
      (by rw [← synAlg_eq]; rfl)
  · rintro ⟨p, hp, hpy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (f := (ucPoly (F := F) c).toRingHom) (ucPoly_surjective c) p) hp
    refine ⟨q, hqm, ?_⟩
    show eval₂ (algebraMap K[X] (SynF K F c) : K[X] →+* F) y q = 0
    refine (congrArg (fun φ : K[X] →+* F => eval₂ φ y q) (synAlg_eq (F := F) c)).trans ?_
    show eval₂ ((algebraMap (JacSym.polyA (algebraMap K[X] F X) {c}) F).comp (ucPoly (F := F) c).toRingHom) y q = 0
    rw [← eval₂_map, hq, hpy]

theorem chartRing_map_synEquiv :
    (JacSym.chartRing (algebraMap K[X] F X) {c}).map (synEquiv K F c).toAlgHom =
      (integralClosure K[X] (SynF K F c)).restrictScalars K := by
  ext z
  rw [Subalgebra.mem_restrictScalars, Subalgebra.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_rfinSyn_iff c y).2 hy
  · intro hz
    exact ⟨(synEquiv K F c).symm z, (mem_rfinSyn_iff c _).1 (by simpa using hz), by simp⟩

/-- `B_{c} ≃ₐ[K]` the `x'`-integers of the chart synonym. -/
noncomputable def rfinSynEquiv : JacSym.chartRing (algebraMap K[X] F X) {c} ≃ₐ[K]
    (integralClosure K[X] (SynF K F c)).restrictScalars K :=
  ((synEquiv K F c).subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (chartRing_map_synEquiv c))

theorem rfinSynEquiv_coe (y : JacSym.chartRing (algebraMap K[X] F X) {c}) :
    ((rfinSynEquiv c y : (integralClosure K[X] (SynF K F c)).restrictScalars K) : SynF K F c) =
      synEquiv K F c y := rfl

end RfinSyn

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacDivisors_L =====
section

/-!
# S4-JacDivisors L (O13: pull-back of Weil divisors along dominant morphisms)
For a dominant morphism `φ : X ⟶ Y` of integral locally Noetherian schemes with `Y` locally factorial,
a Weil divisor `D` on `Y` is locally `div f` (file K); `φ^* D` is locally `div (φ^* f)`.
* `ffMap_algebraMap`: `φ^*` on `K(Y)` restricts to the stalk maps.
* `exists_isUnit_of_ord_eq_zero`: `div g = 0` near a factorial point makes `g` a unit of the stalk.
* `pullback φ D`, `pullback_eq_div_of`, `pullback_div`, `pullback_add`, `pullback_neg`, `pullback_sub`,
  `pullback_mem_weilDivisors`, `pullback_linEquiv`, `pullback_id`, `pullback_comp` (translates are the case of
  automorphisms).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing RamanujanPetersson.IsogDegA

universe u

section
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : X ⟶ Y) [IsDominant φ]

/-- The pull-back of rational functions restricts to the stalk maps. -/
lemma ffMap_algebraMap (x : X) (a : Y.presheaf.stalk (φ x)) :
    (ffMap φ).hom (algebraMap _ Y.functionField a) =
      algebraMap _ X.functionField (φ.stalkMap x a) := by
  have h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have key : Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial :
      genericPoint Y ⤳ φ x) ≫ ffMap φ = φ.stalkMap x ≫ X.presheaf.stalkSpecializes h := by
    rw [← Scheme.Hom.stalkSpecializes_stalkMap, ffMap, TopCat.Presheaf.stalkSpecializes_comp_assoc]
  exact congrArg (fun g => g.hom a) key

lemma ffMap_ne_zero {f : Y.functionField} (hf : f ≠ 0) : (ffMap φ).hom f ≠ 0 :=
  (map_ne_zero_iff _ (ffMap φ).hom.injective).mpr hf

end

section
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

lemma ord_algebraMap_isUnit (x : X) {u : X.presheaf.stalk x} (hu : IsUnit u) :
    Scheme.ord (algebraMap _ X.functionField u) x = 0 := by
  by_cases hx : coheight x = 1
  · have := ord_algebraMap_stalk hx (b := u) hu.ne_zero (n := 0) (by rw [Ring.ord_of_isUnit hu]; rfl)
    simpa using this
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- A rational function without zeros or poles near a factorial point is a unit of the stalk. -/
lemma exists_isUnit_of_ord_eq_zero (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {g : X.functionField} (hg : g ≠ 0) (h : ∀ z : X, z ⤳ x → coheight z = 1 → Scheme.ord g z = 0) :
    ∃ u : X.presheaf.stalk x, IsUnit u ∧ algebraMap _ X.functionField u = g := by
  obtain ⟨a, ha⟩ := mem_range_algebraMap_stalk_of_ord_nonneg x g fun z hz h1 => (h z hz h1).ge
  obtain ⟨b, hb⟩ := mem_range_algebraMap_stalk_of_ord_nonneg x g⁻¹ fun z hz h1 => by
    rw [ord_inv' hg, h z hz h1]; rfl
  refine ⟨a, IsUnit.of_mul_eq_one b ?_, ha⟩
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hg]

lemma ord_eq_of_div_eq {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) {z : X}
    (h : div X f z = div X g z) : Scheme.ord (f / g) z = 0 := by
  have e := Scheme.ord_mul (x := z) hg (div_ne_zero hf hg)
  rw [show g * (f / g) = f by field_simp] at e
  rw [div_apply, div_apply] at h
  omega

end

section
variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  [IsLocallyNoetherian Y] (φ : X ⟶ Y) [IsDominant φ]

/-- Two local equations of the same divisor at `φ x` have pull-backs of the same order at `x`. -/
lemma ord_ffMap_eq (x : X) [UniqueFactorizationMonoid (Y.presheaf.stalk (φ x))]
    {f g : Y.functionField} (hf : f ≠ 0) (hg : g ≠ 0) {V : Set Y} (hV : IsOpen V) (hx : φ x ∈ V)
    (hfg : ∀ w ∈ V, div Y f w = div Y g w) :
    Scheme.ord ((ffMap φ).hom f) x = Scheme.ord ((ffMap φ).hom g) x := by
  obtain ⟨u, hu, hug⟩ := exists_isUnit_of_ord_eq_zero (φ x) (div_ne_zero hf hg)
    fun z hz _ => ord_eq_of_div_eq hf hg (hfg z (hz.mem_open hV hx))
  have e : (ffMap φ).hom f = (ffMap φ).hom g * algebraMap _ X.functionField (φ.stalkMap x u) := by
    rw [← ffMap_algebraMap, hug, ← map_mul, show g * (f / g) = f by field_simp]
  rw [e, Scheme.ord_mul (ffMap_ne_zero φ hg), ord_algebraMap_isUnit x (hu.map _), add_zero]
  rw [← ffMap_algebraMap, hug]
  exact ffMap_ne_zero φ (div_ne_zero hf hg)

end

section
variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- `f` is a local equation of `D` at `y`. -/
def IsLocEq (D : AlgebraicCycle Y ℤ) (y : Y) (f : Y.functionField) : Prop :=
  f ≠ 0 ∧ ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∀ w ∈ V, D w = div Y f w

open Classical in
/-- A chosen local equation (junk `1` when there is none). -/
noncomputable def locEq (D : AlgebraicCycle Y ℤ) (y : Y) : Y.functionField :=
  if h : ∃ f, IsLocEq D y f then h.choose else 1

lemma isLocEq_locEq {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (y : Y)
    [UniqueFactorizationMonoid (Y.presheaf.stalk y)] : IsLocEq D y (locEq D y) := by
  have h : ∃ f, IsLocEq D y f := by
    obtain ⟨f, hf, V, hV⟩ := exists_locally_principal hD y
    exact ⟨f, hf, V, hV⟩
  rw [locEq, dif_pos h]
  exact h.choose_spec

end

section
variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  [IsLocallyNoetherian Y] (φ : X ⟶ Y) [IsDominant φ]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

lemma ord_ffMap_locEq {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) {f : Y.functionField}
    (hf : f ≠ 0) {V : Set Y} (hV : IsOpen V) (hDV : ∀ w ∈ V, D w = div Y f w) {x : X} (hx : φ x ∈ V) :
    Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x = Scheme.ord ((ffMap φ).hom f) x := by
  obtain ⟨hg, V', hV', hxV', hDV'⟩ := isLocEq_locEq hD (φ x)
  exact ord_ffMap_eq φ x hg hf (hV'.inter hV) ⟨hxV', hx⟩
    fun w hw => (hDV' w hw.1).symm.trans (hDV w hw.2)

lemma locallyFinite_pullback {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (x₀ : X) :
    ∃ t ∈ 𝓝 x₀, (t ∩ Function.support
      (fun x => Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x)).Finite := by
  obtain ⟨hf, V, hV, hx₀, hDV⟩ := isLocEq_locEq hD (φ x₀)
  obtain ⟨t, ht, hfin⟩ := locallyFinite_ord ((ffMap φ).hom (locEq D (φ x₀))) x₀
  refine ⟨t ∩ φ ⁻¹' V, Filter.inter_mem ht ((hV.preimage φ.continuous).mem_nhds hx₀),
    hfin.subset ?_⟩
  rintro x ⟨⟨hxt, hxV⟩, hx⟩
  refine ⟨hxt, ?_⟩
  rw [Function.mem_support, ord_ffMap_locEq φ hD hf hV hDV hxV] at hx
  exact hx

open Classical in
/-- The pull-back `φ^* D` of a Weil divisor (junk `0` for cycles that are not Weil divisors). -/
noncomputable def pullback (D : AlgebraicCycle Y ℤ) : AlgebraicCycle X ℤ :=
  if hD : D ∈ weilDivisors Y then
    { toFun := fun x => Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun x _ => locallyFinite_pullback φ hD x }
  else 0

lemma pullback_apply {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (x : X) :
    pullback φ D x = Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x := by
  rw [pullback, dif_pos hD]
  rfl

/-- Pull-back through any local equation. -/
lemma pullback_eq_div_of {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) {f : Y.functionField}
    (hf : f ≠ 0) {V : Set Y} (hV : IsOpen V) (hDV : ∀ w ∈ V, D w = div Y f w) {x : X} (hx : φ x ∈ V) :
    pullback φ D x = div X ((ffMap φ).hom f) x := by
  rw [pullback_apply φ hD, div_apply, ord_ffMap_locEq φ hD hf hV hDV hx]

lemma pullback_div {f : Y.functionField} (hf : f ≠ 0) :
    pullback φ (div Y f) = div X ((ffMap φ).hom f) := by
  ext x
  exact pullback_eq_div_of φ (div_mem_weilDivisors f) hf isOpen_univ (fun _ _ => rfl) trivial

lemma pullback_mem_weilDivisors (D : AlgebraicCycle Y ℤ) : pullback φ D ∈ weilDivisors X := by
  by_cases hD : D ∈ weilDivisors Y
  · intro x hx
    rw [pullback_apply φ hD] at hx
    by_contra h
    exact hx (Scheme.ord_eq_zero_of_coheight_neq_one h _)
  · rw [pullback, dif_neg hD]
    exact (weilDivisors X).zero_mem

lemma pullback_add {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y) :
    pullback φ (D + E) = pullback φ D + pullback φ E := by
  ext x
  obtain ⟨hf, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (φ x)
  obtain ⟨hg, V', hV', hxV', hEV'⟩ := isLocEq_locEq hE (φ x)
  have hDE : ∀ w ∈ V ∩ V', (D + E) w = div Y (locEq D (φ x) * locEq E (φ x)) w := by
    intro w hw
    rw [div_mul hf hg, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hDV w hw.1, hEV' w hw.2]
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    pullback_eq_div_of φ ((weilDivisors Y).add_mem hD hE) (mul_ne_zero hf hg) (hV.inter hV') hDE
      ⟨hxV, hxV'⟩, pullback_eq_div_of φ hD hf hV hDV hxV, pullback_eq_div_of φ hE hg hV' hEV' hxV',
    map_mul, div_mul (ffMap_ne_zero φ hf) (ffMap_ne_zero φ hg),
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply]

lemma pullback_zero : pullback φ (0 : AlgebraicCycle Y ℤ) = 0 := by
  have h := pullback_add φ (weilDivisors Y).zero_mem (weilDivisors Y).zero_mem
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

lemma pullback_neg {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) :
    pullback φ (-D) = -pullback φ D := by
  have h := pullback_add φ hD ((weilDivisors Y).neg_mem hD)
  rw [add_neg_cancel, pullback_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma pullback_sub {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y) :
    pullback φ (D - E) = pullback φ D - pullback φ E := by
  rw [sub_eq_add_neg, pullback_add φ hD ((weilDivisors Y).neg_mem hE), pullback_neg φ hE,
    sub_eq_add_neg]

/-- Pull-back preserves linear equivalence of Weil divisors. -/
lemma pullback_linEquiv {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y)
    (h : LinEquiv Y D E) : LinEquiv X (pullback φ D) (pullback φ E) := by
  obtain ⟨f, hf, rfl⟩ := linEquiv_iff.mp h
  refine linEquiv_iff.mpr ⟨(ffMap φ).hom f, ffMap_ne_zero φ hf, ?_⟩
  rw [pullback_add φ hE (div_mem_weilDivisors f), pullback_div φ hf]

end

section
variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsIntegral Z] [IsLocallyNoetherian Z]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
  [∀ z : Z, UniqueFactorizationMonoid (Z.presheaf.stalk z)]

lemma pullback_id {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) : pullback (𝟙 Y) D = D := by
  ext y
  obtain ⟨hf, V, hV, hyV, hDV⟩ := isLocEq_locEq hD y
  rw [pullback_eq_div_of (𝟙 Y) hD hf hV hDV hyV, ffMap_id, hDV y hyV]
  rfl

lemma pullback_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z) [IsDominant φ] [IsDominant ψ] {D : AlgebraicCycle Z ℤ}
    (hD : D ∈ weilDivisors Z) : pullback (φ ≫ ψ) D = pullback φ (pullback ψ D) := by
  ext x
  obtain ⟨hf, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (ψ (φ x))
  have hV' : IsOpen (ψ ⁻¹' V) := hV.preimage ψ.continuous
  rw [pullback_eq_div_of (φ ≫ ψ) hD hf hV hDV (by simpa using hxV),
    pullback_eq_div_of φ (pullback_mem_weilDivisors ψ D) (ffMap_ne_zero ψ hf) hV'
      (fun w hw => pullback_eq_div_of ψ hD hf hV hDV hw) hxV, ffMap_comp]
  rfl

end

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_JacDivisors_M =====
section

/-!
# S4-JacDivisors M (O14, step E1: rational maps into proper targets are defined in codimension one)
* `fromSpecStalkOfMem_specializes`: the stalk maps of a partial map are compatible with specialization.
* `mem_domain_of_valuationRing`: if `Y ⟶ S` satisfies the existence part of the valuative criterion (e.g. it is
  proper) and is locally of finite type, an `S`-partial map from an integral `X` is defined at every point whose
  stalk is a valuation ring.
* `valuationRing_stalk`: a codimension-one point with factorial stalk has a discrete valuation ring as stalk.
* `mem_domain_of_coheight_eq_one`: hence rational maps from a locally factorial `X` to a proper `S`-scheme are
  defined at all codimension-one points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

section
variable {X Y : Scheme.{u}}

lemma fromSpecStalkOfMem_specializes (f : X.PartialMap Y) {x y : X} (h : x ⤳ y) (hx : x ∈ f.domain)
    (hy : y ∈ f.domain) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hy = f.fromSpecStalkOfMem hx := by
  have e : Spec.map (X.presheaf.stalkSpecializes h) ≫ f.domain.fromSpecStalkOfMem y hy =
      f.domain.fromSpecStalkOfMem x hx := by
    rw [← cancel_mono f.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rw [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.PartialMap.fromSpecStalkOfMem, ← Category.assoc, e]

variable {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- E1: a partial map into a target satisfying the valuative existence criterion is defined (as a rational map)
at every point with a valuation-ring stalk. -/
theorem mem_domain_of_valuationRing [IsIntegral X] [LocallyOfFiniteType sY]
    (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] : x ∈ f.toRationalMap.domain := by
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hη : genericPoint X ∈ f.domain :=
    (genericPoint_spec X).specializes trivial |>.mem_open f.domain.2
      f.dense_domain.nonempty.choose_spec
  have hsq : f.fromSpecStalkOfMem hη ≫ sY =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc, hf, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc]
    change _ = (Spec.map (X.presheaf.stalkSpecializes hgx) ≫ X.fromSpecStalk x) ≫ sX
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hdom : IsDomain (X.presheaf.stalk x) := inferInstance
  let sq : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x, commRing := inferInstance, domain := hdom,
      valuationRing := ‹_›, K := X.functionField, field := inferInstance,
      algebra := inferInstance, isFractionRing := inferInstance,
      i₁ := f.fromSpecStalkOfMem hη, i₂ := X.fromSpecStalk x ≫ sX, commSq := ⟨hsq⟩ }
  let L := (hY sq).exists_lift.some
  let l : Spec (X.presheaf.stalk x) ⟶ Y := L.l
  have hl : l ≫ sY = X.fromSpecStalk x ≫ sX := L.fac_right
  have hl' : Spec.map (X.presheaf.stalkSpecializes hgx) ≫ l = f.fromSpecStalkOfMem hη := L.fac_left
  let g := Scheme.PartialMap.ofFromSpecStalk sX sY l hl
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl
  have hηg : genericPoint X ∈ g.domain := hgx.mem_open g.domain.2 hxg
  have hgf : g.equiv f := by
    refine Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq g f hηg hη ?_
    rw [← fromSpecStalkOfMem_specializes g hgx hηg hxg,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hl'
  have hgf' : g.toRationalMap = f.toRationalMap := Scheme.PartialMap.toRationalMap_eq_iff.mpr hgf
  rw [← hgf']
  exact g.le_domain_toRationalMap hxg

end

section
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A codimension-one point with factorial stalk has a discrete valuation ring as stalk. -/
theorem isDiscreteValuationRing_stalk {z : X} (hz : coheight z = 1)
    [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have hdim : ringKrullDim (X.presheaf.stalk z) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hz]; rfl
  have hnf : ¬ IsField (X.presheaf.stalk z) := fun h => by
    have := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at this
    exact absurd this (by decide)
  have hm : (maximalIdeal (X.presheaf.stalk z)).height = 1 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk z)
    rw [hdim] at h
    exact_mod_cast h
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk z) hnf).out 0 4).mpr
    (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hm)

end

section
variable {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- E1 at codimension-one points of a locally factorial `X`. -/
theorem mem_domain_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sY]
    (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)
    {z : X} (hz : coheight z = 1) [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    z ∈ f.toRationalMap.domain := by
  have := isDiscreteValuationRing_stalk hz
  exact mem_domain_of_valuationRing sX sY hY f hf z

/-- The generic point is in the domain. -/
lemma genericPoint_mem_domain [IrreducibleSpace X] (f : X.PartialMap Y) :
    genericPoint X ∈ f.toRationalMap.domain :=
  f.le_domain_toRationalMap ((genericPoint_spec X).specializes trivial |>.mem_open f.domain.2
    f.dense_domain.nonempty.choose_spec)

end

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_JacDivisors_O =====
section

/-!
# S4-JacDivisors O (O14, steps E1' and E4-E5: where a rational map is undefined, a codimension-one divisor is)
* `exists_specMap_of_range`: a morphism `Spec R ⟶ Y` with image in an affine open `W` factors through `Spec Γ(Y, W)`.
* `specMap_cancel`: `Spec K ⟶ Spec R` is an epimorphism onto affine targets when `R ⟶ K` is injective.
* `mem_domain_of_lift`: a lift `Spec 𝒪_x ⟶ Y` of the generic germ of a partial map puts `x` in the domain.
* `mem_domain_of_range` (E4): over an affine base, if the generic ring map `Γ(Y, W) ⟶ K(X)` of a partial map lands in
  `𝒪_x`, the rational map is defined at `x`.
* `exists_not_mem_of_not_mem_domain` (E5, Hartogs): at a factorial point `p` outside the domain there is a
  codimension-one generalization `ζ` of `p` that the map does not send into `W`.
* `mem_domain_of_coheight_le_one` (E1'): into a proper target, points of codimension at most one are in the domain.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

/-- O-a: a morphism from an affine scheme whose image lies in an affine open factors through it. -/
lemma exists_specMap_of_range {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W) {R : CommRingCat.{u}}
    (t : Spec R ⟶ Y) (ht : Set.range t ⊆ (W : Set Y)) :
    ∃ θ : Γ(Y, W) ⟶ R, t = Spec.map θ ≫ hW.fromSpec := by
  refine ⟨Spec.preimage (IsOpenImmersion.lift hW.fromSpec t (by rw [hW.range_fromSpec]; exact ht)), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

lemma specMap_comp_fromSpec_inj {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W) {R : CommRingCat.{u}}
    {θ₁ θ₂ : Γ(Y, W) ⟶ R} (h : Spec.map θ₁ ≫ hW.fromSpec = Spec.map θ₂ ≫ hW.fromSpec) : θ₁ = θ₂ :=
  Spec.map_injective ((cancel_mono hW.fromSpec).mp h)

/-- O-b: cancellation of `Spec K ⟶ Spec R` (for `R ⟶ K` injective) against maps into an affine scheme. -/
lemma specMap_cancel {A R K : CommRingCat.{u}} (ι : R ⟶ K) (hι : Function.Injective ι)
    {g₁ g₂ : Spec R ⟶ Spec A} (h : Spec.map ι ≫ g₁ = Spec.map ι ≫ g₂) : g₁ = g₂ := by
  obtain ⟨a₁, rfl⟩ : ∃ a, Spec.map a = g₁ := ⟨_, Spec.map_preimage g₁⟩
  obtain ⟨a₂, rfl⟩ : ∃ a, Spec.map a = g₂ := ⟨_, Spec.map_preimage g₂⟩
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext a
  apply hι
  have := ConcreteCategory.congr_hom h a
  simpa only [CommRingCat.comp_apply] using this

section
variable {X Y : Scheme.{u}}

/-- The stalk map of a partial map at a point sent into an affine open `W` factors through `Spec Γ(Y, W)`. -/
lemma exists_specMap_fromSpecStalkOfMem (f : X.PartialMap Y) {W : Y.Opens} (hW : IsAffineOpen W) {z : X}
    (hz : z ∈ f.domain) (hzW : f.hom ⟨z, hz⟩ ∈ W) :
    ∃ θ : Γ(Y, W) ⟶ X.presheaf.stalk z, f.fromSpecStalkOfMem hz = Spec.map θ ≫ hW.fromSpec := by
  refine exists_specMap_of_range hW _ ?_
  have hcl' : f.domain.fromSpecStalkOfMem z hz (closedPoint (X.presheaf.stalk z)) = ⟨z, hz⟩ := by
    apply Subtype.ext
    change (f.domain.fromSpecStalkOfMem z hz ≫ f.domain.ι) (closedPoint (X.presheaf.stalk z)) = z
    rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
  have hcl : f.fromSpecStalkOfMem hz (closedPoint (X.presheaf.stalk z)) = f.hom ⟨z, hz⟩ := by
    rw [← hcl']
    rfl
  rintro _ ⟨q, rfl⟩
  exact ((specializes_closedPoint q).map (f.fromSpecStalkOfMem hz).continuous).mem_open W.isOpen
    (hcl ▸ hzW)

/-- O-d: for `z` sent into `W`, the generic ring map `Γ(Y, W) ⟶ K(X)` lands in `𝒪_z`. -/
lemma mem_range_of_mem [IsIntegral X] (f : X.PartialMap Y) (hη : genericPoint X ∈ f.domain)
    {W : Y.Opens} (hW : IsAffineOpen W) (θ : Γ(Y, W) ⟶ X.presheaf.stalk (genericPoint X))
    (hθ : f.fromSpecStalkOfMem hη = Spec.map θ ≫ hW.fromSpec) {z : X} (hz : z ∈ f.domain)
    (hzW : f.hom ⟨z, hz⟩ ∈ W) (a : Γ(Y, W)) :
    θ a ∈ Set.range (algebraMap (X.presheaf.stalk z) X.functionField) := by
  have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  obtain ⟨θz, hθz⟩ := exists_specMap_fromSpecStalkOfMem f hW hz hzW
  have h1 := fromSpecStalkOfMem_specializes f hgz hη hz
  rw [hθz, hθ, ← Category.assoc, ← Spec.map_comp] at h1
  have h2 : θz ≫ X.presheaf.stalkSpecializes hgz = θ := specMap_comp_fromSpec_inj hW h1
  exact ⟨θz a, by rw [← h2]; rfl⟩

/-- O-e: elements of the stalk at a codimension-one point have nonnegative order there. -/
lemma ord_algebraMap_nonneg [IsIntegral X] [IsLocallyNoetherian X] {z : X} (hz : coheight z = 1)
    (b : X.presheaf.stalk z) :
    0 ≤ Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z := by
  by_cases hb : b = 0
  · simp [hb]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk z) (mem_nonZeroDivisors_of_ne_zero hb))
  rw [ord_algebraMap_stalk hz hb hn.symm]
  exact_mod_cast Nat.zero_le n

variable {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- A lift `Spec 𝒪_x ⟶ Y` of the generic germ of `f` puts `x` in the domain of `f`. -/
lemma mem_domain_of_lift [IsIntegral X] [LocallyOfFiniteType sY] (f : X.PartialMap Y)
    (hη : genericPoint X ∈ f.domain) (x : X) (l : Spec (X.presheaf.stalk x) ⟶ Y)
    (hl : l ≫ sY = X.fromSpecStalk x ≫ sX)
    (hl' : Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫ l =
      f.fromSpecStalkOfMem hη) : x ∈ f.toRationalMap.domain := by
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let g := Scheme.PartialMap.ofFromSpecStalk sX sY l hl
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl
  have hηg : genericPoint X ∈ g.domain := hgx.mem_open g.domain.2 hxg
  have hgf : g.equiv f := by
    refine Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq g f hηg hη ?_
    rw [← fromSpecStalkOfMem_specializes g hgx hηg hxg,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hl'
  have hgf' : g.toRationalMap = f.toRationalMap := Scheme.PartialMap.toRationalMap_eq_iff.mpr hgf
  rw [← hgf']
  exact g.le_domain_toRationalMap hxg

/-- E1': into a target satisfying the valuative existence criterion, a partial map from a locally factorial
integral `X` is defined at every point of codimension at most one. -/
theorem mem_domain_of_coheight_le_one [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sY]
    (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)
    {z : X} (hz : coheight z ≤ 1) [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    z ∈ f.toRationalMap.domain := by
  rcases lt_or_eq_of_le hz with h0 | h1
  · have hmax : IsMax z := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
    have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
    have hzg : z ⤳ genericPoint X := hmax (show z ≤ genericPoint X from hgz)
    rw [(inseparable_iff_specializes_and.mpr ⟨hzg, hgz⟩).eq]
    exact genericPoint_mem_domain f
  · exact mem_domain_of_coheight_eq_one sX sY hY f hf h1

end

section
variable {X Y : Scheme.{u}} {A : CommRingCat.{u}} (sX : X ⟶ Spec A) (sY : Y ⟶ Spec A)

/-- E4: over an affine base, if the generic ring map `θ : Γ(Y, W) ⟶ K(X)` of `f` lands in `𝒪_x`, the rational
map of `f` is defined at `x`. -/
theorem mem_domain_of_range [IsIntegral X] [LocallyOfFiniteType sY] (f : X.PartialMap Y)
    (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (hη : genericPoint X ∈ f.domain) {W : Y.Opens}
    (hW : IsAffineOpen W) (θ : Γ(Y, W) ⟶ X.presheaf.stalk (genericPoint X))
    (hθ : f.fromSpecStalkOfMem hη = Spec.map θ ≫ hW.fromSpec) (x : X)
    (hx : ∀ a, θ a ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    x ∈ f.toRationalMap.domain := by
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective _ _
  choose σ hσ using hx
  let σ' : Γ(Y, W) →+* X.presheaf.stalk x :=
    { toFun := σ
      map_one' := hinj (by rw [hσ, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hσ, map_mul, map_mul, hσ, hσ])
      map_zero' := hinj (by rw [hσ, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hσ, map_add, map_add, hσ, hσ]) }
  have hcomp : CommRingCat.ofHom σ' ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) = θ := by
    ext a
    exact hσ a
  let l : Spec (X.presheaf.stalk x) ⟶ Y := Spec.map (CommRingCat.ofHom σ') ≫ hW.fromSpec
  have hl' : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ l =
      f.fromSpecStalkOfMem hη := by
    rw [hθ, ← hcomp, Spec.map_comp, Category.assoc]
    rfl
  have hsq : f.fromSpecStalkOfMem hη ≫ sY =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc, hf, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc]
    change _ = (Spec.map (X.presheaf.stalkSpecializes hgx) ≫ X.fromSpecStalk x) ≫ sX
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hl : l ≫ sY = X.fromSpecStalk x ≫ sX := by
    refine specMap_cancel (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) hinj ?_
    rw [← Category.assoc, hl', hsq]
  exact mem_domain_of_lift sX sY f hη x l hl hl'

/-- E5 (Hartogs): if `f` sends some point into the affine open `W` but is undefined at a factorial point `p`,
then some codimension-one generalization `ζ` of `p` is not sent into `W`. -/
theorem exists_not_mem_of_not_mem_domain [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sY]
    (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX) {W : Y.Opens} (hW : IsAffineOpen W)
    {z₀ : X} (hz₀ : z₀ ∈ f.domain) (hz₀W : f.hom ⟨z₀, hz₀⟩ ∈ W)
    {p : X} [UniqueFactorizationMonoid (X.presheaf.stalk p)] (hp : p ∉ f.toRationalMap.domain) :
    ∃ ζ : X, ζ ⤳ p ∧ coheight ζ = 1 ∧ ∀ hζ : ζ ∈ f.domain, f.hom ⟨ζ, hζ⟩ ∉ W := by
  have hgz₀ : genericPoint X ⤳ z₀ := (genericPoint_spec X).specializes trivial
  have hη : genericPoint X ∈ f.domain := hgz₀.mem_open f.domain.2 hz₀
  obtain ⟨θ₀, hθ₀⟩ := exists_specMap_fromSpecStalkOfMem f hW hz₀ hz₀W
  let θ : Γ(Y, W) ⟶ X.presheaf.stalk (genericPoint X) := θ₀ ≫ X.presheaf.stalkSpecializes hgz₀
  have hθ : f.fromSpecStalkOfMem hη = Spec.map θ ≫ hW.fromSpec := by
    rw [← fromSpecStalkOfMem_specializes f hgz₀ hη hz₀, hθ₀, Spec.map_comp, Category.assoc]
  have hnot : ¬ ∀ a, θ a ∈ Set.range (algebraMap (X.presheaf.stalk p) X.functionField) :=
    fun h => hp (mem_domain_of_range sX sY f hf hη hW θ hθ p h)
  push Not at hnot
  obtain ⟨a, ha⟩ := hnot
  have hneg : ¬ ∀ z : X, z ⤳ p → coheight z = 1 → 0 ≤ Scheme.ord (θ a) z :=
    fun h => ha (mem_range_algebraMap_stalk_of_ord_nonneg p (θ a) h)
  push Not at hneg
  obtain ⟨ζ, hζp, hζ1, hlt⟩ := hneg
  refine ⟨ζ, hζp, hζ1, fun hζ hζW => ?_⟩
  obtain ⟨b, hb⟩ := mem_range_of_mem f hη hW θ hθ hζ hζW a
  rw [← hb] at hlt
  exact absurd (ord_algebraMap_nonneg hζ1 b) (not_le.mpr hlt)

end

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_ThetaSquare_CPull =====
section

/-!
# S4-ThetaSquare, file CPull: pulling Weil divisors back along non-dominant morphisms (T4a)

For `f : C ⟶ Y` between integral locally Noetherian schemes, `Y` locally factorial, and a Weil divisor `D` on `Y`
whose support avoids `ξ = f (η_C)` (`Avoid f D`), the local equations of `D` are units at `ξ`, so they pull back to
`K(C)` through the stalk map at `η_C`; `cpull f D` is the cycle `x ↦ ord_x (f^* (locEq D (f x)))`.
* `fpull f`: rational functions regular at `ξ` pulled back to `K(C)`; `fpull_algebraMap_at`: on `O_{Y, f x}` it is
  the stalk map at `x`.
* `cpull`, `cpull_apply`, `cpull_eq_of` (any local equation), `cpull_add`, `cpull_div`, `cpull_eq_zero_of` (off the
  support), `cpull_nonneg` and `cpull_pos` (effective divisors), `cpull_comp` (`f ≫ φ` with `φ` dominant).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaSquare

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing RamanujanPetersson.JacDivisors
  RamanujanPetersson.IsogDegA

universe u

section
variable {X : Scheme.{u}} [IsIntegral X]

/-- The algebra map of a stalk factors through any generization. -/
lemma algebraMap_stalkSpecializes {z y : X} (h : z ⤳ y) (a : X.presheaf.stalk y) :
    algebraMap _ X.functionField ((X.presheaf.stalkSpecializes h).hom a) =
      algebraMap _ X.functionField a :=
  congrArg (fun g => g.hom a) (TopCat.Presheaf.stalkSpecializes_comp X.presheaf
    ((genericPoint_spec X).specializes trivial : genericPoint X ⤳ z) h)

end

section
variable {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y] (f : C ⟶ Y)

/-- `ξ = f (η_C)` specializes to every `f x`. -/
lemma xi_specializes (x : C) : f (genericPoint C) ⤳ f x :=
  f.base.hom.map_specializes ((genericPoint_spec C).specializes trivial)

open Classical in
/-- Pull-back to `K(C)` of the rational functions that are regular at `ξ = f (η_C)` (junk `0` otherwise). -/
noncomputable def fpull (g : Y.functionField) : C.functionField :=
  if h : ∃ u : Y.presheaf.stalk (f (genericPoint C)), algebraMap _ Y.functionField u = g
  then (f.stalkMap (genericPoint C)).hom h.choose else 0

lemma fpull_algebraMap (u : Y.presheaf.stalk (f (genericPoint C))) :
    fpull f (algebraMap _ Y.functionField u) = (f.stalkMap (genericPoint C)).hom u := by
  have h : ∃ u' : Y.presheaf.stalk (f (genericPoint C)),
      algebraMap _ Y.functionField u' = algebraMap _ Y.functionField u := ⟨u, rfl⟩
  rw [fpull, dif_pos h]
  congr 1
  exact IsFractionRing.injective _ Y.functionField h.choose_spec

lemma fpull_one : fpull f 1 = 1 := by
  rw [← map_one (algebraMap (Y.presheaf.stalk (f (genericPoint C))) Y.functionField), fpull_algebraMap,
    map_one]

/-- On the stalk at `f x`, `fpull` is the stalk map at `x`. -/
lemma fpull_algebraMap_at (x : C) (a : Y.presheaf.stalk (f x)) :
    fpull f (algebraMap _ Y.functionField a) =
      algebraMap _ C.functionField ((f.stalkMap x).hom a) := by
  rw [← algebraMap_stalkSpecializes (xi_specializes f x) a, fpull_algebraMap]
  exact f.stalkSpecializes_stalkMap_apply (genericPoint C) x
    ((genericPoint_spec C).specializes trivial) a

lemma fpull_mul (u v : Y.presheaf.stalk (f (genericPoint C))) :
    fpull f (algebraMap _ Y.functionField u * algebraMap _ Y.functionField v) =
      fpull f (algebraMap _ Y.functionField u) * fpull f (algebraMap _ Y.functionField v) := by
  rw [← map_mul, fpull_algebraMap, fpull_algebraMap, fpull_algebraMap, map_mul]

lemma fpull_mul_at (x : C) (u : Y.presheaf.stalk (f (genericPoint C))) (w : Y.presheaf.stalk (f x)) :
    fpull f (algebraMap _ Y.functionField u * algebraMap _ Y.functionField w) =
      fpull f (algebraMap _ Y.functionField u) * algebraMap _ C.functionField ((f.stalkMap x).hom w) := by
  rw [← algebraMap_stalkSpecializes (xi_specializes f x) w, fpull_mul, ← fpull_algebraMap_at f x w,
    algebraMap_stalkSpecializes]

lemma fpull_ne_zero {u : Y.presheaf.stalk (f (genericPoint C))} (hu : IsUnit u) :
    fpull f (algebraMap _ Y.functionField u) ≠ 0 := by
  rw [fpull_algebraMap]
  exact (hu.map _).ne_zero

end

section
variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

/-- The support of `D` avoids `ξ = f (η_C)`. -/
def Avoid (D : AlgebraicCycle Y ℤ) : Prop :=
  ∃ V : Set Y, IsOpen V ∧ f (genericPoint C) ∈ V ∧ ∀ w ∈ V, D w = 0

lemma avoid_add {D E : AlgebraicCycle Y ℤ} (hD : Avoid f D) (hE : Avoid f E) : Avoid f (D + E) := by
  obtain ⟨V, hV, h1, h2⟩ := hD
  obtain ⟨V', hV', h1', h2'⟩ := hE
  refine ⟨V ∩ V', hV.inter hV', ⟨h1, h1'⟩, fun w hw => ?_⟩
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, h2 w hw.1, h2' w hw.2, add_zero]

/-- A local equation of `D` at `f x` is a unit at `ξ`. -/
lemma exists_unit_of_isLocEq {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) {x : C} {g : Y.functionField}
    (hg : IsLocEq D (f x) g) :
    ∃ u : Y.presheaf.stalk (f (genericPoint C)), IsUnit u ∧ algebraMap _ Y.functionField u = g := by
  obtain ⟨hg0, V, hV, hxV, hDV⟩ := hg
  obtain ⟨V', hV', hξ, hD0⟩ := hA
  have hξV : f (genericPoint C) ∈ V := (xi_specializes f x).mem_open hV hxV
  refine exists_isUnit_of_ord_eq_zero _ hg0 fun z hz _ => ?_
  show div Y g z = 0
  rw [← hDV z (hz.mem_open hV hξV)]
  exact hD0 z (hz.mem_open hV' hξ)

/-- Two local equations at `f x` give the same order at `x`. -/
lemma ord_fpull_eq_of {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) {x : C} {g h : Y.functionField}
    (hg : IsLocEq D (f x) g) (hh : IsLocEq D (f x) h) :
    Scheme.ord (fpull f g) x = Scheme.ord (fpull f h) x := by
  obtain ⟨uh, huh, rfl⟩ := exists_unit_of_isLocEq f hA hh
  obtain ⟨hg0, V1, hV1, hx1, hD1⟩ := hg
  obtain ⟨hh0, V2, hV2, hx2, hD2⟩ := hh
  obtain ⟨w, hw, hwr⟩ := exists_isUnit_of_ord_eq_zero (f x) (div_ne_zero hg0 hh0)
    fun z hz _ => ord_eq_of_div_eq hg0 hh0
      ((hD1 z (hz.mem_open hV1 hx1)).symm.trans (hD2 z (hz.mem_open hV2 hx2)))
  have e : g = algebraMap _ Y.functionField uh * algebraMap _ Y.functionField w := by
    rw [hwr]
    field_simp
  rw [e, fpull_mul_at, Scheme.ord_mul (fpull_ne_zero f huh), ord_algebraMap_isUnit x (hw.map _), add_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ C.functionField)).mpr (hw.map _).ne_zero

lemma ord_fpull_locEq {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    {g : Y.functionField} (hg : IsLocEq D (f x) g) :
    Scheme.ord (fpull f (locEq D (f x))) x = Scheme.ord (fpull f g) x :=
  ord_fpull_eq_of f hA (isLocEq_locEq hD (f x)) hg

lemma locallyFinite_cpull {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x₀ : C) :
    ∃ t ∈ 𝓝 x₀, (t ∩ Function.support
      (fun x => Scheme.ord (fpull f (locEq D (f x))) x)).Finite := by
  obtain ⟨hf, V, hV, hx₀, hDV⟩ := isLocEq_locEq hD (f x₀)
  obtain ⟨t, ht, hfin⟩ := locallyFinite_ord (fpull f (locEq D (f x₀))) x₀
  refine ⟨t ∩ f ⁻¹' V, Filter.inter_mem ht ((hV.preimage f.continuous).mem_nhds hx₀),
    hfin.subset ?_⟩
  rintro x ⟨⟨hxt, hxV⟩, hx⟩
  refine ⟨hxt, ?_⟩
  rw [Function.mem_support, ord_fpull_locEq f hD hA ⟨hf, V, hV, hxV, hDV⟩] at hx
  exact hx

open Classical in
/-- The pull-back `f^* D` of a Weil divisor whose support avoids `f (η_C)` (junk `0` otherwise). -/
noncomputable def cpull (D : AlgebraicCycle Y ℤ) : AlgebraicCycle C ℤ :=
  if hD : D ∈ weilDivisors Y ∧ Avoid f D then
    { toFun := fun x => Scheme.ord (fpull f (locEq D (f x))) x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun x _ => locallyFinite_cpull f hD.1 hD.2 x }
  else 0

lemma cpull_apply {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x : C) :
    cpull f D x = Scheme.ord (fpull f (locEq D (f x))) x := by
  rw [cpull, dif_pos ⟨hD, hA⟩]
  rfl

/-- `cpull` through any local equation. -/
lemma cpull_eq_of {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    {g : Y.functionField} (hg : IsLocEq D (f x) g) : cpull f D x = Scheme.ord (fpull f g) x := by
  rw [cpull_apply f hD hA, ord_fpull_locEq f hD hA hg]

lemma cpull_eq_zero_of {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    {V : Set Y} (hV : IsOpen V) (hxV : f x ∈ V) (h0 : ∀ w ∈ V, D w = 0) : cpull f D x = 0 := by
  rw [cpull_eq_of f hD hA (g := 1) ⟨one_ne_zero, V, hV, hxV, fun w hw => by
    rw [h0 w hw, JacDivisors.div_one]; rfl⟩, fpull_one]
  change div C 1 x = 0
  rw [JacDivisors.div_one]
  rfl

lemma cpull_add {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y)
    (hAD : Avoid f D) (hAE : Avoid f E) : cpull f (D + E) = cpull f D + cpull f E := by
  ext x
  obtain ⟨hg, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (f x)
  obtain ⟨hh, V', hV', hxV', hEV'⟩ := isLocEq_locEq hE (f x)
  obtain ⟨ug, hug, hg'⟩ := exists_unit_of_isLocEq f hAD (isLocEq_locEq hD (f x))
  obtain ⟨uh, huh, hh'⟩ := exists_unit_of_isLocEq f hAE (isLocEq_locEq hE (f x))
  have hDE : IsLocEq (D + E) (f x) (locEq D (f x) * locEq E (f x)) := by
    refine ⟨mul_ne_zero hg hh, V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun w hw => ?_⟩
    rw [div_mul hg hh, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hDV w hw.1, hEV' w hw.2]
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    cpull_eq_of f ((weilDivisors Y).add_mem hD hE) (avoid_add f hAD hAE) hDE,
    cpull_apply f hD hAD, cpull_apply f hE hAE, ← hg', ← hh', fpull_mul,
    Scheme.ord_mul (fpull_ne_zero f hug) (fpull_ne_zero f huh)]

/-- The pull-back of a principal divisor. -/
lemma cpull_div {g : Y.functionField} (hg : g ≠ 0) (hA : Avoid f (div Y g)) :
    cpull f (div Y g) = div C (fpull f g) := by
  ext x
  rw [cpull_eq_of f (div_mem_weilDivisors g) hA ⟨hg, Set.univ, isOpen_univ, trivial, fun _ _ => rfl⟩,
    div_apply]

/-- A local equation of a divisor that is effective near `y` is regular at `y`. -/
lemma exists_stalk_of_nonneg {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (y : Y)
    (h : ∀ z : Y, z ⤳ y → coheight z = 1 → 0 ≤ D z) :
    ∃ a : Y.presheaf.stalk y, algebraMap _ Y.functionField a = locEq D y := by
  obtain ⟨-, V, hV, hyV, hDV⟩ := isLocEq_locEq hD y
  obtain ⟨a, ha⟩ := mem_range_algebraMap_stalk_of_ord_nonneg y (locEq D y) fun z hz h1 => by
    have := h z hz h1
    rw [hDV z (hz.mem_open hV hyV)] at this
    exact this
  exact ⟨a, ha⟩

lemma cpull_nonneg {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x : C)
    (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → 0 ≤ D z) : 0 ≤ cpull f D x := by
  obtain ⟨a, ha⟩ := exists_stalk_of_nonneg hD (f x) h
  rw [cpull_apply f hD hA, ← ha, fpull_algebraMap_at]
  by_cases hx : coheight x = 1
  · exact ord_algebraMap_nonneg hx _
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

lemma cpull_pos {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    (hx : coheight x = 1) (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → 0 ≤ D z) {z₀ : Y}
    (hz₀ : z₀ ⤳ f x) (hpos : 0 < D z₀) : 0 < cpull f D x := by
  obtain ⟨a, ha⟩ := exists_stalk_of_nonneg hD (f x) h
  obtain ⟨hg0, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (f x)
  obtain ⟨ug, hug, hg'⟩ := exists_unit_of_isLocEq f hA (isLocEq_locEq hD (f x))
  have hna : ¬ IsUnit a := by
    intro hu
    have h1 : D z₀ = 0 := by
      rw [hDV z₀ (hz₀.mem_open hV hxV), div_apply, ← ha,
        ← algebraMap_stalkSpecializes hz₀ a]
      exact ord_algebraMap_isUnit z₀ (hu.map _)
    omega
  have hne : (f.stalkMap x).hom a ≠ 0 := by
    intro h0
    have := fpull_ne_zero f hug
    rw [hg', ← ha, fpull_algebraMap_at, h0, map_zero] at this
    exact this rfl
  have hmem : (f.stalkMap x).hom a ∈ maximalIdeal (C.presheaf.stalk x) :=
    (mem_maximalIdeal _).mpr fun hu => hna (isUnit_of_map_unit (f.stalkMap x).hom a hu)
  rw [cpull_apply f hD hA, ← ha, fpull_algebraMap_at]
  exact ord_algebraMap_stalk_pos hx hne hmem

end

section
variable {C Y Z : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsIntegral Z] [IsLocallyNoetherian Z]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
  [∀ z : Z, UniqueFactorizationMonoid (Z.presheaf.stalk z)] (f : C ⟶ Y) (φ : Y ⟶ Z) [IsDominant φ]

lemma fpull_ffMap (u : Z.presheaf.stalk (φ (f (genericPoint C)))) :
    fpull f ((ffMap φ).hom (algebraMap _ Z.functionField u)) =
      fpull (f ≫ φ) (algebraMap _ Z.functionField u) := by
  rw [ffMap_algebraMap, fpull_algebraMap]
  refine Eq.trans ?_ (fpull_algebraMap (f ≫ φ) u).symm
  rw [Scheme.Hom.stalkMap_comp]
  rfl

lemma avoid_pullback {D : AlgebraicCycle Z ℤ} (hD : D ∈ weilDivisors Z) (hA : Avoid (f ≫ φ) D) :
    Avoid f (pullback φ D) := by
  obtain ⟨V, hV, hξ, h0⟩ := hA
  refine ⟨φ ⁻¹' V, hV.preimage φ.continuous, hξ, fun w hw => ?_⟩
  rw [pullback_eq_div_of φ hD one_ne_zero hV (fun w' hw' => by rw [h0 w' hw', JacDivisors.div_one]; rfl) hw,
    map_one, JacDivisors.div_one]
  rfl

/-- Pull-back along `f ≫ φ` is pull-back along `φ` (dominant) and then along `f`. -/
lemma cpull_comp {D : AlgebraicCycle Z ℤ} (hD : D ∈ weilDivisors Z) (hA : Avoid (f ≫ φ) D) :
    cpull (f ≫ φ) D = cpull f (pullback φ D) := by
  ext x
  obtain ⟨hg, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (φ (f x))
  have hloc : IsLocEq D ((f ≫ φ) x) (locEq D (φ (f x))) := ⟨hg, V, hV, hxV, hDV⟩
  obtain ⟨ug, -, hg'⟩ := exists_unit_of_isLocEq (f ≫ φ) hA hloc
  have hloc' : IsLocEq (pullback φ D) (f x) ((ffMap φ).hom (locEq D (φ (f x)))) :=
    ⟨ffMap_ne_zero φ hg, φ ⁻¹' V, hV.preimage φ.continuous, hxV,
      fun w hw => pullback_eq_div_of φ hD hg hV hDV hw⟩
  rw [cpull_eq_of (f ≫ φ) hD hA hloc,
    cpull_eq_of f (pullback_mem_weilDivisors φ D) (avoid_pullback f φ hD hA) hloc', ← hg']
  exact congrArg (fun t => Scheme.ord t x) (fpull_ffMap f φ ug).symm

end

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaCube_Det =====
section

/-!
# S4-ThetaCube, file Det (D-B2, part 1): determinants of pulled-back rational functions
General facts on `fpull` (pull-back of rational functions regular at `f (η_C)`):
* `algebraMap_generic`, `fpull_id`;
* `fpull_fpull`: pulling back twice through stalks;
* **`fpull_det`**: the determinant of a matrix of pulled-back functions is regular at `ℓ (η_C)` and its
  pull-back along `ℓ` is the determinant of the composite pull-backs; `fpull_det_eq`;
* `isUnit_of_stalkMap_ne_zero`, **`avoid_div_of_isUnit`** (for `cpull_div`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory Order Topology RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare

universe u

section Gen

variable {C P X : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral X]

/-- On the generic stalk, `algebraMap` to the function field is the identity. -/
lemma algebraMap_generic (v : X.presheaf.stalk (genericPoint X)) :
    @algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField _ _
      (stalkFunctionFieldAlgebra X (genericPoint X)) v = v := by
  have h : (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial :
      genericPoint X ⤳ genericPoint X)) = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  exact (congrArg (fun t => t.hom v) h).trans rfl

lemma fpull_id (g : X.functionField) : fpull (𝟙 X) g = g := by
  have h := fpull_algebraMap (𝟙 X) (g : X.presheaf.stalk ((𝟙 X : X ⟶ X) (genericPoint X)))
  have e1 : algebraMap (X.presheaf.stalk ((𝟙 X : X ⟶ X) (genericPoint X))) X.functionField g = g :=
    algebraMap_generic g
  have e2 : ((𝟙 X : X ⟶ X).stalkMap (genericPoint X)).hom g = g := by
    rw [Scheme.Hom.stalkMap_id]
    rfl
  rw [e1] at h
  exact h.trans e2

variable (ℓ : C ⟶ P)

/-- Pulling back twice through the stalk at `ℓ (η_C)`. -/
lemma fpull_fpull (z : P ⟶ X) (g : X.functionField)
    (hg : ∃ w : X.presheaf.stalk ((ℓ ≫ z) (genericPoint C)), algebraMap _ X.functionField w = g) :
    ∃ v : P.presheaf.stalk (ℓ (genericPoint C)), algebraMap _ P.functionField v = fpull z g ∧
      (ℓ.stalkMap (genericPoint C)).hom v = fpull (ℓ ≫ z) g := by
  obtain ⟨w, rfl⟩ := hg
  refine ⟨(z.stalkMap (ℓ (genericPoint C))).hom w, (fpull_algebraMap_at z (ℓ (genericPoint C)) w).symm, ?_⟩
  rw [fpull_algebraMap, Scheme.Hom.stalkMap_comp]
  rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Determinants of pulled-back functions** are regular at `ℓ (η_C)`, with the expected pull-back. -/
theorem fpull_det (z : κ → (P ⟶ X)) (g : κ → κ → X.functionField)
    (hg : ∀ a l, ∃ w : X.presheaf.stalk ((ℓ ≫ z a) (genericPoint C)), algebraMap _ X.functionField w = g a l) :
    ∃ v : P.presheaf.stalk (ℓ (genericPoint C)),
      algebraMap _ P.functionField v = (Matrix.of fun a l => fpull (z a) (g a l)).det ∧
      (ℓ.stalkMap (genericPoint C)).hom v = (Matrix.of fun a l => fpull (ℓ ≫ z a) (g a l)).det := by
  choose v hv1 hv2 using fun a l => fpull_fpull ℓ (z a) (g a l) (hg a l)
  refine ⟨(Matrix.of v).det, ?_, ?_⟩
  · rw [RingHom.map_det]
    congr 1
    ext a l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact hv1 a l
  · rw [RingHom.map_det]
    congr 1
    ext a l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact hv2 a l

theorem fpull_det_eq (z : κ → (P ⟶ X)) (g : κ → κ → X.functionField)
    (hg : ∀ a l, ∃ w : X.presheaf.stalk ((ℓ ≫ z a) (genericPoint C)), algebraMap _ X.functionField w = g a l) :
    fpull ℓ (Matrix.of fun a l => fpull (z a) (g a l)).det =
      (Matrix.of fun a l => fpull (ℓ ≫ z a) (g a l)).det := by
  obtain ⟨v, h1, h2⟩ := fpull_det ℓ z g hg
  rw [← h1, fpull_algebraMap, h2]

/-- A germ at `ℓ (η_C)` with nonzero pull-back is a unit. -/
lemma isUnit_of_stalkMap_ne_zero {v : P.presheaf.stalk (ℓ (genericPoint C))}
    (hv : (ℓ.stalkMap (genericPoint C)).hom v ≠ 0) : IsUnit v := by
  have h : IsUnit ((ℓ.stalkMap (genericPoint C)).hom v : C.functionField) := isUnit_iff_ne_zero.mpr hv
  exact isUnit_of_map_unit (ℓ.stalkMap (genericPoint C)).hom v h

end Gen

section Av

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

/-- **The divisor of a unit at `f (η_C)` avoids `f (η_C)`.** -/
theorem avoid_div_of_isUnit {v : Y.presheaf.stalk (f (genericPoint C))} (hv : IsUnit v) :
    Avoid f (div Y (algebraMap _ Y.functionField v)) := by
  obtain ⟨U, m, s, hs⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf v
  refine ⟨Y.basicOpen s, (Y.basicOpen s).isOpen, ?_, fun w hw => ?_⟩
  · exact (Y.mem_basicOpen s _ m).mpr (by rw [hs]; exact hv)
  · have hwU : w ∈ U := Y.basicOpen_le s hw
    have hunit : IsUnit (Y.presheaf.germ U w hwU s) := (Y.mem_basicOpen s w hwU).mp hw
    have : Nonempty U := ⟨⟨w, hwU⟩⟩
    have e : algebraMap _ Y.functionField (Y.presheaf.germ U w hwU s) =
        algebraMap _ Y.functionField v := by
      rw [← hs, Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]
    rw [div_apply, ← e]
    exact ord_algebraMap_isUnit w hunit

end Av

end RamanujanPetersson.ThetaCube

end

-- ===== S4.Def_RP_JacDivisors_N =====
section

/-!
# S4-JacDivisors N (O14, steps E6-E7: a prime divisor through `Δ x` meets any morphism in codimension one)
* `exists_uniformizer_specializes`: near a point `x` with factorial stalk, a uniformizer `r` of a codimension-one
  generalization `ζ` of `x` cuts out exactly the specializations of `ζ` among the generalizations of `x`.
* `exists_coheight_le_one_not_mem_basicOpen`: Krull's principal ideal theorem on a chart: if `x ∉ D(r)` there is a
  generalization `v` of `x` of codimension at most one with `v ∉ D(r)`.
* `exists_specializes_of_coheight_eq_one`: for any morphism `Δ : V ⟶ P` and a codimension-one generalization `ζ` of
  `Δ x` (factorial stalk at `Δ x`), some generalization `v` of `x` of codimension at most one has `ζ ⤳ Δ v`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

section
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A uniformizer of a codimension-one generalization `ζ` of `x` cuts out the specializations of `ζ` near `x`. -/
lemma exists_uniformizer_specializes {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (ζ : X) (hζ : ζ ⤳ x) (hζ1 : coheight ζ = 1) :
    ∃ r : Γ(X, U), r ≠ 0 ∧ ζ ∉ X.basicOpen r ∧
      ∀ w : X, w ⤳ x → w ∉ X.basicOpen r → ζ ⤳ w := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hx
  obtain ⟨r, hr0, hr⟩ := exists_uniformizer hU y ζ hζ hζ1
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hζU : ζ ∈ U := hζ.mem_open U.isOpen hx
  have hζr : ζ ∉ X.basicOpen r := by
    intro h
    have h1 := ord_germ_eq_zero r h
    rw [hr ζ hζ hζ1, if_pos rfl] at h1
    exact one_ne_zero h1
  refine ⟨r, hr0, hζr, fun w hw hwr => ?_⟩
  have hwU : w ∈ U := hw.mem_open U.isOpen hx
  obtain ⟨q, rfl⟩ := exists_fromSpec_eq hU hwU
  have hrq : r ∈ q.asIdeal := by
    by_contra h
    exact hwr ((fromSpec_mem_basicOpen_iff hU r q).mpr h)
  have : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {r}) (J := q.asIdeal)
    ((Ideal.span_singleton_le_iff_mem _).mpr hrq)
  have hpp : p.IsPrime := hp.1.1
  have hrp : r ∈ p := hp.1.2 (Ideal.mem_span_singleton_self r)
  have hp1 : p.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
    have hne : p ≠ ⊥ := fun h => hr0 (by rw [h] at hrp; exact hrp)
    rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    exact fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)
  let pp : Spec Γ(X, U) := ⟨p, hpp⟩
  have hpp1 : coheight (hU.fromSpec pp) = 1 := by rw [coheight_fromSpec]; exact hp1
  have hppq : hU.fromSpec pp ⤳ hU.fromSpec q := (fromSpec_specializes_iff hU pp q).mpr hpq
  have hppy : hU.fromSpec pp ⤳ hU.fromSpec y := hppq.trans hw
  have hpos := ord_germ_pos (fromSpec_mem hU pp) hpp1 hr0
    (by rw [fromSpec_mem_basicOpen_iff]; exact not_not.mpr hrp)
  rw [hr _ hppy hpp1] at hpos
  split_ifs at hpos with heq
  · rw [← heq]; exact hppq
  · exact absurd hpos (lt_irrefl 0)

end

/-- Krull's principal ideal theorem on an affine chart. -/
lemma exists_coheight_le_one_not_mem_basicOpen {X : Scheme.{u}} [IsLocallyNoetherian X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (r : Γ(X, U)) (hxr : x ∉ X.basicOpen r) :
    ∃ v : X, v ⤳ x ∧ coheight v ≤ 1 ∧ v ∈ U ∧ v ∉ X.basicOpen r := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hx
  have hry : r ∈ y.asIdeal := by
    by_contra h
    exact hxr ((fromSpec_mem_basicOpen_iff hU r y).mpr h)
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨p, hp, hpy⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {r}) (J := y.asIdeal)
    ((Ideal.span_singleton_le_iff_mem _).mpr hry)
  have hpp : p.IsPrime := hp.1.1
  let pp : Spec Γ(X, U) := ⟨p, hpp⟩
  refine ⟨hU.fromSpec pp, (fromSpec_specializes_iff hU pp y).mpr hpy, ?_, fromSpec_mem hU pp, ?_⟩
  · rw [coheight_fromSpec]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  · rw [fromSpec_mem_basicOpen_iff]
    exact not_not.mpr (hp.1.2 (Ideal.mem_span_singleton_self r))

/-- E6-E7: a prime divisor `ζ` through `Δ x` (factorial stalk at `Δ x`) contains `Δ v` for some generalization `v`
of `x` of codimension at most one. -/
theorem exists_specializes_of_coheight_eq_one {V P : Scheme.{u}} [IsIntegral P] [IsLocallyNoetherian P]
    [IsLocallyNoetherian V] (Δ : V ⟶ P) (x : V) [UniqueFactorizationMonoid (P.presheaf.stalk (Δ x))]
    {ζ : P} (hζ : ζ ⤳ Δ x) (hζ1 : coheight ζ = 1) :
    ∃ v : V, v ⤳ x ∧ coheight v ≤ 1 ∧ ζ ⤳ Δ v := by
  obtain ⟨_, ⟨UP, hUP, rfl⟩, hxUP, -⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (Δ x)) isOpen_univ
  replace hUP : IsAffineOpen UP := hUP
  obtain ⟨r, -, hζr, hr⟩ := exists_uniformizer_specializes hUP hxUP ζ hζ hζ1
  have hxr : Δ x ∉ P.basicOpen r := fun h => hζr (hζ.mem_open (P.basicOpen r).isOpen h)
  obtain ⟨_, ⟨UV, hUV, rfl⟩, hxUV, hUVle⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (Δ ⁻¹ᵁ UP : Set V) from hxUP)
      (Δ ⁻¹ᵁ UP).isOpen
  replace hUV : IsAffineOpen UV := hUV
  let r' : Γ(V, UV) := Δ.appLE UP UV hUVle r
  have hbo : ∀ v ∈ UV, v ∈ V.basicOpen r' ↔ Δ v ∈ P.basicOpen r := by
    intro v hv
    rw [← SetLike.mem_coe, Scheme.basicOpen_appLE Δ UV UP hUVle r]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  obtain ⟨v, hvx, hv1, hvU, hvr⟩ :=
    exists_coheight_le_one_not_mem_basicOpen hUV hxUV r' (by rw [hbo x hxUV]; exact hxr)
  refine ⟨v, hvx, hv1, hr _ (hvx.map Δ.base.hom.continuous) ?_⟩
  rw [← hbo v hvU]
  exact hvr

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_JacDivisors_P =====
section

/-!
# S4-JacDivisors P (O14, steps E2 and E8: the difference map `Φ(v, w) = φ(v) φ(w)⁻¹` is defined on the diagonal)
For `V G : Over (Spec k)` with `G` a group object and a partial map `f : V ⇀ G` over `k` with domain `D`:
* `sqOpen D = pr₁⁻¹ D ∩ pr₂⁻¹ D ⊆ V ×_k V` and `quotHom f = (f ∘ pr₁) · (f ∘ pr₂)⁻¹ : sqOpen D ⟶ G` over `k`;
  `quotPM f` is the corresponding partial map `V ×_k V ⇀ G`.
* `quotHom_diag`: `Φ(Δ v) = e` (the unit point of `G`) for `v ∈ D`.
* `diag_mem_domain` (E8): if `D` contains every point of codimension at most one, `V ×_k V` is integral and locally
  Noetherian, and the stalk of `V ×_k V` at `Δ x` is factorial, then `Φ` is defined at `Δ x`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology MonoidalCategory MonObj CartesianMonoidalCategory

universe u

section
variable {k : Type u} [Field k] {V G : Over (Spec (.of k))}

/-- The diagonal `V ⟶ V ×_k V`. -/
noncomputable abbrev diag (V : Over (Spec (.of k))) : V ⟶ V ⊗ V := lift (𝟙 V) (𝟙 V)

/-- `pr₁⁻¹ D ∩ pr₂⁻¹ D`. -/
noncomputable def sqOpen (D : V.left.Opens) : (V ⊗ V).left.Opens :=
  (fst V V).left ⁻¹ᵁ D ⊓ (snd V V).left ⁻¹ᵁ D

/-- `sqOpen D` as an object over `k`. -/
noncomputable abbrev sqOver (D : V.left.Opens) : Over (Spec (.of k)) :=
  Over.mk ((sqOpen D).ι ≫ (V ⊗ V).hom)

lemma fst_diag_apply (v : V.left) : (fst V V).left ((diag V).left v) = v := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
  rfl

lemma snd_diag_apply (v : V.left) : (snd V V).left ((diag V).left v) = v := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  rfl

lemma diag_mem {D : V.left.Opens} {v : V.left} (hv : v ∈ D) : (diag V).left v ∈ sqOpen D :=
  ⟨show (fst V V).left ((diag V).left v) ∈ D by rw [fst_diag_apply]; exact hv,
   show (snd V V).left ((diag V).left v) ∈ D by rw [snd_diag_apply]; exact hv⟩

lemma sqOpen_le_fst (D : V.left.Opens) : sqOpen D ≤ (fst V V).left ⁻¹ᵁ D := inf_le_left

lemma sqOpen_le_snd (D : V.left.Opens) : sqOpen D ≤ (snd V V).left ⁻¹ᵁ D := inf_le_right

lemma diag_le (D : V.left.Opens) : D ≤ (diag V).left ⁻¹ᵁ sqOpen D := fun _ hw => diag_mem hw

lemma diag_resLE_pr (D : V.left.Opens) (p : V ⊗ V ⟶ V) (hp : diag V ≫ p = 𝟙 V)
    (h₁ : D ≤ (diag V).left ⁻¹ᵁ sqOpen D) (h₂ : sqOpen D ≤ p.left ⁻¹ᵁ D) :
    (diag V).left.resLE (sqOpen D) D h₁ ≫ p.left.resLE D (sqOpen D) h₂ = 𝟙 _ := by
  rw [← cancel_mono D.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc, ← Over.comp_left, hp, Over.id_left,
    Category.comp_id, Category.id_comp]

/-- `f ∘ pr` on `sqOpen D`, as a map over `k`. -/
noncomputable def prRes (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    (p : V ⊗ V ⟶ V) (hp : sqOpen f.domain ≤ p.left ⁻¹ᵁ f.domain) : sqOver f.domain ⟶ G :=
  Over.homMk (p.left.resLE f.domain (sqOpen f.domain) hp ≫ f.hom) (by
    change (p.left.resLE _ _ hp ≫ f.hom) ≫ G.hom = (sqOpen f.domain).ι ≫ (V ⊗ V).hom
    rw [Category.assoc, hf, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w p])

variable [GrpObj G]

/-- E2: `Φ = (f ∘ pr₁) · (f ∘ pr₂)⁻¹ : sqOpen D ⟶ G` over `k`. -/
noncomputable def quotHom (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    sqOver f.domain ⟶ G :=
  prRes f hf (fst V V) (sqOpen_le_fst _) * (prRes f hf (snd V V) (sqOpen_le_snd _))⁻¹

/-- `Φ(Δ v)` is the unit point of `G` for `v ∈ D`. -/
lemma quotHom_diag (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    {v : V.left} (hv : v ∈ f.domain) :
    (quotHom f hf).left ⟨(diag V).left v, diag_mem hv⟩ = η[G].left (default : Spec (.of k)) := by
  let D' : Over (Spec (.of k)) := Over.mk (f.domain.ι ≫ V.hom)
  let fD : D' ⟶ G := Over.homMk f.hom hf
  let δ : D' ⟶ sqOver f.domain :=
    Over.homMk ((diag V).left.resLE (sqOpen f.domain) f.domain (diag_le _)) (by
      change _ ≫ (sqOpen f.domain).ι ≫ (V ⊗ V).hom = f.domain.ι ≫ V.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w (diag V)])
  have h1 : δ ≫ prRes f hf (fst V V) (sqOpen_le_fst _) = fD := by
    apply Over.OverMorphism.ext
    change (diag V).left.resLE _ _ _ ≫ (fst V V).left.resLE _ _ _ ≫ f.hom = f.hom
    rw [← Category.assoc, diag_resLE_pr _ _ (lift_fst _ _), Category.id_comp]
  have h2 : δ ≫ prRes f hf (snd V V) (sqOpen_le_snd _) = fD := by
    apply Over.OverMorphism.ext
    change (diag V).left.resLE _ _ _ ≫ (snd V V).left.resLE _ _ _ ≫ f.hom = f.hom
    rw [← Category.assoc, diag_resLE_pr _ _ (lift_snd _ _), Category.id_comp]
  have h : δ ≫ quotHom f hf = 1 := by
    rw [quotHom, comp_mul, GrpObj.comp_inv, h1, h2, mul_inv_cancel]
  have hδ : δ.left ⟨v, hv⟩ = ⟨(diag V).left v, diag_mem hv⟩ := by
    apply Subtype.ext
    change ((diag V).left.resLE (sqOpen f.domain) f.domain (diag_le _) ≫ (sqOpen f.domain).ι) ⟨v, hv⟩ = _
    rw [Scheme.Hom.resLE_comp_ι]
    rfl
  rw [← hδ]
  change (δ ≫ quotHom f hf).left ⟨v, hv⟩ = _
  rw [h, Hom.one_def]
  change η[G].left ((toUnit D').left ⟨v, hv⟩) = _
  congr 1
  exact @Subsingleton.elim (Spec (.of k)) _ _ _

/-- `Φ` as a partial map `V ×_k V ⇀ G`. -/
noncomputable def quotPM [IrreducibleSpace (V ⊗ V).left] [IrreducibleSpace V.left]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    (V ⊗ V).left.PartialMap G.left where
  domain := sqOpen f.domain
  dense_domain := (sqOpen f.domain).isOpen.dense ⟨_, diag_mem f.dense_domain.nonempty.choose_spec⟩
  hom := (quotHom f hf).left

lemma quotPM_comp [IrreducibleSpace (V ⊗ V).left] [IrreducibleSpace V.left]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    (quotPM f hf).hom ≫ G.hom = (quotPM f hf).domain.ι ≫ (V ⊗ V).hom :=
  Over.w (quotHom f hf)

/-- E8: the difference map is defined at `Δ x` for every `x`, provided the domain of `f` contains all points of
codimension at most one and the stalk of `V ×_k V` at `Δ x` is factorial. -/
theorem diag_mem_domain [IsIntegral (V ⊗ V).left] [IsLocallyNoetherian (V ⊗ V).left]
    [IrreducibleSpace V.left] [IsLocallyNoetherian V.left] [LocallyOfFiniteType G.hom]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    (hcod : ∀ v : V.left, coheight v ≤ 1 → v ∈ f.domain) (x : V.left)
    [UniqueFactorizationMonoid ((V ⊗ V).left.presheaf.stalk ((diag V).left x))] :
    (diag V).left x ∈ (quotPM f hf).toRationalMap.domain := by
  by_contra hx
  obtain ⟨v₀, hv₀⟩ := f.dense_domain.nonempty
  obtain ⟨_, ⟨W, hW, rfl⟩, heW, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (η[G].left (default : Spec (.of k)))) isOpen_univ
  replace hW : IsAffineOpen W := hW
  have hΔW : ∀ (v : V.left) (hv : v ∈ f.domain),
      (quotPM f hf).hom ⟨(diag V).left v, diag_mem hv⟩ ∈ W := fun v hv => by
    change (quotHom f hf).left ⟨(diag V).left v, diag_mem hv⟩ ∈ W
    rw [quotHom_diag f hf hv]
    exact heW
  obtain ⟨ζ, hζx, hζ1, hζW⟩ := exists_not_mem_of_not_mem_domain (V ⊗ V).hom G.hom (quotPM f hf)
    (quotPM_comp f hf) hW (z₀ := (diag V).left v₀) (diag_mem hv₀) (hΔW v₀ hv₀) hx
  obtain ⟨v, -, hv1, hζv⟩ := exists_specializes_of_coheight_eq_one (diag V).left x hζx hζ1
  have hvD := hcod v hv1
  have hζN : ζ ∈ sqOpen f.domain := hζv.mem_open (sqOpen f.domain).isOpen (diag_mem hvD)
  apply hζW hζN
  have hsp : (⟨ζ, hζN⟩ : (quotPM f hf).domain) ⤳ ⟨(diag V).left v, diag_mem hvD⟩ :=
    (subtype_specializes_iff _ _).mpr hζv
  exact (hsp.map (quotPM f hf).hom.continuous).mem_open W.isOpen (hΔW v hvD)

end

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_ThetaCube_Alg =====
section

/-!
# Unit S4-ThetaCube, file Alg: pure algebra for numerical classes (obligation T6, algebra part)

* `int_eq_zero_of_dvd`: an integer divisible by every positive natural number is `0`;
* `addHom_int_eq_zero_of_divisible`, `addHom_int_eq_zero_of_torsion`: there is no nonzero additive map from a divisible
  group, or from a torsion group, to `ℤ`;
* `mem_numKer_of_add`, `mem_numKer_of_add_torsion`: a map `f : H → M` that is additive modulo `numKer I`, from a
  divisible (or torsion) group `H`, takes values in `numKer I` (used with `H = J(k)` for the translation parameter of
  `a^* Θ_x`);
* `mem_numKer_of_nsmul`: `numKer I` is saturated (`I` is `ℤ`-valued).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.DegPoly

/-- An integer divisible by every positive natural number is `0`. -/
theorem int_eq_zero_of_dvd {v : ℤ} (h : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ v) : v = 0 := by
  obtain ⟨w, hw⟩ := h (v.natAbs + 1) (Nat.succ_pos _)
  by_contra hv
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hw
    exact hv hw
  have h1 := congrArg Int.natAbs hw
  rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
  have h2 : 1 ≤ w.natAbs := Int.natAbs_pos.mpr hw0
  have h3 := Nat.mul_le_mul_left (v.natAbs + 1) h2
  rw [mul_one] at h3
  linarith

variable {H : Type*} [AddCommGroup H]

/-- No nonzero additive map from a divisible group to `ℤ`. -/
theorem addHom_int_eq_zero_of_divisible (hdiv : ∀ (h : H) (n : ℕ), 0 < n → ∃ y : H, n • y = h)
    (f : H →+ ℤ) (h : H) : f h = 0 := by
  refine int_eq_zero_of_dvd fun n hn => ?_
  obtain ⟨y, rfl⟩ := hdiv h n hn
  exact ⟨f y, by rw [map_nsmul, nsmul_eq_mul]⟩

/-- No nonzero additive map from a torsion group to `ℤ`. -/
theorem addHom_int_eq_zero_of_torsion (htor : ∀ h : H, ∃ n : ℕ, 0 < n ∧ n • h = 0)
    (f : H →+ ℤ) (h : H) : f h = 0 := by
  obtain ⟨n, hn, hnh⟩ := htor h
  have e : (n : ℤ) * f h = 0 := by rw [← nsmul_eq_mul, ← map_nsmul, hnh, map_zero]
  rcases mul_eq_zero.mp e with e | e
  · exact absurd (by exact_mod_cast e) hn.ne'
  · exact e

variable {M : Type*} [AddCommGroup M] {g : ℕ}

/-- The slot functional `x ↦ I (w₁, …, f x, …, w_g)` of a map additive modulo `numKer I`. -/
def slotHom (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) (f : H → M)
    (hf : ∀ x y : H, f (x + y) - f x - f y ∈ numKer I) (w : Fin g → M) (i : Fin g) : H →+ ℤ :=
  AddMonoidHom.mk' (fun x => I (Function.update w i (f x))) fun x y => by
    have h := mem_numKer.mp (hf x y) w i
    rw [I.map_update_sub, I.map_update_sub] at h
    change I (Function.update w i (f (x + y))) =
      I (Function.update w i (f x)) + I (Function.update w i (f y))
    linarith

/-- **T6 (algebra).** A map from a divisible group that is additive modulo `numKer I` lands in `numKer I`. -/
theorem mem_numKer_of_add (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)
    (hdiv : ∀ (h : H) (n : ℕ), 0 < n → ∃ y : H, n • y = h) (f : H → M)
    (hf : ∀ x y : H, f (x + y) - f x - f y ∈ numKer I) (x : H) : f x ∈ numKer I :=
  mem_numKer.mpr fun w i => addHom_int_eq_zero_of_divisible hdiv (slotHom I f hf w i) x

/-- **T6 (algebra), torsion form.** -/
theorem mem_numKer_of_add_torsion (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)
    (htor : ∀ h : H, ∃ n : ℕ, 0 < n ∧ n • h = 0) (f : H → M)
    (hf : ∀ x y : H, f (x + y) - f x - f y ∈ numKer I) (x : H) : f x ∈ numKer I :=
  mem_numKer.mpr fun w i => addHom_int_eq_zero_of_torsion htor (slotHom I f hf w i) x

/-- `numKer I` is saturated: `n • u ∈ numKer I` with `n ≠ 0` gives `u ∈ numKer I`. -/
theorem mem_numKer_of_nsmul (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) {n : ℕ} (hn : 0 < n) {u : M}
    (h : n • u ∈ numKer I) : u ∈ numKer I := by
  refine mem_numKer.mpr fun w i => ?_
  have e := mem_numKer.mp h w i
  rw [← Nat.cast_smul_eq_nsmul ℤ, I.map_update_smul, smul_eq_mul] at e
  rcases mul_eq_zero.mp e with e | e
  · exact absurd (by exact_mod_cast e) hn.ne'
  · exact e

end RamanujanPetersson.ThetaCube

end


