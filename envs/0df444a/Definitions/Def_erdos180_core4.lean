-- Prove2me | Definitions.Def_erdos180_core4
-- name    : erdos180_core4
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-04T01:57:44.706708+00:00
-- url     : https://prove2.me/theorems/41f758a9-3548-4562-95be-bc8bed197190
-- title:
--   Normalising a disjoint line pair, characteristic-two avoidance, and the explicit constants
-- statement:
--   The final part of the definition bundle.
--
--   `symplecticLineNormalizer` produces, for any two disjoint lines $L, M$ of the quadrangle, a
--   symplectic automorphism carrying $L$ to the standard "horizontal" line and $M$ to the standard
--   "vertical" one; `symplecticHorizontalProjection`, `symplecticVerticalProjection` and
--   `symplecticLineGraphMap` are the coordinate maps that this normalisation makes available. This
--   is what reduces the general configuration to a single normal form.
--
--   `CharTwoLinePairAvoidance` is the property established for fields of characteristic two and
--   used in Proposition 4.2 of the source: for even $q$ the incidence graph $I_q$ contains no
--   $J$-pattern, i.e. no two independent triples $\{x,y,z\}$ and $\{x',y,z\}$, each with at least
--   two common centres, whose third bases satisfy $x \sim x'$. Geometrically, if $y, z$ are
--   non-collinear points and $U = y + z$, their common centres are exactly the projective points of
--   $U^{\perp}$; a third point with two common centres with $y$ and $z$ is orthogonal to all of
--   $U^{\perp}$ and hence lies in $U$, and any two distinct projective points of the nondegenerate
--   symplectic plane $U$ are non-orthogonal. Self-duality of $W(q)$ for even $q$ transfers the same
--   conclusion to the line class.
--
--   `compactnessDegreePowerConstant` and `compactnessHostPowerConstant` are the explicit constants
--   in the resulting bounds $d^{16} \le C_1 n^5$ and $e(G)^{16} \le C_2 n^{21}$; the latter is the
--   quantitative form of $\mathrm{ex}(n,\mathcal{F}) = O(n^{21/16}) = O(n^{4/3 - 1/48})$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6970-L9283

import Definitions.Def_erdos180_core3
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

def symplecticCoordinateInterleave :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] SymplecticVector K where
  toFun x := ![x.1 0, x.2 0, x.1 1, x.2 1]
  invFun x := (![x 0, x 2], ![x 1, x 3])
  left_inv := by
    intro x
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;> simp [smul_eq_mul]

def symplecticLineCoordinateEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticVector K ≃ₗ[K] SymplecticVector K :=
  ((L.1.prodEquivOfIsCompl M.1
      (symplecticLine_isCompl_of_disjoint K hLM)).symm.trans
      ((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))).trans
      (symplecticCoordinateInterleave K)

lemma symplecticLinePairing_coordinate_expansion
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
  let b := symplecticLineBasis K L
  have hsum :
      (∑ i : Fin 2, b.equivFun x i • b i) = x :=
    b.sum_equivFun x
  calc
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
        symplecticLinePairing K L M y x := rfl
    _ = symplecticLinePairing K L M y
          (∑ i : Fin 2, b.equivFun x i • b i) :=
      congrArg (symplecticLinePairing K L M y) hsum.symm
    _ = ∑ i : Fin 2,
          b.equivFun x i *
            standardSymplecticForm K
              ((b i : L.1) : SymplecticVector K)
              (y : SymplecticVector K) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp [smul_eq_mul, symplecticLinePairing]
    _ = (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
      simp [Fin.sum_univ_two, b,
        symplecticLineDualCoordinates_apply]

lemma symplecticLineCoordinateEquiv_apply_add
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    symplecticLineCoordinateEquiv K L M hLM
        ((x : SymplecticVector K) + (y : SymplecticVector K)) =
      ![(symplecticLineBasis K L).equivFun x 0,
        symplecticLineDualCoordinates K L M hLM y 0,
        (symplecticLineBasis K L).equivFun x 1,
        symplecticLineDualCoordinates K L M hLM y 1] := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  have hsplit :
      (L.1.prodEquivOfIsCompl M.1 hcompl).symm
        ((x : SymplecticVector K) +
          (y : SymplecticVector K)) = (x, y) := by
    apply (L.1.prodEquivOfIsCompl M.1 hcompl).symm_apply_eq.mpr
    rfl
  change
    symplecticCoordinateInterleave K
      (((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))
        ((L.1.prodEquivOfIsCompl M.1 hcompl).symm
          ((x : SymplecticVector K) +
            (y : SymplecticVector K)))) = _
  rw [hsplit]
  rfl

lemma symplecticLineCoordinateEquiv_form
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (u v : SymplecticVector K) :
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM u)
        (symplecticLineCoordinateEquiv K L M hLM v) =
      standardSymplecticForm K u v := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  obtain ⟨⟨x, y⟩, hu⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective u
  obtain ⟨⟨x', y'⟩, hv⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective v
  rw [← hu, ← hv]
  change
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K))
  calc
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y' 0 -
        symplecticLineDualCoordinates K L M hLM y 0 *
          (symplecticLineBasis K L).equivFun x' 0 +
        ((symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y' 1 -
        symplecticLineDualCoordinates K L M hLM y 1 *
          (symplecticLineBasis K L).equivFun x' 1) := by
        simp [symplecticLineCoordinateEquiv_apply_add,
          standardSymplecticForm]
    _ = standardSymplecticForm K
          (x : SymplecticVector K) (y' : SymplecticVector K) -
        standardSymplecticForm K
          (x' : SymplecticVector K) (y : SymplecticVector K) := by
        rw [symplecticLinePairing_coordinate_expansion K L M hLM x y',
          symplecticLinePairing_coordinate_expansion K L M hLM x' y]
        ring
    _ = standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K)) := by
        have hxx :
            standardSymplecticForm K
              (x : SymplecticVector K)
              (x' : SymplecticVector K) = 0 :=
          L.2.2 x x.2 x' x'.2
        have hyy :
            standardSymplecticForm K
              (y : SymplecticVector K)
              (y' : SymplecticVector K) = 0 :=
          M.2.2 y y.2 y' y'.2
        rw [standardSymplecticForm_add_left,
          standardSymplecticForm_add_right,
          standardSymplecticForm_add_right,
          hxx, hyy,
          standardSymplecticForm_swap K
            (y : SymplecticVector K)
            (x' : SymplecticVector K)]
        ring

def symplecticLineNormalizer
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticAutomorphism K :=
  { symplecticLineCoordinateEquiv K L M hLM with
    map_app' := by
      intro u v
      change
        standardSymplecticForm K
            (symplecticLineCoordinateEquiv K L M hLM u)
            (symplecticLineCoordinateEquiv K L M hLM v) =
          standardSymplecticForm K u v
      exact symplecticLineCoordinateEquiv_form K L M hLM u v }

def symplecticVerticalLinearMap :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun y := ![0, y 0, 0, y 1]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c y := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticVerticalLinearMap_injective :
    Function.Injective (symplecticVerticalLinearMap K) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [symplecticVerticalLinearMap] using congrFun huv 1
  · simpa [symplecticVerticalLinearMap] using congrFun huv 3

def symplecticVerticalLine : SymplecticLine K :=
  ⟨LinearMap.range (symplecticVerticalLinearMap K), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symplecticVerticalLinearMap_injective K)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp [symplecticVerticalLinearMap,
        standardSymplecticForm]⟩

def symplecticHorizontalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 0, v 2]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

def symplecticVerticalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 1, v 3]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticHorizontalProjection_ker :
    LinearMap.ker (symplecticHorizontalProjection K) =
      (symplecticVerticalLine K).1 := by
  apply le_antisymm
  · intro v hv
    have hzero := LinearMap.mem_ker.mp hv
    have hfirst := congrFun hzero 0
    have hthird := congrFun hzero 1
    simp [symplecticHorizontalProjection] at hfirst hthird
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K)
    refine ⟨![v 1, v 3], ?_⟩
    funext i
    fin_cases i <;>
      simp [symplecticVerticalLinearMap, hfirst, hthird]
  · intro v hv
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
    obtain ⟨y, rfl⟩ := hv
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalProjection,
        symplecticVerticalLinearMap]

lemma symplecticLineHorizontalProjection_injective
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    Function.Injective
      ((symplecticHorizontalProjection K).comp L.1.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    have hproj := LinearMap.mem_ker.mp hx
    change
      symplecticHorizontalProjection K
          (x : SymplecticVector K) = 0 at hproj
    have hxvertical :
        (x : SymplecticVector K) ∈
          (symplecticVerticalLine K).1 := by
      rw [← symplecticHorizontalProjection_ker K]
      exact LinearMap.mem_ker.mpr hproj
    have hxzero : (x : SymplecticVector K) = 0 := by
      have hbot :
          (x : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hvertical.le_bot ⟨x.2, hxvertical⟩
      simpa using hbot
    have hxsub : x = 0 := by
      apply Subtype.ext
      simpa using hxzero
    exact (Submodule.mem_bot K).2 hxsub
  · exact bot_le

def symplecticLineHorizontalProjectionEquiv
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    L.1 ≃ₗ[K] (Fin 2 → K) :=
  ((symplecticHorizontalProjection K).comp L.1.subtype).linearEquivOfInjective
      (symplecticLineHorizontalProjection_injective K L hvertical)
      (by simp [L.2.1])

def symplecticLineGraphMap
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (symplecticVerticalProjection K).comp
    (L.1.subtype.comp
      (symplecticLineHorizontalProjectionEquiv K L hvertical).symm.toLinearMap)

def CharTwoLinePairAvoidance : Prop :=
  ∀ (Y Z X X' : SymplecticLine K),
    Disjoint Y.1 Z.1 →
    Disjoint X.1 Y.1 →
    Disjoint X.1 Z.1 →
    Disjoint X'.1 Y.1 →
    Disjoint X'.1 Z.1 →
    X ≠ X' →
    ∀ (C C' : Fin 2 → SymplecticLine K),
      Function.Injective C →
      Function.Injective C' →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) →
      Disjoint X.1 X'.1

end

noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology

noncomputable def compactnessDegreePowerConstant : ℝ :=
  (48 : ℝ) ^ (4 : ℕ) + 1769472 + 1

noncomputable def compactnessHostPowerConstant : ℝ :=
  (2 : ℝ) ^ (16 : ℕ) * compactnessDegreePowerConstant

end

noncomputable section
open Finset SimpleGraph
open scoped Classical

noncomputable def compactnessSharpHostPowerConstant : ℝ :=
  compactnessHostPowerConstant

end

end Erdos180


