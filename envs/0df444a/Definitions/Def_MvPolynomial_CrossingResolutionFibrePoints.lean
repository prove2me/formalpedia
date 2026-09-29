-- Prove2me | Definitions.Def_MvPolynomial_CrossingResolutionFibrePoints
-- name    : MvPolynomial_CrossingResolutionFibrePoints
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/92b5f8b6-e342-5ae2-9655-541f427b7c14
-- title:
--   Fibre points of the crossing resolution over a prime
-- statement:
--   Throughout, $W$ is a commutative ring, $t\in W$, $\mathfrak p$ an ideal of $W$ with $t\in\mathfrak p$ (taken prime, or maximal, where that is needed), and $e$ a natural number. The chart ring is `CrossingQuotient W t` $=W[X_0,X_1]/(X_0X_1-t)$, with $U,V$ the classes of $X_0,X_1$, so $UV$ is the image of $t$.
--
--   Three $W$-algebra maps out of the chart ring are defined by the universal property `lift`: `originHom` sends $U,V\mapsto 0$ into $W/\mathfrak p$; `lineVHom` sends $U\mapsto X$, $V\mapsto 0$ into $(W/\mathfrak p)[X]$; `lineUHom` sends $U\mapsto 0$, $V\mapsto X$. Their kernels `originIdeal`, `lineVIdeal`, `lineUIdeal` are prime when $\mathfrak p$ is, `originIdeal` is maximal when $\mathfrak p$ is, and they are identified as $(U,V)+\mathfrak p$, $(V)+\mathfrak p$, $(U)+\mathfrak p$; the identifications come with $W$-algebra isomorphisms (`quotIUEquiv`, `quotIVEquiv`, and for $\mathfrak p=(t)$ also `quotSpanUEquiv`, `quotSpanVEquiv`) of the corresponding quotients with $(W/\mathfrak p)[X]$, carrying the class of $V$ (resp. $U$) to $X$. Further, when $\mathfrak p$ is maximal any proper ideal containing $U$, $V$ and the image of $\mathfrak p$ equals `originIdeal`.
--
--   On the localisation away from $V$, `overlapHom` is the map to Laurent polynomials over $W/\mathfrak p$ induced by `lineUHom`; its kernel `overlapIdeal` contracts to `lineUIdeal` along the localisation map and to `lineVIdeal` along the chart transition `transitionUp`. `vertexIdeal`, `branchVPrime`, `branchUPrime` are the same three primes for $t^e$ in place of $t$ ($1\le e$), and the contractions of the chart primes along `resolutionChart t e i` are computed: the origin, and the line primes at interior indices, contract to the vertex, while the $V$-line at $i=0$ and the $U$-line at $i=e-1$ give the two branch primes.
--
--   On the scheme `Resolution t e`, `chartPt t e i P` is the image of a prime $P$ under the open immersion $\iota_i$, and `origin`, `lineGen`, `lineUGen` are the points so obtained from the three ideals, with `vertexPt`, `branchVPt`, `branchUPt` the corresponding points of the crossing $uv=t^e$. The incidences are established: `lineUGen` at $i$ equals `lineGen` at $i+1$, the three families are injective and pairwise distinct, `lineGen i` and `lineUGen i` specialise to `origin i`, each point lies in exactly the expected chart ranges, and the closures of the generic points are described chart by chart. A small auxiliary namespace collects topological facts about $\overline{\{\eta\}}\cap\operatorname{range} f$ for embeddings and open embeddings, together with the description of the closure of a point of a prime spectrum as the set of primes above it.
--
--   **Relation to Mathlib.** The chart ring, the transition maps and the glued resolution are the project's own constructions; Mathlib supplies the ambient machinery used here (`Localization.Away`, `LaurentPolynomial`, prime spectra and colimits of schemes) but has no notion of the crossing $uv=t^e$ or of its resolution, so the distinguished chart primes, the vertex and branch primes, and the fibre points are defined in the project.
--
--   **Where it is used.** These declarations identify the points of the fibre of the resolution of the crossing $uv=t^{e}$ over a prime $\mathfrak p\ni t$ of the base, showing that it is a chain of $e+1$ lines whose consecutive generic points specialise to the intermediate origins. This is the local model for the special fibre of a regular model of a curve with a node of thickness $e$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvPolynomial_CrossingResolutionFibrePoints.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000
set_option autoImplicit false

noncomputable section

open Polynomial LaurentPolynomial

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W)

theorem ringHom_ext' {L : Type*} [Semiring L] {f g : CrossingQuotient W t →+* L}
    (hW : ∀ w : W, f (algebraMap W _ w) = g (algebraMap W _ w)) (hU : f (U t) = g (U t)) (hV : f (V t) = g (V t)) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    have h := hW w
    rwa [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq] at h
  · intro i
    fin_cases i
    · exact hU
    · exact hV

variable (ht : t ∈ 𝔭)
include ht

theorem algebraMap_quotient_eq_zero : algebraMap W (W ⧸ 𝔭) t = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr ht

omit ht in
theorem algebraMap_poly_eq_zero_of_mem {w : W} (hw : w ∈ 𝔭) : algebraMap W (W ⧸ 𝔭)[X] w = 0 := by
  have hw0 : algebraMap W (W ⧸ 𝔭) w = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hw
  rw [IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], hw0, map_zero]

theorem algebraMap_poly_eq_zero : algebraMap W (W ⧸ 𝔭)[X] t = 0 := by
  rw [IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], algebraMap_quotient_eq_zero t 𝔭 ht, map_zero]

def originHom : CrossingQuotient W t →ₐ[W] W ⧸ 𝔭 :=
  lift t 0 0 (by rw [mul_zero, algebraMap_quotient_eq_zero t 𝔭 ht])

def lineVHom : CrossingQuotient W t →ₐ[W] (W ⧸ 𝔭)[X] :=
  lift t Polynomial.X 0 (by rw [mul_zero, algebraMap_poly_eq_zero t 𝔭 ht])

def lineUHom : CrossingQuotient W t →ₐ[W] (W ⧸ 𝔭)[X] :=
  lift t 0 Polynomial.X (by rw [zero_mul, algebraMap_poly_eq_zero t 𝔭 ht])

@[simp] theorem originHom_U : originHom t 𝔭 ht (U t) = 0 := lift_U _ _ _ _
@[simp] theorem originHom_V : originHom t 𝔭 ht (V t) = 0 := lift_V _ _ _ _
@[simp] theorem lineVHom_U : lineVHom t 𝔭 ht (U t) = Polynomial.X := lift_U _ _ _ _
@[simp] theorem lineVHom_V : lineVHom t 𝔭 ht (V t) = 0 := lift_V _ _ _ _
@[simp] theorem lineUHom_U : lineUHom t 𝔭 ht (U t) = 0 := lift_U _ _ _ _
@[simp] theorem lineUHom_V : lineUHom t 𝔭 ht (V t) = Polynomial.X := lift_V _ _ _ _

def originIdeal : Ideal (CrossingQuotient W t) := RingHom.ker (originHom t 𝔭 ht).toRingHom

def lineVIdeal : Ideal (CrossingQuotient W t) := RingHom.ker (lineVHom t 𝔭 ht).toRingHom

def lineUIdeal : Ideal (CrossingQuotient W t) := RingHom.ker (lineUHom t 𝔭 ht).toRingHom

theorem mem_originIdeal_iff (c) : c ∈ originIdeal t 𝔭 ht ↔ originHom t 𝔭 ht c = 0 := RingHom.mem_ker
theorem mem_lineVIdeal_iff (c) : c ∈ lineVIdeal t 𝔭 ht ↔ lineVHom t 𝔭 ht c = 0 := RingHom.mem_ker
theorem mem_lineUIdeal_iff (c) : c ∈ lineUIdeal t 𝔭 ht ↔ lineUHom t 𝔭 ht c = 0 := RingHom.mem_ker

instance isPrime_originIdeal [𝔭.IsPrime] : (originIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _
instance isPrime_lineVIdeal [𝔭.IsPrime] : (lineVIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _
instance isPrime_lineUIdeal [𝔭.IsPrime] : (lineUIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _

theorem originHom_surjective : Function.Surjective (originHom t 𝔭 ht) := fun w => by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  exact ⟨algebraMap W _ w, (originHom t 𝔭 ht).commutes w⟩

theorem isMaximal_originIdeal [𝔭.IsMaximal] : (originIdeal t 𝔭 ht).IsMaximal := by
  letI := Ideal.Quotient.field 𝔭
  exact RingHom.ker_isMaximal_of_surjective (originHom t 𝔭 ht) (originHom_surjective t 𝔭 ht)

theorem U_mem_originIdeal : U t ∈ originIdeal t 𝔭 ht := by simp [mem_originIdeal_iff]
theorem V_mem_originIdeal : V t ∈ originIdeal t 𝔭 ht := by simp [mem_originIdeal_iff]
theorem V_mem_lineVIdeal : V t ∈ lineVIdeal t 𝔭 ht := by simp [mem_lineVIdeal_iff]
theorem U_mem_lineUIdeal : U t ∈ lineUIdeal t 𝔭 ht := by simp [mem_lineUIdeal_iff]

theorem U_notMem_lineVIdeal [𝔭.IsPrime] : U t ∉ lineVIdeal t 𝔭 ht := by
  simp [mem_lineVIdeal_iff, Polynomial.X_ne_zero]

theorem V_notMem_lineUIdeal [𝔭.IsPrime] : V t ∉ lineUIdeal t 𝔭 ht := by
  simp [mem_lineUIdeal_iff, Polynomial.X_ne_zero]

theorem algebraMap_mem_originIdeal {w : W} (hw : w ∈ 𝔭) : algebraMap W _ w ∈ originIdeal t 𝔭 ht := by
  rw [mem_originIdeal_iff, AlgHom.commutes]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hw

theorem algebraMap_mem_lineVIdeal {w : W} (hw : w ∈ 𝔭) : algebraMap W _ w ∈ lineVIdeal t 𝔭 ht := by
  have hw0 : algebraMap W (W ⧸ 𝔭) w = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hw
  rw [mem_lineVIdeal_iff, AlgHom.commutes, IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], hw0, map_zero]

theorem algebraMap_mem_lineUIdeal {w : W} (hw : w ∈ 𝔭) : algebraMap W _ w ∈ lineUIdeal t 𝔭 ht := by
  have hw0 : algebraMap W (W ⧸ 𝔭) w = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hw
  rw [mem_lineUIdeal_iff, AlgHom.commutes, IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], hw0, map_zero]

theorem aeval_zero_comp_lineVHom :
    (Polynomial.aeval (0 : W ⧸ 𝔭)).toRingHom.comp (lineVHom t 𝔭 ht).toRingHom = (originHom t 𝔭 ht).toRingHom := by
  refine ringHom_ext' t (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X]]
    exact Polynomial.aeval_C _ _
  · simp
  · simp

theorem aeval_zero_comp_lineUHom :
    (Polynomial.aeval (0 : W ⧸ 𝔭)).toRingHom.comp (lineUHom t 𝔭 ht).toRingHom = (originHom t 𝔭 ht).toRingHom := by
  refine ringHom_ext' t (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X]]
    exact Polynomial.aeval_C _ _
  · simp
  · simp

theorem lineVIdeal_le_originIdeal : lineVIdeal t 𝔭 ht ≤ originIdeal t 𝔭 ht := by
  intro c hc
  rw [mem_lineVIdeal_iff] at hc
  rw [mem_originIdeal_iff]
  have := congrArg (fun f => f c) (aeval_zero_comp_lineVHom t 𝔭 ht)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
  rw [← this, hc, map_zero]

theorem lineUIdeal_le_originIdeal : lineUIdeal t 𝔭 ht ≤ originIdeal t 𝔭 ht := by
  intro c hc
  rw [mem_lineUIdeal_iff] at hc
  rw [mem_originIdeal_iff]
  have := congrArg (fun f => f c) (aeval_zero_comp_lineUHom t 𝔭 ht)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
  rw [← this, hc, map_zero]

theorem lineVIdeal_ne_lineUIdeal [𝔭.IsPrime] : lineVIdeal t 𝔭 ht ≠ lineUIdeal t 𝔭 ht := fun h =>
  U_notMem_lineVIdeal t 𝔭 ht (h ▸ U_mem_lineUIdeal t 𝔭 ht)

theorem originIdeal_ne_lineVIdeal [𝔭.IsPrime] : originIdeal t 𝔭 ht ≠ lineVIdeal t 𝔭 ht := fun h =>
  U_notMem_lineVIdeal t 𝔭 ht (h ▸ U_mem_originIdeal t 𝔭 ht)

theorem originIdeal_ne_lineUIdeal [𝔭.IsPrime] : originIdeal t 𝔭 ht ≠ lineUIdeal t 𝔭 ht := fun h =>
  V_notMem_lineUIdeal t 𝔭 ht (h ▸ V_mem_originIdeal t 𝔭 ht)

def lineULaurent : CrossingQuotient W t →+* LaurentPolynomial (W ⧸ 𝔭) :=
  (toLaurent : (W ⧸ 𝔭)[X] →+* LaurentPolynomial (W ⧸ 𝔭)).comp (lineUHom t 𝔭 ht).toRingHom

theorem lineULaurent_apply (c) : lineULaurent t 𝔭 ht c = toLaurent (lineUHom t 𝔭 ht c) := rfl

theorem isUnit_lineULaurent_V : IsUnit (lineULaurent t 𝔭 ht (V t)) := by
  rw [lineULaurent_apply, lineUHom_V, toLaurent_X]; exact isUnit_T 1

def overlapHom : Localization.Away (V t) →+* LaurentPolynomial (W ⧸ 𝔭) :=
  IsLocalization.Away.lift (V t) (isUnit_lineULaurent_V t 𝔭 ht)

theorem overlapHom_algebraMap (c) :
    overlapHom t 𝔭 ht (algebraMap (CrossingQuotient W t) (Localization.Away (V t)) c) = lineULaurent t 𝔭 ht c :=
  IsLocalization.Away.lift_eq _ _ _

theorem overlapHom_invSelf :
    overlapHom t 𝔭 ht (IsLocalization.Away.invSelf (V t)) = (T (-1) : LaurentPolynomial (W ⧸ 𝔭)) := by
  have h1 : overlapHom t 𝔭 ht (algebraMap (CrossingQuotient W t) (Localization.Away (V t)) (V t)) *
      overlapHom t 𝔭 ht (IsLocalization.Away.invSelf (V t)) = 1 := by
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have h2 : overlapHom t 𝔭 ht (algebraMap (CrossingQuotient W t) (Localization.Away (V t)) (V t)) =
      (T 1 : LaurentPolynomial (W ⧸ 𝔭)) := by
    rw [overlapHom_algebraMap, lineULaurent_apply, lineUHom_V, toLaurent_X]
  rw [h2] at h1
  have h3 : (T 1 : LaurentPolynomial (W ⧸ 𝔭)) * T (-1) = 1 := by rw [← T_add]; simp
  exact (isUnit_T 1).mul_left_cancel (h1.trans h3.symm)

def overlapIdeal : Ideal (Localization.Away (V t)) := RingHom.ker (overlapHom t 𝔭 ht)

instance isPrime_overlapIdeal [𝔭.IsPrime] : (overlapIdeal t 𝔭 ht).IsPrime := RingHom.ker_isPrime _

omit ht in
theorem FibrePointsAux.ker_comp_of_injective {A B C : Type*} [Ring A] [Ring B] [Ring C] (g : B →+* C) (hg : Function.Injective g)
    (f : A →+* B) : RingHom.ker (g.comp f) = RingHom.ker f := by
  ext x; simp [RingHom.mem_ker, map_eq_zero_iff g hg]

theorem comap_algebraMap_overlapIdeal :
    (overlapIdeal t 𝔭 ht).comap (algebraMap (CrossingQuotient W t) (Localization.Away (V t))) = lineUIdeal t 𝔭 ht := by
  rw [overlapIdeal, RingHom.comap_ker, overlapHom, IsLocalization.Away.lift_comp]
  exact FibrePointsAux.ker_comp_of_injective _ toLaurent_injective _

theorem comap_transitionUp_overlapIdeal :
    (overlapIdeal t 𝔭 ht).comap (transitionUp t).toRingHom = lineVIdeal t 𝔭 ht := by
  rw [overlapIdeal, RingHom.comap_ker]
  have key : (overlapHom t 𝔭 ht).comp (transitionUp t).toRingHom =
      ((invert : LaurentPolynomial (W ⧸ 𝔭) ≃ₐ[W ⧸ 𝔭] LaurentPolynomial (W ⧸ 𝔭)) :
          LaurentPolynomial (W ⧸ 𝔭) →+* LaurentPolynomial (W ⧸ 𝔭)).comp
        ((toLaurent : (W ⧸ 𝔭)[X] →+* LaurentPolynomial (W ⧸ 𝔭)).comp (lineVHom t 𝔭 ht).toRingHom) := by
    refine ringHom_ext' t (fun w => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
        RingHom.coe_coe, RingHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (V t)), overlapHom_algebraMap,
        lineULaurent_apply, AlgHom.commutes, IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X],
        Polynomial.algebraMap_eq, toLaurent_C, invert_C]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [transitionUp_U, overlapHom_invSelf, lineVHom_U, toLaurent_X, invert_T]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [transitionUp_V, map_mul, lineVHom_V, map_zero, map_zero,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (V t)), overlapHom_algebraMap,
        lineULaurent_apply, AlgHom.commutes, algebraMap_poly_eq_zero t 𝔭 ht, map_zero, zero_mul]
  rw [key, FibrePointsAux.ker_comp_of_injective
      ((invert : LaurentPolynomial (W ⧸ 𝔭) ≃ₐ[W ⧸ 𝔭] LaurentPolynomial (W ⧸ 𝔭)) :
          LaurentPolynomial (W ⧸ 𝔭) →+* LaurentPolynomial (W ⧸ 𝔭))
      (invert : LaurentPolynomial (W ⧸ 𝔭) ≃ₐ[W ⧸ 𝔭] LaurentPolynomial (W ⧸ 𝔭)).injective,
    FibrePointsAux.ker_comp_of_injective _ toLaurent_injective]
  rfl

variable (e : ℕ)

theorem t_pow_mem (he : 1 ≤ e) : t ^ e ∈ 𝔭 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, pow_one]; exact 𝔭.mul_mem_right _ ht

def vertexIdeal (he : 1 ≤ e) : Ideal (CrossingQuotient W (t ^ e)) := originIdeal (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e he)

def branchVPrime (he : 1 ≤ e) : Ideal (CrossingQuotient W (t ^ e)) := lineVIdeal (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e he)

def branchUPrime (he : 1 ≤ e) : Ideal (CrossingQuotient W (t ^ e)) := lineUIdeal (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e he)

omit ht in
theorem one_le (i : Fin e) : 1 ≤ e := Nat.one_le_of_lt i.2

theorem comap_resolutionChart_originIdeal (i : Fin e) :
    (originIdeal t 𝔭 ht).comap (resolutionChart t e i).toRingHom = vertexIdeal t 𝔭 ht e (one_le e i) := by
  rw [originIdeal, RingHom.comap_ker, vertexIdeal, originIdeal]
  congr 1
  refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U, map_mul,
      originHom_U, mul_zero]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, map_mul,
      originHom_V, mul_zero]

theorem comap_resolutionChart_lineVIdeal_of_pos (i : Fin e) (hi : 1 ≤ (i : ℕ)) :
    (lineVIdeal t 𝔭 ht).comap (resolutionChart t e i).toRingHom = vertexIdeal t 𝔭 ht e (one_le e i) := by
  rw [lineVIdeal, RingHom.comap_ker, vertexIdeal, originIdeal]
  have key : (lineVHom t 𝔭 ht).toRingHom.comp (resolutionChart t e i).toRingHom =
      (Polynomial.C : W ⧸ 𝔭 →+* (W ⧸ 𝔭)[X]).comp (originHom (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e (one_le e i))).toRingHom := by
    refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], Polynomial.algebraMap_eq]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U, map_mul,
        lineVHom_U, originHom_U, map_zero, AlgHom.commutes]
      rw [algebraMap_poly_eq_zero_of_mem 𝔭 (t_pow_mem t 𝔭 ht _ hi), zero_mul]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, map_mul,
        lineVHom_V, originHom_V, map_zero, mul_zero]
  rw [key, FibrePointsAux.ker_comp_of_injective _ Polynomial.C_injective]

theorem comap_resolutionChart_lineUIdeal_of_lt (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    (lineUIdeal t 𝔭 ht).comap (resolutionChart t e i).toRingHom = vertexIdeal t 𝔭 ht e (one_le e i) := by
  rw [lineUIdeal, RingHom.comap_ker, vertexIdeal, originIdeal]
  have key : (lineUHom t 𝔭 ht).toRingHom.comp (resolutionChart t e i).toRingHom =
      (Polynomial.C : W ⧸ 𝔭 →+* (W ⧸ 𝔭)[X]).comp (originHom (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e (one_le e i))).toRingHom := by
    refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], Polynomial.algebraMap_eq]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U, map_mul,
        lineUHom_U, originHom_U, map_zero, mul_zero]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, map_mul,
        lineUHom_V, originHom_V, map_zero, AlgHom.commutes]
      rw [algebraMap_poly_eq_zero_of_mem 𝔭 (t_pow_mem t 𝔭 ht _ (by omega)), zero_mul]
  rw [key, FibrePointsAux.ker_comp_of_injective _ Polynomial.C_injective]

theorem comap_resolutionChart_lineVIdeal_zero (i : Fin e) (hi : (i : ℕ) = 0) :
    (lineVIdeal t 𝔭 ht).comap (resolutionChart t e i).toRingHom = branchVPrime t 𝔭 ht e (one_le e i) := by
  rw [lineVIdeal, RingHom.comap_ker, branchVPrime, lineVIdeal]
  congr 1
  refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U, map_mul,
      lineVHom_U, AlgHom.commutes, hi, pow_zero, map_one, one_mul]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, map_mul,
      lineVHom_V, mul_zero]

theorem comap_resolutionChart_lineUIdeal_last (i : Fin e) (hi : (i : ℕ) + 1 = e) :
    (lineUIdeal t 𝔭 ht).comap (resolutionChart t e i).toRingHom = branchUPrime t 𝔭 ht e (one_le e i) := by
  rw [lineUIdeal, RingHom.comap_ker, branchUPrime, lineUIdeal]
  congr 1
  refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U, map_mul,
      lineUHom_U, mul_zero]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, map_mul,
      lineUHom_V, AlgHom.commutes, show e - 1 - (i : ℕ) = 0 by omega, pow_zero, map_one, one_mul]

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open Polynomial

universe u

variable {W : Type u} [CommRing W] (t : W)

theorem mem_span_t : t ∈ Ideal.span ({t} : Set W) := Ideal.mem_span_singleton_self t

omit t in

theorem FibrePointsAux.algHom_base_ext {B : Type*} [Semiring B] [Algebra W B] (f g : W →ₐ[W] B) : f = g :=
  AlgHom.ext fun w => (f.commutes w).trans (g.commutes w).symm

theorem algebraMap_mem_span_U : algebraMap W (CrossingQuotient W t) t ∈ Ideal.span {U t} := by
  rw [← U_mul_V]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem algebraMap_mem_span_V : algebraMap W (CrossingQuotient W t) t ∈ Ideal.span {V t} := by
  rw [← U_mul_V]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

def quotBase (I : Ideal (CrossingQuotient W t)) (hI : algebraMap W (CrossingQuotient W t) t ∈ I) :
    (W ⧸ Ideal.span ({t} : Set W)) →ₐ[W] CrossingQuotient W t ⧸ I :=
  Ideal.Quotient.liftₐ (Ideal.span {t}) ((Ideal.Quotient.mkₐ W I).comp (Algebra.ofId W _)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    change Ideal.Quotient.mk I (algebraMap W (CrossingQuotient W t) (c * t)) = 0
    rw [map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_left _ hI))

theorem quotBase_mk (I : Ideal (CrossingQuotient W t)) (hI) (w : W) :
    quotBase t I hI (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk I (algebraMap W _ w) := rfl

def quotSpanUEquiv_fwd : (CrossingQuotient W t ⧸ Ideal.span {U t}) →ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  Ideal.Quotient.liftₐ (Ideal.span {U t}) (lineUHom t (Ideal.span {t}) (mem_span_t t)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, lineUHom_U, mul_zero])

theorem quotSpanUEquiv_fwd_mk (c : CrossingQuotient W t) :
    quotSpanUEquiv_fwd t (Ideal.Quotient.mk _ c) = lineUHom t (Ideal.span {t}) (mem_span_t t) c := rfl

def quotSpanUEquiv_bwd : (W ⧸ Ideal.span ({t} : Set W))[X] →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
  Polynomial.aevalTower (quotBase t _ (algebraMap_mem_span_U t)) (Ideal.Quotient.mk _ (V t))

theorem quotSpanUEquiv_bwd_X : quotSpanUEquiv_bwd t Polynomial.X = Ideal.Quotient.mk _ (V t) :=
  Polynomial.aevalTower_X _ _

theorem quotSpanUEquiv_bwd_C (w : W) :
    quotSpanUEquiv_bwd t (Polynomial.C (Ideal.Quotient.mk _ w)) = Ideal.Quotient.mk _ (algebraMap W _ w) := by
  rw [quotSpanUEquiv_bwd, Polynomial.aevalTower_C, quotBase_mk]

theorem quotSpanUEquiv_fwd_bwd : (quotSpanUEquiv_fwd t).comp (quotSpanUEquiv_bwd t) = AlgHom.id W _ := by
  refine Polynomial.algHom_ext' (Ideal.Quotient.algHom_ext W (FibrePointsAux.algHom_base_ext _ _)) ?_
  rw [AlgHom.comp_apply, quotSpanUEquiv_bwd_X, quotSpanUEquiv_fwd_mk, lineUHom_V, AlgHom.id_apply]

theorem quotSpanUEquiv_bwd_fwd : (quotSpanUEquiv_bwd t).comp (quotSpanUEquiv_fwd t) = AlgHom.id W _ := by
  refine Ideal.Quotient.algHom_ext W ?_
  refine Ideal.Quotient.algHom_ext W ?_
  refine MvPolynomial.algHom_ext (fun i => ?_)
  fin_cases i
  · change quotSpanUEquiv_bwd t (quotSpanUEquiv_fwd t (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [quotSpanUEquiv_fwd_mk, lineUHom_U]
    first
      | rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
      | exact quotSpanUEquiv_bwd_X t
  · change quotSpanUEquiv_bwd t (quotSpanUEquiv_fwd t (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [quotSpanUEquiv_fwd_mk, lineUHom_V]
    first
      | rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
      | exact quotSpanUEquiv_bwd_X t

def quotSpanUEquiv : (CrossingQuotient W t ⧸ Ideal.span {U t}) ≃ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  AlgEquiv.ofAlgHom (quotSpanUEquiv_fwd t) (quotSpanUEquiv_bwd t) (quotSpanUEquiv_fwd_bwd t) (quotSpanUEquiv_bwd_fwd t)

theorem quotSpanUEquiv_mk (c : CrossingQuotient W t) :
    quotSpanUEquiv t (Ideal.Quotient.mk _ c) = lineUHom t (Ideal.span {t}) (mem_span_t t) c := rfl

theorem quotSpanUEquiv_mk_V : quotSpanUEquiv t (Ideal.Quotient.mk _ (V t)) = Polynomial.X := by
  rw [quotSpanUEquiv_mk, lineUHom_V]

def quotSpanVEquiv_fwd : (CrossingQuotient W t ⧸ Ideal.span {V t}) →ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  Ideal.Quotient.liftₐ (Ideal.span {V t}) (lineVHom t (Ideal.span {t}) (mem_span_t t)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, lineVHom_V, mul_zero])

theorem quotSpanVEquiv_fwd_mk (c : CrossingQuotient W t) :
    quotSpanVEquiv_fwd t (Ideal.Quotient.mk _ c) = lineVHom t (Ideal.span {t}) (mem_span_t t) c := rfl

def quotSpanVEquiv_bwd : (W ⧸ Ideal.span ({t} : Set W))[X] →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
  Polynomial.aevalTower (quotBase t _ (algebraMap_mem_span_V t)) (Ideal.Quotient.mk _ (U t))

theorem quotSpanVEquiv_bwd_X : quotSpanVEquiv_bwd t Polynomial.X = Ideal.Quotient.mk _ (U t) :=
  Polynomial.aevalTower_X _ _

theorem quotSpanVEquiv_bwd_C (w : W) :
    quotSpanVEquiv_bwd t (Polynomial.C (Ideal.Quotient.mk _ w)) = Ideal.Quotient.mk _ (algebraMap W _ w) := by
  rw [quotSpanVEquiv_bwd, Polynomial.aevalTower_C, quotBase_mk]

theorem quotSpanVEquiv_fwd_bwd : (quotSpanVEquiv_fwd t).comp (quotSpanVEquiv_bwd t) = AlgHom.id W _ := by
  refine Polynomial.algHom_ext' (Ideal.Quotient.algHom_ext W (FibrePointsAux.algHom_base_ext _ _)) ?_
  rw [AlgHom.comp_apply, quotSpanVEquiv_bwd_X, quotSpanVEquiv_fwd_mk, lineVHom_U, AlgHom.id_apply]

theorem quotSpanVEquiv_bwd_fwd : (quotSpanVEquiv_bwd t).comp (quotSpanVEquiv_fwd t) = AlgHom.id W _ := by
  refine Ideal.Quotient.algHom_ext W ?_
  refine Ideal.Quotient.algHom_ext W ?_
  refine MvPolynomial.algHom_ext (fun i => ?_)
  fin_cases i
  · change quotSpanVEquiv_bwd t (quotSpanVEquiv_fwd t (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [quotSpanVEquiv_fwd_mk, lineVHom_U]
    first
      | rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
      | exact quotSpanVEquiv_bwd_X t
  · change quotSpanVEquiv_bwd t (quotSpanVEquiv_fwd t (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [quotSpanVEquiv_fwd_mk, lineVHom_V]
    first
      | rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
      | exact quotSpanVEquiv_bwd_X t

def quotSpanVEquiv : (CrossingQuotient W t ⧸ Ideal.span {V t}) ≃ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  AlgEquiv.ofAlgHom (quotSpanVEquiv_fwd t) (quotSpanVEquiv_bwd t) (quotSpanVEquiv_fwd_bwd t) (quotSpanVEquiv_bwd_fwd t)

theorem quotSpanVEquiv_mk (c : CrossingQuotient W t) :
    quotSpanVEquiv t (Ideal.Quotient.mk _ c) = lineVHom t (Ideal.span {t}) (mem_span_t t) c := rfl

theorem quotSpanVEquiv_mk_U : quotSpanVEquiv t (Ideal.Quotient.mk _ (U t)) = Polynomial.X := by
  rw [quotSpanVEquiv_mk, lineVHom_U]

theorem lineUIdeal_span_eq : lineUIdeal t (Ideal.span {t}) (mem_span_t t) = Ideal.span {U t} := by
  have h : (lineUHom t (Ideal.span {t}) (mem_span_t t)).toRingHom =
      (quotSpanUEquiv t).toAlgHom.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {U t})) := rfl
  rw [lineUIdeal, h, ← RingHom.comap_ker]
  have : RingHom.ker (quotSpanUEquiv t).toAlgHom.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (quotSpanUEquiv t).injective
  rw [this, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem lineVIdeal_span_eq : lineVIdeal t (Ideal.span {t}) (mem_span_t t) = Ideal.span {V t} := by
  have h : (lineVHom t (Ideal.span {t}) (mem_span_t t)).toRingHom =
      (quotSpanVEquiv t).toAlgHom.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {V t})) := rfl
  rw [lineVIdeal, h, ← RingHom.comap_ker]
  have : RingHom.ker (quotSpanVEquiv t).toAlgHom.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (quotSpanVEquiv t).injective
  rw [this, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem lineUHom_surjective : Function.Surjective (lineUHom t (Ideal.span {t}) (mem_span_t t)) := fun p => by
  obtain ⟨z, hz⟩ := (quotSpanUEquiv t).surjective p
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨c, hz⟩

theorem originIdeal_span_eq : originIdeal t (Ideal.span {t}) (mem_span_t t) = Ideal.span {U t, V t} := by
  apply le_antisymm
  · intro c hc
    rw [mem_originIdeal_iff] at hc

    have h0 : (Polynomial.aeval (0 : W ⧸ Ideal.span ({t} : Set W))) (lineUHom t (Ideal.span {t}) (mem_span_t t) c) = 0 := by
      have := congrArg (fun f => f c) (aeval_zero_comp_lineUHom t (Ideal.span {t}) (mem_span_t t))
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      rw [this, hc]
    rw [Polynomial.coe_aeval_eq_eval, ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff] at h0
    obtain ⟨q, hq⟩ := h0
    obtain ⟨c', rfl⟩ := lineUHom_surjective t q
    have hmem : c - V t * c' ∈ lineUIdeal t (Ideal.span {t}) (mem_span_t t) := by
      rw [mem_lineUIdeal_iff, map_sub, map_mul, lineUHom_V, hq, sub_self]
    rw [lineUIdeal_span_eq] at hmem
    have : c = (c - V t * c') + V t * c' := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hmem) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  · rw [Ideal.span_le]
    rintro a (rfl | rfl)
    · exact U_mem_originIdeal t _ _
    · exact V_mem_originIdeal t _ _

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

theorem span_pow_le (he : 1 ≤ e) : Ideal.span ({t ^ e} : Set W) ≤ Ideal.span {t} :=
  (Ideal.span_singleton_le_iff_mem _).mpr (t_pow_mem t _ (mem_span_t t) e he)

theorem factor_comp_originHom (he : 1 ≤ e) :
    (Ideal.Quotient.factor (span_pow_le t e he)).comp
        (originHom (t ^ e) (Ideal.span {t ^ e}) (mem_span_t (t ^ e))).toRingHom =
      (originHom (t ^ e) (Ideal.span {t}) (t_pow_mem t _ (mem_span_t t) e he)).toRingHom := by
  refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, originHom_U, map_zero]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, originHom_V, map_zero]

theorem vertexIdeal_span_eq (he : 1 ≤ e) :
    vertexIdeal t (Ideal.span {t}) (mem_span_t t) e he =
      Ideal.span {U (t ^ e), V (t ^ e), algebraMap W (CrossingQuotient W (t ^ e)) t} := by
  apply le_antisymm
  · intro c hc
    change c ∈ originIdeal (t ^ e) (Ideal.span {t}) _ at hc
    rw [mem_originIdeal_iff] at hc

    have h1 : Ideal.Quotient.factor (span_pow_le t e he)
        (originHom (t ^ e) (Ideal.span {t ^ e}) (mem_span_t (t ^ e)) c) = 0 := by
      have := congrArg (fun f => f c) (factor_comp_originHom t e he)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      rw [this, hc]
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (originHom (t ^ e) (Ideal.span {t ^ e}) (mem_span_t (t ^ e)) c)
    rw [← hz, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨w, hw⟩ := h1

    have hmem : c - algebraMap W _ (w * t) ∈ originIdeal (t ^ e) (Ideal.span {t ^ e}) (mem_span_t (t ^ e)) := by
      rw [mem_originIdeal_iff, map_sub, AlgHom.commutes, ← hz, ← hw, sub_eq_zero]; rfl
    rw [originIdeal_span_eq] at hmem
    have : c = (c - algebraMap W _ (w * t)) + algebraMap W _ w * algebraMap W _ t := by rw [map_mul]; ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.span_mono ?_ hmem) (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    · intro a ha
      rcases ha with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  · rw [Ideal.span_le]
    rintro a (rfl | rfl | rfl)
    · exact U_mem_originIdeal _ _ _
    · exact V_mem_originIdeal _ _ _
    · exact algebraMap_mem_originIdeal _ _ _ (mem_span_t t)

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)
include ht

theorem span_t_le : Ideal.span ({t} : Set W) ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).mpr ht

theorem factor_comp_originHom_span :
    (Ideal.Quotient.factor (span_t_le t 𝔭 ht)).comp (originHom t (Ideal.span {t}) (mem_span_t t)).toRingHom =
      (originHom t 𝔭 ht).toRingHom := by
  refine ringHom_ext' t (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, originHom_U, map_zero]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, originHom_V, map_zero]

theorem originIdeal_eq_span_sup_map :
    originIdeal t 𝔭 ht = Ideal.span {U t, V t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t)) := by
  apply le_antisymm
  · intro c hc
    rw [mem_originIdeal_iff] at hc
    have h1 : Ideal.Quotient.factor (span_t_le t 𝔭 ht) (originHom t (Ideal.span {t}) (mem_span_t t) c) = 0 := by
      have := congrArg (fun f => f c) (factor_comp_originHom_span t 𝔭 ht)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      rw [this, hc]
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (originHom t (Ideal.span {t}) (mem_span_t t) c)
    rw [← hw, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at h1
    have hmem : c - algebraMap W _ w ∈ originIdeal t (Ideal.span {t}) (mem_span_t t) := by
      rw [mem_originIdeal_iff, map_sub, AlgHom.commutes, ← hw, sub_eq_zero]; rfl
    rw [originIdeal_span_eq] at hmem
    have : c = (c - algebraMap W _ w) + algebraMap W _ w := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hmem) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ h1))
  · refine sup_le ?_ ?_
    · rw [Ideal.span_le]
      rintro a (rfl | rfl)
      · exact U_mem_originIdeal _ _ _
      · exact V_mem_originIdeal _ _ _
    · rw [Ideal.map_le_iff_le_comap]
      intro w hw
      exact algebraMap_mem_originIdeal _ _ _ hw

theorem originIdeal_le_of_mem {P : Ideal (CrossingQuotient W t)} (hU : U t ∈ P) (hV : V t ∈ P)
    (h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P) : originIdeal t 𝔭 ht ≤ P := by
  rw [originIdeal_eq_span_sup_map]
  refine sup_le ?_ ?_
  · rw [Ideal.span_le]; rintro a (rfl | rfl) <;> assumption
  · rw [Ideal.map_le_iff_le_comap]; exact fun w hw => h𝔭 w hw

theorem eq_originIdeal_of_mem [𝔭.IsMaximal] {P : Ideal (CrossingQuotient W t)} (hP : P ≠ ⊤) (hU : U t ∈ P)
    (hV : V t ∈ P) (h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P) : P = originIdeal t 𝔭 ht :=
  ((isMaximal_originIdeal t 𝔭 ht).eq_of_le hP (originIdeal_le_of_mem t 𝔭 ht hU hV h𝔭)).symm

variable (e : ℕ)

theorem isMaximal_vertexIdeal [𝔭.IsMaximal] (he : 1 ≤ e) : (vertexIdeal t 𝔭 ht e he).IsMaximal :=
  isMaximal_originIdeal _ _ _

theorem eq_vertexIdeal_of_mem [𝔭.IsMaximal] (he : 1 ≤ e) {P : Ideal (CrossingQuotient W (t ^ e))} (hP : P ≠ ⊤)
    (hU : U (t ^ e) ∈ P) (hV : V (t ^ e) ∈ P)
    (h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W (t ^ e)) w ∈ P) : P = vertexIdeal t 𝔭 ht e he :=
  eq_originIdeal_of_mem (t ^ e) 𝔭 _ hP hU hV h𝔭

theorem vertexIdeal_eq_span_sup_map (he : 1 ≤ e) :
    vertexIdeal t 𝔭 ht e he =
      Ideal.span {U (t ^ e), V (t ^ e)} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W (t ^ e))) :=
  originIdeal_eq_span_sup_map (t ^ e) 𝔭 _

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open Polynomial

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)

theorem span_U_sup_map_le_lineUIdeal :
    Ideal.span {U t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t)) ≤ lineUIdeal t 𝔭 ht := by
  refine sup_le ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact U_mem_lineUIdeal t 𝔭 ht
  · rw [Ideal.map_le_iff_le_comap]; exact fun w hw => algebraMap_mem_lineUIdeal t 𝔭 ht hw

theorem span_V_sup_map_le_lineVIdeal :
    Ideal.span {V t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t)) ≤ lineVIdeal t 𝔭 ht := by
  refine sup_le ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact V_mem_lineVIdeal t 𝔭 ht
  · rw [Ideal.map_le_iff_le_comap]; exact fun w hw => algebraMap_mem_lineVIdeal t 𝔭 ht hw

def quotBaseP (I : Ideal (CrossingQuotient W t)) (hI : 𝔭.map (algebraMap W (CrossingQuotient W t)) ≤ I) :
    (W ⧸ 𝔭) →ₐ[W] CrossingQuotient W t ⧸ I :=
  Ideal.Quotient.liftₐ 𝔭 ((Ideal.Quotient.mkₐ W I).comp (Algebra.ofId W _)) (by
    intro a ha
    change Ideal.Quotient.mk I (algebraMap W (CrossingQuotient W t) a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI (Ideal.mem_map_of_mem _ ha)))

theorem quotBaseP_mk (I : Ideal (CrossingQuotient W t)) (hI) (w : W) :
    quotBaseP t 𝔭 I hI (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk I (algebraMap W _ w) := rfl

section lineU

abbrev IU : Ideal (CrossingQuotient W t) := Ideal.span {U t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t))

def quotIUEquiv_fwd : (CrossingQuotient W t ⧸ IU t 𝔭) →ₐ[W] (W ⧸ 𝔭)[X] :=
  Ideal.Quotient.liftₐ (IU t 𝔭) (lineUHom t 𝔭 ht) (fun a ha =>
    (mem_lineUIdeal_iff t 𝔭 ht a).mp (span_U_sup_map_le_lineUIdeal t 𝔭 ht ha))

theorem quotIUEquiv_fwd_mk (c : CrossingQuotient W t) :
    quotIUEquiv_fwd t 𝔭 ht (Ideal.Quotient.mk _ c) = lineUHom t 𝔭 ht c := rfl

def quotIUEquiv_bwd : (W ⧸ 𝔭)[X] →ₐ[W] (CrossingQuotient W t ⧸ IU t 𝔭) :=
  Polynomial.aevalTower (quotBaseP t 𝔭 _ le_sup_right) (Ideal.Quotient.mk _ (V t))

theorem quotIUEquiv_bwd_X : quotIUEquiv_bwd t 𝔭 Polynomial.X = Ideal.Quotient.mk _ (V t) :=
  Polynomial.aevalTower_X _ _

theorem quotIUEquiv_fwd_bwd : (quotIUEquiv_fwd t 𝔭 ht).comp (quotIUEquiv_bwd t 𝔭) = AlgHom.id W _ := by
  refine Polynomial.algHom_ext' (Ideal.Quotient.algHom_ext W (FibrePointsAux.algHom_base_ext _ _)) ?_
  rw [AlgHom.comp_apply, quotIUEquiv_bwd_X, quotIUEquiv_fwd_mk, lineUHom_V, AlgHom.id_apply]

theorem quotIUEquiv_bwd_fwd : (quotIUEquiv_bwd t 𝔭).comp (quotIUEquiv_fwd t 𝔭 ht) = AlgHom.id W _ := by
  refine Ideal.Quotient.algHom_ext W ?_
  refine Ideal.Quotient.algHom_ext W ?_
  refine MvPolynomial.algHom_ext (fun i => ?_)
  fin_cases i
  · change quotIUEquiv_bwd t 𝔭 (quotIUEquiv_fwd t 𝔭 ht (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [quotIUEquiv_fwd_mk, lineUHom_U, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.subset_span rfl)
  · change quotIUEquiv_bwd t 𝔭 (quotIUEquiv_fwd t 𝔭 ht (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [quotIUEquiv_fwd_mk, lineUHom_V]
    exact quotIUEquiv_bwd_X t 𝔭

def quotIUEquiv : (CrossingQuotient W t ⧸ IU t 𝔭) ≃ₐ[W] (W ⧸ 𝔭)[X] :=
  AlgEquiv.ofAlgHom (quotIUEquiv_fwd t 𝔭 ht) (quotIUEquiv_bwd t 𝔭) (quotIUEquiv_fwd_bwd t 𝔭 ht)
    (quotIUEquiv_bwd_fwd t 𝔭 ht)

theorem lineUIdeal_eq_span_sup_map :
    lineUIdeal t 𝔭 ht = Ideal.span {U t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t)) := by
  have h : (lineUHom t 𝔭 ht).toRingHom =
      (quotIUEquiv t 𝔭 ht).toAlgHom.toRingHom.comp (Ideal.Quotient.mk (IU t 𝔭)) := rfl
  rw [lineUIdeal, h, ← RingHom.comap_ker]
  have : RingHom.ker (quotIUEquiv t 𝔭 ht).toAlgHom.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (quotIUEquiv t 𝔭 ht).injective
  rw [this, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem lineUIdeal_le_iff {P : Ideal (CrossingQuotient W t)} :
    lineUIdeal t 𝔭 ht ≤ P ↔ U t ∈ P ∧ ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P := by
  rw [lineUIdeal_eq_span_sup_map, sup_le_iff, Ideal.span_le, Set.singleton_subset_iff, Ideal.map_le_iff_le_comap]
  rfl

end lineU

section lineV

abbrev IV : Ideal (CrossingQuotient W t) := Ideal.span {V t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t))

def quotIVEquiv_fwd : (CrossingQuotient W t ⧸ IV t 𝔭) →ₐ[W] (W ⧸ 𝔭)[X] :=
  Ideal.Quotient.liftₐ (IV t 𝔭) (lineVHom t 𝔭 ht) (fun a ha =>
    (mem_lineVIdeal_iff t 𝔭 ht a).mp (span_V_sup_map_le_lineVIdeal t 𝔭 ht ha))

theorem quotIVEquiv_fwd_mk (c : CrossingQuotient W t) :
    quotIVEquiv_fwd t 𝔭 ht (Ideal.Quotient.mk _ c) = lineVHom t 𝔭 ht c := rfl

def quotIVEquiv_bwd : (W ⧸ 𝔭)[X] →ₐ[W] (CrossingQuotient W t ⧸ IV t 𝔭) :=
  Polynomial.aevalTower (quotBaseP t 𝔭 _ le_sup_right) (Ideal.Quotient.mk _ (U t))

theorem quotIVEquiv_bwd_X : quotIVEquiv_bwd t 𝔭 Polynomial.X = Ideal.Quotient.mk _ (U t) :=
  Polynomial.aevalTower_X _ _

theorem quotIVEquiv_fwd_bwd : (quotIVEquiv_fwd t 𝔭 ht).comp (quotIVEquiv_bwd t 𝔭) = AlgHom.id W _ := by
  refine Polynomial.algHom_ext' (Ideal.Quotient.algHom_ext W (FibrePointsAux.algHom_base_ext _ _)) ?_
  rw [AlgHom.comp_apply, quotIVEquiv_bwd_X, quotIVEquiv_fwd_mk, lineVHom_U, AlgHom.id_apply]

theorem quotIVEquiv_bwd_fwd : (quotIVEquiv_bwd t 𝔭).comp (quotIVEquiv_fwd t 𝔭 ht) = AlgHom.id W _ := by
  refine Ideal.Quotient.algHom_ext W ?_
  refine Ideal.Quotient.algHom_ext W ?_
  refine MvPolynomial.algHom_ext (fun i => ?_)
  fin_cases i
  · change quotIVEquiv_bwd t 𝔭 (quotIVEquiv_fwd t 𝔭 ht (Ideal.Quotient.mk _ (U t))) = Ideal.Quotient.mk _ (U t)
    rw [quotIVEquiv_fwd_mk, lineVHom_U]
    exact quotIVEquiv_bwd_X t 𝔭
  · change quotIVEquiv_bwd t 𝔭 (quotIVEquiv_fwd t 𝔭 ht (Ideal.Quotient.mk _ (V t))) = Ideal.Quotient.mk _ (V t)
    rw [quotIVEquiv_fwd_mk, lineVHom_V, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.subset_span rfl)

def quotIVEquiv : (CrossingQuotient W t ⧸ IV t 𝔭) ≃ₐ[W] (W ⧸ 𝔭)[X] :=
  AlgEquiv.ofAlgHom (quotIVEquiv_fwd t 𝔭 ht) (quotIVEquiv_bwd t 𝔭) (quotIVEquiv_fwd_bwd t 𝔭 ht)
    (quotIVEquiv_bwd_fwd t 𝔭 ht)

theorem lineVIdeal_eq_span_sup_map :
    lineVIdeal t 𝔭 ht = Ideal.span {V t} ⊔ 𝔭.map (algebraMap W (CrossingQuotient W t)) := by
  have h : (lineVHom t 𝔭 ht).toRingHom =
      (quotIVEquiv t 𝔭 ht).toAlgHom.toRingHom.comp (Ideal.Quotient.mk (IV t 𝔭)) := rfl
  rw [lineVIdeal, h, ← RingHom.comap_ker]
  have : RingHom.ker (quotIVEquiv t 𝔭 ht).toAlgHom.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (quotIVEquiv t 𝔭 ht).injective
  rw [this, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem lineVIdeal_le_iff {P : Ideal (CrossingQuotient W t)} :
    lineVIdeal t 𝔭 ht ≤ P ↔ V t ∈ P ∧ ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P := by
  rw [lineVIdeal_eq_span_sup_map, sup_le_iff, Ideal.span_le, Set.singleton_subset_iff, Ideal.map_le_iff_le_comap]
  rfl

end lineV

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open AlgebraicGeometry CategoryTheory GlueIndex

universe u

variable {W : Type u} [CommRing W] (t : W)

theorem U_notMem_and_V_notMem_of_mem_range_torusToChart {P : chartScheme t} (i : ℕ)
    (hP : P ∈ Set.range (torusToChart t i)) : U t ∉ P.asIdeal ∧ V t ∉ P.asIdeal := by
  have := isIso_ofHom_twistEquiv t i
  rw [torusToChart_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ] at hP
  change P ∈ Set.range (PrimeSpectrum.comap (algebraMap (CrossingQuotient W t) (TorusRing t))) at hP
  rw [PrimeSpectrum.localization_away_comap_range (TorusRing t)
    (algebraMap W (CrossingQuotient W t) t)] at hP
  change algebraMap W (CrossingQuotient W t) t ∉ P.asIdeal at hP
  rw [← U_mul_V] at hP
  exact ⟨fun h => hP (P.asIdeal.mul_mem_right _ h), fun h => hP (P.asIdeal.mul_mem_left _ h)⟩

namespace Resolution

variable (e : ℕ)

theorem ι_apply_ne_of_V_mem {i j : Fin e} (hij : i ≠ j) {x y : chartScheme t}
    (hx : V t ∈ x.asIdeal) (hy : V t ∈ y.asIdeal) : ι t e i x ≠ ι t e j y := by
  intro h
  obtain ⟨a, hi, hj, z, hzi, hzj⟩ := (ι_apply_eq_iff t e x y).mp h
  cases a with
  | chart k =>
    simp only [chart_le_chart] at hi hj
    exact hij (hi.symm.trans hj)
  | overlap k hk =>
    have hi' := hi; have hj' := hj
    simp only [overlap_le_chart] at hi' hj'
    by_cases hik : (i : ℕ) = k
    · rw [glueMap_overlap_chart_of_eq t e hk hi hik] at hzi
      exact V_notMem_of_mem_range_overlapToChartLeft t ⟨z, hzi⟩ hx
    · by_cases hjk : (j : ℕ) = k
      · rw [glueMap_overlap_chart_of_eq t e hk hj hjk] at hzj
        exact V_notMem_of_mem_range_overlapToChartLeft t ⟨z, hzj⟩ hy
      · apply hij; apply Fin.ext
        rcases hi' with h1 | h1
        · exact absurd (congrArg Fin.val h1) hik
        rcases hj' with h2 | h2
        · exact absurd (congrArg Fin.val h2) hjk
        omega
  | torus h0 =>
    rw [glueMap_torus_chart] at hzi
    exact (U_notMem_and_V_notMem_of_mem_range_torusToChart t i ⟨z, hzi⟩).2 hx

theorem ι_apply_ne_of_U_mem {i j : Fin e} (hij : i ≠ j) {x y : chartScheme t}
    (hx : U t ∈ x.asIdeal) (hy : U t ∈ y.asIdeal) : ι t e i x ≠ ι t e j y := by
  intro h
  obtain ⟨a, hi, hj, z, hzi, hzj⟩ := (ι_apply_eq_iff t e x y).mp h
  cases a with
  | chart k =>
    simp only [chart_le_chart] at hi hj
    exact hij (hi.symm.trans hj)
  | overlap k hk =>
    have hi' := hi; have hj' := hj
    simp only [overlap_le_chart] at hi' hj'
    by_cases hik : (i : ℕ) = k
    · by_cases hjk : (j : ℕ) = k
      · exact hij (Fin.ext (hik.trans hjk.symm))
      · rw [glueMap_overlap_chart_of_ne t e hk hj hjk] at hzj
        exact U_notMem_of_mem_range_overlapToChartRight t ⟨z, hzj⟩ hy
    · rw [glueMap_overlap_chart_of_ne t e hk hi hik] at hzi
      exact U_notMem_of_mem_range_overlapToChartRight t ⟨z, hzi⟩ hx
  | torus h0 =>
    rw [glueMap_torus_chart] at hzi
    exact (U_notMem_and_V_notMem_of_mem_range_torusToChart t i ⟨z, hzi⟩).1 hx

theorem ι_apply_injective (i : Fin e) : Function.Injective (ι t e i : chartScheme t → Resolution t e) :=
  (ι t e i).isOpenEmbedding.injective

variable (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

def chartPt (i : Fin e) (P : Ideal (CrossingQuotient W t)) [P.IsPrime] : Resolution t e :=
  ι t e i ⟨P, inferInstance⟩

def origin (i : Fin e) : Resolution t e := chartPt t e i (originIdeal t 𝔭 ht)

def lineGen (i : Fin e) : Resolution t e := chartPt t e i (lineVIdeal t 𝔭 ht)

def lineUGen (i : Fin e) : Resolution t e := chartPt t e i (lineUIdeal t 𝔭 ht)

theorem origin_def (i : Fin e) : origin t e 𝔭 ht i = ι t e i ⟨originIdeal t 𝔭 ht, inferInstance⟩ := rfl
theorem lineGen_def (i : Fin e) : lineGen t e 𝔭 ht i = ι t e i ⟨lineVIdeal t 𝔭 ht, inferInstance⟩ := rfl
theorem lineUGen_def (i : Fin e) : lineUGen t e 𝔭 ht i = ι t e i ⟨lineUIdeal t 𝔭 ht, inferInstance⟩ := rfl

theorem lineUGen_eq_lineGen_succ (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    lineUGen t e 𝔭 ht i = lineGen t e 𝔭 ht ⟨(i : ℕ) + 1, hi⟩ := by
  rw [lineUGen_def, lineGen_def]
  refine (ι_apply_eq_iff t e _ _).mpr ⟨overlap i hi, by simp, by simp,
    ⟨overlapIdeal t 𝔭 ht, inferInstance⟩, ?_, ?_⟩
  · rw [glueMap_overlap_chart_self]
    exact PrimeSpectrum.ext (comap_algebraMap_overlapIdeal t 𝔭 ht)
  · rw [glueMap_overlap_chart_succ]
    exact PrimeSpectrum.ext (comap_transitionUp_overlapIdeal t 𝔭 ht)

theorem lineUGen_eq_lineGen {i j : Fin e} (hj : (j : ℕ) = (i : ℕ) + 1) :
    lineUGen t e 𝔭 ht i = lineGen t e 𝔭 ht j := by
  have hi : (i : ℕ) + 1 < e := hj ▸ j.2
  rw [lineUGen_eq_lineGen_succ t e 𝔭 ht i hi]
  congr 1; exact Fin.ext hj.symm

theorem origin_injective : Function.Injective (origin t e 𝔭 ht) := fun i j h => by
  by_contra hij
  exact ι_apply_ne_of_V_mem t e hij (V_mem_originIdeal t 𝔭 ht) (V_mem_originIdeal t 𝔭 ht) h

theorem lineGen_injective : Function.Injective (lineGen t e 𝔭 ht) := fun i j h => by
  by_contra hij
  exact ι_apply_ne_of_V_mem t e hij (V_mem_lineVIdeal t 𝔭 ht) (V_mem_lineVIdeal t 𝔭 ht) h

theorem lineUGen_injective : Function.Injective (lineUGen t e 𝔭 ht) := fun i j h => by
  by_contra hij
  exact ι_apply_ne_of_U_mem t e hij (U_mem_lineUIdeal t 𝔭 ht) (U_mem_lineUIdeal t 𝔭 ht) h

theorem origin_ne_lineGen (i j : Fin e) : origin t e 𝔭 ht i ≠ lineGen t e 𝔭 ht j := by
  by_cases hij : i = j
  · subst hij
    intro h
    have := congrArg PrimeSpectrum.asIdeal (ι_apply_injective t e i h)
    exact originIdeal_ne_lineVIdeal t 𝔭 ht this
  · exact ι_apply_ne_of_V_mem t e hij (V_mem_originIdeal t 𝔭 ht) (V_mem_lineVIdeal t 𝔭 ht)

theorem origin_ne_lineUGen (i j : Fin e) : origin t e 𝔭 ht i ≠ lineUGen t e 𝔭 ht j := by
  by_cases hij : i = j
  · subst hij
    intro h
    have := congrArg PrimeSpectrum.asIdeal (ι_apply_injective t e i h)
    exact originIdeal_ne_lineUIdeal t 𝔭 ht this
  · exact ι_apply_ne_of_U_mem t e hij (U_mem_originIdeal t 𝔭 ht) (U_mem_lineUIdeal t 𝔭 ht)

theorem lineUGen_last_ne_lineGen (i : Fin e) (hi : (i : ℕ) + 1 = e) (j : Fin e) :
    lineUGen t e 𝔭 ht i ≠ lineGen t e 𝔭 ht j := by
  intro h
  rw [lineUGen_def, lineGen_def] at h
  obtain ⟨a, hai, haj, z, hzi, hzj⟩ := (ι_apply_eq_iff t e _ _).mp h
  cases a with
  | chart k =>
    simp only [chart_le_chart] at hai haj
    subst hai; subst haj
    rw [glueMap_chart_chart] at hzi hzj
    have := congrArg PrimeSpectrum.asIdeal (hzi.symm.trans hzj)
    exact lineVIdeal_ne_lineUIdeal t 𝔭 ht this.symm
  | overlap k hk =>
    have hai' := hai
    simp only [overlap_le_chart] at hai'
    have hik : (i : ℕ) ≠ k := by
      intro h2
      rcases hai' with h1 | h1
      · have := congrArg Fin.val h1; omega
      · omega
    rw [glueMap_overlap_chart_of_ne t e hk hai hik] at hzi
    exact U_notMem_of_mem_range_overlapToChartRight t ⟨z, hzi⟩ (U_mem_lineUIdeal t 𝔭 ht)
  | torus h0 =>
    rw [glueMap_torus_chart] at hzi
    exact (U_notMem_and_V_notMem_of_mem_range_torusToChart t i ⟨z, hzi⟩).1 (U_mem_lineUIdeal t 𝔭 ht)

theorem specializes_of_le (i : Fin e) {P Q : Ideal (CrossingQuotient W t)} [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    chartPt t e i P ⤳ chartPt t e i Q :=
  ((PrimeSpectrum.le_iff_specializes ⟨P, inferInstance⟩ ⟨Q, inferInstance⟩).mp h).map (ι t e i).continuous

theorem lineGen_specializes_origin (i : Fin e) : lineGen t e 𝔭 ht i ⤳ origin t e 𝔭 ht i :=
  specializes_of_le t e i (lineVIdeal_le_originIdeal t 𝔭 ht)

theorem lineUGen_specializes_origin (i : Fin e) : lineUGen t e 𝔭 ht i ⤳ origin t e 𝔭 ht i :=
  specializes_of_le t e i (lineUIdeal_le_originIdeal t 𝔭 ht)

theorem origin_mem_closure_lineGen (i : Fin e) : origin t e 𝔭 ht i ∈ closure {lineGen t e 𝔭 ht i} :=
  specializes_iff_mem_closure.mp (lineGen_specializes_origin t e 𝔭 ht i)

theorem origin_mem_closure_lineUGen (i : Fin e) : origin t e 𝔭 ht i ∈ closure {lineUGen t e 𝔭 ht i} :=
  specializes_iff_mem_closure.mp (lineUGen_specializes_origin t e 𝔭 ht i)

theorem origin_mem_closure_lineGen_succ (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    origin t e 𝔭 ht i ∈ closure {lineGen t e 𝔭 ht ⟨(i : ℕ) + 1, hi⟩} := by
  rw [← lineUGen_eq_lineGen_succ t e 𝔭 ht i hi]; exact origin_mem_closure_lineUGen t e 𝔭 ht i

instance isPrime_vertexIdeal (he : 1 ≤ e) : (vertexIdeal t 𝔭 ht e he).IsPrime := isPrime_originIdeal _ _ _
instance isPrime_branchVPrime (he : 1 ≤ e) : (branchVPrime t 𝔭 ht e he).IsPrime := isPrime_lineVIdeal _ _ _
instance isPrime_branchUPrime (he : 1 ≤ e) : (branchUPrime t 𝔭 ht e he).IsPrime := isPrime_lineUIdeal _ _ _

def vertexPt (he : 1 ≤ e) : crossingScheme (t ^ e) := ⟨vertexIdeal t 𝔭 ht e he, inferInstance⟩

def branchVPt (he : 1 ≤ e) : crossingScheme (t ^ e) := ⟨branchVPrime t 𝔭 ht e he, inferInstance⟩

def branchUPt (he : 1 ≤ e) : crossingScheme (t ^ e) := ⟨branchUPrime t 𝔭 ht e he, inferInstance⟩

theorem eq_vertexPt_of_mem [𝔭.IsMaximal] (he : 1 ≤ e) {P : crossingScheme (t ^ e)}
    (hU : U (t ^ e) ∈ P.asIdeal) (hV : V (t ^ e) ∈ P.asIdeal)
    (h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W (t ^ e)) w ∈ P.asIdeal) :
    P = vertexPt t e 𝔭 ht he :=
  PrimeSpectrum.ext (eq_vertexIdeal_of_mem t 𝔭 ht e he P.isPrime.ne_top hU hV h𝔭)

theorem eq_origin_pt_of_mem [𝔭.IsMaximal] {P : chartScheme t}
    (hU : U t ∈ P.asIdeal) (hV : V t ∈ P.asIdeal)
    (h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P.asIdeal) :
    P = ⟨originIdeal t 𝔭 ht, inferInstance⟩ :=
  PrimeSpectrum.ext (eq_originIdeal_of_mem t 𝔭 ht P.isPrime.ne_top hU hV h𝔭)

theorem toCrossing_chartPt (i : Fin e) (P : Ideal (CrossingQuotient W t)) [P.IsPrime] :
    toCrossing t e (chartPt t e i P) = ⟨P.comap (resolutionChart t e i).toRingHom, inferInstance⟩ := by
  rw [chartPt, ← Scheme.Hom.comp_apply, ι_toCrossing]
  rfl

theorem toCrossing_origin (i : Fin e) : toCrossing t e (origin t e 𝔭 ht i) = vertexPt t e 𝔭 ht (one_le e i) := by
  rw [origin, toCrossing_chartPt]; exact PrimeSpectrum.ext (comap_resolutionChart_originIdeal t 𝔭 ht e i)

theorem toCrossing_lineGen_of_pos (i : Fin e) (hi : 1 ≤ (i : ℕ)) :
    toCrossing t e (lineGen t e 𝔭 ht i) = vertexPt t e 𝔭 ht (one_le e i) := by
  rw [lineGen, toCrossing_chartPt]; exact PrimeSpectrum.ext (comap_resolutionChart_lineVIdeal_of_pos t 𝔭 ht e i hi)

theorem toCrossing_lineUGen_of_lt (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    toCrossing t e (lineUGen t e 𝔭 ht i) = vertexPt t e 𝔭 ht (one_le e i) := by
  rw [lineUGen, toCrossing_chartPt]; exact PrimeSpectrum.ext (comap_resolutionChart_lineUIdeal_of_lt t 𝔭 ht e i hi)

theorem toCrossing_lineGen_zero (i : Fin e) (hi : (i : ℕ) = 0) :
    toCrossing t e (lineGen t e 𝔭 ht i) = branchVPt t e 𝔭 ht (one_le e i) := by
  rw [lineGen, toCrossing_chartPt]; exact PrimeSpectrum.ext (comap_resolutionChart_lineVIdeal_zero t 𝔭 ht e i hi)

theorem toCrossing_lineUGen_last (i : Fin e) (hi : (i : ℕ) + 1 = e) :
    toCrossing t e (lineUGen t e 𝔭 ht i) = branchUPt t e 𝔭 ht (one_le e i) := by
  rw [lineUGen, toCrossing_chartPt]; exact PrimeSpectrum.ext (comap_resolutionChart_lineUIdeal_last t 𝔭 ht e i hi)

end Resolution

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace V3Glue.Aux

open Topology

theorem mem_of_closure_singleton_inter_nonempty {X : Type*} [TopologicalSpace X] {η : X} {U : Set X} (hU : IsOpen U)
    (h : (closure {η} ∩ U).Nonempty) : η ∈ U := by
  obtain ⟨z, hz, hzU⟩ := h
  obtain ⟨w, hwU, hw⟩ := mem_closure_iff.mp hz U hU hzU
  rw [Set.mem_singleton_iff] at hw
  exact hw ▸ hwU

theorem closure_singleton_inter_range_eq_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsEmbedding f) (x : X) : closure {f x} ∩ Set.range f = f '' closure {x} := by
  rw [hf.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range, Set.image_singleton]

theorem closure_singleton_inter_range_eq_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsOpenEmbedding f) {η : Y} (hη : η ∉ Set.range f) : closure {η} ∩ Set.range f = ∅ := by
  by_contra h
  exact hη (mem_of_closure_singleton_inter_nonempty hf.isOpen_range (Set.nonempty_iff_ne_empty.mpr h))

theorem PrimeSpectrum.closure_singleton_eq {R : Type*} [CommRing R] (P : PrimeSpectrum R) :
    closure ({P} : Set (PrimeSpectrum R)) = {Q | P.asIdeal ≤ Q.asIdeal} := by
  ext Q
  rw [Set.mem_setOf_eq, ← PrimeSpectrum.le_iff_mem_closure]
  rfl

end V3Glue.Aux

namespace MvPolynomial.CrossingQuotient.Resolution

open AlgebraicGeometry CategoryTheory GlueIndex V3Glue.Aux

universe u

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

theorem eq_of_ι_apply_eq_of_U_mem_of_V_mem {i j : Fin e} {x y : chartScheme t}
    (hU : U t ∈ x.asIdeal) (hV : V t ∈ x.asIdeal) (h : ι t e i x = ι t e j y) : i = j := by
  obtain ⟨a, hi, hj, z, hzi, hzj⟩ := (ι_apply_eq_iff t e x y).mp h
  cases a with
  | chart k =>
    simp only [chart_le_chart] at hi hj
    exact hi.symm.trans hj
  | overlap k hk =>
    by_cases hik : (i : ℕ) = k
    · rw [glueMap_overlap_chart_of_eq t e hk hi hik] at hzi
      exact absurd hV (V_notMem_of_mem_range_overlapToChartLeft t ⟨z, hzi⟩)
    · rw [glueMap_overlap_chart_of_ne t e hk hi hik] at hzi
      exact absurd hU (U_notMem_of_mem_range_overlapToChartRight t ⟨z, hzi⟩)
  | torus h0 =>
    rw [glueMap_torus_chart] at hzi
    exact absurd hU (U_notMem_and_V_notMem_of_mem_range_torusToChart t i ⟨z, hzi⟩).1

theorem U_notMem_and_V_notMem_of_ι_apply_eq_of_two_le {i j : Fin e} {x y : chartScheme t}
    (h : ι t e i x = ι t e j y) (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    U t ∉ x.asIdeal ∧ V t ∉ x.asIdeal := by
  obtain ⟨a, hi, hj, z, hzi, hzj⟩ := (ι_apply_eq_iff t e x y).mp h
  cases a with
  | chart k =>
    simp only [chart_le_chart] at hi hj
    subst hi; subst hj; omega
  | overlap k hk =>
    have hi' := hi; have hj' := hj
    simp only [overlap_le_chart] at hi' hj'
    exfalso
    rcases hi' with h1 | h1 <;> rcases hj' with h2 | h2
    · have := congrArg Fin.val h1; have := congrArg Fin.val h2; omega
    · have := congrArg Fin.val h1; omega
    · have := congrArg Fin.val h2; omega
    · omega
  | torus h0 =>
    rw [glueMap_torus_chart] at hzi
    exact U_notMem_and_V_notMem_of_mem_range_torusToChart t i ⟨z, hzi⟩

theorem V_notMem_and_U_notMem_of_ι_apply_eq_succ {i j : Fin e} {x y : chartScheme t}
    (h : ι t e i x = ι t e j y) (hij : (j : ℕ) = (i : ℕ) + 1) :
    V t ∉ x.asIdeal ∧ U t ∉ y.asIdeal := by
  obtain ⟨a, hi, hj, z, hzi, hzj⟩ := (ι_apply_eq_iff t e x y).mp h
  cases a with
  | chart k =>
    simp only [chart_le_chart] at hi hj
    subst hi; subst hj; omega
  | overlap k hk =>
    have hi' := hi; have hj' := hj
    simp only [overlap_le_chart] at hi' hj'
    have hik : (i : ℕ) = k := by
      rcases hi' with h1 | h1
      · exact congrArg Fin.val h1
      · rcases hj' with h2 | h2
        · have := congrArg Fin.val h2; omega
        · omega
    have hjk : (j : ℕ) ≠ k := by omega
    rw [glueMap_overlap_chart_of_eq t e hk hi hik] at hzi
    rw [glueMap_overlap_chart_of_ne t e hk hj hjk] at hzj
    exact ⟨V_notMem_of_mem_range_overlapToChartLeft t ⟨z, hzi⟩, U_notMem_of_mem_range_overlapToChartRight t ⟨z, hzj⟩⟩
  | torus h0 =>
    rw [glueMap_torus_chart] at hzi hzj
    exact ⟨(U_notMem_and_V_notMem_of_mem_range_torusToChart t i ⟨z, hzi⟩).2,
      (U_notMem_and_V_notMem_of_mem_range_torusToChart t j ⟨z, hzj⟩).1⟩

variable (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

theorem origin_mem_range_ι_iff (i j : Fin e) :
    origin t e 𝔭 ht i ∈ Set.range (ι t e j).base ↔ j = i := by
  constructor
  · rintro ⟨y, hy⟩
    change ι t e j y = ι t e i ⟨originIdeal t 𝔭 ht, inferInstance⟩ at hy
    exact (eq_of_ι_apply_eq_of_U_mem_of_V_mem t e (x := ⟨originIdeal t 𝔭 ht, inferInstance⟩)
      (U_mem_originIdeal t 𝔭 ht) (V_mem_originIdeal t 𝔭 ht) hy.symm).symm
  · rintro rfl; exact ⟨_, rfl⟩

theorem lineGen_mem_range_ι_iff (k i : Fin e) :
    lineGen t e 𝔭 ht k ∈ Set.range (ι t e i).base ↔ (i = k ∨ (i : ℕ) + 1 = k) := by
  constructor
  · rintro ⟨y, hy⟩
    change ι t e i y = ι t e k ⟨lineVIdeal t 𝔭 ht, inferInstance⟩ at hy
    obtain ⟨a, hi, hk, z, hzi, hzk⟩ := (ι_apply_eq_iff t e _ _).mp hy
    cases a with
    | chart m =>
      simp only [chart_le_chart] at hi hk
      exact Or.inl (hi.symm.trans hk)
    | overlap m hm =>
      have hi' := hi; have hk' := hk
      simp only [overlap_le_chart] at hi' hk'
      have hkm : (k : ℕ) ≠ m := by
        intro hkm
        rw [glueMap_overlap_chart_of_eq t e hm hk hkm] at hzk
        exact V_notMem_of_mem_range_overlapToChartLeft t ⟨z, hzk⟩ (V_mem_lineVIdeal t 𝔭 ht)
      have hk2 : (k : ℕ) = m + 1 := by
        rcases hk' with h1 | h1
        · exact absurd (congrArg Fin.val h1) hkm
        · exact h1
      rcases hi' with h2 | h2
      · right; have := congrArg Fin.val h2; omega
      · left; exact Fin.ext (by omega)
    | torus h0 =>
      rw [glueMap_torus_chart] at hzk
      exact absurd (V_mem_lineVIdeal t 𝔭 ht) (U_notMem_and_V_notMem_of_mem_range_torusToChart t k ⟨z, hzk⟩).2
  · rintro (rfl | h)
    · exact ⟨_, rfl⟩
    · refine ⟨⟨lineUIdeal t 𝔭 ht, inferInstance⟩, ?_⟩
      exact (lineUGen_eq_lineGen t e 𝔭 ht (i := i) (j := k) h.symm)

theorem lineUGen_last_mem_range_ι_iff (i j : Fin e) (hi : (i : ℕ) + 1 = e) :
    lineUGen t e 𝔭 ht i ∈ Set.range (ι t e j).base ↔ j = i := by
  constructor
  · rintro ⟨y, hy⟩
    change ι t e j y = ι t e i ⟨lineUIdeal t 𝔭 ht, inferInstance⟩ at hy
    obtain ⟨a, hj, hi2, z, hzj, hzi⟩ := (ι_apply_eq_iff t e _ _).mp hy
    cases a with
    | chart m =>
      simp only [chart_le_chart] at hj hi2
      exact hj.symm.trans hi2
    | overlap m hm =>
      have hi' := hi2
      simp only [overlap_le_chart] at hi'
      have him : (i : ℕ) ≠ m := by
        intro h2
        rcases hi' with h1 | h1
        · have := congrArg Fin.val h1; omega
        · omega
      rw [glueMap_overlap_chart_of_ne t e hm hi2 him] at hzi
      exact absurd (U_mem_lineUIdeal t 𝔭 ht) (U_notMem_of_mem_range_overlapToChartRight t ⟨z, hzi⟩)
    | torus h0 =>
      rw [glueMap_torus_chart] at hzi
      exact absurd (U_mem_lineUIdeal t 𝔭 ht) (U_notMem_and_V_notMem_of_mem_range_torusToChart t i ⟨z, hzi⟩).1
  · rintro rfl; exact ⟨_, rfl⟩

theorem closure_chartPt_inter_range (i : Fin e) (P : Ideal (CrossingQuotient W t)) [P.IsPrime] :
    closure {chartPt t e i P} ∩ Set.range (ι t e i).base =
      (ι t e i).base '' {Q : chartScheme t | P ≤ Q.asIdeal} := by
  rw [chartPt, show (ι t e i) (⟨P, inferInstance⟩ : chartScheme t) = (ι t e i).base ⟨P, inferInstance⟩ from rfl,
    closure_singleton_inter_range_eq_image (ι t e i).isOpenEmbedding.isEmbedding]
  congr 1
  ext Q
  exact (PrimeSpectrum.le_iff_mem_closure (⟨P, inferInstance⟩ : chartScheme t) Q).symm

theorem closure_lineGen_inter_range_self (k : Fin e) :
    closure {lineGen t e 𝔭 ht k} ∩ Set.range (ι t e k).base =
      (ι t e k).base '' {Q : chartScheme t | lineVIdeal t 𝔭 ht ≤ Q.asIdeal} :=
  closure_chartPt_inter_range t e k _

theorem closure_lineGen_inter_range_pred (k i : Fin e) (h : (i : ℕ) + 1 = k) :
    closure {lineGen t e 𝔭 ht k} ∩ Set.range (ι t e i).base =
      (ι t e i).base '' {Q : chartScheme t | lineUIdeal t 𝔭 ht ≤ Q.asIdeal} := by
  rw [← lineUGen_eq_lineGen t e 𝔭 ht (i := i) (j := k) h.symm]
  exact closure_chartPt_inter_range t e i _

theorem closure_lineGen_inter_range_of_ne (k i : Fin e) (h1 : i ≠ k) (h2 : (i : ℕ) + 1 ≠ k) :
    closure {lineGen t e 𝔭 ht k} ∩ Set.range (ι t e i).base = ∅ :=
  closure_singleton_inter_range_eq_empty (ι t e i).isOpenEmbedding
    (fun h => by rcases (lineGen_mem_range_ι_iff t e 𝔭 ht k i).mp h with h | h <;> [exact h1 h; exact h2 h])

theorem closure_lineUGen_last_inter_range_self (i : Fin e) :
    closure {lineUGen t e 𝔭 ht i} ∩ Set.range (ι t e i).base =
      (ι t e i).base '' {Q : chartScheme t | lineUIdeal t 𝔭 ht ≤ Q.asIdeal} :=
  closure_chartPt_inter_range t e i _

theorem closure_lineUGen_last_inter_range_of_ne (i j : Fin e) (hi : (i : ℕ) + 1 = e) (hij : j ≠ i) :
    closure {lineUGen t e 𝔭 ht i} ∩ Set.range (ι t e j).base = ∅ :=
  closure_singleton_inter_range_eq_empty (ι t e j).isOpenEmbedding
    (fun h => hij ((lineUGen_last_mem_range_ι_iff t e 𝔭 ht i j hi).mp h))

theorem mem_closure_lineGen_iff (k : Fin e) (z : Resolution t e) :
    z ∈ closure {lineGen t e 𝔭 ht k} ↔
      (∃ Q : chartScheme t, lineVIdeal t 𝔭 ht ≤ Q.asIdeal ∧ (ι t e k).base Q = z) ∨
      (∃ (i : Fin e) (Q : chartScheme t), (i : ℕ) + 1 = k ∧ lineUIdeal t 𝔭 ht ≤ Q.asIdeal ∧ (ι t e i).base Q = z) := by
  constructor
  · intro hz
    obtain ⟨i, y, rfl⟩ := exists_ι_apply_eq t e z
    have hmem : (ι t e i) y ∈ closure {lineGen t e 𝔭 ht k} ∩ Set.range (ι t e i).base := ⟨hz, y, rfl⟩
    by_cases h1 : i = k
    · subst h1
      rw [closure_lineGen_inter_range_self] at hmem
      obtain ⟨Q, hQ, hQy⟩ := hmem
      exact Or.inl ⟨Q, hQ, hQy⟩
    · by_cases h2 : (i : ℕ) + 1 = k
      · rw [closure_lineGen_inter_range_pred t e 𝔭 ht k i h2] at hmem
        obtain ⟨Q, hQ, hQy⟩ := hmem
        exact Or.inr ⟨i, Q, h2, hQ, hQy⟩
      · rw [closure_lineGen_inter_range_of_ne t e 𝔭 ht k i h1 h2] at hmem
        exact absurd hmem (Set.notMem_empty _)
  · rintro (⟨Q, hQ, rfl⟩ | ⟨i, Q, hi, hQ, rfl⟩)
    · have : (ι t e k).base Q ∈ closure {lineGen t e 𝔭 ht k} ∩ Set.range (ι t e k).base := by
        rw [closure_lineGen_inter_range_self]; exact ⟨Q, hQ, rfl⟩
      exact this.1
    · have : (ι t e i).base Q ∈ closure {lineGen t e 𝔭 ht k} ∩ Set.range (ι t e i).base := by
        rw [closure_lineGen_inter_range_pred t e 𝔭 ht k i hi]; exact ⟨Q, hQ, rfl⟩
      exact this.1

theorem mem_closure_lineUGen_last_iff (i : Fin e) (hi : (i : ℕ) + 1 = e) (z : Resolution t e) :
    z ∈ closure {lineUGen t e 𝔭 ht i} ↔ ∃ Q : chartScheme t, lineUIdeal t 𝔭 ht ≤ Q.asIdeal ∧ (ι t e i).base Q = z := by
  constructor
  · intro hz
    obtain ⟨j, y, rfl⟩ := exists_ι_apply_eq t e z
    have hmem : (ι t e j) y ∈ closure {lineUGen t e 𝔭 ht i} ∩ Set.range (ι t e j).base := ⟨hz, y, rfl⟩
    by_cases hji : j = i
    · subst hji
      rw [closure_lineUGen_last_inter_range_self] at hmem
      obtain ⟨Q, hQ, hQy⟩ := hmem
      exact ⟨Q, hQ, hQy⟩
    · rw [closure_lineUGen_last_inter_range_of_ne t e 𝔭 ht i j hi hji] at hmem
      exact absurd hmem (Set.notMem_empty _)
  · rintro ⟨Q, hQ, rfl⟩
    have : (ι t e i).base Q ∈ closure {lineUGen t e 𝔭 ht i} ∩ Set.range (ι t e i).base := by
      rw [closure_lineUGen_last_inter_range_self]; exact ⟨Q, hQ, rfl⟩
    exact this.1

section maximal
variable [𝔭.IsMaximal]

theorem eq_originPt_of_lineU_le_of_lineV_le {Q : chartScheme t} (hU : lineUIdeal t 𝔭 ht ≤ Q.asIdeal)
    (hV : lineVIdeal t 𝔭 ht ≤ Q.asIdeal) : Q = ⟨originIdeal t 𝔭 ht, inferInstance⟩ :=
  eq_origin_pt_of_mem t 𝔭 ht ((lineUIdeal_le_iff t 𝔭 ht).mp hU).1 ((lineVIdeal_le_iff t 𝔭 ht).mp hV).1
    ((lineUIdeal_le_iff t 𝔭 ht).mp hU).2

theorem closure_lineGen_inter_closure_lineGen_succ (k k' : Fin e) (hk : (k' : ℕ) = (k : ℕ) + 1) :
    closure {lineGen t e 𝔭 ht k} ∩ closure {lineGen t e 𝔭 ht k'} = {origin t e 𝔭 ht k} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · refine ⟨origin_mem_closure_lineGen t e 𝔭 ht k, ?_⟩
    have hk2 : (k : ℕ) + 1 < e := hk ▸ k'.2
    have : k' = ⟨(k : ℕ) + 1, hk2⟩ := Fin.ext hk
    rw [this]; exact origin_mem_closure_lineGen_succ t e 𝔭 ht k hk2
  · rintro z ⟨hz1, hz2⟩
    rcases (mem_closure_lineGen_iff t e 𝔭 ht k z).mp hz1 with ⟨Q, hQ, rfl⟩ | ⟨i, Q, hi, hQ, rfl⟩
    ·
      rcases (mem_closure_lineGen_iff t e 𝔭 ht k' _).mp hz2 with ⟨Q', hQ', h'⟩ | ⟨i', Q', hi', hQ', h'⟩
      · exfalso
        have hne : k' ≠ k := fun h => by have := congrArg Fin.val h; omega
        exact ι_apply_ne_of_V_mem t e hne ((lineVIdeal_le_iff t 𝔭 ht).mp hQ').1
          ((lineVIdeal_le_iff t 𝔭 ht).mp hQ).1 h'
      · have hik : i' = k := Fin.ext (by omega)
        subst hik
        have hQQ : Q' = Q := ι_apply_injective t e i' h'
        subst hQQ
        rw [eq_originPt_of_lineU_le_of_lineV_le t 𝔭 ht hQ' hQ]; rfl
    ·
      exfalso
      rcases (mem_closure_lineGen_iff t e 𝔭 ht k' _).mp hz2 with ⟨Q', hQ', h'⟩ | ⟨i', Q', hi', hQ', h'⟩
      ·
        have := U_notMem_and_V_notMem_of_ι_apply_eq_of_two_le t e h' (Or.inr (by omega))
        exact this.2 ((lineVIdeal_le_iff t 𝔭 ht).mp hQ').1
      · have hne : i' ≠ i := fun h => by have := congrArg Fin.val h; omega
        exact ι_apply_ne_of_U_mem t e hne ((lineUIdeal_le_iff t 𝔭 ht).mp hQ').1
          ((lineUIdeal_le_iff t 𝔭 ht).mp hQ).1 h'

theorem closure_lineGen_inter_closure_lineGen_of_two_le (k k' : Fin e) (hk : (k : ℕ) + 2 ≤ k') :
    closure {lineGen t e 𝔭 ht k} ∩ closure {lineGen t e 𝔭 ht k'} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hz1, hz2⟩
  rcases (mem_closure_lineGen_iff t e 𝔭 ht k z).mp hz1 with ⟨Q, hQ, rfl⟩ | ⟨i, Q, hi, hQ, rfl⟩ <;>
    rcases (mem_closure_lineGen_iff t e 𝔭 ht k' _).mp hz2 with ⟨Q', hQ', h'⟩ | ⟨i', Q', hi', hQ', h'⟩
  · have := U_notMem_and_V_notMem_of_ι_apply_eq_of_two_le t e h' (Or.inr hk)
    exact this.2 ((lineVIdeal_le_iff t 𝔭 ht).mp hQ').1
  ·
    by_cases h1 : (i' : ℕ) = k + 1
    · have := V_notMem_and_U_notMem_of_ι_apply_eq_succ t e h'.symm h1
      exact this.1 ((lineVIdeal_le_iff t 𝔭 ht).mp hQ).1
    · have := U_notMem_and_V_notMem_of_ι_apply_eq_of_two_le t e h' (Or.inr (by omega))
      exact this.1 ((lineUIdeal_le_iff t 𝔭 ht).mp hQ').1
  · have := U_notMem_and_V_notMem_of_ι_apply_eq_of_two_le t e h' (Or.inr (by omega))
    exact this.2 ((lineVIdeal_le_iff t 𝔭 ht).mp hQ').1
  · have := U_notMem_and_V_notMem_of_ι_apply_eq_of_two_le t e h' (Or.inr (by omega))
    exact this.1 ((lineUIdeal_le_iff t 𝔭 ht).mp hQ').1

theorem closure_lineGen_inter_closure_lineUGen_last (i : Fin e) (hi : (i : ℕ) + 1 = e) :
    closure {lineGen t e 𝔭 ht i} ∩ closure {lineUGen t e 𝔭 ht i} = {origin t e 𝔭 ht i} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨origin_mem_closure_lineGen t e 𝔭 ht i, origin_mem_closure_lineUGen t e 𝔭 ht i⟩, ?_⟩
  rintro z ⟨hz1, hz2⟩
  obtain ⟨Q', hQ', rfl⟩ := (mem_closure_lineUGen_last_iff t e 𝔭 ht i hi z).mp hz2
  rcases (mem_closure_lineGen_iff t e 𝔭 ht i _).mp hz1 with ⟨Q, hQ, h⟩ | ⟨j, Q, hj, hQ, h⟩
  · have hQQ : Q = Q' := ι_apply_injective t e i h
    subst hQQ
    rw [eq_originPt_of_lineU_le_of_lineV_le t 𝔭 ht hQ' hQ]; rfl
  · exfalso
    have hne : j ≠ i := fun h' => by have := congrArg Fin.val h'; omega
    exact ι_apply_ne_of_U_mem t e hne ((lineUIdeal_le_iff t 𝔭 ht).mp hQ).1
      ((lineUIdeal_le_iff t 𝔭 ht).mp hQ').1 h

theorem closure_lineGen_zero_inter_closure_lineUGen_last (k i : Fin e) (hk : (k : ℕ) = 0) (hi : (i : ℕ) + 1 = e)
    (he : 2 ≤ e) : closure {lineGen t e 𝔭 ht k} ∩ closure {lineUGen t e 𝔭 ht i} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨Q', hQ', rfl⟩ := (mem_closure_lineUGen_last_iff t e 𝔭 ht i hi z).mp hz2
  rcases (mem_closure_lineGen_iff t e 𝔭 ht k _).mp hz1 with ⟨Q, hQ, h⟩ | ⟨j, Q, hj, hQ, h⟩
  · by_cases h1 : (i : ℕ) = k + 1
    · have := V_notMem_and_U_notMem_of_ι_apply_eq_succ t e h h1
      exact this.1 ((lineVIdeal_le_iff t 𝔭 ht).mp hQ).1
    · have := U_notMem_and_V_notMem_of_ι_apply_eq_of_two_le t e h (Or.inl (by omega))
      exact this.2 ((lineVIdeal_le_iff t 𝔭 ht).mp hQ).1
  · omega

omit [𝔭.IsMaximal] in
theorem toCrossing_ι_apply (i : Fin e) (P : chartScheme t) :
    toCrossing t e (ι t e i P) = ⟨P.asIdeal.comap (resolutionChart t e i).toRingHom, inferInstance⟩ := by
  rw [← Scheme.Hom.comp_apply, ι_toCrossing]
  rfl

theorem eq_origin_or_mem_closure_lineGen_of_toCrossing_eq_vertexPt (he : 1 ≤ e) (z : Resolution t e)
    (hz : toCrossing t e z = vertexPt t e 𝔭 ht he) :
    (∃ i, z = origin t e 𝔭 ht i) ∨ ∃ k : Fin e, 1 ≤ (k : ℕ) ∧ z ∈ closure {lineGen t e 𝔭 ht k} := by
  obtain ⟨i, P, rfl⟩ := exists_ι_apply_eq t e z
  rw [toCrossing_ι_apply] at hz
  have hcomap : P.asIdeal.comap (resolutionChart t e i).toRingHom = vertexIdeal t 𝔭 ht e he := congrArg PrimeSpectrum.asIdeal hz

  have h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P.asIdeal := by
    intro w hw
    have : algebraMap W (CrossingQuotient W (t ^ e)) w ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact algebraMap_mem_originIdeal _ _ _ hw
    rw [Ideal.mem_comap] at this
    simpa [AlgHom.commutes] using this
  have hUi : algebraMap W _ (t ^ (i : ℕ)) * U t ∈ P.asIdeal := by
    have : U (t ^ e) ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact U_mem_originIdeal _ _ _
    rw [Ideal.mem_comap] at this
    simpa [resolutionChart_U] using this
  have hVi : algebraMap W _ (t ^ (e - 1 - (i : ℕ))) * V t ∈ P.asIdeal := by
    have : V (t ^ e) ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact V_mem_originIdeal _ _ _
    rw [Ideal.mem_comap] at this
    simpa [resolutionChart_V] using this
  have hUV : U t ∈ P.asIdeal ∨ V t ∈ P.asIdeal := by
    apply P.isPrime.mem_or_mem
    rw [U_mul_V]; exact h𝔭 t ht
  have hU0 : (i : ℕ) = 0 → U t ∈ P.asIdeal := fun h0 => by
    rw [h0, pow_zero, map_one, one_mul] at hUi; exact hUi
  have hVlast : (i : ℕ) + 1 = e → V t ∈ P.asIdeal := fun hl => by
    rw [show e - 1 - (i : ℕ) = 0 by omega, pow_zero, map_one, one_mul] at hVi; exact hVi
  by_cases hU : U t ∈ P.asIdeal
  · by_cases hV : V t ∈ P.asIdeal
    · left
      refine ⟨i, ?_⟩
      rw [eq_origin_pt_of_mem t 𝔭 ht hU hV h𝔭]; rfl
    ·
      right
      have hlt : (i : ℕ) + 1 < e := by
        rcases Nat.lt_or_ge ((i : ℕ) + 1) e with h | h
        · exact h
        · exact absurd (hVlast (by omega)) hV
      refine ⟨⟨(i : ℕ) + 1, hlt⟩, by simp, ?_⟩
      rw [mem_closure_lineGen_iff]
      exact Or.inr ⟨i, P, rfl, (lineUIdeal_le_iff t 𝔭 ht).mpr ⟨hU, h𝔭⟩, rfl⟩
  · have hV : V t ∈ P.asIdeal := hUV.resolve_left hU
    right
    have hi1 : 1 ≤ (i : ℕ) := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
      · exact absurd (hU0 h) hU
      · exact h
    refine ⟨i, hi1, ?_⟩
    rw [mem_closure_lineGen_iff]
    exact Or.inl ⟨P, (lineVIdeal_le_iff t 𝔭 ht).mpr ⟨hV, h𝔭⟩, rfl⟩

end maximal

end MvPolynomial.CrossingQuotient.Resolution

end

noncomputable section

namespace MvPolynomial.CrossingQuotient.Resolution

open AlgebraicGeometry CategoryTheory

universe u

variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

theorem mem_of_toCrossing_ι_eq_vertexPt (he : 1 ≤ e) (i : Fin e) (P : chartScheme t)
    (h : toCrossing t e (ι t e i P) = vertexPt t e 𝔭 ht he) :
    (∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P.asIdeal) ∧
      ((i : ℕ) = 0 → U t ∈ P.asIdeal) ∧ ((i : ℕ) + 1 = e → V t ∈ P.asIdeal) := by
  rw [toCrossing_ι_apply] at h
  have hcomap : P.asIdeal.comap (resolutionChart t e i).toRingHom = vertexIdeal t 𝔭 ht e he :=
    congrArg PrimeSpectrum.asIdeal h
  refine ⟨fun w hw => ?_, fun h0 => ?_, fun hl => ?_⟩
  · have : algebraMap W (CrossingQuotient W (t ^ e)) w ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact algebraMap_mem_originIdeal _ _ _ hw
    rw [Ideal.mem_comap] at this
    simpa [AlgHom.commutes] using this
  · have : U (t ^ e) ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact U_mem_originIdeal _ _ _
    rw [Ideal.mem_comap] at this
    simpa [resolutionChart_U, h0] using this
  · have : V (t ^ e) ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact V_mem_originIdeal _ _ _
    rw [Ideal.mem_comap] at this
    simpa [resolutionChart_V, show e - 1 - (i : ℕ) = 0 by omega] using this

theorem origin_mem_closure_lineUGen_pred (d k : Fin e) (hk : (k : ℕ) + 1 = d) :
    origin t e 𝔭 ht d ∈ closure {lineUGen t e 𝔭 ht k} := by
  rw [lineUGen_eq_lineGen t e 𝔭 ht (i := k) (j := d) hk.symm]
  exact origin_mem_closure_lineGen t e 𝔭 ht d

variable [𝔭.IsMaximal]

theorem exists_eq_origin_of_mem_closure_lineUGen_of_lt (k k' : Fin e) (o : Resolution t e) (hkk' : (k : ℕ) < k')
    (hk' : (k' : ℕ) + 1 < e)
    (ho : o ∈ closure {lineUGen t e 𝔭 ht k}) (ho' : o ∈ closure {lineUGen t e 𝔭 ht k'}) :
    ∃ d : Fin e, (d : ℕ) = k + 1 ∧ (k' : ℕ) = k + 1 ∧ o = origin t e 𝔭 ht d := by
  have hk : (k : ℕ) + 1 < e := by omega
  rw [lineUGen_eq_lineGen_succ t e 𝔭 ht k hk] at ho
  rw [lineUGen_eq_lineGen_succ t e 𝔭 ht k' hk'] at ho'
  by_cases h1 : (k' : ℕ) = k + 1
  · have hmem : o ∈ closure {lineGen t e 𝔭 ht ⟨(k : ℕ) + 1, hk⟩} ∩ closure {lineGen t e 𝔭 ht ⟨(k' : ℕ) + 1, hk'⟩} :=
      ⟨ho, ho'⟩
    rw [closure_lineGen_inter_closure_lineGen_succ t e 𝔭 ht _ _ (by simp [h1])] at hmem
    exact ⟨⟨(k : ℕ) + 1, hk⟩, rfl, h1, hmem⟩
  · exfalso
    have hmem : o ∈ closure {lineGen t e 𝔭 ht ⟨(k : ℕ) + 1, hk⟩} ∩ closure {lineGen t e 𝔭 ht ⟨(k' : ℕ) + 1, hk'⟩} :=
      ⟨ho, ho'⟩
    rw [closure_lineGen_inter_closure_lineGen_of_two_le t e 𝔭 ht _ _ (by simp; omega)] at hmem
    exact hmem

theorem eq_or_eq_of_origin_mem_closure_lineUGen (d k : Fin e) (hk : (k : ℕ) + 1 < e)
    (h : origin t e 𝔭 ht d ∈ closure {lineUGen t e 𝔭 ht k}) : (d : ℕ) = k ∨ (d : ℕ) = k + 1 := by
  rw [lineUGen_eq_lineGen_succ t e 𝔭 ht k hk, mem_closure_lineGen_iff] at h
  rcases h with ⟨Q, -, hQ⟩ | ⟨i, Q, hi, -, hQ⟩
  · right
    have : origin t e 𝔭 ht d ∈ Set.range (ι t e ⟨(k : ℕ) + 1, hk⟩).base := ⟨Q, hQ⟩
    rw [origin_mem_range_ι_iff] at this
    exact (congrArg Fin.val this).symm
  · left
    have : origin t e 𝔭 ht d ∈ Set.range (ι t e i).base := ⟨Q, hQ⟩
    rw [origin_mem_range_ι_iff] at this
    have := congrArg Fin.val this
    simp only [Fin.val_mk] at hi this
    omega

theorem eq_origin_of_mem_closure_lineGen_zero (he : 1 ≤ e) (k : Fin e) (hk : (k : ℕ) = 0) (o : Resolution t e)
    (ho : o ∈ closure {lineGen t e 𝔭 ht k}) (hv : toCrossing t e o = vertexPt t e 𝔭 ht he) :
    o = origin t e 𝔭 ht k := by
  rw [mem_closure_lineGen_iff] at ho
  rcases ho with ⟨Q, hQ, rfl⟩ | ⟨i, Q, hi, -, -⟩
  · obtain ⟨h𝔭, hU, -⟩ := mem_of_toCrossing_ι_eq_vertexPt t e 𝔭 ht he k Q hv
    change (ι t e k).base Q = (ι t e k).base _
    rw [eq_origin_pt_of_mem t 𝔭 ht (hU hk) ((lineVIdeal_le_iff t 𝔭 ht).mp hQ).1 h𝔭]
  · omega

theorem eq_origin_of_mem_closure_lineUGen_last (he : 1 ≤ e) (i : Fin e) (hi : (i : ℕ) + 1 = e) (o : Resolution t e)
    (ho : o ∈ closure {lineUGen t e 𝔭 ht i}) (hv : toCrossing t e o = vertexPt t e 𝔭 ht he) :
    o = origin t e 𝔭 ht i := by
  rw [mem_closure_lineUGen_last_iff t e 𝔭 ht i hi] at ho
  obtain ⟨Q, hQ, rfl⟩ := ho
  obtain ⟨h𝔭, -, hV⟩ := mem_of_toCrossing_ι_eq_vertexPt t e 𝔭 ht he i Q hv
  change (ι t e i).base Q = (ι t e i).base _
  rw [eq_origin_pt_of_mem t 𝔭 ht ((lineUIdeal_le_iff t 𝔭 ht).mp hQ).1 (hV hi) h𝔭]

end MvPolynomial.CrossingQuotient.Resolution

end


