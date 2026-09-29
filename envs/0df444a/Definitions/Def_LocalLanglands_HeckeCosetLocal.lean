-- Prove2me | Definitions.Def_LocalLanglands_HeckeCosetLocal
-- name    : LocalLanglands_HeckeCosetLocal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f0217b34-2311-5352-b410-5eb36df78fc2
-- title:
--   Local Hecke cosets for GL2​ over a discrete valuation ring
-- statement:
--   Throughout, $R$ is a discrete valuation domain with fraction field $K$, and $U =$ `integralSubgroup R K` denotes the image of $\mathrm{GL}_2(R)$ in $G = \mathrm{GL}_2(K)$ under the map induced by $R \to K$. The module fixes the standard elements: `unipotentR b` is the unipotent matrix $\begin{pmatrix}1&b\\0&1\end{pmatrix}$ and `weylR` the permutation matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ in $\mathrm{GL}_2(R)$, with images `unipotentInt`, `weylInt` in $G$, both lying in $U$; and, for $\varpi \in R$ with $\varpi \neq 0$ in $K$, `diagPi` is $\mathrm{diag}(\varpi,1) \in G$, with inverse $\mathrm{diag}(\varpi^{-1},1)$. The candidate coset representatives are `localRepSome b` $= \begin{pmatrix}\varpi & b\\0&1\end{pmatrix}$ for $b \in R$ and `localRepInf` $= \begin{pmatrix}1&0\\0&\varpi\end{pmatrix}$, the latter being the conjugate of `diagPi` by the Weyl element. The set `heckeMulSet` is the product $U \cdot \{\mathrm{diag}(\varpi,1)\}$ in $G$.
--
--   The accompanying results analyse the image of `heckeMulSet` in the coset space $G/U$: the cosets of `localRepSome b` and `localRepSome b'` coincide exactly when $\varpi \mid b'-b$; the coset of `localRepInf` differs from every coset of `localRepSome b` as soon as $\varpi$ is not a unit; conversely, if $\varpi$ is a unit all the `localRepSome b` lie in one coset. A conjugation lemma states that $\mathrm{diag}(\varpi,1)^{-1} z\,\mathrm{diag}(\varpi,1) \in U$ whenever $z \in \mathrm{GL}_2(R)$ has upper-right entry divisible by $\varpi$; it yields `exists_rep_of_mem_heckeMulSet`: for $\varpi$ irreducible, every $x \in U \cdot \mathrm{diag}(\varpi,1)$ has $xU$ equal to $\mathrm{localRepSome}(b)\,U$ for some $b \in R$, or to $\mathrm{localRepInf}\,U$. Hence, when $R/\varpi R$ is finite, the image of `heckeMulSet` in $G/U$ is finite, being covered by a family indexed by `Option (R ⧸ Ideal.span {ϖ})`; `three_distinct_cosets` records that the cosets of $\mathrm{localRepSome}(0)$, $\mathrm{localRepSome}(1)$ and $\mathrm{localRepInf}$ are pairwise distinct. Feeding this finiteness into the project's abstract Hecke operator, `localHeckeOperator` is the $S$-linear endomorphism of the $U$-fixed points of a $G$-module $A$ (with commuting $S$-module structure) attached to $\mathrm{diag}(\varpi,1)$ and to the pair $(U,U)$, that is, the sum over coset representatives of $U \cdot \mathrm{diag}(\varpi,1)$ of the translation action.
--
--   **Relation to Mathlib.** Mathlib supplies $\mathrm{GL}_n$ and the functorial map induced by a ring homomorphism; the subgroup $U$ of integral matrices, the abstract Hecke operator on fixed points, and the coset analysis here are the project's own.
--
--   **Where it is used.** These representatives and the finiteness of the coset image supply the input required by the project's abstract Hecke operator construction, giving the local operator at $\mathrm{diag}(\varpi,1)$ for the pair $(\mathrm{GL}_2(R), \mathrm{GL}_2(K))$; specialised to $R = \mathbb{Z}_p$, $K = \mathbb{Q}_p$ it is the local $T_p$ used on the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalLanglands_HeckeCosetLocal.lean

import Mathlib
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_AbstractHeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MulAction
open scoped Pointwise

namespace LocalGL2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

def unipotentR (b : R) : GL (Fin 2) R :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def weylR : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def unipotentInt (K : Type*) [Field K] [Algebra R K] (b : R) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (algebraMap R K) (unipotentR b)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma unipotentInt_mem (b : R) : unipotentInt K b ∈ integralSubgroup R K :=
  ⟨_, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp] lemma coe_unipotentInt (b : R) :
    (unipotentInt K b : Matrix (Fin 2) (Fin 2) K) = !![1, algebraMap R K b; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentInt, unipotentR, Matrix.GeneralLinearGroup.map]

def weylInt (R K : Type*) [CommRing R] [Field K] [Algebra R K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (algebraMap R K) (weylR (R := R))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma weylInt_mem : weylInt R K ∈ integralSubgroup R K :=
  ⟨_, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp] lemma coe_weylInt :
    (weylInt R K : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylInt, weylR, Matrix.GeneralLinearGroup.map]

variable (ϖ : R)

section Defs

variable (hϖ0 : algebraMap R K ϖ ≠ 0)

def diagPi : GL (Fin 2) K :=
  ⟨!![algebraMap R K ϖ, 0; 0, 1], !![(algebraMap R K ϖ)⁻¹, 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hϖ0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hϖ0]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp] lemma coe_diagPi :
    (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) = !![algebraMap R K ϖ, 0; 0, 1] := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp] lemma coe_diagPi_inv :
    ((diagPi ϖ hϖ0)⁻¹ : GL (Fin 2) K).val = !![(algebraMap R K ϖ)⁻¹, 0; 0, 1] := rfl

def localRepSome (b : R) : GL (Fin 2) K :=
  unipotentInt K b * diagPi ϖ hϖ0

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp] lemma coe_localRepSome (b : R) :
    (localRepSome ϖ hϖ0 b : Matrix (Fin 2) (Fin 2) K)
      = !![algebraMap R K ϖ, algebraMap R K b; 0, 1] := by
  show (unipotentInt K b : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      = _
  rw [coe_unipotentInt, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def localRepInf : GL (Fin 2) K :=
  weylInt R K * diagPi ϖ hϖ0 * weylInt R K

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[simp] lemma coe_localRepInf :
    (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, algebraMap R K ϖ] := by
  show (weylInt R K : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      * (weylInt R K : Matrix (Fin 2) (Fin 2) K) = _
  rw [coe_weylInt, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

lemma unipotentInt_inv (b : R) : (unipotentInt K b)⁻¹ = unipotentInt K (-b) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_unipotentInt, coe_unipotentInt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, map_neg]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

@[simp] lemma coe_localRepSome_inv (b : R) :
    ((localRepSome ϖ hϖ0 b)⁻¹ : GL (Fin 2) K).val
      = !![(algebraMap R K ϖ)⁻¹, -(algebraMap R K b) * (algebraMap R K ϖ)⁻¹; 0, 1] := by
  rw [localRepSome, _root_.mul_inv_rev, Units.val_mul, coe_diagPi_inv, unipotentInt_inv,
    coe_unipotentInt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

def heckeMulSet : Set (GL (Fin 2) K) :=
  (integralSubgroup R K : Set (GL (Fin 2) K)) * ({diagPi ϖ hϖ0} : Set (GL (Fin 2) K))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma mem_heckeMulSet_iff {x : GL (Fin 2) K} :
    x ∈ heckeMulSet ϖ hϖ0 ↔ ∃ u ∈ integralSubgroup R K, u * diagPi ϖ hϖ0 = x := by
  unfold heckeMulSet
  rw [Set.mem_mul]
  constructor
  · rintro ⟨u, hu, y, hy, rfl⟩
    exact ⟨u, hu, by rw [Set.mem_singleton_iff] at hy; rw [hy]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, diagPi ϖ hϖ0, rfl, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

lemma mk_localRepSome_mem_image (b : R) :
    QuotientGroup.mk (localRepSome ϖ hϖ0 b)
      ∈ (QuotientGroup.mk '' (heckeMulSet ϖ hϖ0) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)) :=
  Set.mem_image_of_mem _
    ((mem_heckeMulSet_iff ϖ hϖ0).mpr ⟨unipotentInt K b, unipotentInt_mem b, rfl⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

lemma mk_localRepInf_mem_image :
    QuotientGroup.mk (localRepInf ϖ hϖ0)
      ∈ (QuotientGroup.mk '' (heckeMulSet ϖ hϖ0) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)) := by
  refine (Set.mem_image _ _ _).mpr ⟨weylInt R K * diagPi ϖ hϖ0,
    (mem_heckeMulSet_iff ϖ hϖ0).mpr ⟨weylInt R K, weylInt_mem, rfl⟩, ?_⟩
  rw [QuotientGroup.eq]
  show (weylInt R K * diagPi ϖ hϖ0)⁻¹ * (weylInt R K * diagPi ϖ hϖ0 * weylInt R K)
      ∈ integralSubgroup R K
  rw [inv_mul_cancel_left]
  exact weylInt_mem

omit [IsDomain R] [IsDiscreteValuationRing R] in

lemma dvd_sub_of_mk_localRepSome_eq {b b' : R}
    (h : (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
        = QuotientGroup.mk (localRepSome ϖ hϖ0 b')) :
    ϖ ∣ b' - b := by
  rw [QuotientGroup.eq] at h
  obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup h 0 1

  rw [Units.val_mul, coe_localRepSome_inv, coe_localRepSome] at hr
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hr
  norm_num at hr

  have hϖinj := IsFractionRing.injective R K
  refine ⟨r, hϖinj ?_⟩
  rw [map_sub, map_mul]
  field_simp at hr ⊢
  linear_combination -hr

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

lemma mk_localRepSome_eq_of_dvd_sub {b b' : R} (h : ϖ ∣ b' - b) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
      = QuotientGroup.mk (localRepSome ϖ hϖ0 b') := by
  obtain ⟨r, hr⟩ := h
  rw [QuotientGroup.eq]
  refine ⟨unipotentR r, ?_⟩

  refine Units.ext ?_
  show (Matrix.GeneralLinearGroup.map (algebraMap R K) (unipotentR r)).val
      = (((localRepSome ϖ hϖ0 b)⁻¹ * localRepSome ϖ hϖ0 b' : GL (Fin 2) K)).val
  rw [Units.val_mul, coe_localRepSome_inv, coe_localRepSome]
  have hb' : algebraMap R K (b' - b) = algebraMap R K ϖ * algebraMap R K r := by
    rw [← map_mul, hr]
  rw [map_sub] at hb'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentR, Matrix.GeneralLinearGroup.map, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp
  linear_combination -hb'

omit [IsDomain R] [IsDiscreteValuationRing R] in

lemma mk_localRepSome_ne_mk_localRepInf (hϖ : ¬ IsUnit ϖ) (b : R) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
      ≠ QuotientGroup.mk (localRepInf ϖ hϖ0) := by
  intro h
  rw [QuotientGroup.eq] at h
  obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup h 0 0
  rw [Units.val_mul, coe_localRepSome_inv, coe_localRepInf] at hr
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hr
  norm_num at hr

  apply hϖ
  have hϖinj := IsFractionRing.injective R K
  have hone : ϖ * r = 1 := by
    apply hϖinj
    rw [map_mul, map_one, hr, mul_inv_cancel₀ hϖ0]
  exact IsUnit.of_mul_eq_one r hone

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

lemma conj_diagPi_mem_of_dvd (z : GL (Fin 2) R)
    (h : ϖ ∣ (z : Matrix (Fin 2) (Fin 2) R) 0 1) :
    (diagPi ϖ hϖ0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) z * diagPi ϖ hϖ0
      ∈ integralSubgroup R K := by
  obtain ⟨e, he⟩ := h
  set M : Matrix (Fin 2) (Fin 2) R :=
    !![(z : Matrix (Fin 2) (Fin 2) R) 0 0, e;
       (z : Matrix (Fin 2) (Fin 2) R) 1 0 * ϖ, (z : Matrix (Fin 2) (Fin 2) R) 1 1] with hM
  have hdet : M.det = ((z : Matrix (Fin 2) (Fin 2) R)).det := by
    rw [hM, Matrix.det_fin_two_of, Matrix.det_fin_two, he]
    ring
  have hMunit : IsUnit M.det := by
    rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det z).isUnit
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hMunit, ?_⟩
  have hz01 : (algebraMap R K) ((z : Matrix (Fin 2) (Fin 2) R) 0 1)
      = algebraMap R K ϖ * algebraMap R K e := by rw [← map_mul, he]

  have hcomm : diagPi ϖ hϖ0 * Matrix.GeneralLinearGroup.map (algebraMap R K)
        (Matrix.GeneralLinearGroup.mk'' M hMunit)
      = Matrix.GeneralLinearGroup.map (algebraMap R K) z * diagPi ϖ hϖ0 := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagPi]
    rw [show ((Matrix.GeneralLinearGroup.map (algebraMap R K) z) : Matrix (Fin 2) (Fin 2) K)
        = (algebraMap R K).mapMatrix (z : Matrix (Fin 2) (Fin 2) R) from rfl]
    rw [show ((Matrix.GeneralLinearGroup.map (algebraMap R K)
          (Matrix.GeneralLinearGroup.mk'' M hMunit)) : Matrix (Fin 2) (Fin 2) K)
        = (algebraMap R K).mapMatrix M from rfl]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, Matrix.mul_apply, Fin.sum_univ_two, RingHom.mapMatrix_apply, map_mul,
        hz01]
    ring

  symm
  calc (diagPi ϖ hϖ0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) z * diagPi ϖ hϖ0
      = (diagPi ϖ hϖ0)⁻¹ * (Matrix.GeneralLinearGroup.map (algebraMap R K) z
          * diagPi ϖ hϖ0) := by rw [mul_assoc]
    _ = (diagPi ϖ hϖ0)⁻¹ * (diagPi ϖ hϖ0 * Matrix.GeneralLinearGroup.map (algebraMap R K)
          (Matrix.GeneralLinearGroup.mk'' M hMunit)) := by rw [hcomm]
    _ = Matrix.GeneralLinearGroup.map (algebraMap R K)
          (Matrix.GeneralLinearGroup.mk'' M hMunit) := by rw [inv_mul_cancel_left]

omit [IsFractionRing R K] in

theorem exists_rep_of_mem_heckeMulSet (hϖirr : Irreducible ϖ) {x : GL (Fin 2) K}
    (hx : x ∈ heckeMulSet ϖ hϖ0) :
    (∃ b, (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
        = QuotientGroup.mk x)
      ∨ (QuotientGroup.mk (localRepInf ϖ hϖ0) : _ ⧸ integralSubgroup R K)
          = QuotientGroup.mk x := by
  obtain ⟨u, hu, rfl⟩ := (mem_heckeMulSet_iff ϖ hϖ0).mp hx
  obtain ⟨y, rfl⟩ := hu
  by_cases hd : IsUnit ((y : Matrix (Fin 2) (Fin 2) R) 1 1)
  ·
    left
    obtain ⟨d, hd⟩ := hd
    refine ⟨(y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R), ?_⟩
    rw [QuotientGroup.eq]
    have key : (localRepSome ϖ hϖ0 ((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R)))⁻¹
        * (Matrix.GeneralLinearGroup.map (algebraMap R K) y * diagPi ϖ hϖ0)
        = (diagPi ϖ hϖ0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K)
            (unipotentR (-((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R))) * y)
          * diagPi ϖ hϖ0 := by
      rw [localRepSome, _root_.mul_inv_rev, unipotentInt_inv, map_mul, unipotentInt]
      group
    rw [key]
    refine conj_diagPi_mem_of_dvd ϖ hϖ0 _ ?_

    have : ((unipotentR (-((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R))) * y :
        GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
      rw [Units.val_mul]
      show ((!![1, -((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R)); 0, 1] :
          Matrix (Fin 2) (Fin 2) R) * (y : Matrix (Fin 2) (Fin 2) R)) 0 1 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [← hd]
      simp [mul_assoc, Units.inv_mul]
    rw [this]
    exact dvd_zero ϖ
  ·
    right
    have hdvd : ϖ ∣ (y : Matrix (Fin 2) (Fin 2) R) 1 1 := by
      rw [← Ideal.mem_span_singleton, ← hϖirr.maximalIdeal_eq]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hd)
    rw [QuotientGroup.eq]
    have key : (localRepInf ϖ hϖ0)⁻¹
        * (Matrix.GeneralLinearGroup.map (algebraMap R K) y * diagPi ϖ hϖ0)
        = (weylInt R K)⁻¹ * ((diagPi ϖ hϖ0)⁻¹
            * Matrix.GeneralLinearGroup.map (algebraMap R K) (weylR⁻¹ * y)
          * diagPi ϖ hϖ0) := by
      rw [localRepInf, weylInt, map_mul, map_inv]
      group
    rw [key]
    rw [mul_mem_cancel_left (inv_mem (weylInt_mem (R := R) (K := K)))]
    refine conj_diagPi_mem_of_dvd ϖ hϖ0 _ ?_

    have : ((weylR⁻¹ * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1
        = (y : Matrix (Fin 2) (Fin 2) R) 1 1 := by
      rw [Units.val_mul]
      show ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) * (y : Matrix (Fin 2) (Fin 2) R)) 0 1
          = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp
    rw [this]
    exact hdvd

omit [IsFractionRing R K] in

theorem finite_image_mul_diagPi (hϖirr : Irreducible ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})] :
    (QuotientGroup.mk '' (heckeMulSet ϖ hϖ0) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by
  classical
  refine Set.Finite.subset (Set.finite_range
    (fun c : Option (R ⧸ Ideal.span {ϖ}) =>
      (Option.elim c (QuotientGroup.mk (localRepInf ϖ hϖ0))
        (fun cc => QuotientGroup.mk (localRepSome ϖ hϖ0 (Quotient.out cc)))
        : GL (Fin 2) K ⧸ integralSubgroup R K))) ?_
  rintro _ ⟨x, hx, rfl⟩
  rcases exists_rep_of_mem_heckeMulSet ϖ hϖ0 hϖirr hx with ⟨b, hb⟩ | hinf
  · refine ⟨some (Ideal.Quotient.mk _ b), ?_⟩
    show QuotientGroup.mk (localRepSome ϖ hϖ0 (Quotient.out (Ideal.Quotient.mk _ b))) = _
    rw [← hb]
    refine mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 ?_
    rw [← Ideal.mem_span_singleton]
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm
  · exact ⟨none, hinf⟩

noncomputable def localHeckeOperator (hϖirr : Irreducible ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})]
    {A : Type*} [AddCommMonoid A] [DistribMulAction (GL (Fin 2) K) A]
    (S : Type*) [Ring S] [Module S A] [SMulCommClass (GL (Fin 2) K) S A] :
    MulAction.fixedPoints (integralSubgroup R K) A
      →ₗ[S] MulAction.fixedPoints (integralSubgroup R K) A :=
  AbstractHeckeOperator.HeckeOperator (R := S) (diagPi ϖ hϖ0) (integralSubgroup R K)
    (integralSubgroup R K) (finite_image_mul_diagPi ϖ hϖ0 hϖirr)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem three_distinct_cosets (hϖirr : Irreducible ϖ) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 0) : _ ⧸ integralSubgroup R K)
        ≠ QuotientGroup.mk (localRepSome ϖ hϖ0 1)
      ∧ (QuotientGroup.mk (localRepSome ϖ hϖ0 0) : _ ⧸ integralSubgroup R K)
          ≠ QuotientGroup.mk (localRepInf ϖ hϖ0)
      ∧ (QuotientGroup.mk (localRepSome ϖ hϖ0 1) : _ ⧸ integralSubgroup R K)
          ≠ QuotientGroup.mk (localRepInf ϖ hϖ0) := by
  refine ⟨fun h => ?_, mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖirr.not_isUnit 0,
    mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖirr.not_isUnit 1⟩
  have := dvd_sub_of_mk_localRepSome_eq ϖ hϖ0 h
  rw [sub_zero] at this
  exact hϖirr.not_isUnit (isUnit_of_dvd_one this)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem localRepInf_not_covered_by_finite (hϖirr : Irreducible ϖ) :
    ∀ b : R, (QuotientGroup.mk (localRepInf ϖ hϖ0) : _ ⧸ integralSubgroup R K)
      ≠ QuotientGroup.mk (localRepSome ϖ hϖ0 b) :=
  fun b h => mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖirr.not_isUnit b h.symm

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem localRepSome_collapse_of_isUnit (hϖu : IsUnit ϖ) (b : R) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
      = QuotientGroup.mk (localRepSome ϖ hϖ0 0) :=
  mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 hϖu.dvd

end Defs

example : Fintype.card (Option (Fin 2)) = 2 + 1 := by decide

end LocalGL2


