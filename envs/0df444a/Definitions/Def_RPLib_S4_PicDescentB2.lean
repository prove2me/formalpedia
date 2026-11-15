-- Prove2me | Definitions.Def_RPLib_S4_PicDescentB2
-- name    : RPLib_S4_PicDescentB2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:07:18.487+00:00
-- url     : https://prove2.me/theorems/bfa7d933-cc68-4458-bc38-d8979933706b
-- title:
--   A constant field extension of a function field in coordinates
-- statement:
--   Let $F/\mathbb{F}_q$ be a function field with full constant field, $L/\mathbb{F}_q$ a finite extension with a power basis, and $F'/L$ a function field with compatible maps $F \to F'$, $L \to F'$, the same separating element $x$ and $[F' : F] = [L : \mathbb{F}_q]$. The file proves that the maps $\mathbb{F}_q[x] \to L[x] \to F'$ factor through $F$, that the generator of $L$ keeps its degree over $F$, that the images of the power basis form an $F$-basis of $F'$, that $$\operatorname{Tr}_{F'/F}(a) = \operatorname{Tr}_{L/\mathbb{F}_q}(a) \quad (a \in L),$$ and that coordinates are traces against the trace-dual basis.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6; M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8

import Definitions.Def_RPLib_S4_PicDescentB1

/-!
# S4-PicDescent, part B2: a generic constant field extension in coordinates

Setting of `RR.IsConstExt`: `F / Fq` a function field with full constant field (`constField Fq F = ⊥`),
`L / Fq` a finite extension with a power basis `pb`, and `F' / L` a function field with compatible maps
`F → F'`, `L → F'`, the same separating element (`hx`) and `[F' : F] = [L : Fq]` (`hdim`).
* `compat_poly`, `compat_rat`: the maps `Fq[x] → L[x] → F'` and `Fq(x) → L(x) → F'` factor through `F`.
* `natDegree_minpoly`: the image `α'` of `pb.gen` keeps its degree over `F` (coefficients of a factor of
  `μ` are algebraic over `Fq`, hence constants).
* `basisF`: the images of `pb.basis` form an `F`-basis of `F'`; `trace_algebraMap_L`:
  `Tr_{F'/F} (a) = Tr_{L/Fq} (a)` for `a ∈ L`.
* `coord_eq_trace`: coordinates are traces against the trace-dual basis `dualB pb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places Polynomial RR

section Compat

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']

theorem compat_poly_hom (hx : algebraMap F F' (xF Fq F) = xF L F') :
    (algebraMap L[X] F').comp (mapRingHom (algebraMap Fq L)) =
      (algebraMap F F').comp (algebraMap Fq[X] F) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : algebraMap L[X] F' (C (algebraMap Fq L a)) = algebraMap Fq F' a := by
      rw [IsScalarTower.algebraMap_apply Fq L F']
      exact (IsScalarTower.algebraMap_apply L L[X] F' _).symm
    have e2 : algebraMap Fq[X] F (C a) = algebraMap Fq F a :=
      (IsScalarTower.algebraMap_apply Fq Fq[X] F a).symm
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C]
    rw [e1, e2, ← IsScalarTower.algebraMap_apply Fq F F']
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    exact hx.symm

theorem compat_poly (hx : algebraMap F F' (xF Fq F) = xF L F') (p : Fq[X]) :
    algebraMap L[X] F' (p.map (algebraMap Fq L)) = algebraMap F F' (algebraMap Fq[X] F p) :=
  RingHom.congr_fun (compat_poly_hom hx) p

theorem compat_rat_hom (hx : algebraMap F F' (xF Fq F) = xF L F') :
    (algebraMap (RatFunc L) F').comp (ratMap Fq L) = (algebraMap F F').comp (algebraMap (RatFunc Fq) F) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors Fq[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratMap_algebraMap, ← IsScalarTower.algebraMap_apply L[X] (RatFunc L) F',
    ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F, compat_poly hx]

theorem compat_rat (hx : algebraMap F F' (xF Fq F) = xF L F') (g : RatFunc Fq) :
    algebraMap (RatFunc L) F' (ratMap Fq L g) = algebraMap F F' (algebraMap (RatFunc Fq) F g) :=
  RingHom.congr_fun (compat_rat_hom hx) g

end Compat

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']

variable (pb : PowerBasis Fq L)

/-- The generator keeps its degree over `F` when `F` has full constant field. -/
theorem natDegree_minpoly (hk : constField Fq F = ⊥) :
    (minpoly F (algebraMap L F' pb.gen)).natDegree = pb.dim := by
  have hint : IsIntegral Fq pb.gen := pb.isIntegral_gen
  have hμ : (minpoly Fq pb.gen).Monic := minpoly.monic hint
  have hα : IsIntegral F (algebraMap L F' pb.gen) := (hint.algebraMap (B := F')).tower_top
  have hdvd : minpoly F (algebraMap L F' pb.gen) ∣ (minpoly Fq pb.gen).map (algebraMap Fq F) := by
    refine minpoly.dvd F _ ?_
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hcoeff : ∀ n, (minpoly F (algebraMap L F' pb.gen)).coeff n ∈ Set.range (algebraMap Fq F) := by
    intro n
    have hi := Polynomial.isIntegral_coeff_of_dvd _ _ hμ (minpoly.monic hα) hdvd n
    have hmem : (minpoly F (algebraMap L F' pb.gen)).coeff n ∈ constField Fq F :=
      mem_algebraicClosure_iff'.2 hi
    rw [hk] at hmem
    exact IntermediateField.mem_bot.1 hmem
  obtain ⟨q0, hq0, hdeg, hmon⟩ :=
    lifts_and_degree_eq_and_monic ((lifts_iff_coeff_lifts _).2 hcoeff) (minpoly.monic hα)
  have h0 : aeval pb.gen q0 = 0 := by
    apply (algebraMap L F').injective
    rw [map_zero, ← aeval_algebraMap_apply, ← aeval_map_algebraMap F, hq0, minpoly.aeval]
  have hle1 : (minpoly Fq pb.gen).natDegree ≤ q0.natDegree :=
    natDegree_le_of_dvd (minpoly.dvd Fq _ h0) hmon.ne_zero
  have hle2 : (minpoly F (algebraMap L F' pb.gen)).natDegree ≤ (minpoly Fq pb.gen).natDegree := by
    have := natDegree_le_of_dvd hdvd ((hμ.map (algebraMap Fq F)).ne_zero)
    rwa [natDegree_map] at this
  have hq : q0.natDegree = (minpoly F (algebraMap L F' pb.gen)).natDegree := natDegree_eq_of_degree_eq hdeg
  rw [← pb.natDegree_minpoly]
  omega

theorem linearIndependent_basis (hk : constField Fq F = ⊥) :
    LinearIndependent F fun j => algebraMap L F' (pb.basis j) := by
  have h := linearIndependent_pow (K := F) (algebraMap L F' pb.gen)
  have e := natDegree_minpoly (F := F) (F' := F') pb hk
  have h2 := h.comp (Fin.cast e.symm) (Fin.cast_injective _)
  convert h2 using 1
  funext j
  simp [PowerBasis.coe_basis, map_pow]

theorem span_basis (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) :
    ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (pb.basis j)) := by
  have : Nonempty (Fin pb.dim) := ⟨⟨0, pb.dim_pos⟩⟩
  have hc : Fintype.card (Fin pb.dim) = Module.finrank F F' := by
    rw [Fintype.card_fin, hdim, pb.finrank]
  exact (LinearIndependent.span_eq_top_of_card_eq_finrank
    (linearIndependent_basis (F := F) (F' := F') pb hk) hc).ge

/-- The `F`-basis of `F'` given by the images of `pb.basis`. -/
noncomputable def basisF (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) : Module.Basis (Fin pb.dim) F F' :=
  Module.Basis.mk (linearIndependent_basis pb hk) (span_basis pb hk hdim)

theorem basisF_apply (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (j : Fin pb.dim) : basisF pb hk hdim j = algebraMap L F' (pb.basis j) :=
  Module.Basis.mk_apply _ _ _

include pb in
theorem finiteDimensional (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) : FiniteDimensional F F' :=
  Module.Finite.of_basis (basisF pb hk hdim)

theorem repr_algebraMap (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (x : L) (k : Fin pb.dim) :
    (basisF pb hk hdim).repr (algebraMap L F' x) k = algebraMap Fq F (pb.basis.repr x k) := by
  have h : algebraMap L F' (∑ i, pb.basis.repr x i • pb.basis i) =
      ∑ i, algebraMap Fq F (pb.basis.repr x i) • basisF pb hk hdim i := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, basisF_apply,
      ← IsScalarTower.algebraMap_apply Fq L F', ← IsScalarTower.algebraMap_apply Fq F F']
  conv_lhs => rw [← pb.basis.sum_repr x]
  rw [h, Module.Basis.repr_sum_self]

include pb in
/-- `Tr_{F'/F} (a) = Tr_{L/Fq} (a)` for `a ∈ L`. -/
theorem trace_algebraMap_L (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) (a : L) :
    Algebra.trace F F' (algebraMap L F' a) = algebraMap Fq F (Algebra.trace Fq L a) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (basisF pb hk hdim), Algebra.trace_eq_matrix_trace pb.basis,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, basisF_apply, ← map_mul, repr_algebraMap]

/-- The trace-dual basis of `pb.basis`. -/
noncomputable def dualB : Module.Basis (Fin pb.dim) Fq L :=
  haveI := pb.finite
  (Algebra.traceForm Fq L).dualBasis (traceForm_nondegenerate Fq L) pb.basis

theorem trace_dualB (i j : Fin pb.dim) :
    Algebra.trace Fq L (dualB pb i * pb.basis j) = if j = i then 1 else 0 := by
  have := pb.finite
  have h := (Algebra.traceForm Fq L).apply_dualBasis_left (traceForm_nondegenerate Fq L) pb.basis i j
  rwa [Algebra.traceForm_apply] at h

/-- Coordinates are traces against the dual basis. -/
theorem coord_eq_trace (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) (f : Fin pb.dim → F) (k : Fin pb.dim) :
    f k = Algebra.trace F F'
      ((∑ j, f j • algebraMap L F' (pb.basis j)) * algebraMap L F' (dualB pb k)) := by
  have h : ∀ j, Algebra.trace F F' (f j • algebraMap L F' (pb.basis j) * algebraMap L F' (dualB pb k)) =
      if j = k then f k else 0 := by
    intro j
    rw [smul_mul_assoc, map_smul, ← map_mul, trace_algebraMap_L pb hk hdim, mul_comm, trace_dualB,
      smul_eq_mul]
    split_ifs with hjk
    · rw [hjk, map_one, mul_one]
    · rw [map_zero, mul_zero]
  rw [Finset.sum_mul, map_sum]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Generic

end RamanujanPetersson.PicDescent


