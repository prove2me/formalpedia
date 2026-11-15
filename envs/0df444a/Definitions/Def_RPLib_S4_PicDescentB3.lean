-- Prove2me | Definitions.Def_RPLib_S4_PicDescentB3
-- name    : RPLib_S4_PicDescentB3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:11:48.603416+00:00
-- url     : https://prove2.me/theorems/76c173ca-f308-4a7e-89b6-5e2b2a611c97
-- title:
--   The generic constant field extension of a function field
-- statement:
--   In the setting of a constant field extension $F'/L$ of $F/\mathbb{F}_q$ given in coordinates, the file proves that $L[x]$ and $\mathcal{O}_\infty(L)$ are integral over the finite and infinite rings of $F$ inside $F'$, and that $\sum_j f_j c_j$ is integral over $L[x]$ (resp. $\mathcal{O}_\infty(L)$) if and only if every $f_j$ is integral over $\mathbb{F}_q[x]$ (resp. $\mathcal{O}_\infty(\mathbb{F}_q)$). Hence $F'$ is the constant field extension $F \otimes_{\mathbb{F}_q} L$ in the sense of the Riemann-Roch library, with $$g(F') = g(F)$$ and full constant field $L$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6 (Theorem 3.6.3); M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8

import Definitions.Def_RPLib_S4_PicDescentB2

/-!
# S4-PicDescent, part B3: the generic constant field extension is an `RR.IsConstExt`

In the setting of part B2 (`hk : constField Fq F = ⊥`, `hdim : [F' : F] = [L : Fq]`, same `x`):
* `isIntegral_Rfin_poly`, `isIntegral_Rinf_Oinf`: `L[x]` and `O_∞(L)` are integral over the rings `Rfin`,
  `Rinf` of `F` inside `F'`;
* `fin_iff`, `inf_iff`: an element `Σ f_j c_j` is integral over `L[x]` (resp. `O_∞(L)`) iff every `f_j` is
  integral over `Fq[x]` (resp. `O_∞(Fq)`) (trace-dual coordinates, `Algebra.isIntegral_trace`);
* `isConstExt`: hence `RR.IsConstExt Fq F L F' pb.basis`; `genusF_eq`, `constField_eq_bot`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places Polynomial RR

/-- Integrality over `R` through an intermediate ring `A` whose image is integral over `R`. -/
theorem isIntegral_of_forall_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] [Algebra A B] (h : ∀ a : A, IsIntegral R (algebraMap A B a)) {z : B}
    (hz : IsIntegral A z) : IsIntegral R z := by
  let φ : A →+* integralClosure R B := (algebraMap A B).codRestrict (integralClosure R B) h
  have h1 : IsIntegral (integralClosure R B) (RingHom.id B z) :=
    hz.map_of_comp_eq φ (RingHom.id B) (RingHom.ext fun _ => rfl)
  exact isIntegral_trans z h1

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

/-- Elements of `L` are integral over any subring `R` of `F` containing `Fq`. -/
theorem isIntegral_L {R : Type*} [CommRing R] [Algebra R F] [Algebra R F'] [IsScalarTower R F F']
    (φ : Fq →+* R) (hφ : ∀ r, algebraMap R F (φ r) = algebraMap Fq F r) (a : L) :
    IsIntegral R (algebraMap L F' a) := by
  refine (Algebra.IsIntegral.isIntegral (R := Fq) a).map_of_comp_eq φ (algebraMap L F')
    (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply R F F', hφ, ← IsScalarTower.algebraMap_apply Fq F F',
    ← IsScalarTower.algebraMap_apply Fq L F']

theorem isIntegral_Rfin_L (a : L) : IsIntegral (Rfin Fq F) (algebraMap L F' a) :=
  isIntegral_L ((algebraMap Fq[X] (Rfin Fq F)).comp (algebraMap Fq Fq[X]))
    (fun r => (IsScalarTower.algebraMap_apply Fq[X] (Rfin Fq F) F _).symm.trans
      (IsScalarTower.algebraMap_apply Fq Fq[X] F r).symm) a

theorem isIntegral_Rinf_L (a : L) : IsIntegral (Rinf Fq F) (algebraMap L F' a) :=
  isIntegral_L ((algebraMap (Oinf Fq) (Rinf Fq F)).comp (algebraMap Fq (Oinf Fq)))
    (fun r => (IsScalarTower.algebraMap_apply (Oinf Fq) (Rinf Fq F) F _).symm.trans
      (IsScalarTower.algebraMap_apply Fq (Oinf Fq) F r).symm) a

theorem isIntegral_Rfin_poly (hx : algebraMap F F' (xF Fq F) = xF L F') (p : L[X]) :
    IsIntegral (Rfin Fq F) (algebraMap L[X] F' p) := by
  have hX : IsIntegral (Rfin Fq F) (algebraMap L[X] F' X) := by
    change IsIntegral _ (xF L F')
    rw [← hx]
    have hm : xF Fq F ∈ integralClosure Fq[X] F := isIntegral_algebraMap
    exact isIntegral_algebraMap (R := Rfin Fq F) (A := F') (x := ⟨xF Fq F, hm⟩)
  rw [p.as_sum_range_C_mul_X_pow, map_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  have e : algebraMap L[X] F' (C (p.coeff i)) = algebraMap L F' (p.coeff i) :=
    (IsScalarTower.algebraMap_apply L L[X] F' _).symm
  rw [map_mul, map_pow, e]
  exact (isIntegral_Rfin_L _).mul (hX.pow _)

theorem isIntegral_Rinf_Oinf (pb : PowerBasis Fq L) (hx : algebraMap F F' (xF Fq F) = xF L F')
    (a : Oinf L) : IsIntegral (Rinf Fq F) (algebraMap (Oinf L) F' a) := by
  obtain ⟨g, hg, ha⟩ := exists_Oinf_coord pb.basis a.2
  rw [IsScalarTower.algebraMap_apply (Oinf L) (RatFunc L) F']
  change IsIntegral _ (algebraMap (RatFunc L) F' (a : RatFunc L))
  rw [ha, map_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [map_mul, compat_rat hx, ← IsScalarTower.algebraMap_apply L (RatFunc L) F']
  refine IsIntegral.mul ?_ (isIntegral_Rinf_L _)
  have hm : algebraMap (RatFunc Fq) F (g j) ∈ integralClosure (Oinf Fq) F := by
    have e : algebraMap (RatFunc Fq) F (g j) = algebraMap (Oinf Fq) F ⟨g j, hg j⟩ :=
      IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F ⟨g j, hg j⟩
    rw [e]; exact isIntegral_algebraMap
  exact isIntegral_algebraMap (R := Rinf Fq F) (A := F') (x := ⟨_, hm⟩)

variable (pb : PowerBasis Fq L)

theorem fin_iff (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') (f : Fin pb.dim → F) :
    (∑ j, f j • algebraMap L F' (pb.basis j)) ∈ (algebraMap (Rfin L F') F').range ↔
      ∀ j, f j ∈ (algebraMap (Rfin Fq F) F).range := by
  have := finiteDimensional pb hk hdim
  constructor
  · rintro ⟨z, hz⟩ k
    have hzi : IsIntegral L[X] (∑ j, f j • algebraMap L F' (pb.basis j)) := by rw [← hz]; exact z.2
    have h1 : IsIntegral (Rfin Fq F)
        ((∑ j, f j • algebraMap L F' (pb.basis j)) * algebraMap L F' (dualB pb k)) :=
      (isIntegral_of_forall_algebraMap (isIntegral_Rfin_poly hx) hzi).mul (isIntegral_Rfin_L _)
    have h2 := Algebra.isIntegral_trace (L := F) h1
    rw [← coord_eq_trace pb hk hdim f k] at h2
    exact ⟨⟨f k, isIntegral_trans (f k) h2⟩, rfl⟩
  · intro h
    have hi : IsIntegral L[X] (∑ j, f j • algebraMap L F' (pb.basis j)) := by
      refine IsIntegral.sum _ fun j _ => ?_
      obtain ⟨r, hr⟩ := h j
      rw [Algebra.smul_def, ← hr]
      refine IsIntegral.mul ?_ ?_
      · exact (r.2 : IsIntegral Fq[X] (r : F)).map_of_comp_eq (mapRingHom (algebraMap Fq L))
          (algebraMap F F') (compat_poly_hom hx)
      · rw [IsScalarTower.algebraMap_apply L L[X] F']; exact isIntegral_algebraMap
    exact ⟨⟨_, hi⟩, rfl⟩

theorem inf_iff (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') (f : Fin pb.dim → F) :
    (∑ j, f j • algebraMap L F' (pb.basis j)) ∈ (algebraMap (Rinf L F') F').range ↔
      ∀ j, f j ∈ (algebraMap (Rinf Fq F) F).range := by
  have := finiteDimensional pb hk hdim
  constructor
  · rintro ⟨z, hz⟩ k
    have hzi : IsIntegral (Oinf L) (∑ j, f j • algebraMap L F' (pb.basis j)) := by rw [← hz]; exact z.2
    have h1 : IsIntegral (Rinf Fq F)
        ((∑ j, f j • algebraMap L F' (pb.basis j)) * algebraMap L F' (dualB pb k)) :=
      (isIntegral_of_forall_algebraMap (isIntegral_Rinf_Oinf pb hx) hzi).mul (isIntegral_Rinf_L _)
    have h2 := Algebra.isIntegral_trace (L := F) h1
    rw [← coord_eq_trace pb hk hdim f k] at h2
    exact ⟨⟨f k, isIntegral_trans (f k) h2⟩, rfl⟩
  · intro h
    let φ : Oinf Fq →+* Oinf L :=
      (ratMap Fq L).restrict (Oinf Fq) (Oinf L) fun _ hg => ratMap_mem_Oinf hg
    have hφ : (algebraMap (Oinf L) F').comp φ = (algebraMap F F').comp (algebraMap (Oinf Fq) F) := by
      refine RingHom.ext fun g => ?_
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply (Oinf L) (RatFunc L) F',
        IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F]
      exact compat_rat hx g
    have hi : IsIntegral (Oinf L) (∑ j, f j • algebraMap L F' (pb.basis j)) := by
      refine IsIntegral.sum _ fun j _ => ?_
      obtain ⟨r, hr⟩ := h j
      rw [Algebra.smul_def, ← hr]
      refine IsIntegral.mul ?_ ?_
      · exact (r.2 : IsIntegral (Oinf Fq) (r : F)).map_of_comp_eq φ (algebraMap F F') hφ
      · have e : algebraMap L F' (pb.basis j) =
            algebraMap (Oinf L) F' ⟨_, algebraMap_mem_Oinf L (pb.basis j)⟩ := by
          rw [IsScalarTower.algebraMap_apply (Oinf L) (RatFunc L) F']
          exact IsScalarTower.algebraMap_apply L (RatFunc L) F' _
        rw [e]; exact isIntegral_algebraMap
    exact ⟨⟨_, hi⟩, rfl⟩

/-- **The constant field extension in coordinates.** -/
theorem isConstExt (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') : IsConstExt Fq F L F' pb.basis where
  linearIndependent := linearIndependent_basis pb hk
  span := span_basis pb hk hdim
  xF_eq := hx
  fin := fin_iff pb hk hdim hx
  inf := inf_iff pb hk hdim hx

include pb in
theorem genusF_eq (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') : genusF L F' = genusF Fq F :=
  (isConstExt pb hk hdim hx).genusF_eq

include pb in
theorem constField_eq_bot (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') : constField L F' = ⊥ :=
  (isConstExt pb hk hdim hx).constField_eq_bot hk

end Generic

end RamanujanPetersson.PicDescent


