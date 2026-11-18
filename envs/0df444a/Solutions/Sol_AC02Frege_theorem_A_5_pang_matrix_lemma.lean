-- Prove2me | solution 1 for AC02Frege.theorem_A_5_pang_matrix_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T04:05:41.211218+00:00
-- url     : https://prove2.me/submissions/884851c1-22c1-4a33-9d14-3aa628e361d6

import Mathlib

section
-- Inlined Solutions.CoordinateComplement

namespace AC02Frege.CoordinateComplement

theorem exists_complement_from_family {K V ι : Type} [DivisionRing K] [AddCommGroup V] [Module K V]
    (v : ι → V) (hspan : Submodule.span K (Set.range v) = ⊤) (W : Submodule K V) :
    ∃ (κ : Type) (a : κ → ι), Function.Injective a ∧
      IsCompl W (Submodule.span K (Set.range (v ∘ a))) := by
  classical
  obtain ⟨κ,a,ha,hsp,hli⟩ := exists_linearIndependent' K (W.mkQ ∘ v)
  let C := Submodule.span K (Set.range (v ∘ a))
  have hgen : Submodule.span K (Set.range (W.mkQ ∘ v)) = ⊤ := by
    calc
      _ = (Submodule.span K (Set.range v)).map W.mkQ := by rw [Submodule.map_span,← Set.range_comp]
      _ = ⊤ := by rw [hspan,Submodule.map_top,W.range_mkQ]
  have hmap : C.map W.mkQ = ⊤ := by
    rw [Submodule.map_span,← Set.range_comp]
    change Submodule.span K (Set.range ((W.mkQ ∘ v) ∘ a)) = ⊤
    rw [hsp,hgen]
  have hdisj : Disjoint C W := by
    have h := Submodule.range_ker_disjoint hli
    rw [W.ker_mkQ] at h
    exact h
  have hsup : W ⊔ C = ⊤ := (W.map_mkQ_eq_top C).mp hmap
  exact ⟨κ,a,ha,hdisj.symm,codisjoint_iff.mpr hsup⟩

end AC02Frege.CoordinateComplement
end

section
-- Inlined Solutions.FrobeniusDescent

set_option maxHeartbeats 2000000

open Module

namespace AC02Frege.FrobeniusDescent

def squareMap (K ι : Type) [Field K] [CharP K 2] :
    (ι → K) →ₛₗ[frobenius K 2] (ι → K) where
  toFun v i := frobenius K 2 (v i)
  map_add' v w := by funext i; exact map_add (frobenius K 2) (v i) (w i)
  map_smul' a v := by funext i; exact map_mul (frobenius K 2) a (v i)

theorem square_span {K ι κ : Type} [Field K] [CharP K 2] (v : κ → (ι → K))
    (hv : ∀ i, squareMap K ι (v i) = v i) :
    ∀ x ∈ Submodule.span K (Set.range v), squareMap K ι x ∈ Submodule.span K (Set.range v) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    rw [hv]
    exact Submodule.subset_span (Set.mem_range_self i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ih

theorem square_basis {K ι : Type} [Field K] [CharP K 2] [Fintype ι] (i : ι) :
    squareMap K ι (Pi.basisFun K ι i) = Pi.basisFun K ι i := by
  classical
  funext j
  simp only [squareMap,LinearMap.coe_mk,AddHom.coe_mk,Pi.basisFun_apply]
  by_cases h : j = i <;> simp [h,eq_comm]

/-- The descent step in source Lemma A.7: a Frobenius-stable subspace is spanned by its
Frobenius-fixed vectors. The coordinate-complement construction avoids choosing an echelon form. -/
theorem span_fixed {K ι : Type} [Field K] [CharP K 2] [Fintype ι]
    (W : Submodule K (ι → K)) (hW : ∀ x ∈ W, squareMap K ι x ∈ W) :
    Submodule.span K {x : ι → K | x ∈ W ∧ squareMap K ι x = x} = W := by
  classical
  let b := Pi.basisFun K ι
  obtain ⟨κ,a,ha,hcompl⟩ := CoordinateComplement.exists_complement_from_family b b.span_eq W
  let C := Submodule.span K (Set.range (b ∘ a))
  let P := W.projection C hcompl
  have hC : ∀ x ∈ C, squareMap K ι x ∈ C := square_span (b ∘ a) (fun i => square_basis (a i))
  have hpfix (i : ι) : squareMap K ι (P (b i)) = P (b i) := by
    have hdecomp := Submodule.projection_add_projection_eq_self hcompl (b i)
    have hwm : P (b i) ∈ W := Submodule.projection_apply_mem hcompl _
    have hcm : C.projection W hcompl.symm (b i) ∈ C := Submodule.projection_apply_mem hcompl.symm _
    have hs : squareMap K ι (P (b i))+squareMap K ι (C.projection W hcompl.symm (b i)) = b i := by
      rw [← map_add,hdecomp]
      exact square_basis i
    have hp := congrArg P hs
    rw [map_add,Submodule.projection_apply_of_mem_left hcompl (hW _ hwm),
      Submodule.projection_apply_of_mem_right hcompl (hC _ hcm),add_zero] at hp
    exact hp
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => hx.1)
  · intro x hx
    have hPx : P x = x := Submodule.projection_apply_of_mem_left hcompl hx
    rw [← hPx,← b.sum_repr x,map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨Submodule.projection_apply_mem hcompl _,hpfix i⟩)

end AC02Frege.FrobeniusDescent
end

section
-- Inlined Solutions.MatrixFieldMap

set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MatrixFieldMap

open Module

lemma map_mem_span {K L ι κ : Type} [Field K] [Field L] (f : K →+* L)
    (v : κ → (ι → K)) {x : ι → K} (hx : x ∈ Submodule.span K (Set.range v)) :
    (f ∘ x) ∈ Submodule.span L (Set.range (fun i => f ∘ v i)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    exact Submodule.subset_span (Set.mem_range_self i)
  | zero =>
    have he : f ∘ (0 : ι → K) = (0 : ι → L) := by funext i; exact map_zero f
    rw [he]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    have he : f ∘ (x+y) = (f ∘ x)+(f ∘ y) := by funext i; exact map_add f _ _
    rw [he]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    have he : f ∘ (a • x) = f a • (f ∘ x) := by funext i; exact map_mul f _ _
    rw [he]
    exact Submodule.smul_mem _ _ ih

/-- Matrix rank is unchanged by an embedding of fields. -/
theorem rank_map {K L m n : Type} [Field K] [Field L] [Fintype m] [Fintype n]
    (f : K →+* L) (A : Matrix m n K) : (A.map f).rank = A.rank := by
  classical
  letI : Algebra K L := f.toAlgebra
  obtain ⟨κ,a,ha,hsp,hli⟩ := exists_linearIndependent' K A.col
  letI : Fintype κ := Fintype.ofInjective a ha
  have hli' : LinearIndependent L (fun i : κ => f ∘ A.col (a i)) := by
    exact linearIndependent_algebraMap_comp_iff.mpr hli
  have hsp' : Submodule.span L (Set.range (fun i : κ => f ∘ A.col (a i))) =
      Submodule.span L (Set.range (A.map f).col) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨i,rfl⟩
      exact Submodule.subset_span ⟨a i,rfl⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨j,rfl⟩
      have hj : A.col j ∈ Submodule.span K (Set.range (A.col ∘ a)) := by
        rw [hsp]
        exact Submodule.subset_span (Set.mem_range_self j)
      exact map_mem_span f (A.col ∘ a) hj
  rw [Matrix.rank_eq_finrank_span_cols,Matrix.rank_eq_finrank_span_cols,← hsp',← hsp]
  have h1 := linearIndependent_iff_card_eq_finrank_span.mp hli
  have h2 := linearIndependent_iff_card_eq_finrank_span.mp hli'
  exact h2.symm.trans h1

end AC02Frege.MatrixFieldMap
end

section
-- Inlined Solutions.FrobeniusKernel

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.FrobeniusKernel

open Matrix Module FrobeniusDescent

/-- The kernel inclusion in Pang's hypothesis makes the generic kernel Frobenius stable. -/
theorem kernel_stable {K m n : Type} [Field K] [CharP K 2] [Fintype m] [Fintype n]
    (A : Matrix m n K)
    (h : ∀ v, A *ᵥ v = 0 → A.map (frobenius K 2) *ᵥ v = 0) :
    ∀ v ∈ LinearMap.ker A.mulVecLin, squareMap K n v ∈ LinearMap.ker A.mulVecLin := by
  let B := A.map (frobenius K 2)
  have hle : LinearMap.ker A.mulVecLin ≤ LinearMap.ker B.mulVecLin := h
  have heq : LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    have ha := A.mulVecLin.finrank_range_add_finrank_ker
    have hb := B.mulVecLin.finrank_range_add_finrank_ker
    have hr : finrank K B.mulVecLin.range = finrank K A.mulVecLin.range :=
      MatrixFieldMap.rank_map (frobenius K 2) A
    omega
  intro v hv
  rw [heq]
  change B *ᵥ squareMap K n v = 0
  funext i
  have hi := (frobenius K 2).map_mulVec A v i
  have hz : A *ᵥ v = 0 := hv
  rw [hz] at hi
  simpa only [Function.comp_def,B,squareMap,LinearMap.coe_mk,AddHom.coe_mk,Pi.zero_apply,map_zero] using hi.symm

/-- Frobenius-fixed vectors have coordinates in the embedded two-element field. -/
theorem fixed_binary {K n : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (v : n → K) (hv : squareMap K n v = v) :
    ∃ b : n → ZMod 2, (algebraMap (ZMod 2) K) ∘ b = v := by
  classical
  refine ⟨fun i => if v i = 0 then 0 else 1,?_⟩
  funext i
  have hs : (v i)^2 = v i := by
    simpa only [squareMap,LinearMap.coe_mk,AddHom.coe_mk,frobenius_def] using congrFun hv i
  have hz : v i * (v i-1) = 0 := by calc
    _ = (v i)^2-v i := by ring
    _ = 0 := by rw [hs,sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · simp [h]
  · have h1 : v i = 1 := sub_eq_zero.mp h
    simp [h1]

end AC02Frege.FrobeniusKernel
end

section
-- Inlined Solutions.PangGenericRank

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.PangGenericRank

open Matrix Module FrobeniusDescent FrobeniusKernel

lemma frobenius_binary {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (a : ZMod 2) : frobenius K 2 (algebraMap (ZMod 2) K a) = algebraMap (ZMod 2) K a := by
  fin_cases a <;> simp [frobenius_def]

lemma map_combination {K s p q : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    [Fintype s] (lam : s → K) (M : s → Matrix p q (ZMod 2)) :
    (∑ i, lam i • (M i).map (algebraMap (ZMod 2) K)).map (frobenius K 2) =
      ∑ i, (lam i)^2 • (M i).map (algebraMap (ZMod 2) K) := by
  ext r j
  simp only [Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,map_sum,map_mul]
  simp only [frobenius_def]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← map_pow]
  congr 1
  exact FiniteField.pow_card _

/-- The first assertion of Pang's matrix lemma, stated for any independent coefficient family. -/
theorem rank_eq_stacked {K s p q : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    [Fintype s] [Fintype p] [Fintype q]
    (lam : s → K) (hLI : LinearIndependent (ZMod 2) lam)
    (M : s → Matrix p q (ZMod 2))
    (hker : ∀ v : q → K,
      (∑ i, lam i • (M i).map (algebraMap (ZMod 2) K)) *ᵥ v = 0 →
      (∑ i, (lam i)^2 • (M i).map (algebraMap (ZMod 2) K)) *ᵥ v = 0) :
    (∑ i, lam i • (M i).map (algebraMap (ZMod 2) K)).rank =
      (Matrix.of (fun (ik : s × p) (j : q) => M ik.1 ik.2 j)).rank := by
  classical
  let f := algebraMap (ZMod 2) K
  let A := ∑ i, lam i • (M i).map f
  let S : Matrix (s × p) q (ZMod 2) := Matrix.of (fun ik j => M ik.1 ik.2 j)
  let T := S.map f
  have hstable : ∀ v ∈ LinearMap.ker A.mulVecLin, squareMap K q v ∈ LinearMap.ker A.mulVecLin := by
    apply kernel_stable A
    intro v hv
    rw [map_combination]
    exact hker v hv
  have hcomponent (v : q → K) : T *ᵥ v = 0 ↔ ∀ i, (M i).map f *ᵥ v = 0 := by
    constructor
    · intro hv i
      funext r
      exact congrFun hv (i,r)
    · intro hv
      funext ik
      exact congrFun (hv ik.1) ik.2
  have hbinary {v : q → K} (hv : A *ᵥ v = 0) (hfix : squareMap K q v = v) : T *ᵥ v = 0 := by
    obtain ⟨b,hb⟩ := fixed_binary v hfix
    apply (hcomponent v).mpr
    intro i
    funext r
    have hs := congrFun hv r
    rw [← hb] at hs
    simp only [A,Matrix.sum_mulVec,Matrix.smul_mulVec,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hs
    have hsum : ∑ j, (M j *ᵥ b) r • lam j = 0 := by
      calc
        _ = ∑ j, lam j * ((M j).map f *ᵥ (f ∘ b)) r := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Algebra.smul_def,← f.map_mulVec]
          exact mul_comm _ _
        _ = 0 := hs
    have hi := (Fintype.linearIndependent_iff.mp hLI) (fun j => (M j *ᵥ b) r) hsum i
    rw [← hb,← f.map_mulVec,hi,map_zero]
    rfl
  have hle : LinearMap.ker A.mulVecLin ≤ LinearMap.ker T.mulVecLin := by
    rw [← span_fixed (LinearMap.ker A.mulVecLin) hstable]
    apply Submodule.span_le.mpr
    intro v hv
    exact hbinary hv.1 hv.2
  have hrev : LinearMap.ker T.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    intro v hv
    have hv' := (hcomponent v).mp hv
    change A *ᵥ v = 0
    simp only [A,Matrix.sum_mulVec,Matrix.smul_mulVec,hv',smul_zero,Finset.sum_const_zero]
  have heq := le_antisymm hle hrev
  have ha := A.mulVecLin.finrank_range_add_finrank_ker
  have ht := T.mulVecLin.finrank_range_add_finrank_ker
  have hr : T.rank = S.rank := MatrixFieldMap.rank_map f S
  rw [heq] at ha
  change A.rank = S.rank
  change A.rank + finrank K T.mulVecLin.ker = finrank K (q → K) at ha
  change T.rank + finrank K T.mulVecLin.ker = finrank K (q → K) at ht
  omega

lemma independent_variables (s : ℕ) :
    LinearIndependent (ZMod 2) (fun i : Fin s =>
      algebraMap (MvPolynomial (Fin s) (ZMod 2))
        (FractionRing (MvPolynomial (Fin s) (ZMod 2))) (MvPolynomial.X i)) := by
  let P := MvPolynomial (Fin s) (ZMod 2)
  let E := FractionRing P
  let f := (IsScalarTower.toAlgHom (ZMod 2) P E).toLinearMap
  have hf : Function.Injective f := IsFractionRing.injective P E
  exact (f.linearIndependent_iff_of_injOn hf.injOn).mpr (MvPolynomial.linearIndependent_X _ _)

/-- The exact formal-rank assertion of source Theorem A.5. -/
theorem formal_rank {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    let E := FractionRing (MvPolynomial (Fin s) (ZMod 2))
    let lam : Fin s → E := fun i => algebraMap (MvPolynomial (Fin s) (ZMod 2)) E (MvPolynomial.X i)
    let A := ∑ i, lam i • (M i).map (algebraMap (ZMod 2) E)
    let B := ∑ i, (lam i)^2 • (M i).map (algebraMap (ZMod 2) E)
    (∀ v, A *ᵥ v = 0 → B *ᵥ v = 0) →
      A.rank = (Matrix.of (fun (ik : Fin s × Fin p) (j : Fin q) => M ik.1 ik.2 j)).rank := by
  intro E lam A B h
  exact rank_eq_stacked lam (independent_variables s) M h

end AC02Frege.PangGenericRank
end

section
-- Inlined Solutions.PolynomialMultiplicity

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.PolynomialMultiplicity

open MvPolynomial

variable {σ R : Type} [CommRing R]

/-- Total degree of a monomial index. -/
def weight (d : σ →₀ ℕ) : ℕ := d.sum (fun _ n => n)

@[simp] lemma weight_zero : weight (0 : σ →₀ ℕ) = 0 := by simp [weight]

@[simp] lemma weight_add (d e : σ →₀ ℕ) : weight (d+e) = weight d+weight e := by
  classical
  exact Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)

/-- Translate the variables by a point; coefficients are the multivariate Hasse derivatives. -/
noncomputable def shift (a : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i => X i+C (a i))

@[simp] lemma shift_C (a : σ → R) (r : R) : shift a (C r) = C r := by simp [shift]
@[simp] lemma shift_X (a : σ → R) (i : σ) : shift a (X i) = X i+C (a i) := by simp [shift]

lemma shift_shift (a b : σ → R) (p : MvPolynomial σ R) :
    shift a (shift b p) = shift (a+b) p := by
  have h : (shift a).comp (shift b) = shift (a+b) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,shift_X,map_add,shift_C,Pi.add_apply,map_add]
    ring
  exact DFunLike.congr_fun h p

@[simp] lemma shift_zero (p : MvPolynomial σ R) : shift (0 : σ → R) p = p := by
  have h : shift (0 : σ → R) = AlgHom.id R (MvPolynomial σ R) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [shift_X]
  exact DFunLike.congr_fun h p

lemma shift_injective (a : σ → R) : Function.Injective (shift a) := by
  intro p q hpq
  have h := congrArg (shift (-a)) hpq
  simpa only [shift_shift,neg_add_cancel,shift_zero] using h

@[simp] lemma shift_eq_zero_iff (a : σ → R) (p : MvPolynomial σ R) : shift a p = 0 ↔ p = 0 :=
  map_eq_zero_iff (shift a) (shift_injective a)

lemma exists_weight (p : MvPolynomial σ R) (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ d : σ →₀ ℕ, coeff d p ≠ 0 ∧ weight d = n := by
  obtain ⟨d,hd⟩ := MvPolynomial.exists_coeff_ne_zero hp
  exact ⟨weight d,d,hd,rfl⟩

/-- The least degree of a nonzero coefficient, with value zero on the zero polynomial. -/
noncomputable def natOrder (p : MvPolynomial σ R) : ℕ := by
  classical
  exact if hp : p = 0 then 0 else Nat.find (exists_weight p hp)

lemma natOrder_le {p : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : coeff d p ≠ 0) :
    natOrder p ≤ weight d := by
  classical
  have hp : p ≠ 0 := by intro h; simp [h] at hd
  rw [natOrder,dif_neg hp]
  exact Nat.find_min' _ ⟨d,hd,rfl⟩

lemma exists_min_coeff {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ d : σ →₀ ℕ, coeff d p ≠ 0 ∧ weight d = natOrder p := by
  classical
  rw [natOrder,dif_neg hp]
  exact Nat.find_spec (exists_weight p hp)

lemma coeff_below_order {p : MvPolynomial σ R} {d : σ →₀ ℕ} (h : weight d < natOrder p) :
    coeff d p = 0 := by
  by_contra hn
  exact (Nat.not_lt_of_ge (natOrder_le hn)) h

lemma natOrder_le_totalDegree {p : MvPolynomial σ R} (hp : p ≠ 0) : natOrder p ≤ p.totalDegree := by
  obtain ⟨d,hd,he⟩ := exists_min_coeff hp
  rw [← he]
  exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)

lemma le_natOrder_iff {p : MvPolynomial σ R} (hp : p ≠ 0) (n : ℕ) :
    n ≤ natOrder p ↔ ∀ d : σ →₀ ℕ, weight d < n → coeff d p = 0 := by
  constructor
  · intro hn d hd
    exact coeff_below_order (lt_of_lt_of_le hd hn)
  · intro hn
    obtain ⟨d,hd,he⟩ := exists_min_coeff hp
    by_contra h
    exact hd (hn d (he.trans_lt (Nat.lt_of_not_ge h)))

/-- Multiplicity at a point, for use with nonzero polynomials. -/
noncomputable def multiplicity (p : MvPolynomial σ R) (a : σ → R) : ℕ := natOrder (shift a p)

lemma multiplicity_le {p : MvPolynomial σ R} {a : σ → R} {d : σ →₀ ℕ}
    (hd : coeff d (shift a p) ≠ 0) : multiplicity p a ≤ weight d := natOrder_le hd

/-- A coefficient formulation also valid for the zero polynomial. -/
def Vanishes (p : MvPolynomial σ R) (n : ℕ) : Prop :=
  ∀ d : σ →₀ ℕ, weight d < n → coeff d p = 0

lemma vanishes_zero (n : ℕ) : Vanishes (0 : MvPolynomial σ R) n := by
  intro d hd
  exact MvPolynomial.coeff_zero d

lemma vanishes_add {p q : MvPolynomial σ R} {n : ℕ}
    (hp : Vanishes p n) (hq : Vanishes q n) : Vanishes (p+q) n := by
  intro d hd
  rw [MvPolynomial.coeff_add,hp d hd,hq d hd,add_zero]

lemma vanishes_mul {p q : MvPolynomial σ R} {m n : ℕ}
    (hp : Vanishes p m) (hq : Vanishes q n) : Vanishes (p*q) (m+n) := by
  classical
  intro d hd
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro e he
  have hed : e.1+e.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp he
  have hw : weight e.1+weight e.2 < m+n := by rw [← weight_add,hed]; exact hd
  by_cases h : weight e.1 < m
  · rw [hp _ h,zero_mul]
  · rw [hq _ (by omega),mul_zero]

/-- Substitution by affine linear polynomials does not increase total degree. -/
theorem aeval_totalDegree_le {τ : Type} (g : σ → MvPolynomial τ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (aeval g p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  change (C (coeff d p) * d.prod (fun i k => g i^k)).totalDegree ≤ p.totalDegree
  calc
    _ ≤ (C (coeff d p) : MvPolynomial τ R).totalDegree +
        (d.prod (fun i k => g i^k)).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (d.prod (fun i k => g i^k)).totalDegree := by rw [totalDegree_C,zero_add]
    _ ≤ ∑ i ∈ d.support, (g i^d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

lemma shift_totalDegree_le [Nontrivial R] (a : σ → R) (p : MvPolynomial σ R) :
    (shift a p).totalDegree ≤ p.totalDegree := by
  apply aeval_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp [totalDegree_X])

@[simp] lemma shift_totalDegree [Nontrivial R] (a : σ → R) (p : MvPolynomial σ R) :
    (shift a p).totalDegree = p.totalDegree := by
  apply le_antisymm (shift_totalDegree_le a p)
  have h := shift_totalDegree_le (-a) (shift a p)
  simpa only [shift_shift,neg_add_cancel,shift_zero] using h

lemma multiplicity_le_totalDegree [Nontrivial R] {p : MvPolynomial σ R} (hp : p ≠ 0) (a : σ → R) :
    multiplicity p a ≤ p.totalDegree := by
  have hs : shift a p ≠ 0 := (shift_eq_zero_iff a p).not.mpr hp
  simpa only [multiplicity,shift_totalDegree] using natOrder_le_totalDegree hs

lemma vanishes_sum {ι : Type} (s : Finset ι) (p : ι → MvPolynomial σ R) (n : ℕ)
    (hp : ∀ i ∈ s, Vanishes (p i) n) : Vanishes (∑ i ∈ s, p i) n := by
  intro d hd
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_eq_zero (fun i hi => hp i hi d hd)

lemma vanishes_trivial (p : MvPolynomial σ R) : Vanishes p 0 := by
  intro d hd
  omega

lemma vanishes_prod {ι : Type} (s : Finset ι) (p : ι → MvPolynomial σ R) (n : ι → ℕ)
    (hp : ∀ i ∈ s, Vanishes (p i) (n i)) : Vanishes (∏ i ∈ s, p i) (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vanishes_trivial (1 : MvPolynomial σ R)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact vanishes_mul (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

end AC02Frege.PolynomialMultiplicity
end

section
-- Inlined Solutions.MultiplicitySections

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.PolynomialMultiplicity

open MvPolynomial

variable {σ R : Type} [CommRing R]

lemma right_monomial (m : Option σ →₀ ℕ) (r : R) :
    optionEquivRight R σ (monomial m r) = monomial m.some (Polynomial.monomial (m none) r) := by
  rw [optionEquivRight_apply,aeval_monomial,Finsupp.prod_option_index]
  · rw [MvPolynomial.monomial_eq,← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [algebraMap_eq,Option.elim_none,Option.elim_some,map_mul,mul_assoc]
    simp only [mul_comm,map_finsuppProd,map_pow]
    rw [IsScalarTower.algebraMap_apply R (Polynomial R) (MvPolynomial σ (Polynomial R))]
    rfl
  · simp
  · intros; rw [pow_add]

lemma right_coeff_coeff (p : MvPolynomial (Option σ) R) (d : σ →₀ ℕ) (j : ℕ) :
    (coeff d (optionEquivRight R σ p)).coeff j = coeff (d.optionElim j) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,coeff_add,Polynomial.coeff_add,hp,hq]
  | monomial m r =>
    rw [right_monomial]
    simp only [MvPolynomial.coeff_monomial,Polynomial.coeff_monomial,apply_ite,Polynomial.coeff_zero]
    by_cases hd : m.some = d
    · rw [if_pos hd]
      by_cases hj : m none = j
      · have hm : m = d.optionElim j := by rw [← hd,← hj,Finsupp.optionElim_some]
        simp [Polynomial.coeff_monomial,hj,hm]
      · have hm : m ≠ d.optionElim j := by intro h; have := congrArg (fun u => u none) h; simp_all
        simp [Polynomial.coeff_monomial,hj,Ne.symm hj,hm]
    · rw [if_neg hd]
      have hm : m ≠ d.optionElim j := by intro h; have := congrArg Finsupp.some h; simp_all
      simp [hm]

noncomputable def taylorHom (b : R) : Polynomial R →+* Polynomial R :=
  (Polynomial.aeval (Polynomial.X+Polynomial.C b)).toRingHom

lemma taylorHom_apply (b : R) (p : Polynomial R) : taylorHom b p = Polynomial.taylor b p := by
  rfl

@[simp] lemma taylorHom_C (b r : R) : taylorHom b (Polynomial.C r) = Polynomial.C r := by
  simp [taylorHom]
@[simp] lemma taylorHom_X (b : R) : taylorHom b Polynomial.X = Polynomial.X+Polynomial.C b := by
  simp [taylorHom]

lemma right_shift (p : MvPolynomial (Option σ) R) (a : σ → R) (b : R) :
    optionEquivRight R σ (shift (fun o => o.elim b a) p) =
      MvPolynomial.map (taylorHom b)
        (shift (fun i => Polynomial.C (a i)) (optionEquivRight R σ p)) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [optionEquivRight_C,shift_C]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p o hp =>
    simp only [map_mul,hp]
    congr 1
    cases o with
    | none => simp [shift_X,optionEquivRight_X_none,optionEquivRight_C]
    | some i => simp [shift_X,optionEquivRight_X_some,optionEquivRight_C]

lemma section_coefficient (p : MvPolynomial (Option σ) R) (a : σ → R) (b : R)
    (d : σ →₀ ℕ) (j : ℕ) :
    coeff (d.optionElim j) (shift (fun o => o.elim b a) p) =
      (Polynomial.taylor b (coeff d
        (shift (fun i => Polynomial.C (a i)) (optionEquivRight R σ p)))).coeff j := by
  rw [← right_coeff_coeff,right_shift]
  rfl

@[simp] lemma weight_optionElim (d : σ →₀ ℕ) (j : ℕ) : weight (d.optionElim j) = weight d+j := by
  classical
  simpa only [weight,Finsupp.optionElim_apply_none,Finsupp.some_optionElim,add_comm] using
    (d.optionElim j).sum_option_index (fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

lemma multiplicity_section_le [IsDomain R] (p : MvPolynomial (Option σ) R) (a : σ → R)
    (d : σ →₀ ℕ)
    (hd : coeff d (shift (fun i => Polynomial.C (a i)) (optionEquivRight R σ p)) ≠ 0)
    (b : R) :
    multiplicity p (fun o => o.elim b a) ≤ weight d+
      (coeff d (shift (fun i => Polynomial.C (a i)) (optionEquivRight R σ p))).rootMultiplicity b := by
  let Q := coeff d (shift (fun i => Polynomial.C (a i)) (optionEquivRight R σ p))
  have hQ : Q ≠ 0 := hd
  let j := (Polynomial.taylor b Q).natTrailingDegree
  have hj : (Polynomial.taylor b Q).coeff j ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr ((Polynomial.taylor_eq_zero b Q).not.mpr hQ)
  have hcoeff : coeff (d.optionElim j) (shift (fun o => o.elim b a) p) ≠ 0 := by
    rw [section_coefficient]
    exact hj
  have h := multiplicity_le hcoeff
  rw [weight_optionElim] at h
  exact h.trans_eq (by rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]; rfl)

lemma left_partial_shift (p : MvPolynomial (Option σ) R) (a : σ → R) :
    optionEquivLeft R σ (shift (fun o => o.elim 0 a) p) =
      Polynomial.map (shift a).toRingHom (optionEquivLeft R σ p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [optionEquivLeft_C]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p o hp =>
    simp only [map_mul,Polynomial.map_mul,hp]
    congr 1
    cases o with
    | none => simp [shift_X,optionEquivLeft_X_none,optionEquivLeft_C]
    | some i => simp [shift_X,optionEquivLeft_X_some,optionEquivLeft_C]

lemma section_head_coeff (p : MvPolynomial (Option σ) R) (a : σ → R) (d : σ →₀ ℕ) (j : ℕ) :
    (coeff d (shift (fun i => Polynomial.C (a i)) (optionEquivRight R σ p))).coeff j =
      coeff d (shift a ((optionEquivLeft R σ p).coeff j)) := by
  calc
    _ = coeff (d.optionElim j) (shift (fun o => o.elim 0 a) p) := by
      simpa only [Polynomial.taylor_zero] using (section_coefficient p a 0 d j).symm
    _ = coeff d ((optionEquivLeft R σ (shift (fun o => o.elim 0 a) p)).coeff j) :=
      (optionEquivLeft_coeff_coeff R _ j d).symm
    _ = _ := by rw [left_partial_shift,Polynomial.coeff_map]; rfl

lemma section_degree_le (p : MvPolynomial (Option σ) R) (a : σ → R) (d : σ →₀ ℕ) :
    (coeff d (shift (fun i => Polynomial.C (a i)) (optionEquivRight R σ p))).natDegree ≤
      (optionEquivLeft R σ p).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [section_head_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero,MvPolynomial.coeff_zero]

lemma sum_rootMultiplicity_le [IsDomain R] [Fintype R] (p : Polynomial R) :
    (∑ a : R, p.rootMultiplicity a) ≤ p.natDegree := by
  classical
  simp_rw [← Polynomial.count_roots]
  rw [Multiset.sum_count_eq_card (by simp)]
  exact Polynomial.card_roots' p

end AC02Frege.PolynomialMultiplicity
end

section
-- Inlined Solutions.MultiplicityCubeFibre

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.PolynomialMultiplicity

open MvPolynomial

/-- The fibre estimate in multiplicity Schwartz--Zippel: the leading coefficient controls
vanishing in all but the head variable, and univariate root counting controls the head. -/
theorem cube_fibre_bound {σ : Type} (p : MvPolynomial (Option σ) (ZMod 2)) (hp : p ≠ 0)
    (a : σ → ZMod 2) :
    (∑ b : ZMod 2, multiplicity p (fun o => o.elim b a)) ≤
      2 * multiplicity (optionEquivLeft (ZMod 2) σ p).leadingCoeff a +
        (optionEquivLeft (ZMod 2) σ p).natDegree := by
  classical
  let P := optionEquivLeft (ZMod 2) σ p
  let k := P.natDegree
  let L := P.leadingCoeff
  have hP : P ≠ 0 := (optionEquivLeft (ZMod 2) σ).injective.ne (by simpa using hp)
  have hL : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hLa : shift a L ≠ 0 := (shift_eq_zero_iff a L).not.mpr hL
  obtain ⟨d,hd,hw⟩ := exists_min_coeff hLa
  let Q := coeff d (shift (fun i => Polynomial.C (a i)) (optionEquivRight (ZMod 2) σ p))
  have hQk : Q.coeff k ≠ 0 := by
    rw [section_head_coeff]
    exact hd
  have hQ : Q ≠ 0 := by intro h; simp [h] at hQk
  have hdeg : Q.natDegree ≤ k := section_degree_le p a d
  have hw' : weight d = multiplicity L a := hw
  calc
    _ ≤ ∑ b : ZMod 2, (weight d+Q.rootMultiplicity b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact multiplicity_section_le p a d hQ b
    _ = 2 * weight d+∑ b : ZMod 2, Q.rootMultiplicity b := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ 2 * weight d+k := Nat.add_le_add_left ((sum_rootMultiplicity_le Q).trans hdeg) _
    _ = _ := by rw [hw']

end AC02Frege.PolynomialMultiplicity
end

section
-- Inlined Solutions.MultiplicityRename

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.PolynomialMultiplicity

open MvPolynomial

variable {σ τ R : Type} [CommRing R]

lemma weight_mapDomain (f : σ → τ) (d : σ →₀ ℕ) : weight (d.mapDomain f) = weight d := by
  classical
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

lemma natOrder_rename_le (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R)
    (hp : p ≠ 0) : natOrder (rename f p) ≤ natOrder p := by
  obtain ⟨d,hd,hw⟩ := exists_min_coeff hp
  have hcoeff : coeff (d.mapDomain f) (rename f p) ≠ 0 := by
    rw [MvPolynomial.coeff_rename_mapDomain f hf]
    exact hd
  simpa only [weight_mapDomain,hw] using natOrder_le hcoeff

lemma natOrder_rename (e : σ ≃ τ) (p : MvPolynomial σ R) (hp : p ≠ 0) :
    natOrder (rename e p) = natOrder p := by
  apply le_antisymm (natOrder_rename_le e e.injective p hp)
  have hp' : rename e p ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.rename_injective e e.injective) (by simpa using h)
  have h := natOrder_rename_le e.symm e.symm.injective (rename e p) hp'
  simpa only [MvPolynomial.rename_rename,Equiv.symm_comp_self,MvPolynomial.rename_id,AlgHom.id_apply] using h

lemma shift_rename (f : σ → τ) (p : MvPolynomial σ R) (a : τ → R) :
    shift a (rename f p) = rename f (shift (a ∘ f) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,hp]; simp [shift_X]

lemma multiplicity_rename (e : σ ≃ τ) (p : MvPolynomial σ R) (hp : p ≠ 0) (a : τ → R) :
    multiplicity (rename e p) a = multiplicity p (a ∘ e) := by
  unfold multiplicity
  rw [shift_rename]
  apply natOrder_rename
  exact (shift_eq_zero_iff _ p).not.mpr hp

end AC02Frege.PolynomialMultiplicity
end

section
-- Inlined Solutions.MultiplicityCubeBound

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Classical.propDecidable

namespace AC02Frege.PolynomialMultiplicity

open MvPolynomial

/-- Multiplicity Schwartz--Zippel on the two-element cube, including zero variables.
The factor-two form avoids a negative exponent in that boundary case. -/
theorem cube_sum_bound (σ : Type) [Fintype σ] (p : MvPolynomial σ (ZMod 2)) (hp : p ≠ 0) :
    2 * (∑ a : σ → ZMod 2, multiplicity p a) ≤ p.totalDegree * 2 ^ Fintype.card σ := by
  classical
  refine Fintype.induction_empty_option
    (P := fun τ [inst : Fintype τ] => ∀ (q : MvPolynomial τ (ZMod 2)), q ≠ 0 →
      2 * (∑ a : τ → ZMod 2, multiplicity q a) ≤ q.totalDegree * 2 ^ Fintype.card τ)
    ?_ ?_ ?_ σ p hp
  · intro α β _ e ih p hp
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let p' := rename e.symm p
    have hp' : p' ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.rename_injective e.symm e.symm.injective) (by simpa using h)
    have h := ih p' hp'
    have hdeg : p'.totalDegree = p.totalDegree := MvPolynomial.totalDegree_renameEquiv e.symm p
    have hsum : (∑ a : α → ZMod 2, multiplicity p' a) =
        ∑ b : β → ZMod 2, multiplicity p b := by
      calc
        _ = ∑ a : α → ZMod 2, multiplicity p (a ∘ e.symm) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact multiplicity_rename e.symm p hp a
        _ = _ := by
          simpa only [Equiv.arrowCongr,Equiv.coe_fn_mk,Equiv.refl_apply,Function.comp_def] using
            (Equiv.arrowCongr e (Equiv.refl (ZMod 2))).sum_comp (multiplicity p)
    rw [hdeg,hsum,Fintype.card_congr e] at h
    exact h
  · intro p hp
    have hdeg : p.totalDegree = 0 := by rw [p.eq_C_of_isEmpty]; exact totalDegree_C _
    have hz (a : PEmpty → ZMod 2) : multiplicity p a = 0 := by
      exact Nat.eq_zero_of_le_zero (hdeg ▸ multiplicity_le_totalDegree hp a)
    simp only [hz,Finset.sum_const_zero,mul_zero,zero_mul]
    exact Nat.zero_le _
  · intro α _ ih p hp
    let P := optionEquivLeft (ZMod 2) α p
    let L := P.leadingCoeff
    let k := P.natDegree
    have hP : P ≠ 0 := (optionEquivLeft (ZMod 2) α).injective.ne (by simpa using hp)
    have hL : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hI := ih L hL
    have hdeg : L.totalDegree+k ≤ p.totalDegree := by
      apply totalDegree_coeff_optionEquivLeft_add_le
      rw [natDegree_optionEquivLeft]
      exact degreeOf_le_totalDegree _ _
    have hsplit : (∑ x : Option α → ZMod 2, multiplicity p x) =
        ∑ a : α → ZMod 2, ∑ b : ZMod 2, multiplicity p (fun o => o.elim b a) := by
      rw [← (Equiv.piOptionEquivProd (α := α) (β := fun _ => ZMod 2)).symm.sum_comp (multiplicity p)]
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply congrArg (multiplicity p)
      funext o
      cases o <;> rfl
    have hsum : (∑ x : Option α → ZMod 2, multiplicity p x) ≤
        2 * (∑ a : α → ZMod 2, multiplicity L a)+k * 2 ^ Fintype.card α := by
      rw [hsplit]
      calc
        _ ≤ ∑ a : α → ZMod 2, (2 * multiplicity L a+k) := by
          apply Finset.sum_le_sum
          intro a ha
          exact cube_fibre_bound p hp a
        _ = _ := by simp [Finset.sum_add_distrib,← Finset.mul_sum,Fintype.card_fun,Nat.mul_comm]
    have hscale := Nat.mul_le_mul_right (2 ^ Fintype.card α) hdeg
    have hfinal : 2 * (∑ x : Option α → ZMod 2, multiplicity p x) ≤
        p.totalDegree * (2 ^ Fintype.card α * 2) := by
      calc
        _ ≤ 2 * (2 * (∑ a : α → ZMod 2, multiplicity L a)+k*2^Fintype.card α) :=
          Nat.mul_le_mul_left 2 hsum
        _ ≤ 2 * (L.totalDegree*2^Fintype.card α+k*2^Fintype.card α) :=
          Nat.mul_le_mul_left 2 (Nat.add_le_add_right hI _)
        _ = 2 * ((L.totalDegree+k)*2^Fintype.card α) := by ring
        _ ≤ 2 * (p.totalDegree*2^Fintype.card α) := Nat.mul_le_mul_left 2 hscale
        _ = _ := by ring
    rw [Fintype.card_option,pow_succ]
    convert hfinal using 1
    congr 1
    apply Finset.sum_congr
    · ext x; simp
    · intro x hx; rfl

end AC02Frege.PolynomialMultiplicity
end

section
-- Inlined Solutions.DeterminantMultiplicity

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.PolynomialMultiplicity

open MvPolynomial Matrix

variable {σ R : Type} [CommRing R]

lemma vanishes_smul {S : Type} [SMulZeroClass S R] (a : S) {p : MvPolynomial σ R} {n : ℕ}
    (hp : Vanishes p n) : Vanishes (a • p) n := by
  intro d hd
  rw [MvPolynomial.coeff_smul,hp d hd,smul_zero]

lemma vanishes_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ R)) (t : ι → ℕ)
    (hA : ∀ i j, Vanishes (A i j) (t j)) : Vanishes A.det (∑ j, t j) := by
  rw [Matrix.det_apply]
  apply vanishes_sum
  intro π hπ
  apply vanishes_smul
  exact vanishes_prod _ _ _ (fun i hi => hA (π i) i)

lemma coeff_zero_shift (a : σ → R) (p : MvPolynomial σ R) : coeff 0 (shift a p) = eval a p := by
  have hh : constantCoeff.comp (shift a).toRingHom = eval a := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp [shift_X]
  exact DFunLike.congr_fun hh p

lemma vanishes_one {p : MvPolynomial σ R} (hp : coeff 0 p = 0) : Vanishes p 1 := by
  intro d hd
  have hw : weight d = 0 := by omega
  have he : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hw
  simpa only [he] using hp

lemma vanishes_C_mul_iff [IsDomain R] (a : R) (ha : a ≠ 0) (p : MvPolynomial σ R) (n : ℕ) :
    Vanishes (C a*p) n ↔ Vanishes p n := by
  constructor
  · intro h d hd
    have hh := h d hd
    rw [MvPolynomial.coeff_C_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left ha
  · intro h
    simpa only [zero_add] using vanishes_mul (vanishes_trivial (C a)) h

/-- Rank loss at a point is bounded by determinant multiplicity. This version works for
arbitrary polynomial matrices, not only linear matrix pencils. -/
theorem rank_loss_le_multiplicity {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial σ K)) (hN : N.det ≠ 0) (a : σ → K) :
    Fintype.card ι ≤ (N.map (eval a)).rank+multiplicity N.det a := by
  classical
  let A := N.map (eval a)
  obtain ⟨U,V,e,hU,hV,he⟩ := Matrix.exists_rank_normal_form A
  let T := U.map (C : K →+* MvPolynomial σ K) * N * V.map (C : K →+* MvPolynomial σ K)
  have heval : T.map (eval a) = (fromBlocks 1 0 0 0).submatrix e e := by
    have hmap (B : Matrix ι ι K) : (B.map (C : K →+* MvPolynomial σ K)).map (eval a) = B := by
      ext i j
      exact eval_C _
    simp only [T,Matrix.map_mul]
    rw [hmap,hmap]
    exact he
  let t : ι → ℕ := fun j => (e j).elim (fun _ => 0) (fun _ => 1)
  have hsum : (∑ j, t j) = Fintype.card ι-A.rank := by
    change (∑ j, (fun x : Fin A.rank ⊕ Fin (Fintype.card ι-A.rank) => x.elim (fun _ => 0) (fun _ => 1)) (e j)) = _
    rw [e.sum_comp,Fintype.sum_sum_type]
    simp
  have hentry (i j : ι) : Vanishes (shift a (T i j)) (t j) := by
    rcases hj : e j with jj | jj
    · change Vanishes _ ((e j).elim _ _)
      rw [hj]
      exact vanishes_trivial _
    · change Vanishes _ ((e j).elim _ _)
      rw [hj]
      apply vanishes_one
      rw [coeff_zero_shift]
      change (T.map (eval a)) i j = 0
      rw [heval]
      change fromBlocks (1 : Matrix (Fin A.rank) (Fin A.rank) K) 0 0 0 (e i) (e j) = 0
      rw [hj]
      cases e i <;> rfl
  have hd := vanishes_det (T.map (shift a)) t hentry
  have hshift : (T.map (shift a)).det = shift a T.det :=
    ((shift a).toRingHom.map_det T).symm
  rw [hshift,hsum] at hd
  have hdet : T.det = C U.det*N.det*C V.det := by
    have hcu : (U.map (C : K →+* MvPolynomial σ K)).det = C U.det :=
      ((C : K →+* MvPolynomial σ K).map_det U).symm
    have hcv : (V.map (C : K →+* MvPolynomial σ K)).det = C V.det :=
      ((C : K →+* MvPolynomial σ K).map_det V).symm
    simp only [T,Matrix.det_mul,hcu,hcv]
  have hscalar : shift a T.det = C (U.det*V.det)*shift a N.det := by
    rw [hdet,map_mul,map_mul,shift_C,shift_C,map_mul]
    ring
  rw [hscalar] at hd
  have hu : U.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det U).mp hU).ne_zero
  have hv : V.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det V).mp hV).ne_zero
  have hvan : Vanishes (shift a N.det) (Fintype.card ι-A.rank) :=
    (vanishes_C_mul_iff _ (mul_ne_zero hu hv) _ _).mp hd
  have ho : Fintype.card ι-A.rank ≤ multiplicity N.det a :=
    (le_natOrder_iff ((shift_eq_zero_iff a N.det).not.mpr hN) _).mpr hvan
  have hr := A.rank_le_card_width
  change Fintype.card ι ≤ A.rank+multiplicity N.det a
  omega

end AC02Frege.PolynomialMultiplicity
end

section
-- Inlined Solutions.DeterminantDegree

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.DeterminantDegree

open MvPolynomial Matrix

/-- A determinant with affine linear entries has total degree at most its size. -/
theorem totalDegree_det_le {σ R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ R)) (hA : ∀ i j, (A i j).totalDegree ≤ 1) :
    A.det.totalDegree ≤ Fintype.card ι := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro π hπ
  rw [Units.smul_def]
  calc
    _ ≤ (∏ i, A (π i) i).totalDegree := MvPolynomial.totalDegree_smul_le _ _
    _ ≤ ∑ i, (A (π i) i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum (fun i hi => hA (π i) i)
    _ = Fintype.card ι := by simp

end AC02Frege.DeterminantDegree
end

section
-- Inlined Solutions.FiniteFunctionColumns

open Module Function Submodule

namespace ProofComplexity.FiniteFunctionColumns

/-- Independent functions admit a full-size independent set of evaluation columns. -/
theorem exists_columns {K X I : Type*} [Field K] [Fintype X] [Fintype I]
    (v : I → X → K) (hv : LinearIndependent K v) :
    ∃ S : Set X, Nat.card S = Fintype.card I ∧
      LinearIndependent K (fun x : S => fun i => v i x.1) := by
  classical
  obtain ⟨S,_,_,hspan,hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K (fun x i => v i x)) (Set.empty_subset (Set.univ : Set X))
  have hfull : span K (Set.range (fun x : S => fun i => v i x.1)) = ⊤ := by
    apply top_unique
    rw [← span_flip_eq_top_iff_linearIndependent.mpr hv]
    apply span_le.mpr
    rintro z ⟨x,rfl⟩
    have hz := hspan (Set.mem_image_of_mem (fun x i => v i x) (Set.mem_univ x))
    apply (show span K ((fun x i => v i x) '' S) ≤ span K (Set.range (fun x : S => fun i => v i x.1)) from ?_) hz
    apply span_mono
    rintro z ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩
  let b : Basis S K (I → K) := Basis.mk hli (ge_of_eq hfull)
  refine ⟨S,?_,hli⟩
  rw [Nat.card_eq_fintype_card]
  exact (finrank_eq_card_basis b).symm.trans (finrank_fintype_fun_eq_card K)

/-- Keeping selected nonzero evaluation columns lower-bounds the rank after multiplication. -/
theorem surviving_columns_le_rank {X I : Type*} [Fintype X] [Fintype I]
    (v : I → X → ZMod 2) (S : Set X)
    (hS : LinearIndependent (ZMod 2) (fun x : S => fun i => v i x.1)) (q : X → ZMod 2) :
    Nat.card {x : S // q x.1 = 1} ≤
      finrank (ZMod 2) (span (ZMod 2) (Set.range (fun i => q * v i))) := by
  classical
  let A : Matrix I X (ZMod 2) := fun i x => q x * v i x
  let Y := {x : S // q x.1 = 1}
  let B : Matrix Y I (ZMod 2) := fun y i => v i y.1.1
  have hB : LinearIndependent (ZMod 2) B.row := hS.comp (fun y : Y => y.1) Subtype.val_injective
  have he : (A.submatrix id (fun y : Y => y.1.1)).transpose = B := by
    ext y i
    change q y.1.1 * v i y.1.1 = v i y.1.1
    rw [y.2,one_mul]
  have hb := Matrix.rank_submatrix_le A id (fun y : Y => y.1.1)
  rw [← Matrix.rank_transpose (A.submatrix id (fun y : Y => y.1.1)),he,hB.rank_matrix] at hb
  rw [Matrix.rank_eq_finrank_span_row] at hb
  have hrow : A.row = (fun i => q * v i) := by funext i x; rfl
  rw [hrow] at hb
  simpa only [Nat.card_eq_fintype_card,Y] using hb

end ProofComplexity.FiniteFunctionColumns
end

section
-- Inlined Solutions.MatrixFullMinor

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MatrixFullMinor

open Module

/-- A matrix over a field has a nonzero square minor of size equal to its rank. -/
theorem exists_minor {K m n : Type} [Field K] [Fintype m] [Fintype n] (A : Matrix m n K) :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n), Function.Injective r ∧
      Function.Injective c ∧ (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨κ,a,ha,hsp,hli⟩ := exists_linearIndependent' K A.row
  letI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = A.rank := by
    rw [Matrix.rank_eq_finrank_span_row,← hsp]
    exact linearIndependent_iff_card_eq_finrank_span.mp hli
  let e : Fin A.rank ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let r : Fin A.rank → m := a ∘ e
  let v : Fin A.rank → n → K := A.row ∘ r
  have hv : LinearIndependent K v := hli.comp e e.injective
  obtain ⟨S,hS,hLI⟩ := ProofComplexity.FiniteFunctionColumns.exists_columns v hv
  have hcS : Fintype.card S = A.rank := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using hS
  let d : Fin A.rank ≃ S := Fintype.equivOfCardEq (by simpa using hcS.symm)
  let c : Fin A.rank → n := fun j => (d j).1
  have hcols : LinearIndependent K (A.submatrix r c).col := hLI.comp d d.injective
  have hunit : IsUnit (A.submatrix r c) := Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact ⟨r,c,ha.comp e.injective,Subtype.val_injective.comp d.injective,
    (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero⟩

end AC02Frege.MatrixFullMinor
end

section
-- Inlined Solutions.MatrixRankRetention

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MatrixRankRetention

open MvPolynomial Matrix PolynomialMultiplicity

noncomputable def pencil {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    Matrix (Fin p) (Fin q) (MvPolynomial (Fin s) (ZMod 2)) :=
  ∑ i : Fin s, (X i : MvPolynomial (Fin s) (ZMod 2)) • (M i).map (C : ZMod 2 →+* MvPolynomial (Fin s) (ZMod 2))

lemma pencil_eval {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2))
    (ε : Fin s → ZMod 2) : (pencil M).map (eval ε) = ∑ i, ε i • M i := by
  ext r j
  simp [pencil,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,map_sum,map_mul]

lemma pencil_generic {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    let P := MvPolynomial (Fin s) (ZMod 2)
    let E := FractionRing P
    (pencil M).map (algebraMap P E) =
      ∑ i, algebraMap P E (X i) • (M i).map (algebraMap (ZMod 2) E) := by
  intro P E
  have hC (z : ZMod 2) : algebraMap P E (C z) = algebraMap (ZMod 2) E z :=
    (IsScalarTower.algebraMap_apply (ZMod 2) P E z).symm
  ext r j
  simp only [pencil,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,map_sum,map_mul,hC]

lemma pencil_degree {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) (r : Fin p) (j : Fin q) :
    ((pencil M) r j).totalDegree ≤ 1 := by
  simp only [pencil,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- Source Lemma A.10 for the binary cube, with no kernel hypothesis. -/
theorem expected_rank {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    let P := MvPolynomial (Fin s) (ZMod 2)
    let E := FractionRing P
    let A := ∑ i, algebraMap P E (X i) • (M i).map (algebraMap (ZMod 2) E)
    (A.rank : ℝ)/2 ≤ (∑ ε : Fin s → ZMod 2, ((∑ i, ε i • M i).rank : ℝ))/2^s := by
  classical
  intro P E A
  let f := algebraMap P E
  have hmap : (pencil M).map f = A := pencil_generic M
  obtain ⟨r,c,hr,hc,hminor⟩ := MatrixFullMinor.exists_minor A
  let N := (pencil M).submatrix r c
  have hNm : (N.map f).det ≠ 0 := by
    rw [← Matrix.submatrix_map,hmap]
    exact hminor
  have hN : N.det ≠ 0 := by
    intro hz
    apply hNm
    have hd : f N.det = (N.map f).det := f.map_det N
    rw [← hd,hz,map_zero]
  have hdeg : N.det.totalDegree ≤ A.rank := by
    simpa only [Fintype.card_fin] using
      DeterminantDegree.totalDegree_det_le N (fun i j => pencil_degree M (r i) (c j))
  have hpoint (ε : Fin s → ZMod 2) :
      A.rank ≤ (∑ i, ε i • M i).rank+multiplicity N.det ε := by
    have hn := rank_loss_le_multiplicity N hN ε
    have heval : N.map (eval ε) = (∑ i, ε i • M i).submatrix r c := by
      rw [← Matrix.submatrix_map,pencil_eval]
    rw [heval,Fintype.card_fin] at hn
    exact hn.trans (Nat.add_le_add_right (Matrix.rank_submatrix_le _ r c) _)
  have hsum : A.rank*2^s ≤ (∑ ε : Fin s → ZMod 2, (∑ i, ε i • M i).rank)+
      ∑ ε : Fin s → ZMod 2, multiplicity N.det ε := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun ε hε => hpoint ε)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
      Fintype.card_fin,ZMod.card,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using h
  have hmult : 2*(∑ ε : Fin s → ZMod 2, multiplicity N.det ε) ≤ A.rank*2^s := by
    have h := cube_sum_bound (Fin s) N.det hN
    simp only [Fintype.card_fin] at h
    have h' := h.trans (Nat.mul_le_mul_right _ hdeg)
    convert h' using 1
    congr 1
    congr 1
    apply Finset.sum_congr
    · ext x; simp
    · intro x hx; rfl
  have hnat : A.rank*2^s ≤ 2*(∑ ε : Fin s → ZMod 2, (∑ i, ε i • M i).rank) := by omega
  have hreal : (A.rank : ℝ)*2^s ≤ 2*(∑ ε : Fin s → ZMod 2, ((∑ i, ε i • M i).rank : ℝ)) := by
    exact_mod_cast hnat
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^s)).mpr
  nlinarith

lemma exists_half_rank {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    let P := MvPolynomial (Fin s) (ZMod 2)
    let E := FractionRing P
    let A := ∑ i, algebraMap P E (X i) • (M i).map (algebraMap (ZMod 2) E)
    ∃ ε : Fin s → ZMod 2, (A.rank : ℝ)/2 ≤ ((∑ i, ε i • M i).rank : ℝ) := by
  classical
  intro P E A
  have havg := expected_rank M
  by_contra! h
  have hsum := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty (fun ε hε => h ε)
  have hs : (∑ ε : Fin s → ZMod 2, ((∑ i, ε i • M i).rank : ℝ)) < 2^s*((A.rank : ℝ)/2) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card,
      nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hsum
  have hl := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^s)).mp havg
  nlinarith

end AC02Frege.MatrixRankRetention
end

section
-- Inlined Solutions.PangMatrix

set_option maxHeartbeats 2000000

namespace AC02Frege.PangMatrix

open MvPolynomial Matrix

theorem pang_matrix_lemma {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    let E := FractionRing (MvPolynomial (Fin s) (ZMod 2))
    let lam : Fin s → E := fun i => algebraMap (MvPolynomial (Fin s) (ZMod 2)) E (X i)
    let Mlam : Matrix (Fin p) (Fin q) E := ∑ i, lam i • (M i).map (algebraMap (ZMod 2) E)
    let Mlam2 : Matrix (Fin p) (Fin q) E := ∑ i, (lam i) ^ 2 • (M i).map (algebraMap (ZMod 2) E)
    let c : ℕ := (Matrix.of (fun (ik : Fin s × Fin p) (j : Fin q) => M ik.1 ik.2 j)).rank
    (∀ v : Fin q → E, Mlam *ᵥ v = 0 → Mlam2 *ᵥ v = 0) →
      Mlam.rank = c ∧
      (c : ℝ) / 2 ≤ (∑ ε : Fin s → ZMod 2, ((∑ i, ε i • M i).rank : ℝ)) / 2 ^ s ∧
      ∃ ε : Fin s → ZMod 2, (c : ℝ) / 2 ≤ ((∑ i, ε i • M i).rank : ℝ)  := by
  intro E lam A B c hker
  have hr : A.rank = c := PangGenericRank.formal_rank M hker
  refine ⟨hr,?_,?_⟩
  · have h := MatrixRankRetention.expected_rank M
    change (A.rank : ℝ)/2 ≤ _ at h
    simpa only [hr] using h
  · have h := MatrixRankRetention.exists_half_rank M
    change ∃ ε : Fin s → ZMod 2, (A.rank : ℝ)/2 ≤ ((∑ i, ε i • M i).rank : ℝ) at h
    simpa only [hr] using h

end AC02Frege.PangMatrix
end

open AC02Frege MvPolynomial Matrix

theorem solution {s p q : ℕ} (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2)) :
    let E := FractionRing (MvPolynomial (Fin s) (ZMod 2))
    let lam : Fin s → E := fun i => algebraMap (MvPolynomial (Fin s) (ZMod 2)) E (X i)
    let Mlam : Matrix (Fin p) (Fin q) E := ∑ i, lam i • (M i).map (algebraMap (ZMod 2) E)
    let Mlam2 : Matrix (Fin p) (Fin q) E := ∑ i, (lam i) ^ 2 • (M i).map (algebraMap (ZMod 2) E)
    let c : ℕ := (Matrix.of (fun (ik : Fin s × Fin p) (j : Fin q) => M ik.1 ik.2 j)).rank
    (∀ v : Fin q → E, Mlam *ᵥ v = 0 → Mlam2 *ᵥ v = 0) →
      Mlam.rank = c ∧
      (c : ℝ) / 2 ≤ (∑ ε : Fin s → ZMod 2, ((∑ i, ε i • M i).rank : ℝ)) / 2 ^ s ∧
      ∃ ε : Fin s → ZMod 2, (c : ℝ) / 2 ≤ ((∑ i, ε i • M i).rank : ℝ)  := by
  exact AC02Frege.PangMatrix.pang_matrix_lemma M
