-- Prove2me | solution 1 for ArithmeticE.cyclic_jet_test
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T18:43:36.226299+00:00
-- url     : https://prove2.me/submissions/7df07528-98f7-459f-a137-20e04ff2cc48

import Definitions.Def_clearedDerivativeRows
import Definitions.Def_polynomialDerivativeFrame

noncomputable section
open scoped BigOperators
open Polynomial ArithmeticE Matrix Module
namespace CyclicSelection

private def lin {m : ℕ} (f : Fin m → PowerSeries ℂ) :
    (Fin m → Polynomial ℂ) →ₗ[Polynomial ℂ] PowerSeries ℂ where
  toFun p := ∑ i, (p i : PowerSeries ℂ) * f i
  map_add' p q := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c p := by
    change (∑ i, ((c * p i : Polynomial ℂ) : PowerSeries ℂ) * f i) =
      (c : PowerSeries ℂ) * ∑ i, (p i : PowerSeries ℂ) * f i
    simp [Finset.mul_sum, mul_assoc]

private lemma torsion_free : Module.IsTorsionFree (Polynomial ℂ) (PowerSeries ℂ) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro p f h
  change (p : PowerSeries ℂ)*f=0 at h
  rcases mul_eq_zero.mp h with hp | hf
  · exact Or.inl ((Polynomial.coe_injective ℂ) (by simpa using hp))
  · exact Or.inr hf

lemma span_coordinates (m : ℕ) (f : Fin m → PowerSeries ℂ) :
    ∃ (n : ℕ) (g : Fin n → PowerSeries ℂ)
      (S : Matrix (Fin m) (Fin n) (Polynomial ℂ))
      (U : Matrix (Fin n) (Fin m) (Polynomial ℂ)),
      (∀ i, f i = ∑ j, (S i j : PowerSeries ℂ)*g j) ∧
      (∀ c : Fin n → Polynomial ℂ, (∑ j, (c j : PowerSeries ℂ)*g j)=0 → ∀ j, c j=0) ∧
      U*S=1 := by
  classical
  letI := torsion_free
  let L := lin f
  let V := LinearMap.range L
  haveI : Module.Finite (Polynomial ℂ) V := Module.Finite.range L
  let n := Module.finrank (Polynomial ℂ) V
  let b : Basis (Fin n) (Polynomial ℂ) V := Module.finBasis (Polynomial ℂ) V
  let E := Pi.basisFun (Polynomial ℂ) (Fin m)
  let A := b.equivFun.toLinearMap.comp L.rangeRestrict
  let S : Matrix (Fin m) (Fin n) (Polynomial ℂ) := fun i j => A (E i) j
  have hf : ∀ i, L (E i) = f i := by intro i; simp [L, lin, E, Pi.single_apply, apply_ite]
  have hS : ∀ p j, A p j = ∑ i, p i * S i j := by
    intro p j
    have h := congrArg (fun v : Fin n → Polynomial ℂ => v j) (congrArg A (E.sum_repr p))
    simpa [S, E, map_sum, map_smul] using h.symm
  have hlifts : ∀ j : Fin n, ∃ p, L.rangeRestrict p = b j := by
    intro j
    obtain ⟨p,hp⟩ := (b j).property
    exact ⟨p, Subtype.ext hp⟩
  choose U hU using hlifts
  refine ⟨n,fun j => (b j).val,S,U,?_,?_,?_⟩
  · intro i
    have h := congrArg Subtype.val (b.sum_equivFun (L.rangeRestrict (E i)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    change (∑ j, (S i j : PowerSeries ℂ) * (b j).val) = L (E i) at h
    rw [hf] at h
    exact h.symm
  · intro c hc j
    have hz : (∑ i, c i • b i : V) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      change (∑ i, (c i : PowerSeries ℂ) * (b i).val) = 0
      exact hc
    have h := congrArg (fun v : V => b.equivFun v j) hz
    simpa [Finsupp.single_apply] using h
  · funext j k
    have h : A (U j) k = if j=k then 1 else 0 := by
      simp [A, hU, eq_comm]
    change (∑ i, U j i * S i k) = if j=k then 1 else 0
    rw [← hS]
    exact h

lemma row_contract {m n : ℕ} (g : Fin n → PowerSeries ℂ)
    (S : Matrix (Fin m) (Fin n) (Polynomial ℂ)) (p : Fin m → Polynomial ℂ) :
    (∑ i, (p i : PowerSeries ℂ) * ∑ j, (S i j : PowerSeries ℂ)*g j) =
      ∑ j, ((p ᵥ* S) j : PowerSeries ℂ)*g j := by
  simp only [Matrix.vecMul, dotProduct, ← Polynomial.coeToPowerSeries.ringHom_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma specialized_row_ne_zero {m n : ℕ} (f : Fin m → PowerSeries ℂ)
    (g : Fin n → PowerSeries ℂ)
    (S : Matrix (Fin m) (Fin n) (Polynomial ℂ))
    (U : Matrix (Fin n) (Fin m) (Polynomial ℂ))
    (hf : ∀ i, f i = ∑ j, (S i j : PowerSeries ℂ)*g j)
    (hUS : U*S=1) (ξ : ℂ) (a : Fin m → ℂ)
    (hnot : ¬ ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i : PowerSeries ℂ)*f i)=0 ∧ ∀ i, (p i).eval ξ=a i) :
    a ᵥ* (S.map (Polynomial.eval ξ)) ≠ 0 := by
  classical
  intro hz
  let c : Fin m → Polynomial ℂ := fun i => C (a i)
  let v := c ᵥ* S
  let p := c-v ᵥ* U
  have hp : p ᵥ* S=0 := by
    simp [p, v, Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc, hUS]
  have hv : ∀ j, (v j).eval ξ=0 := by
    intro j
    have h := congrFun hz j
    simpa [v,c,Matrix.vecMul,dotProduct,eval_finsetSum] using h
  apply hnot
  refine ⟨p,?_,?_⟩
  · simp_rw [hf]
    rw [row_contract, hp]
    simp
  · intro i
    simp [p,c,Matrix.vecMul,dotProduct,eval_finsetSum,hv]


lemma algebraic_row_basis {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin m) ℂ) (hUS : U*S=1)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hane : a ᵥ* S ≠ 0) :
    ∃ (hn : 0<n) (w : Fin n → Fin m → ℂ),
      (∀ i j, IsAlgebraic ℚ (w i j)) ∧ w ⟨0,hn⟩=a ∧
      LinearIndependent ℂ (fun i => w i ᵥ* S) := by
  classical
  have hn : 0<n := by
    by_contra h
    have : n=0 := by omega
    subst n
    exact hane (Subsingleton.elim _ _)
  let W := {v : Fin m → ℂ // ∀ i, IsAlgebraic ℚ (v i)}
  let t : Set (Fin n → ℂ) := Set.range (fun v : W => v.val ᵥ* S)
  have hrows : ∀ i : Fin m, (fun j => S i j) ∈ t := by
    intro i
    have he : ∀ j : Fin m, IsAlgebraic ℚ ((Pi.single i 1 : Fin m → ℂ) j) := by
      intro j
      by_cases h : i=j
      · subst j; simpa using (isAlgebraic_one : IsAlgebraic ℚ (1:ℂ))
      · simpa [Pi.single_apply,h] using (isAlgebraic_zero : IsAlgebraic ℚ (0:ℂ))
    exact ⟨⟨Pi.single i 1,he⟩, by ext j; simp [Matrix.vecMul,dotProduct,Pi.single_apply]⟩
  have hmem : ∀ v : Fin m → ℂ, v ᵥ* S ∈ Submodule.span ℂ t := by
    intro v
    have h : (∑ i, v i • (fun j => S i j)) ∈ Submodule.span ℂ t :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hrows i)))
    have hv : (∑ i, v i • (fun j => S i j)) = v ᵥ* S := by
      funext j
      simp [Matrix.vecMul,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← hv]
    exact h
  have ht : ⊤ ≤ Submodule.span ℂ t := by
    intro v _
    simpa [Matrix.vecMul_vecMul,hUS] using hmem (v ᵥ* U)
  have hs : LinearIndepOn ℂ id {a ᵥ* S} := (linearIndepOn_singleton_iff ℂ).mpr hane
  have hst : ({a ᵥ* S} : Set (Fin n → ℂ)) ⊆ t := by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact ⟨⟨a,ha⟩,rfl⟩
  let b := Basis.extendLe hs hst ht
  let I := hs.extend hst
  letI : Fintype I := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card I = n := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  obtain ⟨j,hj⟩ : ∃ j : I, b j = a ᵥ* S :=
    Basis.subset_extendLe hs hst ht (Set.mem_singleton _)
  let e' : I ≃ Fin n := e.trans (Equiv.swap (e j) ⟨0,hn⟩)
  have hej : e' j = ⟨0,hn⟩ := by simp [e']
  have hpre : ∀ i : I, ∃ v : Fin m → ℂ, (∀ k, IsAlgebraic ℚ (v k)) ∧ v ᵥ* S=b i := by
    intro i
    obtain ⟨v,hv⟩ := Basis.extendLe_subset hs hst ht (Set.mem_range_self i)
    exact ⟨v.val,v.property,hv⟩
  choose v hv hvs using hpre
  let w : Fin n → Fin m → ℂ := fun i => if i=⟨0,hn⟩ then a else v (e'.symm i)
  have hw : ∀ i, w i ᵥ* S = (b.reindex e') i := by
    intro i
    by_cases hi : i=⟨0,hn⟩
    · subst i
      have hsymm : e'.symm ⟨0,hn⟩=j := by rw [← hej]; simp
      simp [w,Basis.reindex_apply,hsymm,hj]
    · simp [w,hi,Basis.reindex_apply,hvs]
  refine ⟨hn,w,?_,by simp [w],?_⟩
  · intro i k
    by_cases hi : i=⟨0,hn⟩
    · simpa [w,hi] using ha k
    · simpa [w,hi] using hv (e'.symm i) k
  · simpa only [hw] using (b.reindex e').linearIndependent


lemma differentiate_row {m : ℕ} (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ) : PowerSeries ℂ)*f j)
    (P : Fin m → Polynomial ℂ) :
    (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ
      (∑ i, (P i : PowerSeries ℂ)*f i) =
    ∑ i, ((T.map (algebraMap ℚ ℂ)*(P i).derivative +
      ∑ j, P j*(B j i).map (algebraMap ℚ ℂ) : Polynomial ℂ) : PowerSeries ℂ)*f i := by
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_coe,
    Polynomial.coe_add, Polynomial.coe_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, add_mul]
  have hcross : (∑ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) *
      ((P i : PowerSeries ℂ)*PowerSeries.derivative ℂ (f i))) =
      ∑ i, ((∑ j, P j*(B j i).map (algebraMap ℚ ℂ) : Polynomial ℂ) : PowerSeries ℂ)*f i := by
    simp_rw [mul_left_comm (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ), hode]
    simp only [←Polynomial.coeToPowerSeries.ringHom_apply,map_sum,map_mul,
      Finset.mul_sum,Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
  rw [hcross, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma numerator_identity {m : ℕ} (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ) : PowerSeries ℂ)*f j)
    (P : Fin m → Polynomial ℂ) (k : ℕ) :
    (∑ i, (clearedDerivativeRows T B P k i : PowerSeries ℂ)*f i) =
      (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ)^k *
        (PowerSeries.derivative ℂ)^[k] (∑ i, (P i : PowerSeries ℂ)*f i) := by
  induction k with
  | zero => simp [clearedDerivativeRows]
  | succ k ih =>
    let t : PowerSeries ℂ := T.map (algebraMap ℚ ℂ)
    have hstep : (∑ i, (clearedDerivativeRows T B P (k+1) i : PowerSeries ℂ)*f i) =
        t * PowerSeries.derivative ℂ (∑ i, (clearedDerivativeRows T B P k i : PowerSeries ℂ)*f i) -
          (k:PowerSeries ℂ)*PowerSeries.derivative ℂ t *
            (∑ i, (clearedDerivativeRows T B P k i : PowerSeries ℂ)*f i) := by
      rw [show t = (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) from rfl,
        differentiate_row f T B hode, PowerSeries.derivative_coe]
      simp only [clearedDerivativeRows, Polynomial.coe_sub, Polynomial.coe_mul,
        Polynomial.coe_C, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [map_natCast]
      ring
    rw [hstep, ih]
    change t * PowerSeries.derivative ℂ (t^k * _) -
      (k:PowerSeries ℂ)*PowerSeries.derivative ℂ t*(t^k * _) = t^(k+1)*_
    rw [Derivation.leibniz,PowerSeries.derivative_pow,Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel, pow_succ]; ring


lemma cyclic_test
    (m : ℕ) (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ) : PowerSeries ℂ) * f j)
    (ξ : ℂ) (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hnot : ¬ ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i : PowerSeries ℂ) * f i = 0) ∧ ∀ i, (p i).eval ξ = a i) :
    ∃ (n : ℕ) (w : ℕ → Fin m → ℂ),
      0 < n ∧
      (∀ k < n, ∀ i, IsAlgebraic ℚ (w k i)) ∧
      (∀ i, w 0 i = a i) ∧
      ∀ P : Fin m → Polynomial ℂ,
        (∀ k < n, ∀ i, (clearedDerivativeRows T B P k i).eval ξ = w k i) →
        PolynomialDerivativeFrame (∑ i, (P i : PowerSeries ℂ) * f i) ξ n := by
  classical
  obtain ⟨n,g,S,U,hf,hg,hUS⟩ := span_coordinates m f
  let Se := S.map (Polynomial.eval ξ)
  let Ue := U.map (Polynomial.eval ξ)
  have hUe : Ue*Se=1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) (Polynomial ℂ) =>
      M.map (Polynomial.evalRingHom ξ)) hUS
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hane : a ᵥ* Se ≠ 0 := specialized_row_ne_zero f g S U hf hUS ξ a hnot
  obtain ⟨hn,wf,hwf,hwf0,hli⟩ := algebraic_row_basis Se Ue hUe a ha hane
  let w : ℕ → Fin m → ℂ := fun k => if hk : k<n then wf ⟨k,hk⟩ else 0
  refine ⟨n,w,hn,?_,?_,?_⟩
  · intro k hk i
    simpa [w,hk] using hwf ⟨k,hk⟩ i
  · intro i
    simp [w,hn,hwf0]
  · intro P hjets
    let t : Polynomial ℂ := T.map (algebraMap ℚ ℂ)
    let F : PowerSeries ℂ := ∑ i, (P i : PowerSeries ℂ)*f i
    let R : ℕ → Fin n → Polynomial ℂ := fun k => clearedDerivativeRows T B P k ᵥ* S
    let A : Matrix (Fin n) (Fin n) (Polynomial ℂ) := fun i j => t^(n-i.val)*R i.val j
    have ht : t.eval ξ ≠ 0 := by simpa only [t,eval_map] using hreg
    have hcoords : ∀ k, (t : PowerSeries ℂ)^k * (PowerSeries.derivative ℂ)^[k] F =
        ∑ j, (R k j : PowerSeries ℂ)*g j := by
      intro k
      rw [← numerator_identity f T B hode P k]
      simp_rw [hf]
      exact row_contract g S _
    have heval : ∀ i : Fin n, (fun j => (A i j).eval ξ) =
        (t.eval ξ)^(n-i.val) • (wf i ᵥ* Se) := by
      intro i
      funext j
      simp only [A,eval_mul,eval_pow,R,Matrix.vecMul,dotProduct,eval_finsetSum]
      simp only [eval_mul,hjets i.val i.is_lt,w,i.is_lt,dite_true,
        Pi.smul_apply,smul_eq_mul,Se,Matrix.map_apply,Matrix.vecMul,dotProduct]
    have hAli : LinearIndependent ℂ (A.map (Polynomial.eval ξ)).row := by
      change LinearIndependent ℂ (fun i j => (A i j).eval ξ)
      have hfun : (fun i j => (A i j).eval ξ) =
          (fun i => (t.eval ξ)^(n-i.val) • (wf i ᵥ* Se)) := funext heval
      rw [hfun]
      have h := hli.units_smul (fun i => Units.mk0 ((t.eval ξ)^(n-i.val)) (pow_ne_zero _ ht))
      exact h
    have hdet : A.det.eval ξ ≠ 0 := by
      have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hAli
      have hd := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
      change ((Polynomial.evalRingHom ξ).mapMatrix A).det ≠ 0 at hd
      rw [← (Polynomial.evalRingHom ξ).map_det A] at hd
      exact hd
    refine ⟨t^n,g,A,R n,by simpa using pow_ne_zero n ht,hg,?_,?_,hdet⟩
    · intro i
      have hpow : (t : PowerSeries ℂ)^n =
          (t : PowerSeries ℂ)^(n-i.val)*(t : PowerSeries ℂ)^i.val := by
        rw [← pow_add,Nat.sub_add_cancel i.is_lt.le]
      rw [Polynomial.coe_pow]
      change (t : PowerSeries ℂ)^n*(PowerSeries.derivative ℂ)^[i.val] F = _
      rw [hpow,mul_assoc,hcoords]
      simp [A,Finset.mul_sum,mul_assoc]
    · simpa only [Polynomial.coe_pow] using hcoords n

end CyclicSelection

theorem solution
    (m : ℕ) (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ) : PowerSeries ℂ) * f j)
    (hbasis : RelationBasis f)
    (ξ : ℂ) (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hnot : ¬ ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i : PowerSeries ℂ) * f i = 0) ∧ ∀ i, (p i).eval ξ = a i) :
    ∃ (n : ℕ) (w : ℕ → Fin m → ℂ),
      0 < n ∧
      (∀ k < n, ∀ i, IsAlgebraic ℚ (w k i)) ∧
      (∀ i, w 0 i = a i) ∧
      ∀ P : Fin m → Polynomial ℂ,
        (∀ k < n, ∀ i, (clearedDerivativeRows T B P k i).eval ξ = w k i) →
        PolynomialDerivativeFrame (∑ i, (P i : PowerSeries ℂ) * f i) ξ n := by
  exact CyclicSelection.cyclic_test m f T B hode ξ hreg a ha hnot

#print axioms solution
