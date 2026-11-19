-- Prove2me | solution 1 for APSCounting893.Main.jacobian_independence_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:33:17.958387+00:00
-- url     : https://prove2.me/submissions/ad823390-3d05-4656-9fb8-21fb36e700b9

import Mathlib
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_pderiv_lt {K : Type*} [CommRing K] [IsDomain K] {ι : Type*}
    (p : MvPolynomial (ι) K) (i : ι) (h : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs (e : ι →₀ ℕ) (he : e ∈ (pderiv i p).support) :
      e.sum (fun _ k => k) + 1 ≤ p.totalDegree := by
    have hcoef := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv] at hcoef
    have hq : p.coeff (e + Finsupp.single i 1) ≠ 0 :=
      fun hz => hcoef (by rw [hz, zero_mul])
    have hh := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hq)
    have heq : (e + Finsupp.single i 1).sum (fun _ k => k) = e.sum (fun _ k => k) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    rwa [heq] at hh
  have hd : 0 < p.totalDegree := by
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr h
    have hh := hs e he
    omega
  have hb : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro e he
    have hh := hs e he
    omega
  omega

lemma eq_C_of_forall_pderiv_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ι : Type*}
    (p : MvPolynomial (ι) K) (hp : ∀ i, pderiv i p = 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext e
  by_cases he : e = 0
  · subst e
    simp
  have hi : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hi
  have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hre : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  have hc := congrArg (MvPolynomial.coeff (e - Finsupp.single i 1)) (hp i)
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero, hre] at hc
  have hval : (e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 = e i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have hn : (((e - Finsupp.single i 1 : ι →₀ ℕ) i : ℕ) : K) + 1 ≠ 0 := by
    have hh : (((e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hpc : p.coeff e = 0 := (mul_eq_zero.mp hc).resolve_right hn
  simp [MvPolynomial.coeff_C, Ne.symm he, hpc]

lemma pderiv_aeval_chain {K : Type*} [CommRing K] [IsDomain K] {ι κ : Type*} [Fintype ι]
    (F : ι → MvPolynomial (κ) K) (p : MvPolynomial (ι) K) (j : κ) :
    pderiv j (MvPolynomial.aeval F p) =
      ∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp,
      map_add, MvPolynomial.pderiv_X, map_mul, MvPolynomial.aeval_X]
    simp only [add_mul, Finset.sum_add_distrib]
    have h1 : (∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i)) * F k =
        ∑ i, MvPolynomial.aeval F (pderiv i p) * F k * pderiv j (F i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h1]
    congr 1
    simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma algebraicIndependent_of_jacobian_minor_ne_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → MvPolynomial κ K) (g : ι → κ)
    (hdet : (Matrix.of (fun i j : ι => pderiv (g j) (F i))).det ≠ 0) :
    AlgebraicIndependent K F := by
  classical
  have hkill : ∀ d : ℕ, ∀ p : MvPolynomial (ι) K,
      p.totalDegree = d → MvPolynomial.aeval F p = 0 → p = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hdeg hp
      let J : Matrix ι ι (MvPolynomial κ K) := fun i j => pderiv (g j) (F i)
      let v : ι → MvPolynomial κ K := fun i => MvPolynomial.aeval F (pderiv i p)
      have hvec : Matrix.vecMul v J = 0 := by
        funext j
        change (∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv (g j) (F i)) = 0
        rw [← pderiv_aeval_chain, hp, map_zero]
      have hv : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
      have hd (i : ι) : pderiv i p = 0 := by
        by_cases h : pderiv i p = 0
        · exact h
        apply ih (pderiv i p).totalDegree (by rw [← hdeg]; exact totalDegree_pderiv_lt p i h)
          (pderiv i p) rfl
        exact congrFun hv i
      have hc := eq_C_of_forall_pderiv_zero p hd
      have he := congrArg (MvPolynomial.aeval F) hc
      rw [hp, MvPolynomial.aeval_C] at he
      have hc0 : p.coeff 0 = 0 := by
        apply MvPolynomial.C_injective (R := K) (σ := κ)
        change MvPolynomial.C (p.coeff 0) = MvPolynomial.C 0
        simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.C_0] using he.symm
      rw [hc, hc0, MvPolynomial.C_0]
  apply algebraicIndependent_iff_injective_aeval.mpr
  apply (injective_iff_map_eq_zero (MvPolynomial.aeval F).toRingHom).mpr
  intro p hp
  exact hkill p.totalDegree p rfl hp

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace APSCounting893.Main

lemma kahler_mapBaseChange_injective_of_formallySmooth
    (R S T : Type) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth S T] :
    Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
  apply (LinearMap.injective_iff_eq_zero_of_exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T)).mpr
  ext x
  rw [show x = 0 from Subsingleton.elim _ _,map_zero]
  rfl

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open MvPolynomial
namespace APSCounting893.Main

lemma algebraicIndependent_differentials {K L : Type} [Field K] [CharZero K] [Field L]
    [Algebra K L] [Algebra.EssFiniteType K L] {r : ℕ} (v : Fin r → L)
    (hv : AlgebraicIndependent K v) :
    LinearIndependent L (fun i => KaehlerDifferential.D K L (v i)) := by
  classical
  let P := MvPolynomial (Fin r) K
  let Q := FractionRing P
  letI : Algebra P L := (MvPolynomial.aeval v).toRingHom.toAlgebra
  letI : IsScalarTower K P L := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap K L x = MvPolynomial.aeval v (MvPolynomial.C x)
    simp)
  let lift : Q →ₐ[K] L := IsFractionRing.liftAlgHom (K := Q) (g := MvPolynomial.aeval v) hv
  letI : Algebra Q L := lift.toRingHom.toAlgebra
  letI : IsScalarTower K Q L := IsScalarTower.of_algebraMap_eq (fun x => (lift.commutes x).symm)
  letI : IsScalarTower P Q L := IsScalarTower.of_algebraMap_eq (fun x => by
    change MvPolynomial.aeval v x = lift (algebraMap P Q x)
    exact (IsFractionRing.lift_algebraMap (K := Q) (L := L)
      (g := (MvPolynomial.aeval (R := K) v).toRingHom)
      (show Function.Injective ((MvPolynomial.aeval (R := K) v).toRingHom) from hv) x).symm)
  letI : Algebra.EssFiniteType Q L := Algebra.EssFiniteType.of_comp K Q L
  letI : Algebra.FormallySmooth Q L := inferInstance
  letI : Algebra.FormallySmooth P Q := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors P)
  letI : Algebra.FormallySmooth P L := Algebra.FormallySmooth.comp P Q L
  let b := (KaehlerDifferential.mvPolynomialBasis K (Fin r)).baseChange L
  have hinj := kahler_mapBaseChange_injective_of_formallySmooth K P L
  have hh := b.linearIndependent.map' (KaehlerDifferential.mapBaseChange K P L)
    (LinearMap.ker_eq_bot.mpr hinj)
  have he (i : Fin r) : KaehlerDifferential.mapBaseChange K P L (b i) = KaehlerDifferential.D K L (v i) := by
    rw [show b i = 1 ⊗ₜ[P] KaehlerDifferential.D K P (MvPolynomial.X i) from by
      simp only [b,Module.Basis.baseChange_apply,KaehlerDifferential.mvPolynomialBasis_apply]
      rfl,
      KaehlerDifferential.mapBaseChange_tmul,one_smul,KaehlerDifferential.map_D]
    change KaehlerDifferential.D K L (MvPolynomial.aeval v (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  simpa only [Function.comp_def,he] using hh

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma polynomial_derivation_formula {K M σ : Type} [CommRing K] [Fintype σ]
    [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
    [IsScalarTower K (MvPolynomial σ K) M]
    (δ : Derivation K (MvPolynomial σ K) M) (p : MvPolynomial σ K) :
    δ p = ∑ j, (MvPolynomial.pderiv j p) • δ (MvPolynomial.X j) := by
  classical
  let b := KaehlerDifferential.mvPolynomialBasis K σ
  have hh := congrArg δ.liftKaehlerDifferential (b.sum_repr (KaehlerDifferential.D K (MvPolynomial σ K) p))
  simpa only [b,KaehlerDifferential.mvPolynomialBasis_apply,KaehlerDifferential.mvPolynomialBasis_repr_apply,
    map_sum,map_smul,Derivation.liftKaehlerDifferential_comp_D] using hh.symm

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma jacobian_rows_independent_of_algebraicIndependent {K : Type} [Field K] [CharZero K]
    {n r : ℕ} (F : Fin r → MvPolynomial (Fin n) K) (hF : AlgebraicIndependent K F) :
    LinearIndependent (FractionRing (MvPolynomial (Fin n) K))
      (fun i j => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
        (MvPolynomial.pderiv j (F i))) := by
  classical
  let R := MvPolynomial (Fin n) K
  let L := FractionRing R
  letI : Algebra.EssFiniteType R L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors R)
  letI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K R L
  let f : R →ₐ[K] L := IsScalarTower.toAlgHom K R L
  have hf : Function.Injective f := IsFractionRing.injective R L
  have hD := algebraicIndependent_differentials (fun i => f (F i)) (hF.map' hf)
  let T : (Fin n → L) →ₗ[L] KaehlerDifferential K L :=
    { toFun := fun u => ∑ j, u j • KaehlerDifferential.D K L (algebraMap R L (MvPolynomial.X j))
      map_add' := by intro u v; simp [add_smul,Finset.sum_add_distrib]
      map_smul' := by intro a u; simp [Finset.smul_sum,smul_smul] }
  have hchain (p : R) : T (fun j => algebraMap R L (MvPolynomial.pderiv j p)) =
      KaehlerDifferential.D K L (algebraMap R L p) := by
    let δ := (KaehlerDifferential.D K L).compAlgebraMap R
    have hh := polynomial_derivation_formula δ p
    rw [Derivation.compAlgebraMap_apply] at hh
    rw [hh]
    change (∑ j, algebraMap R L (MvPolynomial.pderiv j p) •
      KaehlerDifferential.D K L (algebraMap R L (MvPolynomial.X j))) = _
    apply Finset.sum_congr rfl
    intro j hj
    rw [Derivation.compAlgebraMap_apply]
    exact IsScalarTower.algebraMap_smul L _ _
  apply LinearIndependent.of_comp T
  change LinearIndependent L (fun i => T (fun j => algebraMap R L (MvPolynomial.pderiv j (F i))))
  have he : (fun i => T (fun j => algebraMap R L (MvPolynomial.pderiv j (F i)))) =
      fun i => KaehlerDifferential.D K L (algebraMap R L (F i)) := funext (fun i => hchain (F i))
  rw [he]
  exact hD

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open Matrix
namespace APSCounting893.Main

lemma exists_nonzero_column_minor_of_independent_rows {K : Type} [Field K] {n r : ℕ}
    (M : Matrix (Fin r) (Fin n) K) (hM : LinearIndependent K M.row) :
    ∃ g : Fin r → Fin n, Function.Injective g ∧ (M.submatrix id g).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range M.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← M.rank_eq_finrank_span_cols,hM.rank_matrix]
    simp
  obtain ⟨κ,a,ha,hsp,hli⟩ := exists_linearIndependent' K M.col
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hsp' : ⊤ ≤ Submodule.span K (Set.range (M.col ∘ a)) := by rw [hsp,hspan]
  let b : Module.Basis κ K (Fin r → K) := Module.Basis.mk hli hsp'
  have hcard : Fintype.card (Fin r) = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : Fin r ≃ κ := Fintype.equivOfCardEq hcard
  let g : Fin r → Fin n := a ∘ e
  refine ⟨g,ha.comp e.injective,?_⟩
  have hi : LinearIndependent K (M.submatrix id g).col := by
    have he : (M.submatrix id g).col = (M.col ∘ a) ∘ e := by
      funext j i
      rfl
    rw [he]
    exact hli.comp e e.injective
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hi
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_jacobian_minor_of_algebraicIndependent {K : Type} [Field K] [CharZero K]
    {n r : ℕ} (F : Fin r → MvPolynomial (Fin n) K) (hF : AlgebraicIndependent K F) :
    ∃ g : Fin r → Fin n, Function.Injective g ∧
      (Matrix.of (fun i j => MvPolynomial.pderiv (g j) (F i))).det ≠ 0 := by
  classical
  let R := MvPolynomial (Fin n) K
  let L := FractionRing R
  let M : Matrix (Fin r) (Fin n) L := fun i j => algebraMap R L (MvPolynomial.pderiv j (F i))
  have hrows : LinearIndependent L M.row := jacobian_rows_independent_of_algebraicIndependent F hF
  obtain ⟨g,hg,hdet⟩ := exists_nonzero_column_minor_of_independent_rows M hrows
  refine ⟨g,hg,?_⟩
  intro hz
  apply hdet
  have hh := congrArg (algebraMap R L) hz
  rw [map_zero,RingHom.map_det] at hh
  exact hh

end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
open APSCounting893.Main

theorem solution {K : Type} [Field K] [CharZero K] {n r : ℕ}
    (F : Fin r → MvPolynomial (Fin n) K) :
    AlgebraicIndependent K F ↔
      ∃ g : Fin r → Fin n, Function.Injective g ∧
        (Matrix.of (fun i j => MvPolynomial.pderiv (g j) (F i))).det ≠ 0 := by
  constructor
  · exact exists_jacobian_minor_of_algebraicIndependent F
  · rintro ⟨g,hg,hdet⟩
    exact algebraicIndependent_of_jacobian_minor_ne_zero F g hdet
end Component_8

open APSCounting893.Main

