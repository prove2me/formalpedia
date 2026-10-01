-- Prove2me | Definitions.Def_Yukon_92756c7c5028ffe108a201de
-- name    : Yukon_92756c7c5028ffe108a201de
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:42.830407+00:00
-- url     : https://prove2.me/theorems/8c51148c-08b3-479e-ab59-43f775ee2d49
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeCore6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeCore6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeCore6812.lean
--
--   provider-v8:00fe44f7d5e6e6877bd98eabbd081a5b31b8eeb0b53355f0d28d2376a3e4ce09
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODowMGZlNDRmN2Q1ZTZlNjg3N2JkOThlYWJiZDA4MWE1YjMxYjhlZWIwYjUzMzU1ZjBkMjhkMjM3NmEzZTRjZTA5IiwiaGFzaCI6ImJkYTE1ZTJlMzVkZjBiMDkzZGYyNGU1NGFjZWU0NTAzMmJhY2FlZTk1YmFhMDk5MjIzMWNiYThmNGNjNzk1MTAiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzkyNzU2YzdjNTAyOGZmZTEwOGEyMDFkZSIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.BigOperators


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge, piece 3 (algebra): the degree-`< p` relation on a slice

For a surface `F(X₀, x₀, x₁, x₂) = 0` and a slice form `ℓ = Σ q_m(X₀) x_m` with `q_i = 1`, if
`(x_a, ℓ, X₀)` is algebraically independent (`a ≠ i`), then the third coordinate `x_c` is a root
of a nonzero polynomial `P` over `K[X₀, ℓ, x_a]` of degree at most the `(Y,Y',Γ)`-degree of `F`
(`core_poly`): `P(Z) = F(X₀, …)` with `x_a` kept, `x_c ↦ Z`, `x_i ↦ ℓ - q_a x_a - q_c Z`.
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open MvPolynomial

section Core

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem sum_fin3_distinct {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (i a c : Fin 3)
    (hia : i ≠ a) (hic : i ≠ c) (hac : a ≠ c) : ∑ m, f m = f i + f a + f c := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases a <;> fin_cases c <;> simp at hia hic hac ⊢ <;> abel

theorem eq_of_ne_of_ne {i a c m : Fin 3} (hia : i ≠ a) (hic : i ≠ c) (hac : a ≠ c)
    (hma : m ≠ a) (hmc : m ≠ c) : m = i := by
  rw [ne_eq, Fin.ext_iff] at hia hic hac hma hmc
  have := i.isLt; have := a.isLt; have := c.isLt; have := m.isLt
  ext; omega

/-- Degree in the new variable after an affine substitution in `Y, Y', Γ`. -/
theorem natDegree_aeval_le {R : Type*} [CommRing R] [Algebra K R] (F : MvPolynomial (Fin 4) K)
    (g : Fin 4 → Polynomial R) (N : ℕ) (hN : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ N)
    (h0 : (g 0).natDegree = 0) (h1 : ∀ m, (g m).natDegree ≤ 1) : (aeval g F).natDegree ≤ N := by
  rw [aeval_def, eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le (s := F.support) _ fun d hd => ?_
  rw [Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hp : ∀ m, (g m ^ d m).natDegree ≤ d m * (g m).natDegree := fun m =>
    Polynomial.natDegree_pow_le
  refine (Finset.sum_le_sum fun m _ => hp m).trans ?_
  rw [Fin.sum_univ_four, h0, mul_zero, zero_add]
  refine le_trans ?_ (hN d hd)
  have e1 := Nat.mul_le_mul_left (d 1) (h1 1)
  have e2 := Nat.mul_le_mul_left (d 2) (h1 2)
  have e3 := Nat.mul_le_mul_left (d 3) (h1 3)
  simp only [mul_one] at e1 e2 e3
  omega

theorem support_bound_of_weighted (F : MvPolynomial (Fin 4) K) (N : ℕ)
    (hN : weightedTotalDegree ![0, 1, 1, 1] F ≤ N) : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ N := by
  intro d hd
  refine le_trans (le_of_eq ?_) ((le_weightedTotalDegree _ hd).trans hN)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_four]
  simp

/-- `MvPolynomial (Option ι) K → R[X]`, `none ↦ X`, `some j ↦ C (w j)`, is injective when `w` is
algebraically independent. -/
theorem aeval_optionElim_injective {ι R : Type*} [CommRing R] [Algebra K R] (w : ι → R)
    (hw : AlgebraicIndependent K w) :
    Function.Injective (aeval (R := K) (fun o : Option ι =>
      o.elim (Polynomial.X : Polynomial R) fun j => Polynomial.C (w j))) := by
  have h : (aeval (R := K) (fun o : Option ι => o.elim (Polynomial.X : Polynomial R)
      fun j => Polynomial.C (w j)) : MvPolynomial (Option ι) K →ₐ[K] Polynomial R) =
      (Polynomial.mapAlgHom (aeval w)).comp (optionEquivLeft K ι).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro (_ | j)
    · simp [optionEquivLeft_X_none]
    · simp [optionEquivLeft_X_some]
  rw [h, AlgHom.coe_comp]
  exact (Polynomial.map_injective _ hw).comp (optionEquivLeft K ι).injective

/-- The substitution `X₀ ↦ x0, x_a ↦ t, x_c ↦ z, x_i ↦ ℓ - q_a(x0) t - q_c(x0) z`. -/
noncomputable def subVals {M : Type*} [CommRing M] [Algebra K M] (q : Fin 3 → Polynomial K)
    (a c : Fin 3) (x0 ℓ t z : M) : Fin 4 → M :=
  Fin.cons x0 fun m => if m = a then t else if m = c then z else
    ℓ - Polynomial.aeval x0 (q a) * t - Polynomial.aeval x0 (q c) * z

theorem map_subVals {M M' : Type*} [CommRing M] [Algebra K M] [CommRing M'] [Algebra K M']
    (φ : M →ₐ[K] M') (q : Fin 3 → Polynomial K) (a c : Fin 3) (x0 ℓ t z : M) :
    (fun m => φ (subVals q a c x0 ℓ t z m)) = subVals q a c (φ x0) (φ ℓ) (φ t) (φ z) := by
  funext m
  refine Fin.cases ?_ (fun m => ?_) m
  · rfl
  · simp only [subVals, Fin.cons_succ]
    split_ifs
    · rfl
    · rfl
    · simp only [map_sub, map_mul, Polynomial.aeval_algHom_apply]

/-- With `q_i = 1`, the substitution at `ℓ = Σ q_m(x0) y_m` returns the point itself. -/
theorem subVals_cons {M : Type*} [CommRing M] [Algebra K M] (q : Fin 3 → Polynomial K)
    (i a c : Fin 3) (hia : i ≠ a) (hic : i ≠ c) (hac : a ≠ c) (hqi : q i = 1) (x0 : M)
    (y : Fin 3 → M) :
    subVals q a c x0 (∑ m, Polynomial.aeval x0 (q m) * y m) (y a) (y c) = Fin.cons x0 y := by
  funext m
  refine Fin.cases ?_ (fun m => ?_) m
  · rfl
  · simp only [subVals, Fin.cons_succ]
    split_ifs with h1 h2
    · rw [h1]
    · rw [h2]
    · rw [eq_of_ne_of_ne hia hic hac h1 h2, sum_fin3_distinct _ i a c hia hic hac, hqi, map_one,
        one_mul]
      ring

/-- **The slice relation.** -/
theorem core_poly (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) (N : ℕ)
    (hN : ∀ d ∈ F.support, d 1 + d 2 + d 3 ≤ N) (x0 : L) (x : Fin 3 → L)
    (hFx : aeval (Fin.cons x0 x : Fin 4 → L) F = 0) (q : Fin 3 → Polynomial K) (i a c : Fin 3)
    (hia : i ≠ a) (hic : i ≠ c) (hac : a ≠ c) (hqi : q i = 1)
    (hind : AlgebraicIndependent K (fun o : Option (Fin 2) =>
      o.elim (x a) ![∑ m, Polynomial.aeval x0 (q m) * x m, x0])) :
    ∃ P : Polynomial L, P ≠ 0 ∧ P.eval (x c) = 0 ∧ P.natDegree ≤ N ∧
      ∀ n, P.coeff n ∈ Algebra.adjoin K {x0, ∑ m, Polynomial.aeval x0 (q m) * x m, x a} := by
  classical
  set ℓ := ∑ m, Polynomial.aeval x0 (q m) * x m with hℓ
  set S := Algebra.adjoin K ({x0, ℓ, x a} : Set L)
  set w : Option (Fin 2) → L := fun o => o.elim (x a) ![ℓ, x0]
  have hwS : ∀ o, w o ∈ S := by
    rintro (_ | j)
    · exact Algebra.subset_adjoin (by simp [w])
    · fin_cases j
      · exact Algebra.subset_adjoin (by simp [w])
      · exact Algebra.subset_adjoin (by simp [w])
  let wS : Option (Fin 2) → S := fun o => ⟨w o, hwS o⟩
  have hwSind : AlgebraicIndependent K wS := AlgebraicIndependent.of_comp S.val hind
  let V : Option (Option (Fin 2)) → Polynomial S :=
    fun o => o.elim Polynomial.X fun j => Polynomial.C (wS j)
  let σv : Fin 4 → MvPolynomial (Option (Option (Fin 2))) K :=
    subVals q a c (X (some (some 1))) (X (some (some 0))) (X (some none)) (X none)
  let τv : Option (Option (Fin 2)) → MvPolynomial (Fin 4) K := fun o =>
    o.elim (X c.succ) fun o' => o'.elim (X a.succ)
      ![∑ m, Polynomial.aeval (X 0 : MvPolynomial (Fin 4) K) (q m) * X m.succ, X 0]
  have hτσ : (fun m => aeval τv (σv m)) = X := by
    rw [map_subVals]
    simp only [aeval_X]
    rw [show τv (some (some 0)) = ∑ m, Polynomial.aeval (X 0 : MvPolynomial (Fin 4) K) (q m) *
      (fun m : Fin 3 => (X m.succ : MvPolynomial (Fin 4) K)) m from rfl,
      show τv (some (some 1)) = X 0 from rfl, show τv (some none) = X a.succ from rfl,
      show τv none = X c.succ from rfl]
    rw [subVals_cons q i a c hia hic hac hqi]
    funext m
    refine Fin.cases rfl (fun m => rfl) m
  have hσF : aeval σv F ≠ 0 := by
    intro h
    apply hF
    have h1 := congrArg (aeval τv) h
    rw [comp_aeval_apply, map_zero, hτσ, aeval_X_left_apply] at h1
    exact h1
  set Q : Polynomial S := aeval V (aeval σv F)
  have hQ0 : Q ≠ 0 := fun h =>
    hσF (aeval_optionElim_injective wS hwSind (h.trans (map_zero _).symm))
  have hSinj : Function.Injective (algebraMap S L) := Subtype.val_injective
  refine ⟨Q.map (algebraMap S L), ?_, ?_, ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff hSinj).2 hQ0
  · rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    have h1 := comp_aeval_apply ((Polynomial.aeval (R := S) (x c)).restrictScalars K) (f := V)
      (aeval σv F)
    rw [AlgHom.restrictScalars_apply] at h1
    rw [show (Polynomial.aeval (x c)) Q = _ from h1, comp_aeval_apply, map_subVals]
    simp only [aeval_X]
    rw [← hFx, ← subVals_cons q i a c hia hic hac hqi x0 x]
    simp only [V, Option.elim, AlgHom.restrictScalars_apply, Polynomial.aeval_C,
      Polynomial.aeval_X]
    rfl
  · rw [Polynomial.natDegree_map_eq_of_injective hSinj]
    change (aeval V (aeval σv F)).natDegree ≤ N
    rw [comp_aeval_apply, map_subVals]
    simp only [aeval_X]
    have hC : ∀ j, (V (some j)).natDegree = 0 := fun j => Polynomial.natDegree_C _
    refine natDegree_aeval_le F _ N hN (hC _) fun m => ?_
    refine Fin.cases ((hC _).le.trans zero_le_one) (fun m => ?_) m
    simp only [subVals, Fin.cons_succ]
    split_ifs
    · exact (hC _).le.trans zero_le_one
    · exact Polynomial.natDegree_X_le
    · have h1 : ∀ p : Polynomial K, (Polynomial.aeval (V (some (some 1))) p).natDegree = 0 :=
        fun p => by
          rw [show V (some (some 1)) = Polynomial.C (wS (some 1)) from rfl,
            ← Polynomial.algebraMap_eq (R := S), Polynomial.aeval_algebraMap_apply,
            Polynomial.algebraMap_eq]
          exact Polynomial.natDegree_C _
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le ((hC _).le.trans zero_le_one) ?_)) ?_)
      · exact Polynomial.natDegree_mul_le.trans (by rw [h1, hC]; simp)
      · refine Polynomial.natDegree_mul_le.trans ?_
        rw [h1, zero_add]; exact Polynomial.natDegree_X_le
  · intro n
    rw [Polynomial.coeff_map]
    exact (Q.coeff n).2

end Core

end ProximityPrize.SubmissionLower.HFree6812


