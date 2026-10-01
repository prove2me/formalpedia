-- Prove2me | Definitions.Def_Yukon_44eee9f2bbb5bf38cd30ce5d
-- name    : Yukon_44eee9f2bbb5bf38cd30ce5d
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:41.379054+00:00
-- url     : https://prove2.me/theorems/74db364f-2fc5-4848-9c4b-486a867d1cd5
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeElim6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeElim6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeElim6812.lean
--
--   provider-v8:d88089279e5c1bd10ed20fc754af7b95a6a2826bff8d1a657d11cd83c0b99d61
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODpkODgwODkyNzllNWMxYmQxMGVkMjBmYzc1NGFmN2I5NWE2YTI4MjZiZmY4ZDFhNjU3ZDExY2Q4M2MwYjk5ZDYxIiwiaGFzaCI6IjYyZGNhNDI2ODk2NjM5YmM4ZDdjMTJmNzA3MjlmOGQyYWM2ODg3ZDhiZTFjMDI0YWZmNDJhODJlMDM3NzkyMmYiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzQ0ZWVlOWYyYmJiNWJmMzhjZDMwY2U1ZCIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge, piece 2a (algebra): elimination on a generic slice

If a point `y` of an irreducible surface `G = 0` over `Ω` also lies on `P = 0` with `G ∤ P`,
and a linear form `ℓ = X_i + Σ c_m X_m` takes a value `t` transcendental over `Ω`, then every
coordinate of `y` is algebraic over any field `E ∋ t`.  This is the core of the slice
descent: a slice component (a curve over `E`) cannot lie on `G = P = 0`, so its contraction
to `Ω[Y,Y',Γ]` is exactly `(G)`.
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open MvPolynomial

section Resultant

variable {A : Type*} [CommRing A] [IsDomain A] [IsGCDMonoid A]

theorem resultant_ne_zero_of_not_dvd (P Q : Polynomial A) (hP : Irreducible P)
    (hpos : 0 < P.natDegree) (hPQ : ¬ P ∣ Q) : P.resultant Q ≠ 0 := by
  intro hz
  have hprim := hP.isPrimitive (Nat.ne_of_gt hpos)
  let f : A →+* FractionRing A := algebraMap A (FractionRing A)
  have hf : Function.Injective f := IsFractionRing.injective A (FractionRing A)
  have hPd : (P.map f).natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective hf P
  have hQd : (Q.map f).natDegree = Q.natDegree := Polynomial.natDegree_map_eq_of_injective hf Q
  have hres : (P.map f).resultant (Q.map f) = 0 := by
    have h1 := Polynomial.resultant_map_map P Q P.natDegree Q.natDegree f
    show (P.map f).resultant (Q.map f) (P.map f).natDegree (Q.map f).natDegree = 0
    rw [hPd, hQd, h1, show P.resultant Q P.natDegree Q.natDegree = 0 from hz, map_zero]
  have hnot : ¬ IsCoprime (P.map f) (Q.map f) := (Polynomial.resultant_eq_zero_iff.mp hres).2
  have hi : Irreducible (P.map f) := hprim.irreducible_iff_irreducible_map_fraction_map.mp hP
  exact hPQ (hprim.dvd_of_fraction_map_dvd_fraction_map
    ((Irreducible.dvd_iff_not_isCoprime hi).mpr hnot))

end Resultant

variable {Ω : Type*} [Field Ω]

/-- Elimination of variable `0`. -/
theorem exists_eliminant0 {R : Type*} [CommRing R] [Algebra Ω R]
    (G P : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hGP : ¬ G ∣ P)
    (z : Fin 3 → R) (hGz : aeval z G = 0) (hPz : aeval z P = 0) :
    ∃ Q : MvPolynomial (Fin 2) Ω, Q ≠ 0 ∧ aeval (fun m => z m.succ) Q = 0 := by
  classical
  let e := finSuccEquiv Ω 2
  have hback : ∀ q : MvPolynomial (Fin 2) Ω,
      aeval z (e.symm (Polynomial.C q)) = aeval (fun m => z m.succ) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      have h1 : e.symm (Polynomial.C (C a)) = C a :=
        RingHom.congr_fun (finSuccEquiv_comp_C_eq_C (R := Ω) 2) a
      rw [h1, aeval_C, aeval_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
      have h1 : e.symm (Polynomial.C (X j)) = X j.succ := by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply, finSuccEquiv_X_succ]
      simp only [map_mul, h1, hp, aeval_X]
  have hg : Irreducible (e G) := (MulEquiv.irreducible_iff e).mpr hG
  have hgp : ¬ e G ∣ e P := by
    rintro ⟨c, hc⟩
    exact hGP ⟨e.symm c, by apply e.injective; rw [map_mul, AlgEquiv.apply_symm_apply, hc]⟩
  by_cases hdeg : (e G).natDegree = 0
  · refine ⟨(e G).coeff 0, ?_, ?_⟩
    · intro h0
      apply hg.ne_zero
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, h0, map_zero]
    · rw [← hback, ← Polynomial.eq_C_of_natDegree_eq_zero hdeg, AlgEquiv.symm_apply_apply, hGz]
  · obtain ⟨a, b, -, -, hab⟩ :=
      Polynomial.exists_mul_add_mul_eq_C_resultant (e G) (e P) le_rfl le_rfl (Or.inl hdeg)
    refine ⟨(e G).resultant (e P),
      resultant_ne_zero_of_not_dvd (e G) (e P) hg (by omega) hgp, ?_⟩
    rw [← hback, ← hab, map_add, map_mul, map_mul, AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply, map_add, map_mul, map_mul, hGz, hPz, zero_mul, zero_mul,
      add_zero]

/-- Elimination of the third variable, keeping `z m` and `z i`. -/
theorem exists_eliminant {R : Type*} [CommRing R] [Algebra Ω R]
    (G P : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hGP : ¬ G ∣ P)
    (z : Fin 3 → R) (hGz : aeval z G = 0) (hPz : aeval z P = 0) (m i : Fin 3) (hmi : m ≠ i) :
    ∃ Q : MvPolynomial (Fin 2) Ω, Q ≠ 0 ∧ aeval ![z m, z i] Q = 0 := by
  classical
  let i' := Equiv.swap 1 m i
  have hi' : i' ≠ 1 := by
    intro h
    exact hmi ((Equiv.swap_apply_eq_iff.mp h).trans (Equiv.swap_apply_left 1 m)).symm
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 m * Equiv.swap 2 i'
  have hσ1 : σ 1 = m := by
    change Equiv.swap 1 m (Equiv.swap 2 i' 1) = m
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) hi'.symm, Equiv.swap_apply_left]
  have hσ2 : σ 2 = i := by
    change Equiv.swap 1 m (Equiv.swap 2 i' 2) = i
    rw [Equiv.swap_apply_left, Equiv.swap_apply_self]
  let r := renameEquiv Ω σ.symm
  have hr : ∀ p : MvPolynomial (Fin 3) Ω, aeval (z ∘ σ) (r p) = aeval z p := by
    intro p
    change aeval (z ∘ σ) (rename σ.symm p) = aeval z p
    rw [aeval_rename, show (z ∘ σ) ∘ σ.symm = z by funext x; simp]
  have hG' : Irreducible (r G) := (MulEquiv.irreducible_iff r).mpr hG
  have hGP' : ¬ r G ∣ r P := by
    rintro ⟨c, hc⟩
    exact hGP ⟨r.symm c, by apply r.injective; rw [map_mul, AlgEquiv.apply_symm_apply, hc]⟩
  obtain ⟨Q, hQ, hQz⟩ := exists_eliminant0 (r G) (r P) hG' hGP' (z ∘ σ)
    (by rw [hr, hGz]) (by rw [hr, hPz])
  have hfun : (fun j : Fin 2 => (z ∘ σ) j.succ) = ![z m, z i] := by
    funext j
    fin_cases j
    · simp [hσ1]
    · simp [hσ2]
  rw [hfun] at hQz
  exact ⟨Q, hQ, hQz⟩

/-- A root of a nonzero bivariate relation with a transcendental second entry is algebraic. -/
theorem isAlgebraic_of_eliminant {E R : Type*} [Field E] [Field R] [Algebra Ω E] [Algebra E R]
    [Algebra Ω R] [IsScalarTower Ω E R] (t : E) (ht : Transcendental Ω t) (a : R)
    (Q : MvPolynomial (Fin 2) Ω) (hQ : Q ≠ 0) (h : aeval ![a, algebraMap E R t] Q = 0) :
    IsAlgebraic E a := by
  classical
  let e := finSuccEquiv Ω 1
  let φt : MvPolynomial (Fin 1) Ω →ₐ[Ω] E := aeval ![t]
  have hinj : Function.Injective φt :=
    algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_iff_transcendental.mpr ht)
  let q : Polynomial E := (e Q).map φt.toRingHom
  have hq0 : q ≠ 0 := by
    intro h
    apply hQ
    have h1 : e Q = 0 := by
      apply Polynomial.map_injective φt.toRingHom hinj
      rw [Polynomial.map_zero]
      exact h
    simpa using congrArg e.symm h1
  refine ⟨q, hq0, ?_⟩
  let Ψ : MvPolynomial (Fin 2) Ω →ₐ[Ω] R :=
    ((Polynomial.aeval a).restrictScalars Ω).comp ((Polynomial.mapAlgHom φt).comp e.toAlgHom)
  have hΨ : Ψ = aeval ![a, algebraMap E R t] := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j
    · simp [Ψ, e, finSuccEquiv_X_zero]
    · have hX1 : e (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
      show Polynomial.aeval a ((e (X 1)).map (φt : MvPolynomial (Fin 1) Ω →+* E)) = _
      rw [hX1, Polynomial.map_C, Polynomial.aeval_C]
      simp [φt]
  have h1 : Ψ Q = Polynomial.aeval a q := rfl
  rw [← h1, hΨ, h]

/-- **Slice elimination.** -/
theorem coordinates_algebraic_of_not_dvd {E R : Type*} [Field E] [Field R] [Algebra Ω E]
    [Algebra E R] [Algebra Ω R] [IsScalarTower Ω E R]
    (G P : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hGP : ¬ G ∣ P)
    (y : Fin 3 → R) (hGy : aeval y G = 0) (hPy : aeval y P = 0)
    (i : Fin 3) (c : Fin 3 → Ω) (hci : c i = 1) (t : E) (ht : Transcendental Ω t)
    (hℓ : ∑ m, algebraMap Ω R (c m) * y m = algebraMap E R t) :
    ∀ m, IsAlgebraic E (y m) := by
  classical
  let f : Fin 3 → MvPolynomial (Fin 3) Ω := fun m =>
    if m = i then X i - ∑ m' ∈ Finset.univ.erase i, C (c m') * X m' else X m
  let g : Fin 3 → MvPolynomial (Fin 3) Ω := fun m =>
    if m = i then ∑ m', C (c m') * X m' else X m
  have herase : ∀ T : MvPolynomial (Fin 3) Ω,
      ∑ m' ∈ Finset.univ.erase i, C (c m') * (if m' = i then T else X m') =
        ∑ m' ∈ Finset.univ.erase i, C (c m') * X m' := fun T =>
    Finset.sum_congr rfl (fun m' hm' => by rw [if_neg (Finset.ne_of_mem_erase hm')])
  have hsplit : ∑ m', C (c m') * (X m' : MvPolynomial (Fin 3) Ω) =
      X i + ∑ m' ∈ Finset.univ.erase i, C (c m') * X m' := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hci, map_one, one_mul]
  have hgf : ∀ m, bind₁ g (f m) = X m := by
    intro m
    by_cases hm : m = i
    · subst hm
      simp only [f, g, if_true, map_sub, map_sum, map_mul, bind₁_X_right, bind₁_C_right]
      rw [herase, hsplit]
      ring
    · simp [f, g, hm]
  have hfg : ∀ m, bind₁ f (g m) = X m := by
    intro m
    by_cases hm : m = i
    · subst hm
      simp only [f, g, if_true, map_sum, map_mul, bind₁_X_right, bind₁_C_right]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), hci, map_one, one_mul, if_pos rfl,
        herase]
      ring
    · simp [f, g, hm]
  let τ : MvPolynomial (Fin 3) Ω ≃ₐ[Ω] MvPolynomial (Fin 3) Ω :=
    AlgEquiv.ofAlgHom (bind₁ f) (bind₁ g)
      (MvPolynomial.algHom_ext fun m => by simp [hfg])
      (MvPolynomial.algHom_ext fun m => by simp [hgf])
  let z : Fin 3 → R := fun m => if m = i then algebraMap E R t else y m
  have hz : ∀ m, aeval z (f m) = y m := by
    intro m
    by_cases hm : m = i
    · subst hm
      simp only [f, z, if_true, map_sub, map_sum, map_mul, aeval_X, aeval_C]
      rw [Finset.sum_congr rfl (fun m' hm' => by rw [if_neg (Finset.ne_of_mem_erase hm')]),
        ← hℓ, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), hci, map_one, one_mul]
      ring
    · simp [f, z, hm]
  have hτ : ∀ p, aeval z (τ p) = aeval y p := by
    intro p
    change aeval z (bind₁ f p) = aeval y p
    rw [aeval_bind₁, show (fun m => aeval z (f m)) = y from funext hz]
  have hG' : Irreducible (τ G) := (MulEquiv.irreducible_iff τ).mpr hG
  have hGP' : ¬ τ G ∣ τ P := by
    rintro ⟨d, hd⟩
    exact hGP ⟨τ.symm d, by apply τ.injective; rw [map_mul, AlgEquiv.apply_symm_apply, hd]⟩
  have hother : ∀ m, m ≠ i → IsAlgebraic E (y m) := by
    intro m hm
    obtain ⟨Q, hQ, hQz⟩ := exists_eliminant (τ G) (τ P) hG' hGP' z
      (by rw [hτ, hGy]) (by rw [hτ, hPy]) m i hm
    have hzz : ![z m, z i] = ![y m, algebraMap E R t] := by simp [z, hm]
    rw [hzz] at hQz
    exact isAlgebraic_of_eliminant t ht (y m) Q hQ hQz
  intro m
  by_cases hm : m = i
  · subst hm
    have hy : y m = algebraMap E R t -
        ∑ m' ∈ Finset.univ.erase m, algebraMap Ω R (c m') * y m' := by
      rw [← hℓ, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), hci, map_one, one_mul]
      ring
    rw [isAlgebraic_iff_isIntegral, hy]
    refine (integralClosure E R).sub_mem (IsIntegral.algebraMap isIntegral_algebraMap)
      ((integralClosure E R).sum_mem fun m' hm' => ?_)
    refine (integralClosure E R).mul_mem ?_ ?_
    · rw [IsScalarTower.algebraMap_apply Ω E R]
      exact IsIntegral.algebraMap isIntegral_algebraMap
    · exact isAlgebraic_iff_isIntegral.mp (hother m' (Finset.ne_of_mem_erase hm'))
  · exact hother m hm

end ProximityPrize.SubmissionLower.HFree6812


