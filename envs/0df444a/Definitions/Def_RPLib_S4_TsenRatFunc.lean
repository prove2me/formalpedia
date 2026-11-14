-- Prove2me | Definitions.Def_RPLib_S4_TsenRatFunc
-- name    : RPLib_S4_TsenRatFunc
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T01:29:18.944603+00:00
-- url     : https://prove2.me/theorems/8bd3ff76-e25f-4388-9654-363501a4f8ab
-- title:
--   Tsen's theorem, part 2: the rational function field $k(t)$ over an algebraically closed $k$ is $C_1$
-- statement:
--   For $k$ algebraically closed, a polynomial over $k[t]$ in $n$ variables of total degree $< n$ without constant term has a nonzero zero in $k[t]^n$ (substitute polynomials of large degree $N$ in $t$ and count unknown coefficients against equations), and after clearing denominators the field $k(t)$ (`RatFunc k`) is $C_1$. Here a field $K$ is called $C_1$ (in the strong sense) if every polynomial $f \in K[x_1,\dots,x_n]$ of total degree $< n$ with $f(0) = 0$ has a zero $x \ne 0$ in $K^n$ (`RamanujanPetersson.Tsen.IsC1`); for forms this is the classical $C_1$ property (`IsC1.exists_zero_of_isHomogeneous`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (field-theory layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   C. Tsen, Divisionsalgebren ueber Funktionenkoerpern, Nachr. Ges. Wiss. Goettingen, Math.-Phys. Kl. (1933), 335-339; S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785; M. J. Greenberg, Lectures on Forms in Many Variables, Benjamin 1969, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S4_TsenZero

set_option autoImplicit false

/-!
# S4-PD (1), T2: Tsen's theorem for `k(t)`

* `exists_zero_polynomial`: `k` algebraically closed, `F ∈ k[t][x₀,…,x_{n-1}]` with total degree `< n` and no constant
  term has a nonzero zero in `k[t]ⁿ` (substitute `xᵢ = ∑_{j ≤ N} a_{ij} tʲ`, count unknowns against the coefficients of
  the powers of `t`, and apply `exists_common_zero`).
* `exists_clear_denom`: common denominators for a multivariate polynomial over a fraction field.
* `isC1_ratFunc`: `RatFunc k` is `C₁` (strong form `IsC1`).
-/

namespace RamanujanPetersson.Tsen

open Polynomial

section Core

variable {k : Type*} [Field k]

/-- The generic substitution `xᵢ = ∑_{j ≤ N} a_{(i,j)} tʲ`, with the `a`'s as variables. -/
noncomputable def subVar (n N : ℕ) (i : Fin n) : (MvPolynomial (Fin (n * (N + 1))) k)[X] :=
  ∑ j : Fin (N + 1), C (MvPolynomial.X (finProdFinEquiv (i, j))) * X ^ (j : ℕ)

/-- `F` after the generic substitution, a polynomial in `t` over the polynomial ring of the unknowns. -/
noncomputable def subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X]) :
    (MvPolynomial (Fin (n * (N + 1))) k)[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C) (subVar n N) F

/-- The substitution at a point `a` of the unknowns. -/
noncomputable def specVar (n N : ℕ) (a : Fin (n * (N + 1)) → k) (i : Fin n) : k[X] :=
  ∑ j : Fin (N + 1), C (a (finProdFinEquiv (i, j))) * X ^ (j : ℕ)

theorem map_subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X]) (a : Fin (n * (N + 1)) → k) :
    (subPoly n N F).map (MvPolynomial.eval a) = MvPolynomial.eval (specVar n N a) F := by
  unfold subPoly
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  have h1 : (Polynomial.mapRingHom (MvPolynomial.eval a)).comp
      (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k))) = RingHom.id k[X] := by
    rw [Polynomial.mapRingHom_comp]
    have : (MvPolynomial.eval a).comp (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k)) = RingHom.id k := by
      ext c; simp
    rw [this, Polynomial.mapRingHom_id]
  have h2 : (Polynomial.mapRingHom (MvPolynomial.eval a)) ∘ subVar n N = specVar n N a := by
    funext i
    simp [subVar, specVar, Polynomial.map_sum]
  rw [h1, h2]
  rfl

theorem coeff_specVar (n N : ℕ) (a : Fin (n * (N + 1)) → k) (i : Fin n) (j : Fin (N + 1)) :
    (specVar n N a i).coeff j = a (finProdFinEquiv (i, j)) := by
  simp only [specVar, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (Fin.ext h.symm)
  · simp

theorem natDegree_subVar_le (n N : ℕ) (i : Fin n) : (subVar (k := k) n N i).natDegree ≤ N := by
  unfold subVar
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.isLt)

theorem natDegree_subPoly_le (n N c : ℕ) (F : MvPolynomial (Fin n) k[X])
    (hc : ∀ m, (F.coeff m).natDegree ≤ c) :
    (subPoly n N F).natDegree ≤ N * F.totalDegree + c := by
  unfold subPoly
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 : (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k))
      (F.coeff m)).natDegree ≤ c := Polynomial.natDegree_map_le.trans (hc m)
  have hsum : ∑ i, m i ≤ F.totalDegree := by
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this
  have h2 : (∏ i, subVar (k := k) n N i ^ m i).natDegree ≤ N * F.totalDegree := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (subVar (k := k) n N i ^ m i).natDegree ≤ ∑ i, m i * N :=
          Finset.sum_le_sum fun i _ =>
            Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_subVar_le n N i))
      _ = N * ∑ i, m i := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ N * F.totalDegree := Nat.mul_le_mul_left _ hsum
  omega

theorem constantCoeff_coeff_subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X])
    (hF : MvPolynomial.constantCoeff F = 0) (m : ℕ) :
    MvPolynomial.constantCoeff ((subPoly n N F).coeff m) = 0 := by
  have h := congrArg (fun p => Polynomial.coeff p m) (map_subPoly n N F 0)
  simp only [Polynomial.coeff_map] at h
  have h0 : specVar n N (0 : Fin (n * (N + 1)) → k) = 0 := by
    funext i; simp [specVar]
  rw [h0, MvPolynomial.eval_zero, MvPolynomial.eval_zero] at h
  rw [h]
  simp [hF]

/-- **Core of Tsen's theorem.** Over `k[t]`, `k` algebraically closed: a polynomial in `n` variables of total degree
`< n` without constant term has a nonzero zero in `k[t]ⁿ`. -/
theorem exists_zero_polynomial [IsAlgClosed k] {n : ℕ} (F : MvPolynomial (Fin n) k[X])
    (hdeg : F.totalDegree < n) (hF : MvPolynomial.constantCoeff F = 0) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ MvPolynomial.eval x F = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ∀ m, (F.coeff m).natDegree ≤ c :=
    ⟨F.support.sup fun m => (F.coeff m).natDegree, fun m => by
      by_cases hm : m ∈ F.support
      · exact Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
      · rw [MvPolynomial.notMem_support_iff.mp hm]; simp⟩
  have hcount : (c + 1) * F.totalDegree + c + 1 < n * (c + 1 + 1) := by
    have h1 : (F.totalDegree + 1) * (c + 2) ≤ n * (c + 2) := Nat.mul_le_mul_right _ hdeg
    nlinarith [h1]
  let P : Fin ((c + 1) * F.totalDegree + c + 1) → MvPolynomial (Fin (n * (c + 1 + 1))) k :=
    fun m => (subPoly n (c + 1) F).coeff m
  obtain ⟨a, ha, haP⟩ := exists_common_zero hcount P
    (fun m => constantCoeff_coeff_subPoly n (c + 1) F hF m)
  refine ⟨specVar n (c + 1) a, ?_, ?_⟩
  · intro h0
    apply ha
    funext p
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    have := congrArg (fun q => Polynomial.coeff q j) (congrFun h0 i)
    simpa [coeff_specVar] using this
  · ext m
    rw [← map_subPoly, Polynomial.coeff_map]
    by_cases hm : m < (c + 1) * F.totalDegree + c + 1
    · simpa [P] using haP ⟨m, hm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_subPoly_le n (c + 1) c F hc).trans_lt (by omega))]
      simp

end Core

/-- Common denominators: a multivariate polynomial over a fraction field becomes integral after multiplying by one
nonzero element. -/
theorem exists_clear_denom {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {σ : Type*} (f : MvPolynomial σ K) :
    ∃ (b : A) (F : MvPolynomial σ A), b ≠ 0 ∧
      ∀ m, algebraMap A K (F.coeff m) = algebraMap A K b * f.coeff m := by
  classical
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (f.support.image fun m => f.coeff m)
  have hall : ∀ m, ∃ r : A, algebraMap A K r = b • f.coeff m := by
    intro m
    by_cases hm : m ∈ f.support
    · exact RingHom.mem_rangeS.mp (hint _ (Finset.mem_image_of_mem _ hm))
    · exact ⟨0, by rw [MvPolynomial.notMem_support_iff.mp hm, smul_zero, map_zero]⟩
  choose r hr using hall
  refine ⟨b, ∑ m' ∈ f.support, MvPolynomial.monomial m' (r m'), nonZeroDivisors.ne_zero hb, ?_⟩
  intro m
  have hc : (∑ m' ∈ f.support, MvPolynomial.monomial m' (r m')).coeff m =
      if m ∈ f.support then r m else 0 := by
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial]
  rw [hc]
  split_ifs with hm
  · exact (hr m).trans (Algebra.smul_def _ _)
  · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero, map_zero]

/-- **Tsen's theorem for `k(t)`** (strong `C₁` form). -/
theorem isC1_ratFunc (k : Type*) [Field k] [IsAlgClosed k] : IsC1 (RatFunc k) := by
  intro n f hdeg hconst
  obtain ⟨b, F, hb, hF⟩ := exists_clear_denom (A := k[X]) f
  have hinj := IsFractionRing.injective k[X] (RatFunc k)
  have hsupp : F.support ⊆ f.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    apply hm
    apply hinj
    rw [hF, h0, mul_zero, map_zero]
  have hdegF : F.totalDegree < n := by
    refine lt_of_le_of_lt ?_ hdeg
    unfold MvPolynomial.totalDegree
    exact Finset.sup_mono hsupp
  have hconstF : MvPolynomial.constantCoeff F = 0 := by
    apply hinj
    have e1 : MvPolynomial.constantCoeff F = F.coeff 0 := congrFun MvPolynomial.constantCoeff_eq F
    have e2 : MvPolynomial.constantCoeff f = f.coeff 0 := congrFun MvPolynomial.constantCoeff_eq f
    rw [e1, hF, ← e2, hconst, mul_zero, map_zero]
  obtain ⟨x, hx0, hx⟩ := exists_zero_polynomial F hdegF hconstF
  refine ⟨fun i => algebraMap k[X] (RatFunc k) (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    apply hinj
    simpa using congrFun h i
  · have hmap : MvPolynomial.map (algebraMap k[X] (RatFunc k)) F =
        MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f := by
      ext m
      rw [MvPolynomial.coeff_map, hF, MvPolynomial.coeff_C_mul]
    have h1 : MvPolynomial.eval (fun i => algebraMap k[X] (RatFunc k) (x i))
        (MvPolynomial.map (algebraMap k[X] (RatFunc k)) F) =
        algebraMap k[X] (RatFunc k) (MvPolynomial.eval x F) := by
      rw [MvPolynomial.eval_map]
      have := MvPolynomial.eval₂_comp_left (algebraMap k[X] (RatFunc k)) (RingHom.id _) x F
      rw [RingHom.comp_id] at this
      exact this.symm
    rw [hmap, hx, map_zero, map_mul, MvPolynomial.eval_C] at h1
    exact (mul_eq_zero.mp h1).resolve_left (fun h => hb (hinj (h.trans (map_zero _).symm)))

end RamanujanPetersson.Tsen


