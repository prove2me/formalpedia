-- Prove2me | Definitions.Def_RPLib_S4_TsenNorm
-- name    : RPLib_S4_TsenNorm
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T01:29:15.834714+00:00
-- url     : https://prove2.me/theorems/9abcc20b-3727-4772-8b4f-96f4f35a872d
-- title:
--   Tsen's theorem, part 3: finite extensions of $C_1$ fields are $C_1$ (norm forms)
-- statement:
--   For a finite extension $L/K$ with a basis $b_1,\dots,b_e$ and $f \in L[x_1,\dots,x_n]$ there is $P \in K[y_{ij}]$ of total degree $\le e \deg f$ with $P(y) = N_{L/K}(f(\sum_j y_{ij} b_j))$; consequently a finite extension of a $C_1$ field is $C_1$ (Lang). Here a field $K$ is called $C_1$ (in the strong sense) if every polynomial $f \in K[x_1,\dots,x_n]$ of total degree $< n$ with $f(0) = 0$ has a zero $x \ne 0$ in $K^n$ (`RamanujanPetersson.Tsen.IsC1`); for forms this is the classical $C_1$ property (`IsC1.exists_zero_of_isHomogeneous`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (field-theory layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785; J.-P. Serre, Galois Cohomology, Springer 1997, doi:10.1007/978-3-642-59141-9, Chapter II, Section 3

import Mathlib
import Definitions.Def_RPLib_S4_TsenZero

set_option autoImplicit false

/-!
# S4-PD (1), T3: finite extensions of `C₁` fields are `C₁` (the norm form)

* `coeffMap g z`: apply a `K`-linear functional `g : L → K` to every coefficient of `z`; it commutes with evaluation at
  `K`-points (`eval_coeffMap`) and does not raise the total degree.
* `totalDegree_bind₁_le`, `totalDegree_det_le`: degree bounds for linear substitution and determinants.
* `exists_normForm`: for `L/K` with basis `b` (`e` elements) and `f ∈ L[x₀,…,x_{n-1}]` there is
  `P ∈ K[y_{(i,j)}]` with `totalDegree P ≤ e * totalDegree f` and `P(y) = N_{L/K}(f(∑ⱼ y_{(i,j)} bⱼ))`.
* `IsC1.of_finite`: `L/K` finite and `K` is `C₁` imply `L` is `C₁`.
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section CoeffMap

variable {σ K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply a `K`-linear functional to every coefficient. -/
noncomputable def coeffMap (g : L →ₗ[K] K) (z : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ d ∈ z.support, monomial d (g (z.coeff d))

theorem totalDegree_coeffMap_le (g : L →ₗ[K] K) (z : MvPolynomial σ L) :
    (coeffMap g z).totalDegree ≤ z.totalDegree :=
  totalDegree_finsetSum_le fun _ hd => (totalDegree_monomial_le _ _).trans (le_totalDegree hd)

theorem eval_coeffMap (g : L →ₗ[K] K) (z : MvPolynomial σ L) (y : σ → K) :
    eval y (coeffMap g z) = g (eval (fun i => algebraMap K L (y i)) z) := by
  have hp : ∀ d : σ →₀ ℕ, ∏ i ∈ d.support, (algebraMap K L (y i)) ^ d i =
      algebraMap K L (∏ i ∈ d.support, y i ^ d i) := by
    intro d; rw [map_prod]; simp [map_pow]
  rw [coeffMap, map_sum, MvPolynomial.eval_eq (fun i => algebraMap K L (y i)) z, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.eval_monomial, hp d, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul,
    mul_comm]
  rfl

end CoeffMap

theorem totalDegree_bind₁_le {σ τ R : Type*} [CommRing R] (g : σ → MvPolynomial τ R) (f : MvPolynomial σ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) : (bind₁ g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = d i := mul_one _

theorem totalDegree_det_le {σ R : Type*} [CommRing R] {e : ℕ} (M : Matrix (Fin e) (Fin e) (MvPolynomial σ R))
    (D : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ D) : M.det.totalDegree ≤ e * D := by
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro τ _
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R), totalDegree_C]
  rw [h1, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (τ i) i).totalDegree ≤ ∑ _i : Fin e, D := Finset.sum_le_sum fun i _ => hM _ _
    _ = e * D := by simp

section NormForm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- **The norm form.** `P(y) = N_{L/K}(f(∑ⱼ y_{(i,j)} bⱼ))` is a polynomial of degree `≤ e · deg f` over `K`. -/
theorem exists_normForm {e : ℕ} (b : Module.Basis (Fin e) K L) {n : ℕ} (f : MvPolynomial (Fin n) L) :
    ∃ P : MvPolynomial (Fin (n * e)) K, P.totalDegree ≤ e * f.totalDegree ∧
      ∀ y : Fin (n * e) → K,
        eval y P = Algebra.norm K (eval (fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j) f) := by
  classical
  let g : Fin n → MvPolynomial (Fin (n * e)) L :=
    fun i => ∑ j : Fin e, C (b j) * X (finProdFinEquiv (i, j))
  have hg : ∀ i, (g i).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  let z := bind₁ g f
  have hz : ∀ y : Fin (n * e) → K, eval (fun p => algebraMap K L (y p)) z =
      eval (fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j) f := by
    intro y
    refine (eval₂Hom_bind₁ (RingHom.id L) (fun p => algebraMap K L (y p)) g f).trans ?_
    show eval _ f = eval _ f
    refine congrArg (fun x : Fin n → L => eval x f) (funext fun i => ?_)
    show eval _ (g i) = _
    simp only [g, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  let M : Matrix (Fin e) (Fin e) (MvPolynomial (Fin (n * e)) K) :=
    fun i j => coeffMap ((b.coord i).comp (LinearMap.mulRight K (b j))) z
  refine ⟨M.det, ?_, ?_⟩
  · refine (totalDegree_det_le M z.totalDegree fun i j => totalDegree_coeffMap_le _ _).trans ?_
    exact Nat.mul_le_mul_left _ (totalDegree_bind₁_le g f hg)
  · intro y
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    show eval y (coeffMap _ z) = _
    rw [eval_coeffMap, hz]
    rfl

/-- **Lang.** A finite extension of a `C₁` field is `C₁`. -/
theorem IsC1.of_finite (hK : IsC1 K) : IsC1 L := by
  classical
  intro n f hdeg hconst
  obtain ⟨e, b, hepos⟩ : ∃ e, ∃ _ : Module.Basis (Fin e) K L, 0 < e :=
    ⟨_, Module.finBasis K L, Module.finrank_pos⟩
  obtain ⟨P, hPdeg, hP⟩ := exists_normForm b f
  have hdegP : P.totalDegree < n * e :=
    lt_of_le_of_lt hPdeg (by rw [mul_comm n e]; exact Nat.mul_lt_mul_of_pos_left hdeg hepos)
  have hconstP : constantCoeff P = 0 := by
    rw [← MvPolynomial.eval_zero, hP]
    simp [MvPolynomial.eval_zero', hconst]
  obtain ⟨y, hy0, hy⟩ := hK (n * e) P hdegP hconstP
  rw [hP, Algebra.norm_eq_zero_iff] at hy
  refine ⟨fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j, ?_, hy⟩
  intro hx
  apply hy0
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent _ (congrFun hx i) j

end NormForm

end RamanujanPetersson.Tsen


