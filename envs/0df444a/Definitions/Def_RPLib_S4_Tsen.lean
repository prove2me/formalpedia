-- Prove2me | Definitions.Def_RPLib_S4_Tsen
-- name    : RPLib_S4_Tsen
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T01:30:11.958196+00:00
-- url     : https://prove2.me/theorems/83263ecb-1400-49ec-b0e3-ca40329e36bc
-- title:
--   Tsen's theorem: algebraic extensions of $k(t)$, $k$ algebraically closed, are $C_1$; norms are surjective
-- statement:
--   Summary module: an algebraic extension of a $C_1$ field is $C_1$ (Lang); every algebraic extension of $k(t)$ with $k$ algebraically closed is $C_1$ (Tsen); over a $C_1$ field the norm map of every finite extension is surjective. Here a field $K$ is called $C_1$ (in the strong sense) if every polynomial $f \in K[x_1,\dots,x_n]$ of total degree $< n$ with $f(0) = 0$ has a zero $x \ne 0$ in $K^n$ (`RamanujanPetersson.Tsen.IsC1`); for forms this is the classical $C_1$ property (`IsC1.exists_zero_of_isHomogeneous`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (field-theory layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   C. Tsen, Divisionsalgebren ueber Funktionenkoerpern, Nachr. Ges. Wiss. Goettingen, Math.-Phys. Kl. (1933), 335-339; S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785; J.-P. Serre, Galois Cohomology, Springer 1997, doi:10.1007/978-3-642-59141-9, Chapter II, Section 3

import Mathlib
import Definitions.Def_RPLib_S4_TsenRatFunc
import Definitions.Def_RPLib_S4_TsenNorm

set_option autoImplicit false

/-!
# S4-PD (1): Tsen's theorem

* `IsC1.of_algebraic`: an algebraic extension of a `C₁` field is `C₁` (adjoin the coefficients, `IsC1.of_finite`).
* `tsen`: **Tsen's theorem.** Every algebraic extension of `k(t)`, `k` algebraically closed, is `C₁`
  (strong form `IsC1`: polynomials in `n` variables of total degree `< n` without constant term have a nonzero zero).
* `IsC1.norm_surjective`: over a `C₁` field the norm of every finite extension is surjective.
* `tsen_norm_surjective`: the norm of a finite extension of an algebraic extension of `k(t)` is surjective.
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

/-- An algebraic extension of a `C₁` field is `C₁`. -/
theorem IsC1.of_algebraic {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hK : IsC1 K) : IsC1 L := by
  classical
  intro n f hdeg hconst
  let F := IntermediateField.adjoin K (f.coeffs : Set L)
  have : Finite (f.coeffs : Set L) := (Finset.finite_toSet _).to_subtype
  have : FiniteDimensional K F := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hF : IsC1 F := IsC1.of_finite hK
  have hinj : Function.Injective (algebraMap F L) := (algebraMap F L).injective
  obtain ⟨f', hf'⟩ : f ∈ Set.range (MvPolynomial.map (algebraMap F L)) :=
    MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun c hc =>
      ⟨⟨c, IntermediateField.subset_adjoin K _ hc⟩, rfl⟩
  have hdeg' : f'.totalDegree < n := by
    have h1 : (MvPolynomial.map (algebraMap F L) f').totalDegree = f'.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [MvPolynomial.support_map_of_injective _ hinj]
    rw [← h1, hf']
    exact hdeg
  have hconst' : constantCoeff f' = 0 := by
    apply hinj
    rw [← MvPolynomial.constantCoeff_map, hf', hconst, map_zero]
  obtain ⟨x, hx0, hx⟩ := hF n f' hdeg' hconst'
  refine ⟨fun i => algebraMap F L (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact hinj ((congrFun h i).trans (map_zero _).symm)
  · rw [← hf', MvPolynomial.eval_map]
    have h2 := MvPolynomial.eval₂_comp_left (algebraMap F L) (RingHom.id _) x f'
    rw [RingHom.comp_id] at h2
    refine h2.symm.trans ?_
    rw [show MvPolynomial.eval₂ (RingHom.id F) x f' = eval x f' from rfl, hx, map_zero]

/-- **Tsen's theorem.** An algebraic extension of the rational function field `k(t)` over an algebraically closed
field `k` is `C₁`. -/
theorem tsen (k : Type*) [Field k] [IsAlgClosed k] (L : Type*) [Field L] [Algebra (RatFunc k) L]
    [Algebra.IsAlgebraic (RatFunc k) L] : IsC1 L :=
  (isC1_ratFunc k).of_algebraic

/-- Over a `C₁` field, the norm of a finite extension is surjective. -/
theorem IsC1.norm_surjective {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : IsC1 K) : Function.Surjective (Algebra.norm K : L → K) := by
  classical
  intro a
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, Algebra.norm_zero]⟩
  obtain ⟨e, b, hepos⟩ : ∃ e, ∃ _ : Module.Basis (Fin e) K L, 0 < e :=
    ⟨_, Module.finBasis K L, Module.finrank_pos⟩
  obtain ⟨P, hPdeg, hP⟩ := exists_normForm b (X 0 : MvPolynomial (Fin 1) L)
  rw [totalDegree_X, mul_one] at hPdeg
  let Q : MvPolynomial (Fin (1 * e + 1)) K :=
    rename Fin.castSucc P - C a * X (Fin.last (1 * e)) ^ e
  have hQdeg : Q.totalDegree < 1 * e + 1 := by
    show (rename Fin.castSucc P - C a * X (Fin.last (1 * e)) ^ e).totalDegree < 1 * e + 1
    have h1 : (rename Fin.castSucc P).totalDegree ≤ e := (totalDegree_rename_le _ _).trans hPdeg
    have h2 : (C a * X (Fin.last (1 * e)) ^ e : MvPolynomial (Fin (1 * e + 1)) K).totalDegree ≤ e := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_pow _ _).trans ?_
      rw [totalDegree_X, mul_one]
    have := (totalDegree_sub _ _).trans (max_le h1 h2)
    omega
  have hP0 : constantCoeff P = 0 := by
    rw [← MvPolynomial.eval_zero, hP]
    simp [Algebra.norm_zero]
  have hQconst : constantCoeff Q = 0 := by
    simp [Q, MvPolynomial.constantCoeff_rename, hP0, zero_pow hepos.ne']
  obtain ⟨w, hw0, hw⟩ := hK _ Q hQdeg hQconst
  set x : L := ∑ j, w (Fin.castSucc (finProdFinEquiv (0, j))) • b j with hx
  have hnorm : Algebra.norm K x = a * w (Fin.last _) ^ e := by
    have h3 : eval w Q = Algebra.norm K x - a * w (Fin.last _) ^ e := by
      simp only [Q, map_sub, map_mul, map_pow, eval_C, eval_X, MvPolynomial.eval_rename, hP]
      try rfl
    rw [h3] at hw
    exact sub_eq_zero.mp hw
  have ht : w (Fin.last _) ≠ 0 := by
    intro ht
    rw [ht, zero_pow hepos.ne', mul_zero, Algebra.norm_eq_zero_iff] at hnorm
    apply hw0
    funext p
    induction p using Fin.lastCases with
    | last => exact ht
    | cast q =>
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hnorm j
  refine ⟨x * algebraMap K L (w (Fin.last _))⁻¹, ?_⟩
  rw [map_mul, Algebra.norm_algebraMap, hnorm, Module.finrank_eq_card_basis b, Fintype.card_fin, inv_pow,
    mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]

/-- **Tsen, norm form.** For `L` algebraic over `k(t)` (`k` algebraically closed) and `L'/L` finite, the norm
`L' → L` is surjective. -/
theorem tsen_norm_surjective (k : Type*) [Field k] [IsAlgClosed k] (L : Type*) [Field L] [Algebra (RatFunc k) L]
    [Algebra.IsAlgebraic (RatFunc k) L] (L' : Type*) [Field L'] [Algebra L L'] [FiniteDimensional L L'] :
    Function.Surjective (Algebra.norm L : L' → L) :=
  (tsen k L).norm_surjective

end RamanujanPetersson.Tsen


