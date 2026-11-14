-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCRep
-- name    : RPLib_S4_AlgGrpCRep
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:02:01.086453+00:00
-- url     : https://prove2.me/theorems/e79b6b60-d96f-49f0-befa-2ec0676e0b66
-- title:
--   Larsen's alternative library: replicas of a diagonal semisimple part (char 0)
-- statement:
--   `Td Z d` is `derD Z` restricted to the finite-dimensional `Ad d`. For `X = diagonal lam + N` with
--   `N` nilpotent commuting with `diagonal lam`, `Td (diagonal lam)` is semisimple, `Td N` nilpotent, so
--   by uniqueness of the Jordan-Chevalley decomposition `Td (diagonal lam) ∈ K[Td X]`; Lagrange
--   interpolation of an additive `ψ` on the finitely many weights gives `Td (diagonal (ψ ∘ lam))` as a
--   polynomial in `Td (diagonal lam)`. Hence (`diag_replica_mem_lieS`): if `X ∈ Lie H` then
--   `diagonal (ψ ∘ lam) ∈ Lie H`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCWt

/-!
# S4-AlgGrpC, file Rep: replicas of a diagonal semisimple part (char 0)

`Td Z d` is `derD Z` restricted to the finite-dimensional `Ad d`. For `X = diagonal lam + N` with
`N` nilpotent commuting with `diagonal lam`, `Td (diagonal lam)` is semisimple, `Td N` nilpotent, so
by uniqueness of the Jordan-Chevalley decomposition `Td (diagonal lam) ∈ K[Td X]`; Lagrange
interpolation of an additive `ψ` on the finitely many weights gives `Td (diagonal (ψ ∘ lam))` as a
polynomial in `Td (diagonal lam)`. Hence (`diag_replica_mem_lieS`): if `X ∈ Lie H` then
`diagonal (ψ ∘ lam) ∈ Lie H`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

theorem dN_add (A B : Matrix n n K) (v : Var n) : dN (A + B) v = dN A v + dN B v := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp [dN, Finset.sum_add_distrib, mul_add]
  · simp [dN, Finset.sum_add_distrib, add_mul]
    exact add_comm _ _

theorem derD_add (A B : Matrix n n K) : derD (A + B) = derD A + derD B :=
  MvPolynomial.derivation_ext fun v => by rw [Derivation.add_apply, derD_X, derD_X, derD_X, dN_add]

/-- `derD Z` restricted to `Ad d`. -/
def Td (Z : Matrix n n K) (d : ℕ) : Module.End K (Ad (n := n) (K := K) d) :=
  (derD Z).toLinearMap.restrict fun _ hp => derD_mem_Ad Z hp

theorem Td_apply (Z : Matrix n n K) (d : ℕ) (x : Ad (n := n) (K := K) d) :
    (Td Z d x : MvPolynomial (Var n) K) = derD Z x := rfl

theorem Td_add (A B : Matrix n n K) (d : ℕ) : Td (A + B) d = Td A d + Td B d :=
  LinearMap.ext fun x => Subtype.ext (by
    rw [LinearMap.add_apply, Submodule.coe_add, Td_apply, Td_apply, Td_apply, derD_add,
      Derivation.add_apply])

theorem Td_commute {A B : Matrix n n K} (h : Commute A B) (d : ℕ) : Commute (Td A d) (Td B d) :=
  LinearMap.ext fun x => Subtype.ext (by
    rw [Module.End.mul_apply, Module.End.mul_apply, Td_apply, Td_apply, Td_apply, Td_apply,
      derD_apply, derD_apply, derD_apply, derD_apply]
    exact derN_comm_of_commute h x)

theorem Td_pow_apply (Z : Matrix n n K) (d k : ℕ) (x : Ad (n := n) (K := K) d) :
    (((Td Z d) ^ k) x : MvPolynomial (Var n) K) = (derD Z)^[k] x := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply, Function.iterate_zero_apply]
  | succ k ih => rw [pow_succ', Module.End.mul_apply, Td_apply, ih, Function.iterate_succ_apply']

/-- Linear coordinates `x ↦ x A`, `y ↦ B y`. -/
def linP (A B : Matrix n n K) : Var n → MvPolynomial (Var n) K :=
  Sum.elim (fun ij => ∑ k, X (Sum.inl (ij.1, k)) * C (A k ij.2))
    (fun ij => ∑ k, C (B ij.1 k) * X (Sum.inr (k, ij.2)))

theorem derD_linP (N A B : Matrix n n K) (v : Var n) :
    derD N (linP A B v) = linP (N * A) (B * -N) v := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [linP, Sum.elim_inl, map_sum, Derivation.leibniz, derD_X, smul_eq_mul]
    simp only [MvPolynomial.derivation_C, mul_zero, zero_add, dN, Sum.elim_inl,
      Matrix.mul_apply, map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul]
    ring
  · simp only [linP, Sum.elim_inr, map_sum, Derivation.leibniz, derD_X, smul_eq_mul]
    simp only [MvPolynomial.derivation_C, mul_zero, add_zero, dN, Sum.elim_inr, Finset.mul_sum,
      Matrix.mul_apply, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul]
    ring

theorem linP_one (v : Var n) : linP (1 : Matrix n n K) 1 v = X v := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [linP, Sum.elim_inl]
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, C_0, mul_zero])
      (by simp), Matrix.one_apply_eq, C_1, mul_one]
  · simp only [linP, Sum.elim_inr]
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Matrix.one_apply_ne hk.symm, C_0, zero_mul])
      (by simp), Matrix.one_apply_eq, C_1, one_mul]

theorem derD_iterate_X (N : Matrix n n K) (k : ℕ) (v : Var n) :
    (derD N)^[k] (X v) = linP (N ^ k) ((-N) ^ k) v := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, pow_zero, pow_zero, linP_one]
  | succ k ih => rw [Function.iterate_succ_apply', ih, derD_linP, ← pow_succ', ← pow_succ]

theorem Td_isNilpotent {N : Matrix n n K} {m : ℕ} (hN : N ^ m = 0) (d : ℕ) :
    IsNilpotent (Td N d) := by
  have hX : ∀ v, (derD N)^[m + 1] (X v) = 0 := fun v => by
    refine iterate_eq_zero_of_le _ (Nat.le_succ m) ?_
    rw [derD_iterate_X, hN, neg_pow, hN, mul_zero]
    rcases v with ⟨i, j⟩ | ⟨i, j⟩ <;> simp [linP]
  refine ⟨m * d + 1, Ad_ext fun e he => Subtype.ext ?_⟩
  rw [Td_pow_apply, LinearMap.zero_apply, Submodule.coe_zero]
  have hd : e.degree ≤ d := he
  exact iterate_eq_zero_of_le _ (by nlinarith) (iterate_monomial_eq_zero _ m hX e)

theorem Td_diag_mono (lam : n → K) {d : ℕ} {e : Var n →₀ ℕ} (he : e ∈ expS d) :
    Td (Matrix.diagonal lam) d ⟨monomial e 1, monomial_mem_Ad he 1⟩ =
      wt (wtv lam) e • (⟨monomial e 1, monomial_mem_Ad he 1⟩ : Ad (K := K) d) :=
  Subtype.ext (by rw [Td_apply, derD_diag_monomial]; rfl)

theorem aeval_Td_diag (lam : n → K) (d : ℕ) (p : Polynomial K) {e : Var n →₀ ℕ} (he : e ∈ expS d) :
    Polynomial.aeval (Td (Matrix.diagonal lam) d) p ⟨monomial e 1, monomial_mem_Ad he 1⟩ =
      p.eval (wt (wtv lam) e) • (⟨monomial e 1, monomial_mem_Ad he 1⟩ : Ad (K := K) d) :=
  Module.End.aeval_apply_of_hasEigenvector (Module.End.hasEigenvector_iff.2
    ⟨Module.End.mem_eigenspace_iff.2 (Td_diag_mono lam he),
      fun h => one_ne_zero (monomial_eq_zero.1 (congrArg Subtype.val h))⟩)

open Classical in
/-- The finitely many weights on `Ad d`. -/
def wtSet (lam : n → K) (d : ℕ) : Finset K := (expS_finite (n := n) d).toFinset.image (wt (wtv lam))

theorem wt_mem_wtSet (lam : n → K) {d : ℕ} {e : Var n →₀ ℕ} (he : e ∈ expS d) :
    wt (wtv lam) e ∈ wtSet lam d := by
  classical
  rw [wtSet, Finset.mem_image]
  exact ⟨e, (Set.Finite.mem_toFinset _).2 he, rfl⟩

theorem Td_diag_isSemisimple (lam : n → K) (d : ℕ) : (Td (Matrix.diagonal lam) d).IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := ∏ m ∈ wtSet lam d, (Polynomial.X - Polynomial.C m)) ?_ ?_
  · exact (Polynomial.separable_prod_X_sub_C_iff'.2 fun x _ y _ h => h).squarefree
  · refine Ad_ext fun e he => ?_
    rw [aeval_Td_diag lam d _ he, LinearMap.zero_apply, Polynomial.eval_prod,
      Finset.prod_eq_zero (wt_mem_wtSet lam he) (by simp), zero_smul]

theorem Td_diag_mem_adjoin [CharZero K] (lam : n → K) {N : Matrix n n K} (hN : IsNilpotent N)
    (hc : Commute (Matrix.diagonal lam) N) (d : ℕ) :
    Td (Matrix.diagonal lam) d ∈ Algebra.adjoin K {Td (Matrix.diagonal lam + N) d} := by
  obtain ⟨n₀, hn₀a, s₀, hs₀a, hn₀, hs₀, h₀⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := Td (Matrix.diagonal lam + N) d)
  obtain ⟨m, hm⟩ := hN
  have h1 : Commute (Td (Matrix.diagonal lam + N) d) s₀ :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs₀a (Commute.refl _)
  have h2 : Commute s₀ n₀ := Algebra.commute_of_mem_adjoin_singleton_of_commute hn₀a h1.symm
  have h := Module.End.isNilpotent_isSemisimple_unique (Td_isNilpotent hm d)
    (Td_diag_isSemisimple lam d) hn₀ hs₀ (Td_commute hc.symm d) h2.symm
    (by rw [← h₀, Td_add, add_comm])
  rw [h.2]
  exact hs₀a

theorem Td_replica_mem_adjoin (lam : n → K) (ψ : K →+ K) (d : ℕ) :
    Td (Matrix.diagonal fun j => ψ (lam j)) d ∈ Algebra.adjoin K {Td (Matrix.diagonal lam) d} := by
  classical
  have : Polynomial.aeval (Td (Matrix.diagonal lam) d)
      (Lagrange.interpolate (wtSet lam d) id (fun m => ψ m)) =
      Td (Matrix.diagonal fun j => ψ (lam j)) d := by
    refine Ad_ext fun e he => ?_
    rw [aeval_Td_diag lam d _ he, Td_diag_mono _ he, ← id_eq (wt (wtv lam) e),
      Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) (wt_mem_wtSet lam he),
      show (wtv fun j => ψ (lam j)) = fun v => ψ (wtv lam v) from funext (wtv_comp lam ψ), wt_comp]
  rw [← this]
  exact Polynomial.aeval_mem_adjoin_singleton K _

theorem mapsTo_of_mem_adjoin {V : Type*} [AddCommGroup V] [Module K V] {T f : Module.End K V}
    {W : Submodule K V} (hT : ∀ x ∈ W, T x ∈ W) (hf : f ∈ Algebra.adjoin K {T}) :
    ∀ x ∈ W, f x ∈ W := by
  induction hf using Algebra.adjoin_induction with
  | mem g hg => rw [Set.mem_singleton_iff.1 hg]; exact hT
  | algebraMap a => intro x hx; rw [Module.algebraMap_end_apply]; exact W.smul_mem a hx
  | add f g _ _ hf hg => intro x hx; exact W.add_mem (hf x hx) (hg x hx)
  | mul f g _ _ hf hg => intro x hx; exact hf _ (hg x hx)

/-- **Replicas** (diagonal case). If `diagonal lam + N ∈ Lie H` with `N` nilpotent commuting with
`diagonal lam`, then `diagonal (ψ ∘ lam) ∈ Lie H` for every additive `ψ`. -/
theorem diag_replica_mem_lieS [CharZero K] {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (lam : n → K) {N : Matrix n n K} (hN : IsNilpotent N) (hc : Commute (Matrix.diagonal lam) N)
    (hX : Matrix.diagonal lam + N ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) (ψ : K →+ K) :
    Matrix.diagonal (fun j => ψ (lam j)) ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)) := by
  refine mem_lieS_of_derN fun f hf => ?_
  let W : Submodule K (Ad (n := n) (K := K) f.totalDegree) :=
    ((vanI (H : Set (Matrix.GeneralLinearGroup n K))).restrictScalars K).comap (Ad _).subtype
  have hT : ∀ x ∈ W, Td (Matrix.diagonal lam + N) f.totalDegree x ∈ W := fun x hx => by
    change derD _ (x : MvPolynomial (Var n) K) ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K))
    rw [derD_apply]
    exact derN_mem_vanI hX hx
  have hmem := Algebra.adjoin_singleton_le (Td_diag_mem_adjoin lam hN hc f.totalDegree)
    (Td_replica_mem_adjoin lam ψ f.totalDegree)
  have := mapsTo_of_mem_adjoin hT hmem ⟨f, mem_Ad_totalDegree f⟩ hf
  change derD _ f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K)) at this
  rwa [derD_apply] at this

end RamanujanPetersson.AlgGrpC


