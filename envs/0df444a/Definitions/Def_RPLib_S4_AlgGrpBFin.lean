-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBFin
-- name    : RPLib_S4_AlgGrpBFin
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:38:14.862187+00:00
-- url     : https://prove2.me/theorems/281e018e-b2f8-45de-83ff-d1cd24530e8f
-- title:
--   Larsen's alternative library: `Lie H = 0` implies `H` finite)
-- statement:
--   Any field `K` (no characteristic assumption: `lieS` is the tangent space of the reduced closure).
--   Proof: if `Lie H = 0` the gradients at `1` of the equations of `H` span everything, so by the
--   first-order Taylor formula (`taylor1`) the maximal ideal `M` of `1` satisfies `M ≤ vanI H ⊔ M²`;
--   Nakayama gives `r` with `r(1) = 1` and `r M ⊆ vanI H`, so `{1}` is open in `H`, the identity
--   component of `H` is trivial and `H` is finite (`AlgGrpA.finite_iff_idCompGL_eq_bot`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBLie

/-!
# S4-AlgGrpB, file Fin: `Lie H = 0` implies `H` finite (spike API (A3))

Any field `K` (no characteristic assumption: `lieS` is the tangent space of the reduced closure).
Proof: if `Lie H = 0` the gradients at `1` of the equations of `H` span everything, so by the
first-order Taylor formula (`taylor1`) the maximal ideal `M` of `1` satisfies `M ≤ vanI H ⊔ M²`;
Nakayama gives `r` with `r(1) = 1` and `r M ⊆ vanI H`, so `{1}` is open in `H`, the identity
component of `H` is trivial and `H` is finite (`AlgGrpA.finite_iff_idCompGL_eq_bot`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

section Taylor

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K]

/-- First-order Taylor formula at `c`, modulo the square of the maximal ideal of `c`. -/
theorem taylor1 (c : σ → K) (g : MvPolynomial σ K) :
    g - C (eval c g) - ∑ v, C (eval c (pderiv v g)) * (X v - C (c v)) ∈
      (RingHom.ker (eval c)) ^ 2 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have : (p + q) - C (eval c (p + q)) - ∑ v, C (eval c (pderiv v (p + q))) * (X v - C (c v)) =
        (p - C (eval c p) - ∑ v, C (eval c (pderiv v p)) * (X v - C (c v))) +
          (q - C (eval c q) - ∑ v, C (eval c (pderiv v q)) * (X v - C (c v))) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [this]
    exact add_mem hp hq
  | mul_X p u hp =>
    set L := ∑ v, C (eval c (pderiv v p)) * (X v - C (c v)) with hLdef
    have key : ∀ v, C (eval c (pderiv v (p * X u))) * (X v - C (c v)) =
        (if v = u then C (eval c p) * (X u - C (c u)) else 0) +
          C (c u) * (C (eval c (pderiv v p)) * (X v - C (c v))) := by
      intro v
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : v = u
      · subst h
        simp
        ring
      · simp [h, Ne.symm h]
        ring
    have hsum : ∑ v, C (eval c (pderiv v (p * X u))) * (X v - C (c v)) =
        C (c u) * L + C (eval c p) * (X u - C (c u)) := by
      simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        ← Finset.mul_sum, hLdef]
      ring
    have hmem : X u - C (c u) ∈ RingHom.ker (eval c) := by simp [RingHom.mem_ker]
    have hL : L ∈ RingHom.ker (eval c) := by simp [hLdef, RingHom.mem_ker]
    have : p * X u - C (eval c (p * X u)) - ∑ v, C (eval c (pderiv v (p * X u))) * (X v - C (c v)) =
        (p - C (eval c p) - L) * X u + L * (X u - C (c u)) := by
      rw [hsum]
      simp only [eval_X, map_mul]
      ring
    rw [this]
    refine add_mem (Ideal.mul_mem_right _ _ hp) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hL hmem

end Taylor

section Fin

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The gradient at `c` as a `K`-linear map. -/
def gradL (c : Var n → K) : MvPolynomial (Var n) K →ₗ[K] (Var n → K) where
  toFun f v := eval c (pderiv v f)
  map_add' f g := by funext v; simp
  map_smul' a f := by funext v; simp [smul_eval]

/-- The equations `(g g⁻¹)_{ij} = δ_{ij}` of `GL_n`. -/
def invRel (i j : n) : MvPolynomial (Var n) K :=
  ∑ k, X (Sum.inl (i, k)) * X (Sum.inr (k, j)) - C ((1 : Matrix n n K) i j)

theorem invRel_mem_vanI (Z : Set (Matrix.GeneralLinearGroup n K)) (i j : n) :
    invRel i j ∈ vanI Z := by
  refine mem_vanI.2 fun g _ => ?_
  have h : ((g : Matrix n n K) * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) i j =
      (1 : Matrix n n K) i j := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [invRel, map_sub, map_sum, map_mul, eval_X, eval_C, crd_inl, crd_inr]
  rw [← Matrix.mul_apply, h, sub_self]

theorem dirDeriv_invRel (w : Var n → K) (i j : n) :
    dirDeriv (crd 1) w (invRel (K := K) i j) = w (Sum.inl (i, j)) + w (Sum.inr (i, j)) := by
  rw [← snd_aeval_dpt]
  simp [invRel, dpt, TrivSqZeroExt.snd_sum, Matrix.one_apply, Finset.sum_add_distrib,
    apply_ite TrivSqZeroExt.snd] ; ring

/-- `(A3)`: a subgroup of `GL_n(K)` with trivial Lie algebra is finite. -/
theorem finite_of_lieS_eq_bot (H : Subgroup (Matrix.GeneralLinearGroup n K))
    (hL : lieS (H : Set (Matrix.GeneralLinearGroup n K)) = ⊥) : Finite H := by
  classical
  set c : Var n → K := crd 1 with hc
  set J := vanI (H : Set (Matrix.GeneralLinearGroup n K)) with hJ
  set M := RingHom.ker (eval c) with hM
  -- Step 1: the gradients of `J` span everything.
  have hW : Submodule.map (gradL c) (J.restrictScalars K) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set w : Var n → K := fun v => φ fun u => if v = u then 1 else 0 with hw
    have hφw : ∀ f : MvPolynomial (Var n) K, φ (gradL c f) = dirDeriv c w f := by
      intro f
      rw [LinearMap.pi_apply_eq_sum_univ]
      simp [dirDeriv, gradL, hw, smul_eq_mul]
    have hJw : ∀ f ∈ J, dirDeriv c w f = 0 := by
      intro f hf
      rw [← hφw]
      exact hφ ⟨f, hf, rfl⟩
    set Y : Matrix n n K := Matrix.of fun i j => w (Sum.inl (i, j))
    have hYw : dvec Y = w := by
      funext v
      rcases v with ⟨i, j⟩ | ⟨i, j⟩
      · rfl
      · have := hJw _ (invRel_mem_vanI _ i j)
        rw [hc, dirDeriv_invRel] at this
        simp only [dvec_inr, Y, Matrix.of_apply]
        linear_combination -this
    have hY : Y ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)) := by
      intro f hf
      rw [hYw]
      exact hJw f hf
    rw [hL, Submodule.mem_bot] at hY
    have hw0 : w = 0 := by rw [← hYw, hY, dvec_zero]
    apply hφ0
    refine LinearMap.ext fun u => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ φ u]
    refine Finset.sum_eq_zero fun v _ => ?_
    have : φ (fun j => if v = j then 1 else 0) = 0 := congr_fun hw0 v
    rw [this, smul_zero]
  -- Step 2: `M ≤ J ⊔ M²`.
  have hvar : ∀ v, X v - C (c v) ∈ J ⊔ M ^ 2 := by
    intro v
    have hv : (fun u => if v = u then (1 : K) else 0) ∈
        Submodule.map (gradL c) (J.restrictScalars K) := by rw [hW]; trivial
    obtain ⟨f, hfJ, hfv⟩ := hv
    have hf1 : eval c f = 0 := mem_vanI.1 hfJ 1 H.one_mem
    have ht := taylor1 c f
    have hsum : ∑ u, C (eval c (pderiv u f)) * (X u - C (c u)) = X v - C (c v) := by
      have : ∀ u, eval c (pderiv u f) = if v = u then 1 else 0 := fun u => congr_fun hfv u
      simp [this]
    rw [hf1, hsum, map_zero, sub_zero] at ht
    have : X v - C (c v) = f - (f - (X v - C (c v))) := by ring
    rw [this]
    exact sub_mem (Ideal.mem_sup_left hfJ) (Ideal.mem_sup_right ht)
  have hMle : M ≤ J ⊔ M ^ 2 := by
    intro m hm
    have ht := taylor1 c m
    have hm0 : eval c m = 0 := hm
    rw [hm0, map_zero, sub_zero] at ht
    have : m = (m - ∑ v, C (eval c (pderiv v m)) * (X v - C (c v))) +
        ∑ v, C (eval c (pderiv v m)) * (X v - C (c v)) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_right ht)
      (Ideal.sum_mem _ fun v _ => Ideal.mul_mem_left _ _ (hvar v))
  -- Step 3: Nakayama in `P ⧸ J`.
  set N : Submodule (MvPolynomial (Var n) K) (MvPolynomial (Var n) K ⧸ J) :=
    Submodule.map J.mkQ M with hN
  have hNfg : N.FG := (IsNoetherian.noetherian M).map _
  have hNle : N ≤ M • N := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨j, hj, m', hm', rfl⟩ := Submodule.mem_sup.1 (hMle hm)
    have hj0 : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero _).2 hj
    rw [map_add, hj0, zero_add, hN, ← Submodule.map_smul'']
    refine ⟨m', ?_, rfl⟩
    rw [pow_two] at hm'
    exact hm'
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul M N hNfg hNle
  have hrM : ∀ m ∈ M, r * m ∈ J := by
    intro m hm
    have := hr _ ⟨m, hm, rfl⟩
    rw [← map_smul, smul_eq_mul] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  have hr1' : eval c r = 1 := by
    have : eval c (r - 1) = 0 := hr1
    rwa [map_sub, map_one, sub_eq_zero] at this
  -- Step 4: `{1}` is open in `H`, so the identity component is trivial.
  let _ := (zarTop : TopologicalSpace (Matrix.GeneralLinearGroup n K))
  set U : Set (Matrix.GeneralLinearGroup n K) := (zeroS {r})ᶜ with hU
  have hUo : IsOpen U := (isClosed_zeroS _).isOpen_compl
  have hHU : ∀ h ∈ (H : Set (Matrix.GeneralLinearGroup n K)), h ∈ U → h = 1 := by
    intro h hh hhU
    have hr0 : eval (crd h) r ≠ 0 := by
      intro h0
      exact hhU fun p hp => by rw [Set.mem_singleton_iff.1 hp]; exact h0
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hm : X (Sum.inl (i, j)) - C (c (Sum.inl (i, j))) ∈ M := by simp [hM, RingHom.mem_ker]
    have := mem_vanI.1 (hrM _ hm) h hh
    simp only [map_mul, map_sub, eval_X, eval_C, crd_inl] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hr0
    · simpa [hc, sub_eq_zero] using h1
  have h1U : (1 : Matrix.GeneralLinearGroup n K) ∈ U := by
    intro h1
    have := h1 r rfl
    rw [← hc, hr1'] at this
    exact one_ne_zero this
  have hbot : idCompGL H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hS := (isIrreducible_idCompGL H).isPreirreducible
    have hsub := subset_closure_inter_of_isPreirreducible_of_isOpen hS hUo
      ⟨1, (idCompGL H).one_mem, h1U⟩
    have hsing : ((idCompGL H : Set (Matrix.GeneralLinearGroup n K)) ∩ U) ⊆ {1} :=
      fun y hy => hHU y (idCompGL_le H hy.1) hy.2
    have := closure_mono hsing (hsub hx)
    rw [closure_singleton] at this
    exact Subgroup.mem_bot.2 this
  exact (finite_iff_idCompGL_eq_bot H).2 hbot

end Fin

end RamanujanPetersson.AlgGrpB

end


