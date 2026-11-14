-- Prove2me | Definitions.Def_RPLib_S4_LarsenIso
-- name    : RPLib_S4_LarsenIso
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:18:02.516043+00:00
-- url     : https://prove2.me/theorems/34193352-5254-471b-99d8-4a72286f3bc0
-- title:
--   Larsen's alternative library: `End_G(isoLie B)` is scalar when `M4 ≤ 3`
-- statement:
--   For `Bᵀ = ε B` (`ε² = 1`, `B` invertible) and `G ≤ isoSub B`: the `B`-adjoint `starB`, the equivariant
--   projections `piS` (traceless self-adjoint part) and `piE` (onto `isoLie B`), `li_Iso` (`piK, piS, piE` independent,
--   `dim V ≥ 3`) and `endIso_scalar` (`M4 G ≤ 3` ⇒ every `Ad(G)`-equivariant endomorphism of `isoLie B` is scalar).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_LarsenM4

/-!
# S4-Larsen: `End_G(isoLie B)` is scalar when `M4 ≤ 3`

For `Bᵀ = ε B` (`ε² = 1`, `B` invertible) and `G ≤ isoSub B`: the `B`-adjoint `starB`, the equivariant
projections `piS` (traceless self-adjoint part) and `piE` (onto `isoLie B`), `li_Iso` (`piK, piS, piE` independent,
`dim V ≥ 3`) and `endIso_scalar` (`M4 G ≤ 3` ⇒ every `Ad(G)`-equivariant endomorphism of `isoLie B` is scalar).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.Larsen

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB RamanujanPetersson.AlgGrpC

attribute [local instance] RamanujanPetersson.AlgGrpA.zarTop

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Iso

variable [CharZero K] {B : Matrix n n K}

/-- The `B`-adjoint `x ↦ B⁻¹ xᵀ B`; it is `Ad(G)`-equivariant for `G ≤ O(B)` and `isoLie B = {x | starB x = -x}`. -/
def starB (B : Matrix n n K) : Matrix n n K →ₗ[K] Matrix n n K where
  toFun x := B⁻¹ * xᵀ * B
  map_add' x y := by rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by
    rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem starB_apply (x : Matrix n n K) : starB B x = B⁻¹ * xᵀ * B := rfl

theorem starB_one (hu : IsUnit B.det) : starB B (1 : Matrix n n K) = 1 := by
  rw [starB_apply, Matrix.transpose_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]

theorem trace_starB (hu : IsUnit B.det) (x : Matrix n n K) : (starB B x).trace = x.trace := by
  rw [starB_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    Matrix.trace_transpose]

theorem mul_starB (hu : IsUnit B.det) (x : Matrix n n K) : B * starB B x = xᵀ * B := by
  rw [starB_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem invT_mul (hu : IsUnit B.det) {ε : K} (hε : ε * ε = 1) (hBt : Bᵀ = ε • B) :
    B⁻¹ᵀ * B = ε • (1 : Matrix n n K) := by
  have h1 : B⁻¹ᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
  rw [hBt, Matrix.mul_smul] at h1
  calc B⁻¹ᵀ * B = (ε * ε) • (B⁻¹ᵀ * B) := by rw [hε, one_smul]
    _ = ε • (1 : Matrix n n K) := by rw [mul_smul, h1]

theorem starB_transpose_mul (hu : IsUnit B.det) {ε : K} (hε : ε * ε = 1) (hBt : Bᵀ = ε • B)
    (x : Matrix n n K) : (starB B x)ᵀ * B = B * x := by
  calc (starB B x)ᵀ * B = Bᵀ * x * (B⁻¹ᵀ * B) := by
        rw [starB_apply, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
        simp only [Matrix.mul_assoc]
    _ = (ε * ε) • (B * x) := by
        rw [invT_mul hu hε hBt, hBt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_smul]
    _ = B * x := by rw [hε, one_smul]

theorem starB_of_mem (hu : IsUnit B.det) {x : Matrix n n K} (hx : x ∈ isoLie B) : starB B x = -x := by
  have h : xᵀ * B = -(B * x) := eq_neg_of_add_eq_zero_left (mem_isoLie.1 hx)
  rw [starB_apply, Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

theorem trace_of_mem (hu : IsUnit B.det) {x : Matrix n n K} (hx : x ∈ isoLie B) : x.trace = 0 := by
  have h := trace_starB hu x
  rw [starB_of_mem hu hx, Matrix.trace_neg] at h
  have h2 : (2 : K) * x.trace = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

theorem iso_mul {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ isoSub B) :
    (g : Matrix n n K)ᵀ * B = B * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
  have h := mem_isoSub.1 hg
  calc (g : Matrix n n K)ᵀ * B
      = (g : Matrix n n K)ᵀ * B * ((g * g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
        rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = B * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
        rw [Units.val_mul, ← Matrix.mul_assoc, h]

theorem starB_conj (hu : IsUnit B.det) {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ isoSub B)
    (x : Matrix n n K) :
    starB B ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
      (g : Matrix n n K) * starB B x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
  have h1 := iso_mul hg
  have h2 := iso_mul ((isoSub B).inv_mem hg)
  rw [inv_inv] at h2
  have h3 : B⁻¹ * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ = (g : Matrix n n K) * B⁻¹ := by
    calc B⁻¹ * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ
        = B⁻¹ * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * (B * B⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = B⁻¹ * (B * (g : Matrix n n K)) * B⁻¹ := by
          rw [← h2]
          simp only [Matrix.mul_assoc]
      _ = (g : Matrix n n K) * B⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  calc starB B ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K))
      = (B⁻¹ * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ) * xᵀ * ((g : Matrix n n K)ᵀ * B) := by
        rw [starB_apply, Matrix.transpose_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = ((g : Matrix n n K) * B⁻¹) * xᵀ * (B * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) := by
        rw [h3, h1]
    _ = (g : Matrix n n K) * starB B x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
        rw [starB_apply]
        simp only [Matrix.mul_assoc]

theorem starB_mem_adComm (hu : IsUnit B.det) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGB : G ≤ isoSub B) : starB B ∈ adComm G :=
  fun _ hg x => starB_conj hu (hGB hg) x

theorem starB_piK (hu : IsUnit B.det) (x : Matrix n n K) : starB B (piK x) = piK x := by
  rw [piK_apply, map_smul, map_smul, starB_one hu]

theorem starB_inv_mul (hu : IsUnit B.det) {ε : K} (hε : ε * ε = 1) (hBt : Bᵀ = ε • B)
    {S : Matrix n n K} (hS : Sᵀ = ε • S) : starB B (B⁻¹ * S) = B⁻¹ * S := by
  calc starB B (B⁻¹ * S) = B⁻¹ * Sᵀ * (B⁻¹ᵀ * B) := by
        rw [starB_apply, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = (ε * ε) • (B⁻¹ * S) := by
        rw [hS, invT_mul hu hε hBt, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, smul_smul]
    _ = B⁻¹ * S := by rw [hε, one_smul]

theorem inv_mul_mem_isoLie (hu : IsUnit B.det) {ε : K} (hε : ε * ε = 1) (hBt : Bᵀ = ε • B)
    {A : Matrix n n K} (hA : Aᵀ = -(ε • A)) : B⁻¹ * A ∈ isoLie B := by
  rw [mem_isoLie, Matrix.transpose_mul, Matrix.mul_assoc, invT_mul hu hε hBt, Matrix.mul_smul, Matrix.mul_one,
    hA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, smul_neg, smul_smul, hε, one_smul,
    neg_add_cancel]

/-- Projection of `End V` onto `isoLie B`: `x ↦ (x - starB x) / 2`. -/
def piE (B : Matrix n n K) : Matrix n n K →ₗ[K] Matrix n n K := (2 : K)⁻¹ • (LinearMap.id - starB B)

/-- Projection onto the traceless `B`-self-adjoint part: `x ↦ (x + starB x) / 2 - piK x`. -/
def piS (B : Matrix n n K) : Matrix n n K →ₗ[K] Matrix n n K :=
  (2 : K)⁻¹ • (LinearMap.id + starB B) - piK

theorem piE_apply (x : Matrix n n K) : piE B x = (2 : K)⁻¹ • (x - starB B x) := rfl

theorem piS_apply (x : Matrix n n K) : piS B x = (2 : K)⁻¹ • (x + starB B x) - piK x := rfl

theorem piE_mem_adComm (hu : IsUnit B.det) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGB : G ≤ isoSub B) : piE B ∈ adComm G :=
  Submodule.smul_mem _ _ (Submodule.sub_mem _ (id_mem_adComm G) (starB_mem_adComm hu hGB))

theorem piS_mem_adComm (hu : IsUnit B.det) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGB : G ≤ isoSub B) : piS B ∈ adComm G :=
  Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ (id_mem_adComm G) (starB_mem_adComm hu hGB)))
    (piK_mem_adComm G)

theorem piE_mem (hu : IsUnit B.det) {ε : K} (hε : ε * ε = 1) (hBt : Bᵀ = ε • B) (x : Matrix n n K) :
    piE B x ∈ isoLie B := by
  rw [mem_isoLie, piE_apply, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
    Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, starB_transpose_mul hu hε hBt, mul_starB hu,
    sub_add_sub_cancel, sub_self, smul_zero]

theorem half_add_self (x : Matrix n n K) : (2 : K)⁻¹ • (x + x) = x := by
  rw [← two_smul K x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem piE_of_mem (hu : IsUnit B.det) {x : Matrix n n K} (hx : x ∈ isoLie B) : piE B x = x := by
  rw [piE_apply, starB_of_mem hu hx, sub_neg_eq_add, half_add_self]

theorem piS_of_mem (hu : IsUnit B.det) {x : Matrix n n K} (hx : x ∈ isoLie B) : piS B x = 0 := by
  rw [piS_apply, starB_of_mem hu hx, add_neg_cancel, smul_zero, piK_eq_zero (trace_of_mem hu hx), sub_zero]

theorem piE_fix {x : Matrix n n K} (hx : starB B x = x) : piE B x = 0 := by
  rw [piE_apply, hx, sub_self, smul_zero]

theorem piS_fix {x : Matrix n n K} (hx : starB B x = x) (ht : x.trace = 0) : piS B x = x := by
  rw [piS_apply, hx, piK_eq_zero ht, sub_zero, half_add_self]

theorem li_Iso (hn : 3 ≤ Fintype.card n) (hu : IsUnit B.det) {ε : K} (hε : ε * ε = 1) (hBt : Bᵀ = ε • B) :
    LinearIndependent K ![(piK : Matrix n n K →ₗ[K] Matrix n n K), piS B, piE B] := by
  obtain ⟨i, j, k, hij, hik, hjk⟩ := Fintype.two_lt_card_iff.1 (lt_of_lt_of_le (by norm_num) hn)
  have : Nonempty n := ⟨i⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : c 0 • (piK : Matrix n n K →ₗ[K] Matrix n n K) + c 1 • piS B + c 2 • piE B = 0 := by
    simpa [Fin.sum_univ_three] using hc
  have hev : ∀ x : Matrix n n K, c 0 • piK x + c 1 • piS B x + c 2 • piE B x = 0 := by
    intro x
    have h := LinearMap.congr_fun hc' x
    rwa [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, LinearMap.zero_apply] at h
  -- `c 0`: test on `1`
  have hS1 : piS B (1 : Matrix n n K) = 0 := by
    rw [piS_apply, starB_one hu, piK_one, half_add_self, sub_self]
  have hE1 : piE B (1 : Matrix n n K) = 0 := piE_fix (starB_one hu)
  have h1 := hev 1
  rw [piK_one, hS1, hE1, smul_zero, smul_zero, add_zero, add_zero] at h1
  have c0 : c 0 = 0 := by simpa using congrFun (congrFun h1 i) i
  -- `c 2`: test on `z = B⁻¹ (E_ij - ε E_ji) ∈ isoLie B`
  have hA : (Matrix.single i j (1 : K) - ε • Matrix.single j i 1)ᵀ =
      -(ε • (Matrix.single i j (1 : K) - ε • Matrix.single j i 1)) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_single, Matrix.transpose_single, smul_sub,
      smul_smul, hε, one_smul, neg_sub]
  have hz := inv_mul_mem_isoLie hu hε hBt hA
  have hz0 : B⁻¹ * (Matrix.single i j (1 : K) - ε • Matrix.single j i 1) ≠ 0 := by
    intro h0
    have e : Matrix.single i j (1 : K) - ε • Matrix.single j i 1 = 0 := by
      rw [← Matrix.one_mul (Matrix.single i j (1 : K) - ε • Matrix.single j i 1),
        ← Matrix.mul_nonsing_inv _ hu, Matrix.mul_assoc, h0, Matrix.mul_zero]
    have e' := congrFun (congrFun e i) j
    simp [hij, hij.symm] at e'
  have h2 := hev (B⁻¹ * (Matrix.single i j (1 : K) - ε • Matrix.single j i 1))
  rw [piK_eq_zero (trace_of_mem hu hz), piS_of_mem hu hz, piE_of_mem hu hz, smul_zero, smul_zero,
    zero_add, zero_add] at h2
  have c2 : c 2 = 0 := (smul_eq_zero.1 h2).resolve_right hz0
  -- `c 1`: otherwise every `S` with `Sᵀ = ε S` is a multiple of `B`; test on two such `S`
  have c1 : c 1 = 0 := by
    by_contra hc1
    have hfix : ∀ S : Matrix n n K, Sᵀ = ε • S → ∃ t : K, S = t • B := by
      intro S hS
      have hw := starB_inv_mul hu hε hBt hS
      have hw' : starB B (piSL (B⁻¹ * S)) = piSL (B⁻¹ * S) := by
        rw [piSL_apply, map_sub, hw, starB_piK hu]
      have h3 := hev (piSL (B⁻¹ * S))
      rw [piK_eq_zero (trace_piSL _), piS_fix hw' (trace_piSL _), piE_fix hw', smul_zero, smul_zero, zero_add,
        add_zero] at h3
      have h4 : B⁻¹ * S = piK (B⁻¹ * S) := sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_left hc1)
      refine ⟨(B⁻¹ * S).trace * (Fintype.card n : K)⁻¹, ?_⟩
      calc S = B * (B⁻¹ * S) := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
        _ = B * piK (B⁻¹ * S) := by rw [← h4]
        _ = ((B⁻¹ * S).trace * (Fintype.card n : K)⁻¹) • B := by
          rw [piK_apply, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    have hsym : ∀ a b : n, (Matrix.single a b (1 : K) + ε • Matrix.single b a 1)ᵀ =
        ε • (Matrix.single a b (1 : K) + ε • Matrix.single b a 1) := by
      intro a b
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_single, Matrix.transpose_single,
        smul_add, smul_smul, hε, one_smul, add_comm]
    obtain ⟨t1, ht1⟩ := hfix _ (hsym i j)
    obtain ⟨t2, ht2⟩ := hfix _ (hsym i k)
    have e1 : t1 * B i k = 0 := by
      have e := congrFun (congrFun ht1 i) k
      rw [Matrix.smul_apply, smul_eq_mul] at e
      rw [← e]
      simp [Matrix.single_apply, hij, hik, hjk, hij.symm, hik.symm, hjk.symm]
    have e2 : t2 * B i k = 1 := by
      have e := congrFun (congrFun ht2 i) k
      rw [Matrix.smul_apply, smul_eq_mul] at e
      rw [← e]
      simp [Matrix.single_apply, hij, hik, hjk, hij.symm, hik.symm, hjk.symm]
    have e3 : t1 * B i j = 1 := by
      have e := congrFun (congrFun ht1 i) j
      rw [Matrix.smul_apply, smul_eq_mul] at e
      rw [← e]
      simp [Matrix.single_apply, hij, hik, hjk, hij.symm, hik.symm, hjk.symm]
    have hBik : B i k ≠ 0 := fun h => by
      rw [h, mul_zero] at e2
      exact zero_ne_one e2
    have ht : t1 = 0 := (mul_eq_zero.1 e1).resolve_right hBik
    rw [ht, zero_mul] at e3
    exact zero_ne_one e3
  intro m
  fin_cases m
  · exact c0
  · exact c1
  · exact c2

/-- `M4 ≤ 3` and `G ≤ O(B)` / `Sp(B)` force every `Ad(G)`-equivariant endomorphism of `isoLie B` to be scalar. -/
theorem endIso_scalar (hn : 3 ≤ Fintype.card n) (hu : IsUnit B.det) {ε : K} (hε : ε * ε = 1)
    (hBt : Bᵀ = ε • B) {G : Subgroup (Matrix.GeneralLinearGroup n K)} (hGB : G ≤ isoSub B) (hM : M4 G ≤ 3) :
    ∀ φ : Matrix n n K →ₗ[K] Matrix n n K, (∀ x ∈ isoLie B, φ x ∈ isoLie B) →
      (∀ g ∈ G, ∀ x ∈ isoLie B,
        φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
          (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
      ∃ c : K, ∀ x ∈ isoLie B, φ x = c • x := by
  intro φ _ hφ
  have hΦ : φ ∘ₗ piE B ∈ adComm G := by
    intro g hg x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, piE_mem_adComm hu hGB g hg x]
    exact hφ g hg _ (piE_mem hu hε hBt x)
  obtain ⟨c, hc⟩ := exists_coeffs hM ![(piK : Matrix n n K →ₗ[K] Matrix n n K), piS B, piE B]
    (fun k => by fin_cases k; exacts [piK_mem_adComm G, piS_mem_adComm hu hGB, piE_mem_adComm hu hGB])
    (li_Iso hn hu hε hBt) hΦ
  refine ⟨c 2, fun x hx => ?_⟩
  have h : c 0 • piK x + c 1 • piS B x + c 2 • piE B x = φ (piE B x) := by
    have h' := LinearMap.congr_fun hc x
    simpa [Fin.sum_univ_three] using h'
  rw [piK_eq_zero (trace_of_mem hu hx), piS_of_mem hu hx, piE_of_mem hu hx, smul_zero, smul_zero, zero_add,
    zero_add] at h
  exact h.symm

end Iso

end RamanujanPetersson.Larsen


