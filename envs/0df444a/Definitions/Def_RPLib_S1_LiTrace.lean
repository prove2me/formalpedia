-- Prove2me | Definitions.Def_RPLib_S1_LiTrace
-- name    : RPLib_S1_LiTrace
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:38:44.149317+00:00
-- url     : https://prove2.me/theorems/14eea8d8-e5bd-4e6e-b3d2-3de85b564692
-- title:
--   Hecke eigenvalues at bad primes when the character is not primitive at $p$: the case $p \parallel N$
-- statement:
--   Let $f$ be a newform of level $N$ with nebentypus $\chi$ and $p \parallel N$ a prime such that $\chi$ is defined modulo $N/p$. Then $$|a_p(f)|^2 = p^{k-2}.$$ Combined with the case $p^2 \mid N$, $|a_p(f)| \le p^{(k-1)/2}$ whenever $p \mid N$ and $\chi$ is defined modulo $N/p$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285-315, doi:10.1007/BF01344468, Theorem 3

import Mathlib
import Definitions.Def_RPLib_S1_LiTraceA

/-!
# S1-LI-TRACE part B: `p ∥ N`, and the bad-prime bound when `χ` is defined mod `N / p`

`W = W_p` with matrix `[[p, y], [N, p w]]` (`p w - L y = 1`, `L = N / p`). Then `W ∘ [[1, j], [0, p]] = p α_j`
with `α_j = [[1, j + y], [L, L j + p w]] ∈ Γ₁(L)`, and `{1} ∪ {α_j}` is a set of representatives of
`(Γ₀(N) ∩ Γ₁(L)) \ Γ₁(L)`. Hence `W f + χ(d) a_p f` is `Γ₁(L)`-invariant, so old; applying `W` once more gives
`χ(d) a_p² = p^(k-2)`.
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace RP.LiTrace

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke RP.Newforms RP.AtkinLehner
open Matrix.SpecialLinearGroup (mapGL)

/-! ### Matrix helpers -/

lemma mapGL_inj {A B : SL(2, ℤ)} (h : mapGL ℝ A = mapGL ℝ B) : A = B := by
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simp only [coe_mapGL_eq] at this
  simpa using this

lemma mul_inv_10 (A B : SL(2, ℤ)) : (A * B⁻¹) 1 0 = A 1 0 * B 1 1 - A 1 1 * B 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Fin.isValue]
  ring

lemma cast_dvd_of_N {N p L : ℕ} (hN : p * L = N) {x : ℤ} (h : ((x : ℤ) : ZMod N) = 0) : (p : ℤ) ∣ x := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact dvd_trans (Int.natCast_dvd_natCast.2 ⟨L, hN.symm⟩) h

lemma cast_N_of_dvd {N p L : ℕ} (hN : p * L = N) (hcop : IsCoprime (p : ℤ) (L : ℤ)) {x : ℤ}
    (hp : (p : ℤ) ∣ x) (hL : (L : ℤ) ∣ x) : ((x : ℤ) : ZMod N) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hN]
  push_cast
  exact hcop.mul_dvd hp hL

/-! ### The data `W_p`, `α_j` -/

/-- `W_p = [[p, y], [N, p w]]` with `p w - L y = 1`, `p L = N`. -/
def alD (N p L : ℕ) (y w : ℤ) (hN : p * L = N) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) : ALData N p :=
  ⟨L, 1, y, 1, w, hN, by linear_combination hwy⟩

/-- `[[1, j + y], [L, L j + p w]]`. -/
def alphaMat (L p : ℕ) (y w : ℤ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, (j : ℤ) + y; (L : ℤ), (L : ℤ) * j + p * w]

lemma det_alphaMat (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (j : ℕ) :
    (alphaMat L p y w j).det = 1 := by
  rw [alphaMat, Matrix.det_fin_two_of]
  linear_combination hwy

/-- `α_j ∈ SL(2, ℤ)`. -/
def alpha (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (j : ℕ) : SL(2, ℤ) :=
  ⟨alphaMat L p y w j, det_alphaMat L p y w hwy j⟩

lemma coe_alpha (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (j : ℕ) :
    ((alpha L p y w hwy j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = alphaMat L p y w j := rfl

lemma alpha_mem (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (j : ℕ) :
    alpha L p y w hwy j ∈ Gamma1 L := by
  refine mem_Gamma1_of _ ?_ ?_
  · rw [coe_alpha]; simp [alphaMat]
  · rw [coe_alpha]; simp [alphaMat]

/-- Representatives: `none ↦ 1`, `some j ↦ α_j`. -/
def aRep (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) : Option (Fin p) → SL(2, ℤ)
  | none => 1
  | some j => alpha L p y w hwy j

lemma aRep_mem (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (r : Option (Fin p)) :
    aRep L p y w hwy r ∈ Gamma1 L := by
  cases r with
  | none => exact one_mem _
  | some j => exact alpha_mem L p y w hwy j

lemma aRep_none_10 (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) :
    (aRep L p y w hwy none) 1 0 = 0 := by
  simp [aRep]

lemma aRep_none_11 (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) :
    (aRep L p y w hwy none) 1 1 = 1 := by
  simp [aRep]

lemma aRep_some_10 (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (j : Fin p) :
    (aRep L p y w hwy (some j)) 1 0 = L := rfl

lemma aRep_some_11 (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (j : Fin p) :
    (aRep L p y w hwy (some j)) 1 1 = (L : ℤ) * ((j : ℕ) : ℤ) + p * w := rfl

lemma rep10_none (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (A : SL(2, ℤ)) :
    (A * (aRep L p y w hwy none)⁻¹) 1 0 = A 1 0 := by
  rw [mul_inv_10, aRep_none_10, aRep_none_11]
  ring

lemma rep10_some (L p : ℕ) (y w : ℤ) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (A : SL(2, ℤ)) (j : Fin p) :
    (A * (aRep L p y w hwy (some j))⁻¹) 1 0 =
      (L : ℤ) * (A 1 0 * ((j : ℕ) : ℤ) - A 1 1) + (p : ℤ) * (A 1 0 * w) := by
  rw [mul_inv_10, aRep_some_10, aRep_some_11]
  ring

/-! ### The product `W_p · [[1, j], [0, p]] = α_j · p` -/

section prod

variable {N p L : ℕ} [NeZero N] [hp : Fact p.Prime]

lemma gl_mul_repU (y w : ℤ) (hN : p * L = N) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (j : ℕ) :
    (alD N p L y w hN hwy).gl * toGL (repU p j) (det_repU_ne j) =
      mapGL ℝ (alpha L p y w hwy j) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (alD N p L y w hN hwy).gl.det := by
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (alD N p L y w hN hwy).gl.det : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix !![(p : ℤ), 0; 0, (p : ℤ)] := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, ALData.gl_det]
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.natCast_apply]
  have hm : (alD N p L y w hN hwy).mat * repU p j =
      ((alpha L p y w hwy j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, (p : ℤ)] := by
    rw [coe_alpha]
    subst hN
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp only [ALData.mat, alD, repU, alphaMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      push_cast <;> ring
  apply Units.ext
  rw [coe_mul_eq (ALData.coe_gl_eq _) (coe_toGL_eq _ _), coe_mul_eq (coe_mapGL_eq _) hsc, hm]

/-- `(W g) ∣ [[1, j], [0, p]] = p^(k-2) (g ∣ α_j)`. -/
lemma alOp_slash_repU (y w : ℤ) (hN : p * L = N) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (k : ℤ)
    (g : S1 N k) (j : ℕ) :
    ⇑((alD N p L y w hN hwy).alOp k g) ∣[k] toGL (repU p j) (det_repU_ne j) =
      ((p : ℂ) ^ (k - 2)) • (⇑g ∣[k] mapGL ℝ (alpha L p y w hwy j)) := by
  rw [ALData.coe_alOp, ← SlashAction.slash_mul, gl_mul_repU, SlashAction.slash_mul,
    Adjoint.slash_scalar k _ (alD N p L y w hN hwy).gl_det_pos, ALData.gl_det, Complex.ofReal_natCast]

/-- `U_p (W g) = p^(k-2) Σ_j g ∣ α_j`. -/
lemma heckeFun_alOp (y w : ℤ) (hN : p * L = N) (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (k : ℤ)
    (g : S1 N k) :
    heckeFun p k ((alD N p L y w hN hwy).alOp k g) =
      ((p : ℂ) ^ (k - 2)) • ∑ j : Fin p, ⇑g ∣[k] mapGL ℝ (alpha L p y w hwy j) := by
  rw [heckeFun_eq_sum_dvd k (⟨L, hN.symm⟩ : p ∣ N), Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => alOp_slash_repU y w hN hwy k g j

end prod

/-! ### Claim B: `Σ_r F ∣ β_r` is `Γ₁(L)`-invariant -/

theorem claimB {N p L : ℕ} [hp : Fact p.Prime] (hpL : ¬ p ∣ L) (y w : ℤ) (hN : p * L = N)
    (hwy : (p : ℤ) * w - (L : ℤ) * y = 1) (k : ℤ) (F : ℍ → ℂ)
    (hF : ∀ δ : SL(2, ℤ), δ ∈ Gamma0 N ⊓ Gamma1 L → F ∣[k] mapGL ℝ δ = F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 L) :
    (∑ r, F ∣[k] mapGL ℝ (aRep L p y w hwy r)) ∣[k] mapGL ℝ γ =
      ∑ r, F ∣[k] mapGL ℝ (aRep L p y w hwy r) := by
  have hcop : IsCoprime (p : ℤ) (L : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpL)
  have hL0 : ((L : ℕ) : ZMod p) ≠ 0 := by
    intro h
    apply hpL
    have h' : (((L : ℤ)) : ZMod p) = 0 := by exact_mod_cast h
    exact Int.natCast_dvd_natCast.1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h')
  refine sum_slash_perm (fun r => mapGL ℝ (aRep L p y w hwy r)) (mapGL ℝ γ) (Gamma0 N ⊓ Gamma1 L)
    ?_ ?_ k F hF
  · intro r
    show ∃ s, ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ⊓ Gamma1 L ∧
      mapGL ℝ (aRep L p y w hwy r) * mapGL ℝ γ = mapGL ℝ δ * mapGL ℝ (aRep L p y w hwy s)
    obtain ⟨A, hAdef⟩ : ∃ A : SL(2, ℤ), A = aRep L p y w hwy r * γ := ⟨_, rfl⟩
    have hA : A ∈ Gamma1 L := by rw [hAdef]; exact mul_mem (aRep_mem L p y w hwy r) hγ
    have key : ∀ s, (p : ℤ) ∣ (A * (aRep L p y w hwy s)⁻¹) 1 0 →
        A * (aRep L p y w hwy s)⁻¹ ∈ Gamma0 N ⊓ Gamma1 L := by
      intro s hs
      have h1 : A * (aRep L p y w hwy s)⁻¹ ∈ Gamma1 L := mul_mem hA (inv_mem (aRep_mem L p y w hwy s))
      refine ⟨?_, h1⟩
      show _ ∈ Gamma0 N
      rw [Gamma0_mem]
      exact cast_N_of_dvd hN hcop hs
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ L).1 ((Gamma1_mem L _).1 h1).2.2)
    have hfin : ∃ s, (p : ℤ) ∣ (A * (aRep L p y w hwy s)⁻¹) 1 0 := by
      by_cases h0 : ((A 1 0 : ℤ) : ZMod p) = 0
      · exact ⟨none, by rw [rep10_none]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0⟩
      · obtain ⟨j, hjp, hj⟩ : ∃ j : ℕ, j < p ∧
            (j : ZMod p) = ((A 1 1 : ℤ) : ZMod p) * ((A 1 0 : ℤ) : ZMod p)⁻¹ :=
          ⟨_, ZMod.val_lt _, ZMod.natCast_zmod_val _⟩
        refine ⟨some ⟨j, hjp⟩, ?_⟩
        rw [rep10_some]
        refine dvd_add (dvd_mul_of_dvd_right ?_ _) (dvd_mul_right _ _)
        show (p : ℤ) ∣ A 1 0 * (j : ℤ) - A 1 1
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hj, mul_left_comm, mul_inv_cancel₀ h0, mul_one, sub_self]
    obtain ⟨s, hs⟩ := hfin
    refine ⟨s, A * (aRep L p y w hwy s)⁻¹, key s hs, ?_⟩
    rw [← map_mul, ← map_mul, inv_mul_cancel_right, hAdef]
  · intro r s δ hδ h
    have h2 : mapGL ℝ (aRep L p y w hwy r) = mapGL ℝ (δ * aRep L p y w hwy s) := by
      rw [map_mul]; exact h
    have h' := mapGL_inj h2
    have hδe : δ = aRep L p y w hwy r * (aRep L p y w hwy s)⁻¹ := by rw [h', mul_inv_cancel_right]
    have h10 : (p : ℤ) ∣ δ 1 0 := cast_dvd_of_N hN (Gamma0_mem.1 hδ.1)
    rw [hδe, mul_inv_10] at h10
    cases r with
    | none =>
      cases s with
      | none => rfl
      | some j =>
        exfalso
        rw [aRep_none_10, aRep_none_11, aRep_some_10, aRep_some_11] at h10
        apply hpL
        have e : (0 : ℤ) * ((L : ℤ) * ((j : ℕ) : ℤ) + p * w) - 1 * L = -(L : ℤ) := by ring
        rw [e, dvd_neg] at h10
        exact Int.natCast_dvd_natCast.1 h10
    | some i =>
      cases s with
      | none =>
        exfalso
        rw [aRep_none_10, aRep_none_11, aRep_some_10, aRep_some_11] at h10
        apply hpL
        have e : (L : ℤ) * 1 - ((L : ℤ) * ((i : ℕ) : ℤ) + p * w) * 0 = (L : ℤ) := by ring
        rw [e] at h10
        exact Int.natCast_dvd_natCast.1 h10
      | some j =>
        rw [aRep_some_10, aRep_some_10, aRep_some_11, aRep_some_11] at h10
        have hm : ((((L : ℤ) * L * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ)) : ZMod p) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          have e : (L : ℤ) * ((L : ℤ) * ((j : ℕ) : ℤ) + p * w) - ((L : ℤ) * ((i : ℕ) : ℤ) + p * w) * L =
              (L : ℤ) * L * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := by ring
          rw [← e]; exact h10
        push_cast at hm
        rcases mul_eq_zero.1 hm with h | h
        · exact absurd (mul_self_eq_zero.1 h) hL0
        · have hij : ((j : ℕ) : ZMod p) = ((i : ℕ) : ZMod p) := sub_eq_zero.1 h
          have hv := congrArg ZMod.val hij
          rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hv
          rw [Fin.ext hv.symm]

/-! ### (b) assembly -/

lemma twistChar_trivOn {N L Q : ℕ} (hLN : L ∣ N) {χ : DirichletCharacter ℂ N}
    (hχ : ∀ u : (ZMod N)ˣ, ZMod.castHom hLN (ZMod L) (u : ZMod N) = 1 → χ u = 1)
    (D : ALData N Q) (hQ' : D.Q' = L) :
    ∀ u : (ZMod N)ˣ, ZMod.castHom hLN (ZMod L) (u : ZMod N) = 1 → D.twistChar χ u = 1 := by
  intro u hu
  rw [ALData.twistChar_apply]
  apply hχ
  subst hQ'
  exact (D.twist_cast_Q' u).trans hu

/-- **Li (b)**, `p ∥ N`: for a newform `f` with `χ` defined mod `N / p` there is `e` with `‖e‖ = 1`
(`e = χ(d)`, `d` from `W_p²`) and `e · a_p² = p^(k-2)`. -/
theorem exists_chi_mul_coeff_sq {N p : ℕ} [NeZero N] [hp : Fact p.Prime] (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N)
    {k : ℤ} {χ : DirichletCharacter ℂ N} (hχ : χ.FactorsThrough (N / p)) {f : S1 N k}
    (hf : IsNewform χ f) :
    ∃ e : ℂ, ‖e‖ = 1 ∧ e * (qExpansion 1 f).coeff p ^ 2 = (p : ℂ) ^ (k - 2) := by
  have hN : p * (N / p) = N := Nat.mul_div_cancel' hpN
  have hpL : ¬ p ∣ N / p := by
    intro h; apply hp2; rw [pow_two]
    calc p * p ∣ p * (N / p) := Nat.mul_dvd_mul_left p h
      _ = N := hN
  have hLN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have hpmem : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hp.out, hpN, NeZero.ne N⟩
  have hcop : IsCoprime (p : ℤ) ((N / p : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpL)
  obtain ⟨u, v, huv⟩ := hcop
  have hwy : (p : ℤ) * u - ((N / p : ℕ) : ℤ) * (-v) = 1 := by linear_combination huv
  have hp0 : (p : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have htriv := trivOn_of_factorsThrough hLN hχ
  -- the Atkin-Lehner data
  have hWf : (alD N p (N / p) (-v) u hN hwy).alOp k f ∈
      chiSubspace k ((alD N p (N / p) (-v) u hN hwy).twistChar χ) :=
    (alD N p (N / p) (-v) u hN hwy).alOp_mem_chiSubspace k hf.mem_chi
  have hWfinv : ∀ δ : SL(2, ℤ), δ ∈ Gamma0 N ⊓ Gamma1 (N / p) →
      ⇑((alD N p (N / p) (-v) u hN hwy).alOp k f) ∣[k] mapGL ℝ δ =
        ⇑((alD N p (N / p) (-v) u hN hwy).alOp k f) :=
    slash_eq_of_chi hLN (twistChar_trivOn hLN htriv _ rfl) hWf
  obtain ⟨e, he⟩ : ∃ e : ℂ, e = χ ((unitMap N ⟨(alD N p (N / p) (-v) u hN hwy).sqSL,
      (alD N p (N / p) (-v) u hN hwy).sqSL_mem⟩ : (ZMod N)ˣ) : ZMod N) := ⟨_, rfl⟩
  have he1 : ‖e‖ = 1 := by rw [he]; exact DirichletCharacter.unit_norm_eq_one χ _
  have hWW : (alD N p (N / p) (-v) u hN hwy).alOp k ((alD N p (N / p) (-v) u hN hwy).alOp k f) =
      ((p : ℂ) ^ (k - 2) * e) • f := by
    rw [ALData.alOp_alOp, (mem_chiSubspace_iff_diamond k χ f).1 hf.mem_chi, smul_smul, he]
  set W := (alD N p (N / p) (-v) u hN hwy).alOp k with hW
  set a := (qExpansion 1 f).coeff p with ha
  -- Σ_j (W f) ∣ α_j = e a f
  have hsum : ∑ j : Fin p, ⇑(W f) ∣[k] mapGL ℝ (alpha (N / p) p (-v) u hwy j) = (e * a) • ⇑f := by
    have h1 := heckeFun_alOp (-v) u hN hwy k (W f)
    have h2 : heckeFun p k (W (W f)) = ((p : ℂ) ^ (k - 2)) • ((e * a) • ⇑f) := by
      rw [← coe_heckeT, hWW, map_smul, hf.heckeT_eq_of_dvd p hpN, smul_smul, smul_smul, FunLike.coe_smul,
        ← ha, mul_assoc]
    exact smul_right_injective _ hp0 (h1.symm.trans h2)
  -- Φ = W f + e a f is Γ₁(N/p)-invariant, hence old
  have hΦ : ∀ γ : SL(2, ℤ), γ ∈ Gamma1 (N / p) →
      ⇑(W f + (e * a) • f) ∣[k] mapGL ℝ γ = ⇑(W f + (e * a) • f) := by
    intro γ hγ
    have hB := claimB hpL (-v) u hN hwy k _ hWfinv hγ
    rw [Fintype.sum_option] at hB
    simp only [aRep, map_one, SlashAction.slash_one] at hB
    rw [hsum] at hB
    rw [FunLike.coe_add, FunLike.coe_smul]
    exact hB
  have hold1 : W f + (e * a) • f ∈ oldSpace N k := mem_oldSpace_of_inv hpmem _ hΦ
  have hold2 : W (W f + (e * a) • f) ∈ oldSpace N k := alOp_mem_oldSpace (alD N p (N / p) (-v) u hN hwy) k hold1
  have hold3 : W (W f + (e * a) • f) - (e * a) • (W f + (e * a) • f) ∈ oldSpace N k :=
    Submodule.sub_mem _ hold2 (Submodule.smul_mem _ _ hold1)
  have hcalc : W (W f + (e * a) • f) - (e * a) • (W f + (e * a) • f) =
      ((p : ℂ) ^ (k - 2) * e - (e * a) ^ 2) • f := by
    rw [map_add, map_smul, hWW]
    module
  rw [hcalc] at hold3
  have h0 := eq_zero_of_smul_mem_old hf hold3
  have hne : e ≠ 0 := by
    intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  refine ⟨e, he1, ?_⟩
  have h3 : e * ((p : ℂ) ^ (k - 2) - e * a ^ 2) = 0 := by linear_combination h0
  have h4 := (mul_eq_zero.1 h3).resolve_left hne
  linear_combination -h4

/-- `‖a_p‖² = p^(k-2)` when `p ∥ N` and `χ` is defined mod `N / p`. -/
theorem norm_coeff_sq_of_not_sq_dvd {N p : ℕ} [NeZero N] [hp : Fact p.Prime] (hpN : p ∣ N)
    (hp2 : ¬ p ^ 2 ∣ N) {k : ℤ} {χ : DirichletCharacter ℂ N} (hχ : χ.FactorsThrough (N / p))
    {f : S1 N k} (hf : IsNewform χ f) :
    ‖(qExpansion 1 f).coeff p‖ ^ 2 = (p : ℝ) ^ (k - 2) := by
  obtain ⟨e, he1, he⟩ := exists_chi_mul_coeff_sq hpN hp2 hχ hf
  have := congrArg norm he
  rw [norm_mul, norm_pow, he1, one_mul, norm_zpow, Complex.norm_natCast] at this
  exact this

/-- **Bad-prime bound, non-primitive case**: if `p ∣ N` is prime and `χ` is defined mod `N / p`, then
`‖a_p(f)‖ ≤ p^((k-1)/2)` for every newform `f` (`a_p = 0` if `p² ∣ N`, `‖a_p‖ = p^((k-2)/2)` if `p ∥ N`). -/
theorem norm_coeff_prime_le {N p : ℕ} [NeZero N] [hp : Fact p.Prime] (hpN : p ∣ N)
    {k : ℤ} {χ : DirichletCharacter ℂ N} (hχ : χ.FactorsThrough (N / p)) {f : S1 N k}
    (hf : IsNewform χ f) :
    ‖(qExpansion 1 f).coeff p‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hB0 : (0 : ℝ) ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := Real.rpow_nonneg hp0 _
  by_cases hp2 : p ^ 2 ∣ N
  · rw [coeff_prime_eq_zero_of_sq_dvd hp2 hχ hf, norm_zero]
    exact hB0
  · have hsq := norm_coeff_sq_of_not_sq_dvd hpN hp2 hχ hf
    have hB2 : ((p : ℝ) ^ (((k : ℝ) - 1) / 2)) * ((p : ℝ) ^ (((k : ℝ) - 1) / 2)) = (p : ℝ) ^ ((k : ℝ) - 1) := by
      rw [← Real.rpow_add (by exact_mod_cast hp.out.pos)]
      congr 1; ring
    have hle : (p : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ ((k : ℝ) - 1) := by
      rw [← Real.rpow_intCast]
      apply Real.rpow_le_rpow_of_exponent_le hp1
      push_cast; linarith
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self hB0 hlt
    rw [hB2, ← pow_two, hsq] at this
    linarith

end RP.LiTrace


