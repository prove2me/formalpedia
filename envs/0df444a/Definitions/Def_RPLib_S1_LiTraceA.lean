-- Prove2me | Definitions.Def_RPLib_S1_LiTraceA
-- name    : RPLib_S1_LiTraceA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:36:17.167061+00:00
-- url     : https://prove2.me/theorems/d3c89a22-5f1a-43b9-96ee-b2798535ea7f
-- title:
--   Hecke eigenvalues at bad primes when the character is not primitive at $p$: the case $p^2 \mid N$
-- statement:
--   Let $f$ be a newform of level $N$ with nebentypus $\chi$, and $p$ a prime with $p^2 \mid N$ such that $\chi$ is defined modulo $N/p$. Then the $U_p$-eigenvalue vanishes: $$a_p(f) = 0.$$ The proof shows that $U_p f$ is invariant under $\Gamma_1(N/p)$, hence old, and old $\cap$ new $= 0$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285-315, doi:10.1007/BF01344468, Theorem 3

import Mathlib
import Definitions.Def_RPLib_S1_AtkinLehner
import Definitions.Def_RPLib_S1_NewformTrace

/-!
# S1-LI-TRACE: Li's bad-prime eigenvalues in the two non-primitive cases

Level `N`, prime `p ∣ N`, `L = N / p`, newform `f` with character `χ` factoring through `L`.
(a) `p² ∣ N`: `U_p f` has level `L`, so `a_p(f) = 0`.
(b) `p ∥ N`: `χ(d) a_p² = p^(k-2)` (`d` from `W_p²`), so `‖a_p‖² = p^(k-2)`.
Route: no trace computation; `U_p` (resp. `g + p^(2-k) U_p W_p g`) is shown `Γ₁(L)`-invariant by a coset
permutation, hence old, and old ∩ new = 0.
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace RP.LiTrace

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke RP.Newforms
open Matrix.SpecialLinearGroup (mapGL)

/-! ### A permutation lemma for sums of slashes -/

/-- If right multiplication by `W` permutes the cosets `H β_r` and `F` is `H`-invariant, then
`Σ_r F ∣ β_r` is `W`-invariant. -/
theorem sum_slash_perm {R : Type*} [Fintype R] (β : R → GL (Fin 2) ℝ) (W : GL (Fin 2) ℝ)
    (H : Subgroup SL(2, ℤ))
    (hE : ∀ r, ∃ s, ∃ δ : SL(2, ℤ), δ ∈ H ∧ β r * W = mapGL ℝ δ * β s)
    (hU : ∀ r s (δ : SL(2, ℤ)), δ ∈ H → β r = mapGL ℝ δ * β s → r = s)
    (k : ℤ) (F : ℍ → ℂ) (hF : ∀ δ : SL(2, ℤ), δ ∈ H → F ∣[k] mapGL ℝ δ = F) :
    (∑ r, F ∣[k] β r) ∣[k] W = ∑ r, F ∣[k] β r := by
  choose σ δ hδ hδeq using hE
  have hinj : Function.Injective σ := by
    intro r r' h
    apply hU r r' (δ r * (δ r')⁻¹) (mul_mem (hδ r) (inv_mem (hδ r')))
    have e1 : β r = mapGL ℝ (δ r) * β (σ r) * W⁻¹ := by rw [← hδeq r]; group
    have e2 : β (σ r') = (mapGL ℝ (δ r'))⁻¹ * (β r' * W) := by rw [hδeq r']; group
    rw [e1, h, e2, map_mul, map_inv]
    group
  have hterm : ∀ r, (F ∣[k] β r) ∣[k] W = F ∣[k] β (σ r) := by
    intro r
    rw [← SlashAction.slash_mul, hδeq r, SlashAction.slash_mul, hF _ (hδ r)]
  rw [SlashAction.sum_slash]
  simp only [hterm]
  exact Fintype.sum_bijective σ (Finite.injective_iff_bijective.mp hinj) _ _ (fun r => rfl)

/-! ### Descent of `Γ₁(L)`-invariant forms, old space -/

/-- A cusp form of level `N` invariant under `Γ₁(L)` is a cusp form of level `L`. -/
def descendCF {L N : ℕ} [NeZero L] [NeZero N] {k : ℤ} (g : S1 N k)
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma1 L → ⇑g ∣[k] mapGL ℝ γ = ⇑g) : S1 L k where
  toFun := ⇑g
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    exact hg γ₀ hγ₀
  holo' := CuspFormClass.holo g
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps g
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (G1 L)).mp hc))

lemma inclCF_descendCF {L N : ℕ} [NeZero L] [NeZero N] (hLN : L ∣ N) {k : ℤ} (g : S1 N k)
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma1 L → ⇑g ∣[k] mapGL ℝ γ = ⇑g) :
    Level.inclCF hLN k (descendCF g hg) = g :=
  DFunLike.coe_injective rfl

/-- A form of level `N` invariant under `Γ₁(N/p)` (`p ∣ N` prime) is old. -/
theorem mem_oldSpace_of_inv {N p : ℕ} [NeZero N] (hp : p ∈ N.primeFactors) {k : ℤ} (g : S1 N k)
    (hg : ∀ γ : SL(2, ℤ), γ ∈ Gamma1 (N / p) → ⇑g ∣[k] mapGL ℝ γ = ⇑g) : g ∈ oldSpace N k := by
  haveI : NeZero (N / p) := neZero_div hp
  have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp
  have h := inclP_mem_oldSpace hp (descendCF g hg)
  rwa [inclP_eq N k hpN, inclCF_descendCF] at h

/-- Every Atkin-Lehner operator preserves the old space. -/
theorem alOp_mem_oldSpace {N Q : ℕ} [NeZero N] (D : RP.AtkinLehner.ALData N Q) (k : ℤ) {g : S1 N k}
    (hg : g ∈ oldSpace N k) : D.alOp k g ∈ oldSpace N k := by
  have key : ∀ (ℓ : ℕ) (hℓ : ℓ ∈ N.primeFactors) (h : S1 N k),
      h ∈ LinearMap.range (Level.inclCF (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hℓ)) k) ⊔
        LinearMap.range (MainLemma.iotaP N ℓ k) → D.alOp k h ∈ oldSpace N k := by
    intro ℓ hℓ h hh
    have hℓp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
    have hℓN : ℓ ∣ N := Nat.dvd_of_mem_primeFactors hℓ
    haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
    haveI : NeZero (N / ℓ) := neZero_div hℓ
    have hML : ℓ * (N / ℓ) = N := Nat.mul_div_cancel' hℓN
    have hℓLM : ℓ * (N / ℓ) ∣ N := ⟨1, by rw [mul_one, hML]⟩
    rw [MainLemma.iotaP_eq N k hℓp hℓN] at hh
    have hsub : LinearMap.range (Level.inclCF (Nat.div_dvd_of_dvd hℓN) k) ⊔
        LinearMap.range (Level.iotaCF ℓ hℓLM k) ≤ oldSpace N k := by
      refine sup_le ?_ ?_
      · rintro _ ⟨h', rfl⟩
        have := inclP_mem_oldSpace hℓ h'
        rwa [inclP_eq N k hℓN] at this
      · rintro _ ⟨h', rfl⟩
        have := iotaP_mem_oldSpace hℓ h'
        rw [MainLemma.iotaP_eq N k hℓp hℓN] at this
        exact this
    exact hsub (D.alOp_mem_old hℓp hML (Nat.div_dvd_of_dvd hℓN) hℓLM k hh)
  refine map_mem_oldSpace (D.alOp k) (fun ℓ hℓ g' => ?_) (fun ℓ hℓ g' => ?_) hg
  · refine key ℓ hℓ _ (Submodule.mem_sup_left ?_)
    rw [inclP_eq N k (Nat.dvd_of_mem_primeFactors hℓ)]
    exact LinearMap.mem_range_self _ _
  · exact key ℓ hℓ _ (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))

/-! ### Characters factoring through `L` -/

lemma trivOn_of_factorsThrough {N L : ℕ} (hLN : L ∣ N) {χ : DirichletCharacter ℂ N}
    (h : χ.FactorsThrough L) :
    ∀ u : (ZMod N)ˣ, ZMod.castHom hLN (ZMod L) (u : ZMod N) = 1 → χ u = 1 := by
  obtain ⟨h', χ₀, rfl⟩ := h
  intro u hu
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hu' : (ZMod.cast (u : ZMod N) : ZMod L) = 1 := hu
  rw [hu', map_one]

/-- A `χ`-form with `χ` trivial on units `≡ 1 mod L` is invariant under `Γ₀(N) ∩ Γ₁(L)`. -/
theorem slash_eq_of_chi {N L : ℕ} (hLN : L ∣ N) {k : ℤ} {χ : DirichletCharacter ℂ N}
    (hχ : ∀ u : (ZMod N)ˣ, ZMod.castHom hLN (ZMod L) (u : ZMod N) = 1 → χ u = 1)
    {g : S1 N k} (hg : g ∈ chiSubspace k χ) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 N ⊓ Gamma1 L) :
    ⇑g ∣[k] mapGL ℝ δ = ⇑g := by
  have h := hg δ hδ.1
  have hχ1 : χ ((δ 1 1 : ℤ) : ZMod N) = 1 := by
    have := hχ (unitMap N ⟨δ, hδ.1⟩) (by
      show ZMod.castHom hLN (ZMod L) ((δ 1 1 : ℤ) : ZMod N) = 1
      rw [map_intCast]
      exact ((Gamma1_mem L δ).1 hδ.2).2.1)
    exact this
  rw [hχ1, one_smul] at h
  exact h

/-- A nonzero multiple of a newform is never old. -/
theorem eq_zero_of_smul_mem_old {N : ℕ} [NeZero N] {k : ℤ} {χ : DirichletCharacter ℂ N} {f : S1 N k}
    (hf : IsNewform χ f) {c : ℂ} (h : c • f ∈ oldSpace N k) : c = 0 := by
  have h0 : c • f = 0 := eq_zero_of_mem_old_new h (Submodule.smul_mem _ c hf.mem_new)
  have h1 := coeff_smul_Gamma1 k c f 1
  rw [h0, hf.coeff_one, mul_one] at h1
  have hz := coeff_smul_Gamma1 k 0 (0 : S1 N k) 1
  rw [zero_smul, zero_mul] at hz
  rw [← h1, hz]

/-! ### (a) `p² ∣ N`: `U_p` lands in level `N / p` -/

theorem heckeFun_slash_of_dvd {N L p : ℕ} [NeZero N] [Fact p.Prime] (hpL : p ∣ L) (hN : p * L = N)
    {k : ℤ} (g : S1 N k)
    (hg : ∀ δ : SL(2, ℤ), δ ∈ Gamma0 N ⊓ Gamma1 L → ⇑g ∣[k] mapGL ℝ δ = ⇑g)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 L) :
    heckeFun p k g ∣[k] mapGL ℝ γ = heckeFun p k g := by
  have hpN : p ∣ N := ⟨L, hN.symm⟩
  have hg1 := (Gamma1_mem L γ).1 hγ
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).1 hg1.2.2
  rw [heckeFun_eq_sum_dvd k hpN]
  refine sum_slash_perm _ _ (Gamma0 N ⊓ Gamma1 L) ?_ ?_ k _ hg
  · intro j
    set A : Matrix (Fin 2) (Fin 2) ℤ := repU p j * (γ : Matrix (Fin 2) (Fin 2) ℤ) with hA
    have hA10 : A 1 0 = (p : ℤ) * γ 1 0 := by
      rw [hA, Matrix.mul_apply, Fin.sum_univ_two]; simp [repU]
    have hA00 : A 0 0 = γ 0 0 + (j : ℤ) * γ 1 0 := by
      rw [hA, Matrix.mul_apply, Fin.sum_univ_two]; simp [repU]
    have hAD : IsDelta L p A := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hA, Matrix.det_mul, det_repU, Matrix.SpecialLinearGroup.det_coe, mul_one]
      · rw [hA10]; push_cast; rw [hg1.2.2, mul_zero]
      · rw [hA00]; push_cast; rw [hg1.1, hg1.2.2, mul_zero, add_zero]
    obtain ⟨s, hs, hc⟩ := exists_condU hAD.1 (not_condInf_of_dvd hpL hAD)
    obtain ⟨δ, hδ1, hδA⟩ := factor_U hAD hc
    refine ⟨⟨s, hs⟩, δ, ⟨?_, hδ1⟩, ?_⟩
    · have h10 : (δ 1 0 : ℤ) = A 1 0 := by
        have := congrFun (congrFun hδA 1) 0
        simpa [repU, Matrix.mul_apply, Fin.sum_univ_two] using this
      show δ ∈ Gamma0 N
      rw [Gamma0_mem, h10, hA10, ht]
      have : ((p : ℤ) * ((L : ℤ) * t) : ℤ) = (N : ℤ) * t := by
        rw [← mul_assoc]; exact_mod_cast congrArg (fun n : ℕ => (n : ℤ) * t) hN
      rw [this]; push_cast; rw [ZMod.natCast_self, zero_mul]
    · rw [toGL_mul_mapGL, mapGL_mul_toGL]
      exact toGL_congr _ _ hδA.symm
  · intro r s δ _ h
    rw [mapGL_mul_toGL] at h
    have h' := toGL_injective _ _ _ _ h
    have hr : CondU p (repU p r) r := by simpa using condU_of_mul (p := p) (1 : Matrix (Fin 2) (Fin 2) ℤ) r
    have hs : CondU p (repU p r) s := by rw [h']; exact condU_of_mul _ s
    exact Fin.ext (condU_unique (det_repU p r) r.isLt s.isLt hr hs)

/-- **Li (a)**: if `p² ∣ N` and `χ` is defined mod `N / p`, then `a_p(f) = 0` for every newform `f`. -/
theorem coeff_prime_eq_zero_of_sq_dvd {N p : ℕ} [NeZero N] [hp : Fact p.Prime] (hp2 : p ^ 2 ∣ N)
    {k : ℤ} {χ : DirichletCharacter ℂ N} (hχ : χ.FactorsThrough (N / p)) {f : S1 N k}
    (hf : IsNewform χ f) : (qExpansion 1 f).coeff p = 0 := by
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p two_ne_zero) hp2
  have hpmem : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hp.out, hpN, NeZero.ne N⟩
  have hLN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have hpL : p ∣ N / p := Nat.dvd_div_of_mul_dvd (by rw [← pow_two]; exact hp2)
  have hN : p * (N / p) = N := Nat.mul_div_cancel' hpN
  have htriv := trivOn_of_factorsThrough hLN hχ
  have hinv : ∀ γ : SL(2, ℤ), γ ∈ Gamma1 (N / p) →
      ⇑(heckeT p k f) ∣[k] mapGL ℝ γ = ⇑(heckeT p k f) := fun γ hγ =>
    heckeFun_slash_of_dvd hpL hN f (slash_eq_of_chi hLN htriv hf.mem_chi) hγ
  have hold := mem_oldSpace_of_inv hpmem _ hinv
  rw [hf.heckeT_eq_of_dvd p hpN] at hold
  exact eq_zero_of_smul_mem_old hf hold

end RP.LiTrace


