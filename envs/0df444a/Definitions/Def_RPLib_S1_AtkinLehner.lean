-- Prove2me | Definitions.Def_RPLib_S1_AtkinLehner
-- name    : RPLib_S1_AtkinLehner
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:31:03.199084+00:00
-- url     : https://prove2.me/theorems/1dcdfb81-8a0a-4d44-b8c3-8349dd5dbe29
-- title:
--   Atkin-Lehner operators: commutation with $T_p$ and action on oldforms
-- statement:
--   With $W_Q$ the Atkin-Lehner operator on $S_k(\Gamma_1(M))$, the file proves $W_Q T_p = T_p\langle v\rangle W_Q$ for primes $p \nmid M$ and computes $W_Q$ on $\mathrm{incl}\,S_k(\Gamma_1(L))$ and $\iota_\ell S_k(\Gamma_1(L))$ for $\ell L = M$. In particular, for a prime $\ell$, $W_Q$ preserves $$\mathrm{incl}\, S_k(\Gamma_1(L)) + \iota_\ell\, S_k(\Gamma_1(L)).$$
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. O. L. Atkin and J. Lehner, Hecke operators on Gamma_0(m), Math. Ann. 185 (1970) 134-160, doi:10.1007/BF01359701; W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285-315, doi:10.1007/BF01344468

import Mathlib
import Definitions.Def_RPLib_S1_AtkinLehnerA

/-!
# S1-WOPS: Atkin-Lehner operators `W_Q` and the Fricke involution `W_M` on `S_k(Γ₁(M))`

Part A (`AtkinLehner_A`): the data, conjugation mod `M`, the twist, the operator `alOp`, and
(1) `W ⟨u⟩ = ⟨twist u⟩ W`, (2) `W S(M, χ) ⊆ S(M, χ ∘ twist)`, (3) `W² = Q^(k-2) ⟨d⟩`, (4) unitarity.
This file: the twist mod `Q` / mod `Q'`, (5) `W T_p = T_p ⟨v⟩ W` for `p ∤ M`, and (6) `W` on `incl` and
`ι_ℓ` from level `L` (`ℓ L = M`), so `W` preserves `incl S_k(Γ₁(L)) + ι_ℓ S_k(Γ₁(L))` for prime `ℓ`.
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup ConjAct
open scoped MatrixGroups Pointwise

noncomputable section

namespace RP.AtkinLehner

open RamanujanPetersson RamanujanPetersson.Diamond RP.Petersson
open Matrix.SpecialLinearGroup (mapGL mapGL_coe_matrix)

variable {M Q : ℕ}

/-! ### Integer matrices in `GL(2, ℝ)` -/

lemma coe_toGL_eq (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    ((Hecke.toGL A hA : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix A := by
  ext i j
  rw [Hecke.toGL_apply]
  simp

lemma coe_mapGL_eq (γ : SL(2, ℤ)) :
    ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Int.castRingHom ℝ).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [mapGL_coe_matrix]
  ext i j
  simp

lemma coe_dg_eq (d : ℕ) [NeZero d] :
    ((Level.dg d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Int.castRingHom ℝ).mapMatrix !![(d : ℤ), 0; 0, 1] := by
  rw [Level.dg_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma coe_scalar_dg_eq (d : ℕ) [NeZero d] :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Level.dg d).det : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix !![(d : ℤ), 0; 0, (d : ℤ)] := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Level.dg_det]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.natCast_apply]

lemma coe_mul_eq {g h : GL (Fin 2) ℝ} {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix A)
    (hh : (h : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix B) :
    ((g * h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix (A * B) := by
  rw [Units.val_mul, hg, hh, map_mul]

lemma real_smul_slash_of_det_pos (k : ℤ) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (r : ℝ)
    (F : ℍ → ℂ) : (r • F) ∣[k] g = r • (F ∣[k] g) := by
  have h : ∀ G : ℍ → ℂ, r • G = (r : ℂ) • G := fun G => by
    ext τ; simp [Complex.real_smul]
  rw [h, h, Hecke.smul_slash_of_det_pos k g hg]

lemma coe_iotaCF (d : ℕ) [NeZero d] {L N : ℕ} (h : d * L ∣ N) (k : ℤ) (f : S1 L k) :
    ⇑(Level.iotaCF d h k f) = ((d : ℝ) ^ (1 - k)) • (⇑f ∣[k] Level.dg d) := rfl

lemma cpow_smul_real_smul (ℓ : ℕ) [NeZero ℓ] (k : ℤ) (F : ℍ → ℂ) :
    ((ℓ : ℂ) ^ (k - 1)) • (((ℓ : ℝ) ^ (1 - k)) • F) = F := by
  ext τ
  have hℓ : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  rw [← mul_assoc, ← zpow_add₀ hℓ, show k - 1 + (1 - k) = 0 by ring, zpow_zero, one_mul]

lemma real_smul_cpow_smul (ℓ : ℕ) [NeZero ℓ] (k : ℤ) (F : ℍ → ℂ) :
    ((ℓ : ℝ) ^ (1 - k)) • ((((ℓ : ℝ) : ℂ)) ^ (k - 2) • F) = ((ℓ : ℂ)⁻¹) • F := by
  ext τ
  have hℓ : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  rw [← mul_assoc, ← zpow_add₀ hℓ, show 1 - k + (k - 2) = -1 by ring, zpow_neg_one]

/-! ### A reindexing lemma for sums of slashes -/

/-- If `β_r W = X δ_r β_{σ r}` with `δ_r ∈ Γ₁(M)`, `X Γ₁ X⁻¹ ⊆ SL₂(ℤ)` and the `β_r` are distinct
modulo `SL₂(ℤ)`, then `(Σ F ∣ β_r) ∣ W = Σ (F ∣ X) ∣ β_r` for `F ∣ X` invariant under `Γ₁(M)`. -/
theorem sum_slash_reindex {R : Type*} [Fintype R] (β : R → GL (Fin 2) ℝ) (W X : GL (Fin 2) ℝ)
    (hE : ∀ r, ∃ s, ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧ β r * W = X * mapGL ℝ δ * β s)
    (hX : ∀ δ : SL(2, ℤ), δ ∈ Gamma1 M → ∃ δ' : SL(2, ℤ), X * mapGL ℝ δ * X⁻¹ = mapGL ℝ δ')
    (hU : ∀ r s (δ : SL(2, ℤ)), β r = mapGL ℝ δ * β s → r = s)
    (k : ℤ) (F G : ℍ → ℂ) (hFG : F ∣[k] X = G)
    (hG : ∀ δ : SL(2, ℤ), δ ∈ Gamma1 M → G ∣[k] mapGL ℝ δ = G) :
    (∑ r, F ∣[k] β r) ∣[k] W = ∑ r, G ∣[k] β r := by
  choose σ δ hδ1 hδeq using hE
  have hinj : Function.Injective σ := by
    intro r r' h
    obtain ⟨δ', hδ'⟩ := hX (δ r * (δ r')⁻¹) (mul_mem (hδ1 r) (inv_mem (hδ1 r')))
    apply hU r r' δ'
    have e1 : β r = X * mapGL ℝ (δ r) * β (σ r) * W⁻¹ := by rw [← hδeq r]; group
    have e2 : β (σ r') = (X * mapGL ℝ (δ r'))⁻¹ * (β r' * W) := by rw [hδeq r']; group
    rw [e1, h, e2, ← hδ', map_mul, map_inv]
    group
  have hterm : ∀ r, (F ∣[k] β r) ∣[k] W = G ∣[k] β (σ r) := by
    intro r
    rw [← SlashAction.slash_mul, hδeq r, SlashAction.slash_mul, SlashAction.slash_mul, hFG,
      hG _ (hδ1 r)]
  rw [SlashAction.sum_slash]
  simp only [hterm]
  exact Fintype.sum_bijective σ (Finite.injective_iff_bijective.mp hinj) _ _ (fun r => rfl)

namespace ALData

/-! ### The twist and the `Q`-part, mod `Q` and mod `Q'` -/

lemma dvd_Q (D : ALData M Q) : Q ∣ M := ⟨D.Q', D.hM.symm⟩

lemma dvd_Q' (D : ALData M Q) : D.Q' ∣ M := Dvd.intro_left Q D.hM

lemma eQ'_cast_Q (D : ALData M Q) : ZMod.castHom D.dvd_Q (ZMod Q) D.eQ' = 0 := by
  rw [eQ', map_intCast]
  push_cast
  rw [ZMod.natCast_self, zero_mul, zero_mul]

lemma eQ'_cast_Q' (D : ALData M Q) : ZMod.castHom D.dvd_Q' (ZMod D.Q') D.eQ' = 1 := by
  rw [eQ', map_intCast]
  have h := congrArg (fun t : ℤ => (t : ZMod D.Q')) D.hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one, ZMod.natCast_self,
    zero_mul, sub_zero] at h
  push_cast
  linear_combination h

/-- `twist u ≡ u⁻¹ mod Q`. -/
lemma twist_cast_Q (D : ALData M Q) (u : (ZMod M)ˣ) :
    ZMod.castHom D.dvd_Q (ZMod Q) (D.twist u : ZMod M) =
      ZMod.castHom D.dvd_Q (ZMod Q) ((u⁻¹ : (ZMod M)ˣ) : ZMod M) := by
  rw [coe_twist, map_add, map_mul, map_mul, map_sub, map_one, eQ'_cast_Q]
  ring

/-- `twist u ≡ u mod Q'`. -/
lemma twist_cast_Q' (D : ALData M Q) (u : (ZMod M)ˣ) :
    ZMod.castHom D.dvd_Q' (ZMod D.Q') (D.twist u : ZMod M) =
      ZMod.castHom D.dvd_Q' (ZMod D.Q') (u : ZMod M) := by
  rw [coe_twist, map_add, map_mul, map_mul, map_sub, map_one, eQ'_cast_Q']
  ring

/-- `partQ u ≡ u mod Q`. -/
lemma partQ_cast_Q (D : ALData M Q) (u : (ZMod M)ˣ) :
    ZMod.castHom D.dvd_Q (ZMod Q) (D.partQ u : ZMod M) = ZMod.castHom D.dvd_Q (ZMod Q) (u : ZMod M) := by
  rw [coe_partQ, map_add, map_mul, map_sub, map_one, eQ'_cast_Q]
  ring

/-- `partQ u ≡ 1 mod Q'`. -/
lemma partQ_cast_Q' (D : ALData M Q) (u : (ZMod M)ˣ) :
    ZMod.castHom D.dvd_Q' (ZMod D.Q') (D.partQ u : ZMod M) = 1 := by
  rw [coe_partQ, map_add, map_mul, map_sub, map_one, eQ'_cast_Q']
  ring

lemma frickeD_partQ (M : ℕ) (u : (ZMod M)ˣ) : (frickeD M).partQ u = u :=
  Units.ext (by rw [coe_partQ, frickeD_eQ']; ring)

section ops

variable [NeZero M] (D : ALData M Q)

lemma coe_gl_eq : ((D.gl : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix D.mat :=
  coe_toGL_eq _ _

lemma alOp_congr {E : ALData M Q} (h : D.mat = E.mat) (k : ℤ) (f : S1 M k) : D.alOp k f = E.alOp k f := by
  apply DFunLike.coe_injective
  rw [coe_alOp, coe_alOp, show D.gl = E.gl from Hecke.toGL_congr _ _ h]

/-! ### (5) `W T_p = T_p ⟨v⟩ W` for `p ∤ M` -/

lemma exists_heckeT_factor {p : ℕ} [Fact p.Prime] (hpM : ¬ p ∣ M) (x y : ℤ) (hxy : x * p - y * M = 1)
    {σ : SL(2, ℤ)} (hσ0 : σ ∈ Gamma0 M)
    (hσ11 : ((σ 1 1 : ℤ) : ZMod M) = (((D.partQ (Hecke.unitP hpM))⁻¹ : (ZMod M)ˣ) : ZMod M))
    (r : Option (Fin p)) :
    ∃ s, ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      Adjoint.rhoP M p x y hxy r * D.gl = D.gl * mapGL ℝ σ * mapGL ℝ δ * Adjoint.rhoP M p x y hxy s := by
  obtain ⟨hdetB, h10, h00⟩ := Hecke.isDelta_betaOpt x y hxy r
  obtain ⟨B', hBB, hdet', h10', h00', h11'⟩ := D.exists_back (Hecke.betaOpt M p x y r) h10
  have h11 : ((Hecke.betaOpt M p x y r 1 1 : ℤ) : ZMod M) = p := by
    have h := hdetB
    rw [Matrix.det_fin_two] at h
    have h' := congrArg (fun t : ℤ => (t : ZMod M)) h
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at h'
    rw [h10, h00] at h'
    linear_combination h'
  have hσ10 : ((σ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 hσ0
  have hw : ((D.partQ (Hecke.unitP hpM) : (ZMod M)ˣ) : ZMod M) = D.eQ' * 1 + (1 - D.eQ') * p := by
    rw [coe_partQ, ZMod.coe_unitOfCoprime]; ring
  have hinv := Units.inv_mul (D.partQ (Hecke.unitP hpM))
  have hA : Hecke.IsDelta M p (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * B') := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, hdet', hdetB]
    · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast
      rw [hσ10, h10']
      ring
    · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast
      rw [h10', h00', hσ11, h00, h11]
      linear_combination hinv - (((D.partQ (Hecke.unitP hpM))⁻¹ : (ZMod M)ˣ) : ZMod M) * hw
  obtain ⟨s, δ, hδ, hfac⟩ := Adjoint.exists_betaOpt_factor x y hxy hA
  refine ⟨s, δ, hδ, ?_⟩
  have hB'eq : B' = (σ : Matrix (Fin 2) (Fin 2) ℤ) *
      ((δ : Matrix (Fin 2) (Fin 2) ℤ) * Hecke.betaOpt M p x y s) := by
    rw [hfac, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  unfold Adjoint.rhoP
  apply Units.ext
  rw [coe_mul_eq (coe_toGL_eq _ _) (coe_gl_eq D),
    coe_mul_eq (coe_mul_eq (coe_mul_eq (coe_gl_eq D) (coe_mapGL_eq σ)) (coe_mapGL_eq δ))
      (coe_toGL_eq _ _), hBB, hB'eq]
  simp only [Matrix.mul_assoc]

/-- **(5)** `W T_p = T_p ⟨v⟩ W` for `p ∤ M`, `v = (Q-part of p)⁻¹` (`≡ p⁻¹ mod Q`, `≡ 1 mod Q'`). -/
theorem alOp_heckeT (k : ℤ) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (f : S1 M k) :
    D.alOp k (Hecke.heckeT p k f) =
      Hecke.heckeT p k (diamond k (D.partQ (Hecke.unitP hpM))⁻¹ (D.alOp k f)) := by
  apply DFunLike.coe_injective
  obtain ⟨x, y, hxy⟩ := Adjoint.exists_xy (M := M) hpM
  obtain ⟨σ, hσ0, hσ11⟩ : ∃ σ : SL(2, ℤ), σ ∈ Gamma0 M ∧
      ((σ 1 1 : ℤ) : ZMod M) = (((D.partQ (Hecke.unitP hpM))⁻¹ : (ZMod M)ˣ) : ZMod M) :=
    ⟨((lift0 (D.partQ (Hecke.unitP hpM))⁻¹ : Gamma0 M) : SL(2, ℤ)), (lift0 _).2,
      congrArg Units.val (unitMap_lift0 _)⟩
  rw [coe_alOp, Hecke.coe_heckeT, Hecke.coe_heckeT, Hecke.heckeFun_eq_sum_ndvd k hpM x y hxy,
    Hecke.heckeFun_eq_sum_ndvd k hpM x y hxy]
  refine sum_slash_reindex (Adjoint.rhoP M p x y hxy) D.gl (D.gl * mapGL ℝ σ)
    (D.exists_heckeT_factor hpM x y hxy hσ0 hσ11) ?_ (Adjoint.rhoP_unique x y hxy) k _ _ ?_
    (fun δ hδ => slash_Gamma1 k (diamond k (D.partQ (Hecke.unitP hpM))⁻¹ (D.alOp k f)) hδ)
  · intro δ hδ
    obtain ⟨δ', -, he⟩ := D.exists_fwd_Gamma1 (conj_mem_Gamma1 hσ0 hδ)
    refine ⟨δ', ?_⟩
    have e : D.gl * mapGL ℝ σ * mapGL ℝ δ * (D.gl * mapGL ℝ σ)⁻¹ =
        D.gl * mapGL ℝ (σ * δ * σ⁻¹) * D.gl⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e, he]; group
  · rw [SlashAction.slash_mul, ← coe_alOp]
    exact (coe_diamond_of_mem k hσ0 _ hσ11.symm (D.alOp k f)).symm

/-- **(5')** On `S_k(M, χ)`: `W (T_p f) = χ(Q-part of p) • T_p (W f)`. -/
theorem alOp_heckeT_chi (k : ℤ) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) {χ : DirichletCharacter ℂ M}
    {f : S1 M k} (hf : f ∈ chiSubspace k χ) :
    D.alOp k (Hecke.heckeT p k f) =
      χ (D.partQ (Hecke.unitP hpM) : ZMod M) • Hecke.heckeT p k (D.alOp k f) := by
  have hW := (mem_chiSubspace_iff_diamond k _ _).1 (D.alOp_mem_chiSubspace k hf)
  rw [alOp_heckeT, hW, map_smul, twistChar_apply, twist_partQ_inv]

/-- **Fricke and `T_p`**: `W_M T_p = T_p ⟨p⟩⁻¹ W_M` for `p ∤ M`. -/
theorem frickeD_alOp_heckeT (k : ℤ) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (f : S1 M k) :
    (frickeD M).alOp k (Hecke.heckeT p k f) =
      Hecke.heckeT p k (diamond k (Hecke.unitP hpM)⁻¹ ((frickeD M).alOp k f)) := by
  rw [alOp_heckeT, frickeD_partQ]

end ops

/-! ### (6) `W` on old forms from level `L` (`ℓ L = M`) -/

/-- Case `ℓ ∣ Q'` (`Q' = ℓ Q₁'`, `L = Q Q₁'`): the same matrix, as data of level `L`. -/
def lowerA (D : ALData M Q) {L ℓ Q1 : ℕ} (hQ' : D.Q' = ℓ * Q1) (hL : Q * Q1 = L) : ALData L Q :=
  ⟨Q1, D.x, D.y, (ℓ : ℤ) * D.z, D.w, hL, by
    have h : (D.Q' : ℤ) = (ℓ : ℤ) * Q1 := by exact_mod_cast hQ'
    linear_combination D.hdet + D.y * D.z * h⟩

/-- Case `ℓ ∣ Q'`: `diag(ℓ, 1) A = A₂ diag(ℓ, 1)` with `A₂` of level `L` (`y ↦ ℓ y`). -/
def lowerA2 (D : ALData M Q) {L ℓ Q1 : ℕ} (hQ' : D.Q' = ℓ * Q1) (hL : Q * Q1 = L) : ALData L Q :=
  ⟨Q1, D.x, (ℓ : ℤ) * D.y, D.z, D.w, hL, by
    have h : (D.Q' : ℤ) = (ℓ : ℤ) * Q1 := by exact_mod_cast hQ'
    linear_combination D.hdet + D.y * D.z * h⟩

/-- Case `ℓ ∣ Q` (`Q = ℓ Q₁`, `L = Q₁ Q'`): `A = A' diag(ℓ, 1)` with `A'` of level `L` (`w ↦ ℓ w`). -/
def lowerB (D : ALData M Q) {L ℓ Q1 : ℕ} (hQ : Q = ℓ * Q1) (hL : Q1 * D.Q' = L) : ALData L Q1 :=
  ⟨D.Q', D.x, D.y, D.z, (ℓ : ℤ) * D.w, hL, by
    have h : (Q : ℤ) = (ℓ : ℤ) * Q1 := by exact_mod_cast hQ
    linear_combination D.hdet - D.x * D.w * h⟩

/-- Case `ℓ ∣ Q`: `diag(ℓ, 1) A = ℓ A''` with `A''` of level `L` (`x ↦ ℓ x`). -/
def lowerB2 (D : ALData M Q) {L ℓ Q1 : ℕ} (hQ : Q = ℓ * Q1) (hL : Q1 * D.Q' = L) : ALData L Q1 :=
  ⟨D.Q', (ℓ : ℤ) * D.x, D.y, D.z, D.w, hL, by
    have h : (Q : ℤ) = (ℓ : ℤ) * Q1 := by exact_mod_cast hQ
    linear_combination D.hdet - D.x * D.w * h⟩

section old

variable [NeZero M] (D : ALData M Q)

lemma gl_lowerA {L ℓ Q1 : ℕ} [NeZero L] (hQ' : D.Q' = ℓ * Q1) (hL : Q * Q1 = L) :
    (D.lowerA hQ' hL).gl = D.gl := by
  apply Units.ext
  rw [coe_gl_eq, coe_gl_eq]
  congr 1
  obtain ⟨Q', x, y, z, w, hM, hdet⟩ := D
  change Q' = ℓ * Q1 at hQ'
  subst hQ' hM hL
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mat, lowerA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> (try push_cast) <;> ring

lemma dg_mul_gl_lowerA2 {L ℓ Q1 : ℕ} [NeZero L] [NeZero ℓ] (hQ' : D.Q' = ℓ * Q1) (hL : Q * Q1 = L) :
    Level.dg ℓ * D.gl = (D.lowerA2 hQ' hL).gl * Level.dg ℓ := by
  apply Units.ext
  rw [coe_mul_eq (coe_dg_eq ℓ) (coe_gl_eq D), coe_mul_eq (coe_gl_eq _) (coe_dg_eq ℓ)]
  congr 1
  obtain ⟨Q', x, y, z, w, hM, hdet⟩ := D
  change Q' = ℓ * Q1 at hQ'
  subst hQ' hM hL
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mat, lowerA2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> (try push_cast) <;> ring

lemma gl_lowerB {L ℓ Q1 : ℕ} [NeZero L] [NeZero ℓ] (hQ : Q = ℓ * Q1) (hL : Q1 * D.Q' = L) :
    D.gl = (D.lowerB hQ hL).gl * Level.dg ℓ := by
  apply Units.ext
  rw [coe_gl_eq D, coe_mul_eq (coe_gl_eq _) (coe_dg_eq ℓ)]
  congr 1
  obtain ⟨Q', x, y, z, w, hM, hdet⟩ := D
  subst hQ hM hL
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mat, lowerB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> (try push_cast) <;> ring

lemma dg_mul_gl_lowerB2 {L ℓ Q1 : ℕ} [NeZero L] [NeZero ℓ] (hQ : Q = ℓ * Q1) (hL : Q1 * D.Q' = L) :
    Level.dg ℓ * D.gl =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Level.dg ℓ).det * (D.lowerB2 hQ hL).gl := by
  apply Units.ext
  rw [coe_mul_eq (coe_dg_eq ℓ) (coe_gl_eq D), coe_mul_eq (coe_scalar_dg_eq ℓ) (coe_gl_eq _)]
  congr 1
  obtain ⟨Q', x, y, z, w, hM, hdet⟩ := D
  subst hQ hM hL
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mat, lowerB2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> (try push_cast) <;> ring

/-- `ℓ ∣ Q'`: `W (incl f) = incl (W_L f)`. -/
theorem alOp_inclCF_lowerA {L ℓ Q1 : ℕ} [NeZero L] (hQ' : D.Q' = ℓ * Q1) (hL : Q * Q1 = L)
    (hLM : L ∣ M) (k : ℤ) (f : S1 L k) :
    D.alOp k (Level.inclCF hLM k f) = Level.inclCF hLM k ((D.lowerA hQ' hL).alOp k f) := by
  apply DFunLike.coe_injective
  rw [coe_alOp, Level.coe_inclCF, Level.coe_inclCF, coe_alOp, gl_lowerA]

/-- `ℓ ∣ Q'`: `W (ι_ℓ f) = ι_ℓ (W_L f)`. -/
theorem alOp_iotaCF_lowerA2 {L ℓ Q1 : ℕ} [NeZero L] [NeZero ℓ] (hQ' : D.Q' = ℓ * Q1)
    (hL : Q * Q1 = L) (hℓLM : ℓ * L ∣ M) (k : ℤ) (f : S1 L k) :
    D.alOp k (Level.iotaCF ℓ hℓLM k f) = Level.iotaCF ℓ hℓLM k ((D.lowerA2 hQ' hL).alOp k f) := by
  apply DFunLike.coe_injective
  rw [coe_alOp, coe_iotaCF, coe_iotaCF, coe_alOp, real_smul_slash_of_det_pos k _ D.gl_det_pos,
    ← SlashAction.slash_mul, ← SlashAction.slash_mul, D.dg_mul_gl_lowerA2 hQ' hL]

/-- `ℓ ∣ Q`: `W (incl f) = ℓ^(k-1) ι_ℓ (W_L f)`. -/
theorem alOp_inclCF_lowerB {L ℓ Q1 : ℕ} [NeZero L] [NeZero ℓ] (hQ : Q = ℓ * Q1)
    (hL : Q1 * D.Q' = L) (hLM : L ∣ M) (hℓLM : ℓ * L ∣ M) (k : ℤ) (f : S1 L k) :
    D.alOp k (Level.inclCF hLM k f) =
      ((ℓ : ℂ) ^ (k - 1)) • Level.iotaCF ℓ hℓLM k ((D.lowerB hQ hL).alOp k f) := by
  apply DFunLike.coe_injective
  rw [coe_alOp, Level.coe_inclCF, D.gl_lowerB hQ hL, SlashAction.slash_mul, FunLike.coe_smul,
    coe_iotaCF, coe_alOp, cpow_smul_real_smul]

/-- `ℓ ∣ Q`: `W (ι_ℓ f) = ℓ⁻¹ incl (W_L f)`. -/
theorem alOp_iotaCF_lowerB2 {L ℓ Q1 : ℕ} [NeZero L] [NeZero ℓ] (hQ : Q = ℓ * Q1)
    (hL : Q1 * D.Q' = L) (hLM : L ∣ M) (hℓLM : ℓ * L ∣ M) (k : ℤ) (f : S1 L k) :
    D.alOp k (Level.iotaCF ℓ hℓLM k f) =
      ((ℓ : ℂ)⁻¹) • Level.inclCF hLM k ((D.lowerB2 hQ hL).alOp k f) := by
  apply DFunLike.coe_injective
  rw [coe_alOp, coe_iotaCF, real_smul_slash_of_det_pos k _ D.gl_det_pos, ← SlashAction.slash_mul,
    D.dg_mul_gl_lowerB2 hQ hL, SlashAction.slash_mul, Adjoint.slash_scalar k _ (Level.dg_det_pos ℓ),
    Level.dg_det, Hecke.smul_slash_of_det_pos k _ (D.lowerB2 hQ hL).gl_det_pos, FunLike.coe_smul,
    Level.coe_inclCF, coe_alOp, real_smul_cpow_smul]

/-- **(6)** For a prime `ℓ` with `ℓ L = M`, `W` preserves `incl S_k(Γ₁(L)) + ι_ℓ S_k(Γ₁(L))`. -/
theorem alOp_mem_old {L ℓ : ℕ} [NeZero L] [NeZero ℓ] (hℓ : ℓ.Prime) (hML : ℓ * L = M) (hLM : L ∣ M)
    (hℓLM : ℓ * L ∣ M) (k : ℤ) {g : S1 M k}
    (hg : g ∈ LinearMap.range (Level.inclCF hLM k) ⊔ LinearMap.range (Level.iotaCF ℓ hℓLM k)) :
    D.alOp k g ∈ LinearMap.range (Level.inclCF hLM k) ⊔ LinearMap.range (Level.iotaCF ℓ hℓLM k) := by
  have hpos : 0 < ℓ := hℓ.pos
  have hdvd : ℓ ∣ Q * D.Q' := by rw [D.hM]; exact ⟨L, hML.symm⟩
  have hle : LinearMap.range (Level.inclCF hLM k) ⊔ LinearMap.range (Level.iotaCF ℓ hℓLM k) ≤
      (LinearMap.range (Level.inclCF hLM k) ⊔ LinearMap.range (Level.iotaCF ℓ hℓLM k)).comap
        (D.alOp k) := by
    rcases (Nat.Prime.dvd_mul hℓ).1 hdvd with ⟨Q1, hQ⟩ | ⟨Q1, hQ'⟩
    · have hL : Q1 * D.Q' = L :=
        Nat.eq_of_mul_eq_mul_left hpos (by rw [hML, ← mul_assoc, ← hQ, D.hM])
      refine sup_le ?_ ?_
      · rintro _ ⟨f, rfl⟩
        rw [Submodule.mem_comap, D.alOp_inclCF_lowerB hQ hL hLM hℓLM]
        exact Submodule.smul_mem _ _ (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
      · rintro _ ⟨f, rfl⟩
        rw [Submodule.mem_comap, D.alOp_iotaCF_lowerB2 hQ hL hLM hℓLM]
        exact Submodule.smul_mem _ _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
    · have hL : Q * Q1 = L :=
        Nat.eq_of_mul_eq_mul_left hpos (by rw [hML, mul_left_comm, ← hQ', D.hM])
      refine sup_le ?_ ?_
      · rintro _ ⟨f, rfl⟩
        rw [Submodule.mem_comap, D.alOp_inclCF_lowerA hQ' hL hLM]
        exact Submodule.mem_sup_left (LinearMap.mem_range_self _ _)
      · rintro _ ⟨f, rfl⟩
        rw [Submodule.mem_comap, D.alOp_iotaCF_lowerA2 hQ' hL hℓLM]
        exact Submodule.mem_sup_right (LinearMap.mem_range_self _ _)
  exact hle hg

end old

/-! ### Fricke on old forms: `W_M ∘ incl = ℓ^(k-1) ι_ℓ ∘ W_L`, `W_M ∘ ι_ℓ = ℓ⁻¹ incl ∘ W_L` -/

section frickeOld

variable [NeZero M]

lemma frickeD_lowerB_mat {L ℓ : ℕ} (hQ : M = ℓ * L) :
    ((frickeD M).lowerB hQ (mul_one L)).mat = (frickeD L).mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat, lowerB, frickeD]

lemma frickeD_lowerB2_mat {L ℓ : ℕ} (hQ : M = ℓ * L) :
    ((frickeD M).lowerB2 hQ (mul_one L)).mat = (frickeD L).mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat, lowerB2, frickeD]

/-- **Fricke on `incl`**: `W_M (incl f) = ℓ^(k-1) ι_ℓ (W_L f)` for `M = ℓ L`. -/
theorem frickeD_alOp_inclCF {L ℓ : ℕ} [NeZero L] [NeZero ℓ] (hML : M = ℓ * L) (hLM : L ∣ M)
    (hℓLM : ℓ * L ∣ M) (k : ℤ) (f : S1 L k) :
    (frickeD M).alOp k (Level.inclCF hLM k f) =
      ((ℓ : ℂ) ^ (k - 1)) • Level.iotaCF ℓ hℓLM k ((frickeD L).alOp k f) := by
  rw [alOp_inclCF_lowerB _ hML (mul_one L) hLM hℓLM, alOp_congr _ (frickeD_lowerB_mat hML)]

/-- **Fricke on `ι_ℓ`**: `W_M (ι_ℓ f) = ℓ⁻¹ incl (W_L f)` for `M = ℓ L`. -/
theorem frickeD_alOp_iotaCF {L ℓ : ℕ} [NeZero L] [NeZero ℓ] (hML : M = ℓ * L) (hLM : L ∣ M)
    (hℓLM : ℓ * L ∣ M) (k : ℤ) (f : S1 L k) :
    (frickeD M).alOp k (Level.iotaCF ℓ hℓLM k f) =
      ((ℓ : ℂ)⁻¹) • Level.inclCF hLM k ((frickeD L).alOp k f) := by
  rw [alOp_iotaCF_lowerB2 _ hML (mul_one L) hLM hℓLM, alOp_congr _ (frickeD_lowerB2_mat hML)]

end frickeOld

end ALData

end RP.AtkinLehner


