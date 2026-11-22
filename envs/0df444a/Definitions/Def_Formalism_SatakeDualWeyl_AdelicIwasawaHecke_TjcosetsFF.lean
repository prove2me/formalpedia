-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:18.144936+00:00
-- url     : https://prove2.me/theorems/adf0f0fb-3321-45e6-ae5a-02f606c095cb
-- title:
--   Tjcosets FF
-- statement:
--   Definitions and structural lemmas for Tjcosets FF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.UG.P
section FF
variable {𝔽 : Type} [Field 𝔽]
def TjcosetsFr (m n : ℕ) (𝔽 : Type) : Type := Fin m → Fin n → 𝔽
instance tjcosets_act (m n : ℕ) : MulAction (GL (Fin n) 𝔽) (TjcosetsFr m n 𝔽) where
  smul g w := fun i => (g : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i
  one_smul w := by
    show (fun i => ((1 : GL (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i) = w
    funext i
    simp
  mul_smul g h w := by
    show (fun i => ((g * h : GL (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i) =
      (fun i => (g : Matrix (Fin n) (Fin n) 𝔽) *ᵥ ((h : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i))
    funext i
    simp [Matrix.mulVec_mulVec]
def tjcosets_idx (n j : ℕ) (i : Fin (n - j)) : Fin n := ⟨j + i, by omega⟩
def standardBasisTuple (n j : ℕ) : TjcosetsFr (n - j) n 𝔽 := fun i => Pi.single (tjcosets_idx n j i) 1
def tjcosets_parMon (n j : ℕ) : Submonoid (GL (Fin n) 𝔽) where
  carrier := {g | ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin n) (Fin n) 𝔽) a b = 0}
  one_mem' := by
    intro a b ha hb
    have : a ≠ b := by intro h; subst h; omega
    simp [this]
  mul_mem' := by
    intro g h hg hh a b ha hb
    simp only [Units.val_mul, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : (c : ℕ) < j
    · rw [hh c b hc hb, mul_zero]
    · rw [hg a c ha (by omega), zero_mul]
theorem tjcosets_inv_mem_of_finite {G : Type} [Group G] [Finite G] (S : Submonoid G) {x : G}
    (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpos := (isOfFinOrder_of_finite x).orderOf_pos
  have e : x ^ (orderOf x - 1) = x⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one])
  rw [← e]
  exact S.pow_mem hx _
def tjcosets_par [Finite 𝔽] (n j : ℕ) : Subgroup (GL (Fin n) 𝔽) :=
  { tjcosets_parMon n j with
    inv_mem' := fun hx => tjcosets_inv_mem_of_finite _ hx }
theorem tjcosets_idx_sub (n j : ℕ) (b : Fin n) (hb : j ≤ (b : ℕ)) :
    tjcosets_idx n j ⟨b - j, by omega⟩ = b := by
  ext
  simp only [tjcosets_idx]
  omega
def tjcosets_ext (n j : ℕ) : (Fin (n - j) → 𝔽) →ₗ[𝔽] (Fin n → 𝔽) where
  toFun u a := if h : j ≤ (a : ℕ) then u ⟨a - j, by omega⟩ else 0
  map_add' x y := by funext a; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by funext a; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp
def tjcosets_pr (n j : ℕ) : (Fin n → 𝔽) →ₗ[𝔽] (Fin (n - j) → 𝔽) where
  toFun x c := x (tjcosets_idx n j c)
  map_add' x y := rfl
  map_smul' c x := rfl
theorem tjcosets_pr_ext (n j : ℕ) (u : Fin (n - j) → 𝔽) :
    tjcosets_pr n j (tjcosets_ext n j u) = u := by
  funext c
  simp [tjcosets_pr, tjcosets_ext, tjcosets_idx]
theorem tjcosets_ext_pr (n j : ℕ) (x : Fin n → 𝔽) (hx : ∀ a : Fin n, (a : ℕ) < j → x a = 0) :
    tjcosets_ext n j (tjcosets_pr n j x) = x := by
  funext a
  simp only [tjcosets_pr, tjcosets_ext, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · rw [tjcosets_idx_sub n j a h]
  · exact (hx a (by omega)).symm
def tjcosets_equiv (n j : ℕ) :
    {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽) ∧
        ∀ i (a : Fin n), (a : ℕ) < j → w i a = 0} ≃
      {u : Fin (n - j) → Fin (n - j) → 𝔽 // LinearIndependent 𝔽 u} where
  toFun w := ⟨tjcosets_pr n j ∘ w.1, by
    have h : (w.1 : Fin (n - j) → Fin n → 𝔽) = tjcosets_ext n j ∘ (tjcosets_pr n j ∘ w.1) := by
      funext i; exact (tjcosets_ext_pr n j _ (w.2.2 i)).symm
    exact LinearIndependent.of_comp (tjcosets_ext n j) (by rw [← h]; exact w.2.1)⟩
  invFun u := ⟨tjcosets_ext n j ∘ u.1, u.2.map' _ (LinearMap.ker_eq_bot.mpr (fun _ _ h => by
      have := congrArg (tjcosets_pr n j) h
      simpa [tjcosets_pr_ext] using this)), fun i a ha => by
      simp only [Function.comp_apply, tjcosets_ext, LinearMap.coe_mk, AddHom.coe_mk]
      rw [dif_neg (by omega)]⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact tjcosets_ext_pr n j _ (w.2.2 i)
  right_inv u := by
    apply Subtype.ext
    funext i
    exact tjcosets_pr_ext n j _
end FF
end Formalism.UG.P


