-- Prove2me | Definitions.Def_RPLib_S1_Diamond
-- name    : RPLib_S1_Diamond
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:14:08.758194+00:00
-- url     : https://prove2.me/theorems/b5e2d597-68ff-413e-bd33-29fa63026f4d
-- title:
--   Diamond operators and the nebentypus decomposition of $S_k(\Gamma_1(M))$
-- statement:
--   For $M \ge 1$ and $d \in (\mathbb{Z}/M\mathbb{Z})^\times$ the diamond operator $\langle d\rangle$ acts on $S_k(\Gamma_1(M))$ by $f \mapsto f|_k\gamma$ for any $\gamma \in \Gamma_0(M)$ with lower-right entry $\equiv d \pmod M$. For a Dirichlet character $\chi$ modulo $M$ let $$S_k(M,\chi) = \{ f : f|_k\gamma = \chi(d_\gamma) f \text{ for all } \gamma \in \Gamma_0(M)\}.$$ The file constructs the diamond action as a group homomorphism, the projections onto the $\chi$-eigenspaces, and proves $S_k(\Gamma_1(M)) = \bigoplus_\chi S_k(M,\chi)$, with $S_k(M,\chi) = 0$ unless $\chi(-1) = (-1)^k$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.2

import Mathlib

/-!
# S1-DIAMOND: diamond operators and the nebentypus decomposition of `S_k(Γ₁(M))`

Namespace `RamanujanPetersson.Diamond`, `import Mathlib` only.

* (a) `unitMap M : Gamma0 M →* (ZMod M)ˣ` (`γ ↦ γ₁₁ mod M`), `mem_Gamma1_iff`, `conj_mem_Gamma1`,
  `Gamma1_subgroupOf_eq_ker`, `Gamma1_normal_Gamma0`, `unitMap_surjective`.
* (b) `slashG0 k γ : S1 M k → S1 M k` (slash by `γ ∈ Γ₀(M)`), `coe_slashG0`, `slashG0L` (linear),
  `slashG0_one`, `slashG0_mul`, `slashG0_congr` / `slashG0_congr'` (only `γ₁₁ mod M` matters).
* (c) `diamond k : (ZMod M)ˣ →* (S1 M k →ₗ[ℂ] S1 M k)`, `diamond_unitMap`, `coe_diamond_of_mem`,
  `diamond_neg_one`.
* (d) `chiSubspace k χ = {f | ∀ γ ∈ Γ₀(M), f ∣[k] γ = χ(γ₁₁) • f}` (the exact N2 form), `mem_chiSubspace_iff_diamond`,
  `chiSubspace_eq_iInf_eigenspace`, `map_mem_chiSubspace_of_commute`.
* (e) `proj k χ = φ(M)⁻¹ • Σ_d χ(d⁻¹) • ⟨d⟩`, `proj_mem`, `proj_eq_self`, `proj_eq_zero`, `sum_proj`,
  `chiSubspace_disjoint`, `iSup_chiSubspace_eq_top`, `iSupIndep_chiSubspace`, `isInternal_chiSubspace`.
* (f) `chiSubspace_eq_bot_of_parity`: `S_k(M, χ) = 0` unless `χ(-1) = (-1)^k`.
-/

open UpperHalfPlane ModularForm MatrixGroups CongruenceSubgroup ConjAct
open scoped Pointwise

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Diamond

variable {M : ℕ}

/-! ### (a) The unit map `Γ₀(M) → (ZMod M)ˣ` and normality of `Γ₁(M)` -/

/-- `γ ↦ (γ₁₁ mod M)` as a group homomorphism `Γ₀(M) →* (ZMod M)ˣ`. -/
def unitMap (M : ℕ) : Gamma0 M →* (ZMod M)ˣ := (Gamma0Map M).toHomUnits

@[simp] lemma coe_unitMap (γ : Gamma0 M) :
    ((unitMap M γ : (ZMod M)ˣ) : ZMod M) = (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := rfl

lemma mem_Gamma1_iff (A : SL(2, ℤ)) :
    A ∈ Gamma1 M ↔ ∃ h : A ∈ Gamma0 M, unitMap M ⟨A, h⟩ = 1 := by
  constructor
  · intro hA
    refine ⟨Gamma1_in_Gamma0 M hA, Units.ext ?_⟩
    rw [coe_unitMap, Units.val_one]
    exact ((Gamma1_mem M A).1 hA).2.1
  · rintro ⟨h, h1⟩
    have h1' : ((A 1 1 : ℤ) : ZMod M) = 1 := by
      have := congrArg Units.val h1
      rwa [coe_unitMap, Units.val_one] at this
    have hk : (⟨A, h⟩ : Gamma0 M) ∈ Gamma1' M := by
      rw [Gamma1_mem']
      exact h1'
    rw [Gamma1_to_Gamma0_mem] at hk
    exact (Gamma1_mem M A).2 hk

lemma conj_mem_Gamma1 {γ a : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (ha : a ∈ Gamma1 M) :
    γ * a * γ⁻¹ ∈ Gamma1 M := by
  obtain ⟨ha0, ha1⟩ := (mem_Gamma1_iff a).1 ha
  have h0 : γ * a * γ⁻¹ ∈ Gamma0 M := mul_mem (mul_mem hγ ha0) (inv_mem hγ)
  refine (mem_Gamma1_iff _).2 ⟨h0, ?_⟩
  have : (⟨γ * a * γ⁻¹, h0⟩ : Gamma0 M) = ⟨γ, hγ⟩ * ⟨a, ha0⟩ * (⟨γ, hγ⟩ : Gamma0 M)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, ha1, mul_one, mul_inv_cancel]

/-- `Γ₁(M)` is the kernel of `unitMap`. -/
theorem Gamma1_subgroupOf_eq_ker (M : ℕ) : (Gamma1 M).subgroupOf (Gamma0 M) = (unitMap M).ker := by
  ext γ
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_Gamma1_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨γ.2, h⟩⟩

/-- `Γ₁(M)` is normal in `Γ₀(M)`. -/
theorem Gamma1_normal_Gamma0 (M : ℕ) : ((Gamma1 M).subgroupOf (Gamma0 M)).Normal := by
  rw [Gamma1_subgroupOf_eq_ker]
  exact (unitMap M).normal_ker

/-- Every unit mod `M` is `γ₁₁ mod M` for some `γ ∈ Γ₀(M)`. -/
theorem unitMap_surjective [NeZero M] : Function.Surjective (unitMap M) := by
  intro d
  set n : ℕ := (d : ZMod M).val with hn
  have hcop : Nat.Coprime n M := ZMod.val_coe_unit_coprime d
  obtain ⟨u, v, huv⟩ : IsCoprime (n : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  let γ : SL(2, ℤ) := ⟨!![u, -v; (M : ℤ), (n : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination huv⟩
  have hγ : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [γ]
  refine ⟨⟨γ, hγ⟩, Units.ext ?_⟩
  rw [coe_unitMap]
  simp only [γ, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_natCast, hn, ZMod.natCast_zmod_val]

/-- A chosen lift of a unit mod `M` to `Γ₀(M)`. -/
def lift0 [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M := (unitMap_surjective (M := M) d).choose

@[simp] lemma unitMap_lift0 [NeZero M] (d : (ZMod M)ˣ) : unitMap M (lift0 d) = d :=
  (unitMap_surjective (M := M) d).choose_spec

/-! ### (b) Slash by `Γ₀(M)` on `S_k(Γ₁(M))` -/

/-- `Γ₁(M)` as a subgroup of `GL(2, ℝ)`. -/
abbrev G1 (M : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-- `S_k(Γ₁(M))`. -/
abbrev S1 (M : ℕ) (k : ℤ) : Type := CuspForm (G1 M) k

lemma G1_le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    G1 M ≤ toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • G1 M := by
  rintro _ ⟨x, hx, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  exact ⟨γ * x * γ⁻¹, conj_mem_Gamma1 hγ hx, by simp [map_mul, map_inv]⟩

lemma slash_Gamma1 (k : ℤ) (f : S1 M k) {γ : SL(2, ℤ)} (h : γ ∈ Gamma1 M) : ⇑f ∣[k] γ = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, h, rfl⟩

/-- Slash by `γ ∈ Γ₀(M)` maps `S_k(Γ₁(M))` to itself. -/
def slashG0 (k : ℤ) (γ : Gamma0 M) (f : S1 M k) : S1 M k :=
  let F2 := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)))
  { toFun := F2
    slash_action_eq' := fun j hj => SlashInvariantFormClass.slash_action_eq F2 j (G1_le_conj γ.2 hj)
    holo' := CuspFormClass.holo F2
    zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps F2 (hc.mono (G1_le_conj γ.2)) }

@[simp] lemma coe_slashG0 (k : ℤ) (γ : Gamma0 M) (f : S1 M k) :
    ⇑(slashG0 k γ f) = ⇑f ∣[k] (γ : SL(2, ℤ)) := rfl

lemma slashG0_apply (k : ℤ) (γ : Gamma0 M) (f : S1 M k) (τ : ℍ) :
    slashG0 k γ f τ = (⇑f ∣[k] (γ : SL(2, ℤ))) τ := rfl

lemma slashG0_one (k : ℤ) (f : S1 M k) : slashG0 k 1 f = f :=
  DFunLike.coe_injective (by rw [coe_slashG0]; exact SlashAction.slash_one k _)

lemma slashG0_mul (k : ℤ) (γ δ : Gamma0 M) (f : S1 M k) :
    slashG0 k (γ * δ) f = slashG0 k δ (slashG0 k γ f) :=
  DFunLike.coe_injective (by simp only [coe_slashG0, Subgroup.coe_mul, SlashAction.slash_mul])

lemma slashG0_of_mem_Gamma1 (k : ℤ) (γ : Gamma0 M) (h : (γ : SL(2, ℤ)) ∈ Gamma1 M) (f : S1 M k) :
    slashG0 k γ f = f :=
  DFunLike.coe_injective (by rw [coe_slashG0]; exact slash_Gamma1 k f h)

/-- The slash by `γ ∈ Γ₀(M)` depends only on `unitMap γ = γ₁₁ mod M`. -/
theorem slashG0_congr (k : ℤ) (γ δ : Gamma0 M) (h : unitMap M γ = unitMap M δ) (f : S1 M k) :
    slashG0 k γ f = slashG0 k δ f := by
  have hε : ((δ * γ⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ Gamma1 M := by
    rw [mem_Gamma1_iff]
    refine ⟨(δ * γ⁻¹).2, ?_⟩
    show unitMap M (δ * γ⁻¹) = 1
    rw [map_mul, map_inv, ← h, mul_inv_cancel]
  apply DFunLike.coe_injective
  rw [coe_slashG0, coe_slashG0]
  have hδ : (δ : SL(2, ℤ)) = ((δ * γ⁻¹ : Gamma0 M) : SL(2, ℤ)) * (γ : SL(2, ℤ)) := by
    simp
  rw [hδ, SlashAction.slash_mul, slash_Gamma1 k f hε]

theorem slashG0_congr' (k : ℤ) (γ δ : Gamma0 M)
    (h : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = (((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)) (f : S1 M k) :
    slashG0 k γ f = slashG0 k δ f :=
  slashG0_congr k γ δ (Units.ext h) f

/-- `slashG0` as a `ℂ`-linear endomorphism of `S_k(Γ₁(M))`. -/
def slashG0L (k : ℤ) (γ : Gamma0 M) : S1 M k →ₗ[ℂ] S1 M k where
  toFun := slashG0 k γ
  map_add' f g := DFunLike.coe_injective (by
    simp only [coe_slashG0, FunLike.coe_add, SlashAction.add_slash])
  map_smul' c f := DFunLike.coe_injective (by
    simp only [coe_slashG0, FunLike.coe_smul, SL_smul_slash, RingHom.id_apply])

@[simp] lemma slashG0L_apply (k : ℤ) (γ : Gamma0 M) (f : S1 M k) : slashG0L k γ f = slashG0 k γ f :=
  rfl

/-! ### (c) Diamond operators -/

section diamond

variable [NeZero M]

/-- The diamond operators `d ↦ ⟨d⟩`, a group hom `(ZMod M)ˣ →* End(S_k(Γ₁(M)))`;
`⟨d⟩ f = f ∣[k] γ` for any `γ ∈ Γ₀(M)` with `γ₁₁ ≡ d mod M`. -/
def diamond (k : ℤ) : (ZMod M)ˣ →* (S1 M k →ₗ[ℂ] S1 M k) where
  toFun d := slashG0L k (lift0 d)
  map_one' := LinearMap.ext fun f => by
    show slashG0 k (lift0 1) f = f
    rw [slashG0_congr k (lift0 1) 1 (by rw [unitMap_lift0, map_one]), slashG0_one]
  map_mul' d e := LinearMap.ext fun f => by
    show slashG0 k (lift0 (d * e)) f = slashG0 k (lift0 d) (slashG0 k (lift0 e) f)
    rw [← slashG0_mul]
    refine slashG0_congr k _ _ ?_ f
    simp only [map_mul, unitMap_lift0]
    exact mul_comm d e

lemma diamond_apply (k : ℤ) (d : (ZMod M)ˣ) (f : S1 M k) : diamond k d f = slashG0 k (lift0 d) f :=
  rfl

theorem diamond_unitMap (k : ℤ) (γ : Gamma0 M) (f : S1 M k) :
    diamond k (unitMap M γ) f = slashG0 k γ f :=
  slashG0_congr k (lift0 (unitMap M γ)) γ (unitMap_lift0 _) f

/-- `⟨d⟩ f = f ∣[k] γ` for every `γ ∈ Γ₀(M)` with `γ₁₁ ≡ d mod M`. -/
theorem coe_diamond_of_mem (k : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (d : (ZMod M)ˣ)
    (hd : (d : ZMod M) = ((γ 1 1 : ℤ) : ZMod M)) (f : S1 M k) :
    ⇑(diamond k d f) = ⇑f ∣[k] γ := by
  have : d = unitMap M ⟨γ, hγ⟩ := Units.ext hd
  rw [this, diamond_unitMap, coe_slashG0]

theorem diamond_commute (k : ℤ) (d e : (ZMod M)ˣ) : Commute (diamond k d) (diamond k e) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

lemma diamond_apply_of_mem_Gamma1 (k : ℤ) {γ : SL(2, ℤ)} (h : γ ∈ Gamma1 M) (f : S1 M k) :
    diamond k (unitMap M ⟨γ, Gamma1_in_Gamma0 M h⟩) f = f := by
  rw [diamond_unitMap, slashG0_of_mem_Gamma1 k _ h]

end diamond

/-! ### (d) The `χ`-subspaces `S_k(M, χ)` -/

/-- `S_k(M, χ) = {f ∈ S_k(Γ₁(M)) | ∀ γ ∈ Γ₀(M), f ∣[k] γ = χ(γ₁₁) • f}` (the exact form used in N2). -/
def chiSubspace (k : ℤ) (χ : DirichletCharacter ℂ M) : Submodule ℂ (S1 M k) where
  carrier := {f | ∀ γ ∈ Gamma0 M, (⇑f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod M) • ⇑f}
  add_mem' {f g} hf hg γ hγ := by
    rw [FunLike.coe_add, SlashAction.add_slash, hf γ hγ, hg γ hγ, smul_add]
  zero_mem' γ hγ := by
    rw [FunLike.coe_zero, SlashAction.zero_slash, smul_zero]
  smul_mem' c f hf γ hγ := by
    rw [FunLike.coe_smul, SL_smul_slash, hf γ hγ, smul_comm]

lemma mem_chiSubspace_iff (k : ℤ) (χ : DirichletCharacter ℂ M) (f : S1 M k) :
    f ∈ chiSubspace k χ ↔ ∀ γ ∈ Gamma0 M, (⇑f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod M) • ⇑f :=
  Iff.rfl

section diamondChi

variable [NeZero M]

/-- `S_k(M, χ)` is the simultaneous `χ(d)`-eigenspace of all diamond operators. -/
theorem mem_chiSubspace_iff_diamond (k : ℤ) (χ : DirichletCharacter ℂ M) (f : S1 M k) :
    f ∈ chiSubspace k χ ↔ ∀ d : (ZMod M)ˣ, diamond k d f = χ (d : ZMod M) • f := by
  constructor
  · intro hf d
    have h := hf _ (lift0 d).2
    have hd : ((((lift0 d : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = d := by
      rw [← coe_unitMap, unitMap_lift0]
    apply DFunLike.coe_injective
    rw [diamond_apply, coe_slashG0, h, hd, FunLike.coe_smul]
  · intro h γ hγ
    have h2 := congrArg DFunLike.coe (h (unitMap M ⟨γ, hγ⟩))
    rw [diamond_unitMap, coe_slashG0, FunLike.coe_smul, coe_unitMap] at h2
    exact h2

theorem chiSubspace_eq_iInf_eigenspace (k : ℤ) (χ : DirichletCharacter ℂ M) :
    chiSubspace k χ = ⨅ d : (ZMod M)ˣ, Module.End.eigenspace (diamond k d) (χ (d : ZMod M)) := by
  ext f
  rw [Submodule.mem_iInf, mem_chiSubspace_iff_diamond]
  simp only [Module.End.mem_eigenspace_iff]

theorem diamond_mem_chiSubspace (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (d : (ZMod M)ˣ) : diamond k d f ∈ chiSubspace k χ := by
  rw [(mem_chiSubspace_iff_diamond k χ f).1 hf d]
  exact Submodule.smul_mem _ _ hf

/-- A linear map commuting with all diamond operators preserves every `S_k(M, χ)`. -/
theorem map_mem_chiSubspace_of_commute (k : ℤ) (T : S1 M k →ₗ[ℂ] S1 M k)
    (hT : ∀ d : (ZMod M)ˣ, Commute T (diamond k d)) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) : T f ∈ chiSubspace k χ := by
  rw [mem_chiSubspace_iff_diamond]
  intro d
  rw [← Module.End.mul_apply, ← (hT d).eq, Module.End.mul_apply,
    (mem_chiSubspace_iff_diamond k χ f).1 hf d, map_smul]

/-- Two different characters give subspaces meeting only in `0`. -/
theorem chiSubspace_disjoint (k : ℤ) {χ ψ : DirichletCharacter ℂ M} (h : χ ≠ ψ) :
    Disjoint (chiSubspace k χ) (chiSubspace k ψ) := by
  rw [Submodule.disjoint_def]
  intro f hχ hψ
  obtain ⟨d, hd⟩ : ∃ d : (ZMod M)ˣ, χ (d : ZMod M) ≠ ψ (d : ZMod M) := by
    by_contra hcon
    push Not at hcon
    exact h (MulChar.ext hcon)
  have e1 := (mem_chiSubspace_iff_diamond k χ f).1 hχ d
  have e2 := (mem_chiSubspace_iff_diamond k ψ f).1 hψ d
  have : (χ (d : ZMod M) - ψ (d : ZMod M)) • f = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hd)

end diamondChi

/-! ### (e) Projectors and the decomposition `S_k(Γ₁(M)) = ⨁_χ S_k(M, χ)` -/

section proj

variable [NeZero M]

lemma totient_ne_zero' : (M.totient : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos M)).ne'

omit [NeZero M] in
lemma chi_inv_mul (χ : DirichletCharacter ℂ M) (d : (ZMod M)ˣ) :
    χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) * χ (d : ZMod M) = 1 := by
  rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

/-- The projector `e_χ = φ(M)⁻¹ Σ_d χ(d)⁻¹ ⟨d⟩` onto `S_k(M, χ)`. -/
def proj (k : ℤ) (χ : DirichletCharacter ℂ M) : S1 M k →ₗ[ℂ] S1 M k :=
  ((M.totient : ℂ)⁻¹) • ∑ d : (ZMod M)ˣ, χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond k d

theorem proj_apply (k : ℤ) (χ : DirichletCharacter ℂ M) (f : S1 M k) :
    proj k χ f = ((M.totient : ℂ)⁻¹) •
      ∑ d : (ZMod M)ˣ, χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond k d f := by
  simp only [proj, LinearMap.smul_apply, LinearMap.sum_apply]

theorem diamond_proj (k : ℤ) (χ : DirichletCharacter ℂ M) (e : (ZMod M)ˣ) (f : S1 M k) :
    diamond k e (proj k χ f) = χ (e : ZMod M) • proj k χ f := by
  have hs : ∑ d : (ZMod M)ˣ, χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond k e (diamond k d f) =
      ∑ d : (ZMod M)ˣ, χ (e : ZMod M) • χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond k d f := by
    refine Fintype.sum_equiv (Equiv.mulLeft e)
      (fun d => χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond k e (diamond k d f))
      (fun d => χ (e : ZMod M) • χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond k d f) (fun d => ?_)
    simp only [Equiv.coe_mulLeft, smul_smul]
    rw [← Module.End.mul_apply, ← (diamond k).map_mul]
    congr 1
    rw [← map_mul, ← Units.val_mul, mul_inv, mul_inv_cancel_left]
  rw [proj_apply, map_smul, map_sum]
  simp only [map_smul]
  rw [hs, ← Finset.smul_sum, smul_comm]

theorem proj_mem (k : ℤ) (χ : DirichletCharacter ℂ M) (f : S1 M k) : proj k χ f ∈ chiSubspace k χ :=
  (mem_chiSubspace_iff_diamond k χ _).2 fun e => diamond_proj k χ e f

theorem proj_mem_of_mem (k : ℤ) (χ : DirichletCharacter ℂ M) {ψ : DirichletCharacter ℂ M}
    {f : S1 M k} (hf : f ∈ chiSubspace k ψ) : proj k χ f ∈ chiSubspace k ψ := by
  rw [proj_apply]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (diamond_mem_chiSubspace k hf d))

theorem proj_eq_self (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : f ∈ chiSubspace k χ) :
    proj k χ f = f := by
  rw [proj_apply]
  have : ∀ d : (ZMod M)ˣ, χ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond k d f = f := by
    intro d
    rw [(mem_chiSubspace_iff_diamond k χ f).1 hf d, smul_smul, chi_inv_mul, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ totient_ne_zero', one_smul]

theorem proj_eq_zero (k : ℤ) {χ ψ : DirichletCharacter ℂ M} (h : χ ≠ ψ) {f : S1 M k}
    (hf : f ∈ chiSubspace k ψ) : proj k χ f = 0 :=
  Submodule.disjoint_def.1 (chiSubspace_disjoint k h) _ (proj_mem k χ f) (proj_mem_of_mem k χ hf)

theorem proj_idem (k : ℤ) (χ : DirichletCharacter ℂ M) (f : S1 M k) :
    proj k χ (proj k χ f) = proj k χ f :=
  proj_eq_self k (proj_mem k χ f)

/-- `Σ_χ e_χ = id` (orthogonality of Dirichlet characters). -/
theorem sum_proj (k : ℤ) (f : S1 M k) : ∑ χ : DirichletCharacter ℂ M, proj k χ f = f := by
  simp only [proj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [Finset.sum_eq_single (1 : (ZMod M)ˣ)]
  · rw [inv_one, Units.val_one, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl, map_one,
      Module.End.one_apply, smul_smul, inv_mul_cancel₀ totient_ne_zero', one_smul]
  · intro d _ hd
    rw [DirichletCharacter.sum_characters_eq ℂ, if_neg, zero_smul]
    rwa [Units.val_eq_one, inv_eq_one]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem iSup_chiSubspace_eq_top (k : ℤ) : ⨆ χ : DirichletCharacter ℂ M, chiSubspace k χ = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [← sum_proj k f]
  exact Submodule.sum_mem _ fun χ _ => Submodule.mem_iSup_of_mem χ (proj_mem k χ f)

theorem iSupIndep_chiSubspace (k : ℤ) :
    iSupIndep (fun χ : DirichletCharacter ℂ M => chiSubspace k χ) := by
  rw [iSupIndep_def]
  intro χ
  rw [Submodule.disjoint_def]
  intro f hf hsup
  have hle : (⨆ (ψ : DirichletCharacter ℂ M) (_ : ψ ≠ χ), chiSubspace k ψ) ≤
      LinearMap.ker (proj k χ) :=
    iSup₂_le fun ψ hψ g hg => LinearMap.mem_ker.2 (proj_eq_zero k (Ne.symm hψ) hg)
  have h0 : proj k χ f = 0 := LinearMap.mem_ker.1 (hle hsup)
  rwa [proj_eq_self k hf] at h0

/-- `S_k(Γ₁(M)) = ⨁_χ S_k(M, χ)`. -/
theorem isInternal_chiSubspace (k : ℤ) [DecidableEq (DirichletCharacter ℂ M)] :
    DirectSum.IsInternal (fun χ : DirichletCharacter ℂ M => chiSubspace k χ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_chiSubspace k)
    (iSup_chiSubspace_eq_top k)

end proj

/-! ### (f) Parity: `S_k(M, χ) = 0` unless `χ(-1) = (-1)^k` -/

lemma neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 M := by
  rw [Gamma0_mem]; simp

lemma mapGL_neg_one : Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) = -1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

lemma neg_one_zpow_neg' (k : ℤ) : (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg.neg_one_zpow]
  · rw [hk.neg_one_zpow, hk.neg.neg_one_zpow]

lemma slash_neg_one (k : ℤ) (F : ℍ → ℂ) : F ∣[k] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ k) • F := by
  change F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ))) = _
  rw [mapGL_neg_one]
  ext τ
  have hdet : ((-1 : GL (Fin 2) ℝ).det.val) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; simp [Matrix.det_neg]
  rw [slash_apply, UpperHalfPlane.neg_smul, one_smul, denom_neg, denom_one, σ,
    if_pos (by rw [hdet]; norm_num), ContinuousAlgEquiv.refl_apply, hdet, abs_one, Complex.ofReal_one, one_zpow,
    mul_one, Pi.smul_apply, smul_eq_mul, neg_one_zpow_neg', mul_comm]

lemma diamond_neg_one [NeZero M] (k : ℤ) (f : S1 M k) : diamond k (-1) f = ((-1 : ℂ) ^ k) • f := by
  apply DFunLike.coe_injective
  rw [coe_diamond_of_mem k neg_one_mem_Gamma0 (-1) (by simp), slash_neg_one, FunLike.coe_smul]

/-- `S_k(M, χ) = 0` unless `χ(-1) = (-1)^k`. -/
theorem chiSubspace_eq_bot_of_parity (k : ℤ) (χ : DirichletCharacter ℂ M)
    (h : χ (-1) ≠ (-1 : ℂ) ^ k) : chiSubspace k χ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have h1 := hf (-1) neg_one_mem_Gamma0
  rw [slash_neg_one] at h1
  have h2 : ((((-1 : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M) = -1 := by simp
  rw [h2] at h1
  have h3 : (χ (-1) - (-1 : ℂ) ^ k) • (⇑f) = 0 := by rw [sub_smul, ← h1, sub_self]
  have h4 : ⇑f = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h)
  apply DFunLike.coe_injective
  rw [h4, FunLike.coe_zero]

theorem mem_chiSubspace_parity (k : ℤ) (χ : DirichletCharacter ℂ M) {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (hf0 : f ≠ 0) : χ (-1) = (-1 : ℂ) ^ k := by
  by_contra h
  rw [chiSubspace_eq_bot_of_parity k χ h, Submodule.mem_bot] at hf
  exact hf0 hf

end RamanujanPetersson.Diamond


