-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenMackeyNorm
-- name    : OddOrder_Peterfalvi_S11_NineElevenMackeyNorm
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:33:49.641071+00:00
-- url     : https://prove2.me/theorems/c047d687-faf5-4de4-8577-fc1638019a10
-- title:
--   Peterfalvi (9.11.4): the Mackey norm and support of $\alpha$
-- statement:
--   Formalizes Peterfalvi (9.11.4) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §9, pp. 56-57): the Mackey norm $\|\alpha\|^2=a+1+(q-1)a^2/u$ and $\mathrm{Supp}(\alpha)\subseteq A(M)$.
--
--   Main declarations: `sum_apply_mul_eq_zero_of_not_subset_characterKernel` (Coset sums of an irreducible character over a non-kernel normal subgroup vanish); `sum_subgroup_apply_eq_zero_of_not_subset_characterKernel` (Subgroup sums of an irreducible character vanish above a non-kernel normal subgroup); `nineElevenGamma_support` (`Supp(γ) ⊆ HU`); `nineElevenGamma_mem_ZIrr` (`γ ∈ ℤ[Irr M]`).
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenMackeyNorm.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenMackeyNorm.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTwoSummand

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

variable {M : Subgroup G}

section AveragingProjector

variable {Γ : Type*} [Group Γ] [Fintype Γ]

omit [Fintype Γ] in
/-- **Coset sums of an irreducible character over a non-kernel normal subgroup vanish**
(Peterfalvi (9.11.4), the `⟨γ, ψ₁⟩ = 0` engine): if `N ⊴ Γ`, `χ ∈ Irr Γ` and `N ⊄ Ker χ`,
then `Σ_{n ∈ N} χ(n·y) = 0` for every `y ∈ Γ`.  The averaging operator `T = Σ_{n∈N} ρ(n)`
on a representation `ρ` realizing `χ` is `Γ`-equivariant (conjugation permutes `N`), so its
range is a subrepresentation; `range T = ⊤` would force `ρ(n) = 1` for all `n ∈ N` (from
`ρ(n) ∘ T = T`), i.e. `N ⊆ Ker χ`; hence `range T = ⊥`, `T = 0`, and the coset sum is
`tr(T ∘ ρ(y)) = 0`. -/
theorem sum_apply_mul_eq_zero_of_not_subset_characterKernel (N : Subgroup Γ) [hN : N.Normal]
    [Fintype ↥N] {χ : ClassFunction Γ ℂ} (hχ : IsIrreducibleCharacter χ)
    (hker : ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)) (y : Γ) :
    ∑ n : ↥N, χ ((n : Γ) * y) = 0 := by
  classical
  obtain ⟨V, _, _, _, ρ, hirr, hchar⟩ := hχ
  -- the averaging operator `T = Σ_{n∈N} ρ(n)`
  set T : V →ₗ[ℂ] V := ∑ n : ↥N, ρ (n : Γ) with hT
  -- left multiplication by `ρ(n)` fixes `T`
  have hmulT : ∀ n : ↥N, ρ (n : Γ) * T = T := by
    intro n
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft n) _ _ fun m => ?_
    rw [← map_mul]
    rfl
  -- `Γ`-equivariance: `ρ(g) * T = T * ρ(g)`
  have hequiv : ∀ g : Γ, ρ g * T = T * ρ g := by
    intro g
    have hconj : ∀ n : ↥N, g * (n : Γ) * g⁻¹ ∈ N := fun n => hN.conj_mem _ n.2 g
    have hconj' : ∀ n : ↥N, g⁻¹ * (n : Γ) * g ∈ N := fun n => by
      have h := hN.conj_mem _ n.2 g⁻¹
      rwa [inv_inv] at h
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv
      ⟨fun n => ⟨g * (n : Γ) * g⁻¹, hconj n⟩, fun n => ⟨g⁻¹ * (n : Γ) * g, hconj' n⟩,
        fun n => Subtype.ext (by change g⁻¹ * (g * (n : Γ) * g⁻¹) * g = (n : Γ); group),
        fun n => Subtype.ext (by change g * (g⁻¹ * (n : Γ) * g) * g⁻¹ = (n : Γ); group)⟩
      _ _ fun n => ?_
    change ρ g * ρ (n : Γ) = ρ (g * (n : Γ) * g⁻¹) * ρ g
    rw [← map_mul, ← map_mul]
    congr 1
    group
  -- the range of `T` is a subrepresentation
  have : Representation.IsIrreducible ρ := hirr
  rcases eq_bot_or_eq_top
      ({ toSubmodule := LinearMap.range T
         apply_mem_toSubmodule := by
           intro g v hv
           obtain ⟨w, rfl⟩ := hv
           refine ⟨ρ g w, ?_⟩
           have h := congrArg (fun f : V →ₗ[ℂ] V => f w) (hequiv g)
           simpa [Module.End.mul_apply] using h.symm } : Subrepresentation ρ)
    with hbot | htop
  · -- `range T = ⊥`, so `T = 0` and the coset sum is a trace of `0`
    have hT0 : T = 0 := by
      have h := congrArg Subrepresentation.toSubmodule hbot
      exact LinearMap.range_eq_bot.mp h
    have hval : ∀ n : ↥N, χ ((n : Γ) * y) = LinearMap.trace ℂ V (ρ (n : Γ) * ρ y) := by
      intro n
      rw [congrFun hchar ((n : Γ) * y), ← map_mul]
      rfl
    rw [Finset.sum_congr rfl fun n _ => hval n, ← map_sum, ← Finset.sum_mul, ← hT, hT0,
      zero_mul, map_zero]
  · -- `range T = ⊤` would force `ρ(n) = 1` on `N`, i.e. `N ⊆ Ker χ`
    exfalso
    apply hker
    intro x hx
    have hxN : x ∈ N := hx
    have hrangeTop : LinearMap.range T = ⊤ := congrArg Subrepresentation.toSubmodule htop
    have hid : ∀ v : V, ρ x v = v := by
      intro v
      have hv : v ∈ LinearMap.range T := hrangeTop ▸ Submodule.mem_top
      obtain ⟨w, rfl⟩ := hv
      have h := congrArg (fun f : V →ₗ[ℂ] V => f w) (hmulT ⟨x, hxN⟩)
      simpa [Module.End.mul_apply] using h
    change χ x = OddOrder.Peterfalvi.S03.characterDegree χ
    change χ x = χ 1
    rw [congrFun hchar x, congrFun hchar 1]
    change LinearMap.trace ℂ V (ρ x) = LinearMap.trace ℂ V (ρ 1)
    congr 1
    rw [map_one]
    exact LinearMap.ext hid

omit [Fintype Γ] in
/-- **Subgroup sums of an irreducible character vanish above a non-kernel normal subgroup**:
if `N ⊴ Γ`, `N ≤ K`, `χ ∈ Irr Γ` and `N ⊄ Ker χ`, then `Σ_{y ∈ K} χ(y) = 0`.  Averaging the
left-translation reindexings `y ↦ n·y` of `↥K` over `n ∈ N` reduces to the coset-sum
vanishing `sum_apply_mul_eq_zero_of_not_subset_characterKernel`. -/
theorem sum_subgroup_apply_eq_zero_of_not_subset_characterKernel {N K : Subgroup Γ}
    [N.Normal] [Finite ↥N] [Fintype ↥K] (hNK : N ≤ K) {χ : ClassFunction Γ ℂ}
    (hχ : IsIrreducibleCharacter χ)
    (hker : ¬ ((N : Set Γ) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)) :
    ∑ y : ↥K, χ (y : Γ) = 0 := by
  classical
  have : Fintype ↥N := Fintype.ofFinite ↥N
  have hcard : ((Fintype.card ↥N : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  refine mul_left_cancel₀ hcard ?_
  rw [mul_zero]
  calc ((Fintype.card ↥N : ℕ) : ℂ) * ∑ y : ↥K, χ (y : Γ)
      = ∑ _n : ↥N, ∑ y : ↥K, χ (y : Γ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ n : ↥N, ∑ y : ↥K, χ ((n : Γ) * y) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        refine (Fintype.sum_equiv (Equiv.mulLeft (⟨(n : Γ), hNK n.2⟩ : ↥K)) _ _
          fun y => ?_).symm
        rfl
    _ = ∑ y : ↥K, ∑ n : ↥N, χ ((n : Γ) * y) := Finset.sum_comm
    _ = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        exact sum_apply_mul_eq_zero_of_not_subset_characterKernel N hχ hker (y : Γ)

/-- **The (9.11.4) orthogonality engine `⟨Ind_K^Γ 1, Ind_D^Γ ζ⟩ = 0`**: for normal `D ⊴ Γ`
and `N ⊴ Γ` with `N ≤ K ≤ D`, and an irreducible character `ζ` of `D` with `N ⊄ Ker ζ`
(realized inside `D`), the induced trivial character of `K` is orthogonal to `Ind_D^Γ ζ`.
Frobenius reciprocity turns the inner product into `Σ_{y ∈ K} (Ind_D^Γ ζ)(y)`; the induction
formula expands this into subgroup sums of `ζ` over the conjugates `x⁻¹Kx ⊆ D` — each of
which contains `N` (normality of `N` in `Γ`), so each vanishes by
`sum_subgroup_apply_eq_zero_of_not_subset_characterKernel`. -/
theorem inner_induce_trivial_induce_eq_zero [Invertible (Nat.card Γ : ℂ)]
    {D N K : Subgroup Γ} [hD : D.Normal] [hNn : N.Normal] [Finite ↥K] [Finite ↥D]
    [Invertible (Nat.card ↥K : ℂ)] [Invertible (Nat.card ↥D : ℂ)]
    (hNK : N ≤ K) (hKD : K ≤ D)
    {ζ : ClassFunction ↥D ℂ} (hζirr : IsIrreducibleCharacter ζ)
    (hker : ¬ ((N.subgroupOf D : Set ↥D) ⊆ OddOrder.Peterfalvi.S03.characterKernel ζ)) :
    ClassFunction.inner (ClassFunction.induce K (trivialClassFunction ↥K))
      (ClassFunction.induce D ζ) = 0 := by
  classical
  have : Fintype ↥K := Fintype.ofFinite ↥K
  have : Fintype ↥D := Fintype.ofFinite ↥D
  have : (N.subgroupOf D).Normal := hNn.subgroupOf D
  have : Fintype ↥(N.subgroupOf D) := Fintype.ofFinite _
  -- the subgroup sum `Σ_{y ∈ K} (Ind_D ζ)(y)` vanishes
  have hsum : ∑ y : ↥K, (ClassFunction.induce D ζ) (y : Γ) = 0 := by
    have hval : ∀ y : ↥K, (ClassFunction.induce D ζ) (y : Γ)
        = ⅟(Nat.card ↥D : ℂ) * ∑ x : Γ,
            ζ ⟨x⁻¹ * (y : Γ) * x, hD.conj_mem' _ (hKD y.2) x⟩ := by
      intro y
      rw [ClassFunction.induce_apply]
      congr 1
      exact Finset.sum_congr rfl fun x _ =>
        ClassFunction.induceTerm_of_mem ζ (hD.conj_mem' _ (hKD y.2) x)
    rw [Finset.sum_congr rfl fun y _ => hval y, ← Finset.mul_sum, Finset.sum_comm]
    have hinner : ∀ x : Γ,
        (∑ y : ↥K, ζ ⟨x⁻¹ * (y : Γ) * x, hD.conj_mem' _ (hKD y.2) x⟩) = 0 := by
      intro x
      -- the conjugate subgroup `x⁻¹Kx`, realized inside `D`
      have hmemK' : ∀ y : ↥K,
          (⟨x⁻¹ * (y : Γ) * x, hD.conj_mem' _ (hKD y.2) x⟩ : ↥D)
            ∈ (MulAut.conj x⁻¹ • K).subgroupOf D := by
        intro y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          ← map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply]
        change x * (x⁻¹ * (y : Γ) * x) * x⁻¹ ∈ K
        have hyy : x * (x⁻¹ * (y : Γ) * x) * x⁻¹ = (y : Γ) := by group
        rw [hyy]
        exact y.2
      have hmemK'' : ∀ z : ↥((MulAut.conj x⁻¹ • K).subgroupOf D),
          x * ((z : ↥D) : Γ) * x⁻¹ ∈ K := by
        intro z
        have hz := z.2
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          ← map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply] at hz
        exact hz
      have : Fintype ↥((MulAut.conj x⁻¹ • K).subgroupOf D) := Fintype.ofFinite _
      have hreindex : (∑ y : ↥K, ζ ⟨x⁻¹ * (y : Γ) * x, hD.conj_mem' _ (hKD y.2) x⟩)
          = ∑ z : ↥((MulAut.conj x⁻¹ • K).subgroupOf D), ζ (z : ↥D) := by
        exact Fintype.sum_equiv
          ⟨fun y => ⟨⟨x⁻¹ * (y : Γ) * x, hD.conj_mem' _ (hKD y.2) x⟩, hmemK' y⟩,
            fun z => ⟨x * ((z : ↥D) : Γ) * x⁻¹, hmemK'' z⟩,
            fun y => Subtype.ext (by
              change x * (x⁻¹ * (y : Γ) * x) * x⁻¹ = (y : Γ); group),
            fun z => Subtype.ext (Subtype.ext (by
              change x⁻¹ * (x * ((z : ↥D) : Γ) * x⁻¹) * x = ((z : ↥D) : Γ); group))⟩
          _ _ fun y => rfl
      rw [hreindex]
      refine sum_subgroup_apply_eq_zero_of_not_subset_characterKernel ?_ hζirr hker
      -- `N ≤ x⁻¹Kx` inside `D`: `x·n·x⁻¹ ∈ N ≤ K` by normality of `N` in `Γ`
      intro n hn
      rw [Subgroup.mem_subgroupOf] at hn
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        ← map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply]
      exact hNK (hNn.conj_mem _ hn x)
    rw [Finset.sum_congr rfl fun x _ => hinner x, Finset.sum_const, smul_zero, mul_zero]
  -- Frobenius reciprocity + folding in the vanishing subgroup sum
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
  have hfold : (∑ y : ↥K, trivialClassFunction ↥K y *
      star ((ClassFunction.restrict K (ClassFunction.induce D ζ)) y)) = 0 := by
    have hstep : ∀ y : ↥K, trivialClassFunction ↥K y *
        star ((ClassFunction.restrict K (ClassFunction.induce D ζ)) y)
        = star ((ClassFunction.induce D ζ) (y : Γ)) := by
      intro y
      rw [trivialClassFunction_apply, one_mul, ClassFunction.restrict_apply]
    rw [Finset.sum_congr rfl fun y _ => hstep y, ← star_sum, hsum, star_zero]
  rw [hfold, mul_zero]

end AveragingProjector

section MackeyCount

variable {Γ : Type*} [Group Γ] [Fintype Γ]

/-- **The norm of the induced trivial character as a conjugation count**:
`‖Ind_K^Γ 1‖²·|K|² = Σ_{x∈Γ} |K ∩ ˣK|`.  Frobenius reciprocity gives
`‖Ind 1‖² = (1/|K|)·Σ_{y∈K} (Ind 1)(y)`, and `(Ind 1)(y) = (1/|K|)·#{x | x⁻¹yx ∈ K}`; the
double count `Σ_{y∈K} #{x | x⁻¹yx ∈ K} = Σ_{x∈Γ} |K ∩ xKx⁻¹|` finishes.  This is
Peterfalvi (9.11.4)'s `‖γ‖²` double-coset count in unnormalized integer form. -/
theorem inner_induce_trivial_self_mul_card_sq [Invertible (Nat.card Γ : ℂ)]
    (K : Subgroup Γ) [Finite ↥K] [Invertible (Nat.card ↥K : ℂ)] :
    ClassFunction.inner (ClassFunction.induce K (trivialClassFunction ↥K))
        (ClassFunction.induce K (trivialClassFunction ↥K))
      * ((Nat.card ↥K : ℂ) * (Nat.card ↥K : ℂ))
      = ((∑ x : Γ, Nat.card ↥(K ⊓ MulAut.conj x • K) : ℕ) : ℂ) := by
  classical
  have : Fintype ↥K := Fintype.ofFinite ↥K
  -- the value of `Ind_K 1` at `y ∈ K` is `(1/|K|)·#{x | x⁻¹yx ∈ K}`
  have hval : ∀ y : ↥K,
      (ClassFunction.induce K (trivialClassFunction ↥K)) (y : Γ)
        = ⅟(Nat.card ↥K : ℂ) *
          (((Finset.univ.filter (fun x : Γ => x⁻¹ * (y : Γ) * x ∈ K)).card : ℕ) : ℂ) := by
    intro y
    rw [ClassFunction.induce_apply]
    congr 1
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x⁻¹ * (y : Γ) * x ∈ K
    · rw [ClassFunction.induceTerm_of_mem _ hx, if_pos hx, trivialClassFunction_apply]
    · rw [ClassFunction.induceTerm_of_not_mem _ hx, if_neg hx]
  -- Frobenius reciprocity and the `y`-sum
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
  have hterm : ∀ y : ↥K, trivialClassFunction ↥K y *
      star ((ClassFunction.restrict K
        (ClassFunction.induce K (trivialClassFunction ↥K))) y)
      = ⅟(Nat.card ↥K : ℂ) *
        (((Finset.univ.filter (fun x : Γ => x⁻¹ * (y : Γ) * x ∈ K)).card : ℕ) : ℂ) := by
    intro y
    rw [trivialClassFunction_apply, one_mul, ClassFunction.restrict_apply, hval y,
      invOf_eq_inv, star_mul', star_inv₀, star_natCast, star_natCast]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.mul_sum]
  -- clear the two `1/|K|` factors
  have hKne : (Nat.card ↥K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hclear : ⅟(Nat.card ↥K : ℂ) * (⅟(Nat.card ↥K : ℂ) *
        ∑ y : ↥K, (((Finset.univ.filter
          (fun x : Γ => x⁻¹ * (y : Γ) * x ∈ K)).card : ℕ) : ℂ))
      * ((Nat.card ↥K : ℂ) * (Nat.card ↥K : ℂ))
      = ∑ y : ↥K, (((Finset.univ.filter
          (fun x : Γ => x⁻¹ * (y : Γ) * x ∈ K)).card : ℕ) : ℂ) := by
    rw [invOf_eq_inv]
    field_simp
  rw [hclear]
  -- the double count: swap the `y`- and `x`-sums, then identify each `x`-fibre
  have hswap : (∑ y : ↥K,
        (Finset.univ.filter (fun x : Γ => x⁻¹ * (y : Γ) * x ∈ K)).card)
      = ∑ x : Γ, Nat.card ↥(K ⊓ MulAut.conj x • K) := by
    have hcount : ∀ y : ↥K,
        (Finset.univ.filter (fun x : Γ => x⁻¹ * (y : Γ) * x ∈ K)).card
          = ∑ x : Γ, if x⁻¹ * (y : Γ) * x ∈ K then 1 else 0 := by
      intro y
      rw [Finset.sum_boole, Nat.cast_id]
    rw [Finset.sum_congr rfl fun y _ => hcount y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    -- `#{y ∈ K | x⁻¹yx ∈ K} = |K ⊓ ˣK|`
    have hiff : ∀ y : ↥K, (x⁻¹ * (y : Γ) * x ∈ K) ↔ (y : Γ) ∈ MulAut.conj x • K := by
      intro y
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
        MulAut.conj_apply, inv_inv]
    rw [Finset.sum_congr rfl fun y _ => by rw [hiff y], Finset.sum_boole, Nat.cast_id,
      ← Fintype.card_subtype, Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      ⟨fun p => ⟨((p : ↥K) : Γ), ⟨(p : ↥K).2, p.2⟩⟩, fun z => ⟨⟨(z : Γ), z.2.1⟩, z.2.2⟩,
        fun p => by apply Subtype.ext; apply Subtype.ext; rfl,
        fun z => by apply Subtype.ext; rfl⟩
  rw [← hswap]
  push_cast
  rfl

/-- Conjugation by a member fixes the group: `k ∈ K → ᵏK = K`. -/
theorem conj_smul_eq_self_of_mem' {Γ : Type*} [Group Γ] {K : Subgroup Γ} {k : Γ}
    (hk : k ∈ K) : MulAut.conj k • K = K := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply]
  constructor
  · intro hx
    have hxx : x = k * (k⁻¹ * x * k⁻¹⁻¹) * k⁻¹ := by group
    rw [hxx]
    exact K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
  · intro hx
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) hx) (K.inv_mem (K.inv_mem hk))

/-- Cardinality of `K ∩ ˣK` is left-`K`-translation invariant in the conjugator:
`|K ⊓ ᵏˣK| = |K ⊓ ˣK|` for `k ∈ K`. -/
theorem card_inf_conj_smul_mul_mem {Γ : Type*} [Group Γ] {K : Subgroup Γ} {k : Γ}
    (hk : k ∈ K) (x : Γ) :
    Nat.card ↥(K ⊓ MulAut.conj (k * x) • K) = Nat.card ↥(K ⊓ MulAut.conj x • K) := by
  have hinf : K ⊓ MulAut.conj (k * x) • K
      = MulAut.conj k • (K ⊓ MulAut.conj x • K) := by
    rw [map_mul, mul_smul, Subgroup.smul_inf, conj_smul_eq_self_of_mem' hk]
  rw [hinf]
  exact Nat.card_congr (Subgroup.equivSMul (MulAut.conj k) _).toEquiv.symm

/-- **The Dedekind intersection identity** `(H⊔U₁) ⊓ (H⊔V) = H ⊔ (U₁⊓V)` for a normal `H`
with `H ⊓ U = ⊥` and `U₁, V ≤ U`.  The `⊆` direction decomposes an element both ways as
`h₁·u₁ = h₂·u₂` (`Subgroup.normal_mul`) and cancels `h₂⁻¹h₁ = u₂u₁⁻¹ ∈ H ⊓ U = ⊥`. -/
theorem sup_inf_sup_of_normal_of_inf_bot {Γ : Type*} [Group Γ] {Hn Uu U₁ V : Subgroup Γ}
    [Hn.Normal] (hHU : Hn ⊓ Uu = ⊥) (hU₁ : U₁ ≤ Uu) (hV : V ≤ Uu) :
    (Hn ⊔ U₁) ⊓ (Hn ⊔ V) = Hn ⊔ (U₁ ⊓ V) := by
  refine le_antisymm ?_ (le_inf (sup_le_sup_left inf_le_left Hn)
    (sup_le_sup_left inf_le_right Hn))
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
  have hx₁' : x ∈ (Hn : Set Γ) * (U₁ : Set Γ) := by
    rw [← Subgroup.normal_mul]; exact hx₁
  have hx₂' : x ∈ (Hn : Set Γ) * (V : Set Γ) := by
    rw [← Subgroup.normal_mul]; exact hx₂
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hx₁'
  obtain ⟨h₂, hh₂, u₂, hu₂, heq⟩ := hx₂'
  have heq' : h₂ * u₂ = h₁ * u₁ := heq
  -- `h₂⁻¹h₁ = u₂u₁⁻¹ ∈ H ⊓ U = ⊥`
  have hkey : h₂⁻¹ * h₁ = u₂ * u₁⁻¹ := by
    calc h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * u₁) * u₁⁻¹ := by group
      _ = h₂⁻¹ * (h₂ * u₂) * u₁⁻¹ := by rw [heq']
      _ = u₂ * u₁⁻¹ := by group
  have hmem : h₂⁻¹ * h₁ ∈ Hn ⊓ Uu := by
    refine ⟨Hn.mul_mem (Hn.inv_mem hh₂) hh₁, ?_⟩
    rw [hkey]
    exact Uu.mul_mem (hV hu₂) (Uu.inv_mem (hU₁ hu₁))
  rw [hHU, Subgroup.mem_bot] at hmem
  have hu12 : u₁ = u₂ := by
    have h1 : u₂ * u₁⁻¹ = 1 := by rw [← hkey, hmem]
    have h2 : u₂ * u₁⁻¹ * u₁ = 1 * u₁ := by rw [h1]
    simpa [mul_assoc] using h2.symm
  exact Subgroup.mul_mem_sup hh₁ ⟨hu₁, hu12 ▸ hu₂⟩

/-- **Cardinality of `H·X`** for a normal `H` with `H ⊓ U = ⊥` and `X ≤ U`:
`|H ⊔ X| = |H|·|X|` (`card_HK_mul_card_inf_eq_card_mul_card` with trivial intersection). -/
theorem card_sup_of_normal_of_inf_bot {Γ : Type*} [Group Γ] {Hn Uu X : Subgroup Γ}
    [Hn.Normal] (hHU : Hn ⊓ Uu = ⊥) (hX : X ≤ Uu) :
    Nat.card ↥(Hn ⊔ X) = Nat.card ↥Hn * Nat.card ↥X := by
  have hbot : Hn ⊓ X = ⊥ := by
    rw [eq_bot_iff, ← hHU]
    exact le_inf inf_le_left (inf_le_right.trans hX)
  have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Hn X
  rw [hbot] at h
  have hone : Nat.card ↥(⊥ : Subgroup Γ) = 1 := by simp
  rw [hone, mul_one] at h
  rw [← h]
  have hset : ((Hn : Set Γ) * (X : Set Γ)) = ((Hn ⊔ X : Subgroup Γ) : Set Γ) :=
    (Subgroup.normal_mul Hn X).symm
  rw [hset]
  rfl

/-- **The fibred Mackey conjugation count** (Peterfalvi (9.11.4)'s `λ(x)`-count): in the
configuration `Γ = (H·U)·W` (complement `hcompl`), `H ⊴ Γ`, `H ⊓ U = ⊥`, `U₁ ⊴ U`
(`hU₁n`), `W ≤ N(U)` (`hWU`), with the (9.11.2) TI-identity `U₁ ∩ ʷU₁ = C` for `w ∈ W^#`
(`hTI`), the conjugation count of `K = H ⊔ U₁` is

`Σ_{x∈Γ} |K ∩ ˣK| = |H|²·|U|·(|U₁| + (|W|−1)·|C|)`.

Every `x = s·w` (`s ∈ H·U`, `w ∈ W`) contributes `|H|·|U₁ ∩ ʷU₁|`: the `H`-part of `s` is
absorbed into `K`, the `U`-part normalizes both `U₁` and `ʷU₁`, and the Dedekind identity
computes `K ∩ ˣK = H ⊔ (U₁ ∩ ʷU₁)`. -/
theorem sum_card_inf_conjSMul_eq {Hn Uu U₁ Cc Ww : Subgroup Γ} [Hn.Normal]
    (hHU : Hn ⊓ Uu = ⊥) (hU₁U : U₁ ≤ Uu)
    (hU₁n : ∀ u ∈ Uu, MulAut.conj u • U₁ = U₁)
    (hWU : ∀ w ∈ Ww, MulAut.conj w • Uu = Uu)
    (hcompl : (Hn ⊔ Uu).IsComplement' Ww)
    (hTI : ∀ w ∈ Ww, w ≠ 1 → U₁ ⊓ MulAut.conj w • U₁ = Cc) :
    (∑ x : Γ, Nat.card ↥((Hn ⊔ U₁) ⊓ MulAut.conj x • (Hn ⊔ U₁)))
      = Nat.card ↥Hn ^ 2 * Nat.card ↥Uu
        * (Nat.card ↥U₁ + (Nat.card ↥Ww - 1) * Nat.card ↥Cc) := by
  classical
  -- conjugation of `K = H ⊔ U₁` decomposes along the normal `H`
  have hconjK : ∀ x : Γ,
      MulAut.conj x • (Hn ⊔ U₁) = Hn ⊔ MulAut.conj x • U₁ := by
    intro x
    rw [Subgroup.smul_sup, Subgroup.Normal.conj_smul_eq_self]
  -- `ʷU₁ ≤ U` for `w ∈ W`, and `ᵘʷU₁ = ʷU₁` for `u ∈ U`
  have hWU₁ : ∀ w ∈ Ww, MulAut.conj w • U₁ ≤ Uu := by
    intro w hw
    calc MulAut.conj w • U₁ ≤ MulAut.conj w • Uu :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hU₁U
      _ = Uu := hWU w hw
  have hconjUW : ∀ u ∈ Uu, ∀ w ∈ Ww,
      MulAut.conj (u * w) • U₁ = MulAut.conj w • U₁ := by
    intro u hu w hw
    have huw : w⁻¹ * u * w ∈ Uu := by
      have h1 : u ∈ MulAut.conj w • Uu := (hWU w hw).symm ▸ hu
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
        MulAut.conj_apply, inv_inv] at h1
      exact h1
    have hsplit : u * w = w * (w⁻¹ * u * w) := by group
    rw [hsplit, map_mul, mul_smul, hU₁n _ huw]
  -- the value on each complement fibre: `|K ∩ ˢʷK| = |H|·|U₁ ∩ ʷU₁|`
  have hval : ∀ s ∈ Hn ⊔ Uu, ∀ w ∈ Ww,
      Nat.card ↥((Hn ⊔ U₁) ⊓ MulAut.conj (s * w) • (Hn ⊔ U₁))
        = Nat.card ↥Hn * Nat.card ↥(U₁ ⊓ MulAut.conj w • U₁) := by
    intro s hs w hw
    have hs' : s ∈ (Hn : Set Γ) * (Uu : Set Γ) := by
      rw [← Subgroup.normal_mul]; exact hs
    obtain ⟨h, hh, u, hu, rfl⟩ := hs'
    have hhK : h ∈ Hn ⊔ U₁ := Subgroup.mem_sup_left hh
    have hassoc : h * u * w = h * (u * w) := by group
    rw [hassoc, card_inf_conj_smul_mul_mem hhK]
    rw [hconjK, hconjUW u hu w hw,
      sup_inf_sup_of_normal_of_inf_bot hHU hU₁U (hWU₁ w hw)]
    exact card_sup_of_normal_of_inf_bot hHU (inf_le_left.trans hU₁U)
  -- reindex the sum over `Γ` along the complement `Γ ≃ (H·U) × W`
  have hcompl' : Subgroup.IsComplement ((Hn ⊔ Uu : Subgroup Γ) : Set Γ)
      ((Ww : Subgroup Γ) : Set Γ) := hcompl
  have hreindex : (∑ x : Γ, Nat.card ↥((Hn ⊔ U₁) ⊓ MulAut.conj x • (Hn ⊔ U₁)))
      = ∑ p : ((Hn ⊔ Uu : Subgroup Γ) : Set Γ) × ((Ww : Subgroup Γ) : Set Γ),
          Nat.card ↥((Hn ⊔ U₁) ⊓ MulAut.conj ((p.1 : Γ) * (p.2 : Γ)) • (Hn ⊔ U₁)) := by
    refine (Equiv.sum_comp hcompl'.equiv.symm
      (fun x : Γ => Nat.card ↥((Hn ⊔ U₁) ⊓ MulAut.conj x • (Hn ⊔ U₁)))).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Subgroup.IsComplement.equiv_symm_apply]
  rw [hreindex, Fintype.sum_prod_type]
  -- collapse the (constant) `H·U`-fibres
  have hfib : ∀ s : ((Hn ⊔ Uu : Subgroup Γ) : Set Γ),
      (∑ w : ((Ww : Subgroup Γ) : Set Γ),
          Nat.card ↥((Hn ⊔ U₁) ⊓ MulAut.conj ((s : Γ) * (w : Γ)) • (Hn ⊔ U₁)))
        = ∑ w : ((Ww : Subgroup Γ) : Set Γ),
            Nat.card ↥Hn * Nat.card ↥(U₁ ⊓ MulAut.conj (w : Γ) • U₁) := by
    intro s
    exact Finset.sum_congr rfl fun w _ => hval (s : Γ) s.2 (w : Γ) w.2
  rw [Finset.sum_congr rfl fun s _ => hfib s, Finset.sum_const, Finset.card_univ]
  -- the `W`-sum: the `w = 1` term contributes `|U₁|`, the `w ≠ 1` terms `|C|` each
  have hone : (1 : Γ) ∈ ((Ww : Subgroup Γ) : Set Γ) := Ww.one_mem
  have hWsum : (∑ w : ((Ww : Subgroup Γ) : Set Γ),
      Nat.card ↥Hn * Nat.card ↥(U₁ ⊓ MulAut.conj (w : Γ) • U₁))
      = Nat.card ↥Hn * (Nat.card ↥U₁ + (Nat.card ↥Ww - 1) * Nat.card ↥Cc) := by
    rw [← Finset.mul_sum]
    congr 1
    have h1mem : (⟨1, hone⟩ : ((Ww : Subgroup Γ) : Set Γ)) ∈ Finset.univ :=
      Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ h1mem]
    have h1term : Nat.card ↥(U₁ ⊓ MulAut.conj ((⟨1, hone⟩ :
        ((Ww : Subgroup Γ) : Set Γ)) : Γ) • U₁) = Nat.card ↥U₁ := by
      have h1 : MulAut.conj (1 : Γ) • U₁ = U₁ := by
        rw [map_one, one_smul]
      change Nat.card ↥(U₁ ⊓ MulAut.conj (1 : Γ) • U₁) = Nat.card ↥U₁
      rw [h1, inf_idem]
    rw [h1term]
    congr 1
    have hrest : ∀ w ∈ Finset.univ.erase (⟨1, hone⟩ : ((Ww : Subgroup Γ) : Set Γ)),
        Nat.card ↥(U₁ ⊓ MulAut.conj (w : Γ) • U₁) = Nat.card ↥Cc := by
      intro w hw
      have hne : (w : Γ) ≠ 1 := by
        intro h1
        exact (Finset.mem_erase.mp hw).1 (Subtype.ext h1)
      rw [hTI (w : Γ) w.2 hne]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem h1mem,
      Finset.card_univ, smul_eq_mul]
    congr 2
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩,
      fun a => rfl, fun a => rfl⟩
  rw [hWsum, smul_eq_mul]
  have hScard : Fintype.card ((Hn ⊔ Uu : Subgroup Γ) : Set Γ)
      = Nat.card ↥Hn * Nat.card ↥Uu := by
    rw [← Nat.card_eq_fintype_card,
      show Nat.card ((Hn ⊔ Uu : Subgroup Γ) : Set Γ) = Nat.card ↥(Hn ⊔ Uu) from
        Nat.card_congr ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩,
          fun a => rfl, fun a => rfl⟩]
    exact card_sup_of_normal_of_inf_bot hHU le_rfl
  rw [hScard]
  ring

end MackeyCount

section NineElevenFourContext

variable {data : TypesIIIIIIVSetup M}

/-- Realization commutes with conjugation: `(ᵐX).subgroupOf M = ᵐ(X.subgroupOf M)` for
`m ∈ M`. -/
theorem subgroupOf_pointwise_conj_smul (X : Subgroup G) (m : ↥M) :
    (MulAut.conj (m : G) • X).subgroupOf M = MulAut.conj m • X.subgroupOf M := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ← map_inv,
    MulAut.smul_def, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply,
    Subgroup.mem_subgroupOf]
  rfl

/-- **A subgroup above the derived subgroup is normal** (conjugation form): if
`[U,U] ≤ U₁ ≤ U` then `ᵍU₁ = U₁` for every `g ∈ U`.  This is how the (9.11.1) equality
configuration `C = U′ ≤ U₁` makes `U₁ ⊴ U` — the input for the `U`-part of a conjugator
acting trivially on the `Ū`-level Mackey count. -/
theorem conj_smul_eq_self_of_derived_le {Uu U₁ : Subgroup G} (hU₁U : U₁ ≤ Uu)
    (hder : derivedInG Uu ≤ U₁) {g : G} (hg : g ∈ Uu) :
    MulAut.conj g • U₁ = U₁ := by
  have helt : ∀ k ∈ Uu, ∀ y ∈ U₁, k * y * k⁻¹ ∈ U₁ := by
    intro k hk y hy
    have hcomm : y⁻¹ * k * y * k⁻¹ ∈ ⁅Uu, Uu⁆ := by
      have h := Subgroup.commutator_mem_commutator (Uu.inv_mem (hU₁U hy)) hk
      simpa [commutatorElement_def, inv_inv] using h
    have hcomm' : y⁻¹ * k * y * k⁻¹ ∈ U₁ := by
      apply hder
      rw [derivedInG_eq_commutator]
      exact hcomm
    have hyy : k * y * k⁻¹ = y * (y⁻¹ * k * y * k⁻¹) := by group
    rw [hyy]
    exact U₁.mul_mem hy hcomm'
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]
  constructor
  · intro hx
    have h := helt g hg _ hx
    have hxx : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [hxx] at h
  · intro hx
    have h := helt g⁻¹ (Uu.inv_mem hg) x hx
    rwa [inv_inv] at h

/-- **`W₁` normalizes `U`** (conjugation form of Peterfalvi (8.4.b) `W1_normalizes_U`). -/
theorem conj_smul_U_eq_self_of_mem_W1 (data : TypesIIIIIIVSetup M) {w : G}
    (hw : w ∈ data.typeP.W1) :
    MulAut.conj w • data.typeP.U = data.typeP.U := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]
  have h := Subgroup.mem_set_normalizer_iff.mp (data.typeP.W1_normalizes_U hw)
    (w⁻¹ * x * w)
  have hxx : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
  constructor
  · intro hx
    have h2 := h.mp hx
    rwa [hxx] at h2
  · intro hx
    apply h.mpr
    rwa [hxx]

/-- `H ≤ M` (ambient form). -/
theorem h_le_M (data : TypesIIIIIIVSetup M) : data.H ≤ M :=
  data.typeP.H_le.trans (Subgroup.map_subtype_le _)

/-- `U ≤ M` (ambient form). -/
theorem u_le_M (data : TypesIIIIIIVSetup M) : data.U ≤ M :=
  data.typeP.U_le.trans (Subgroup.map_subtype_le _)

/-- The realized `H·U`-decomposition of `HU`: `H.subgroupOf M ⊔ U.subgroupOf M = huSub`. -/
theorem hSubgroupOfM_sup_uSubgroupOfM (data : TypesIIIIIIVSetup M) :
    data.H.subgroupOf M ⊔ data.U.subgroupOf M = huSub data :=
  (Subgroup.subgroupOf_sup (h_le_M data) (u_le_M data)).symm

/-- `W₁` (realized in `↥M`) complements `HU` (Peterfalvi (8.4): `M = M′·W₁ = (HU)·W₁`). -/
theorem huSub_isComplement'_w1SubgroupOf (data : TypesIIIIIIVSetup M) :
    (huSub data).IsComplement' (data.typeP.W1.subgroupOf M) := by
  rw [huSub_eq_derivedInG_subgroupOf]
  exact data.typeP.M_complement

/-- `H ⊓ U = ⊥`, realized in `↥M`. -/
theorem hSubgroupOfM_inf_uSubgroupOfM_eq_bot (data : TypesIIIIIIVSetup M) :
    data.H.subgroupOf M ⊓ data.U.subgroupOf M = ⊥ := by
  rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
    show data.H ⊓ data.U = ⊥ from typeP_H_inf_U data.typeP]
  simp

/-- The realized `K = H·U₁ ≤ HU` (the (9.11.4) induction source below `HU`). -/
theorem hSubgroupOfM_sup_le_huSub (data : TypesIIIIIIVSetup M) {U₁ : Subgroup G}
    (hU₁U : U₁ ≤ data.U) :
    data.H.subgroupOf M ⊔ U₁.subgroupOf M ≤ huSub data := by
  rw [← hSubgroupOfM_sup_uSubgroupOfM data]
  exact sup_le_sup_left (Subgroup.subgroupOf_mono M hU₁U) _

variable [Finite G]

omit [Finite G] in
/-- **`Supp(γ) ⊆ HU`** (Peterfalvi (9.11.4), the `γ`-side of `Supp(α) ⊆ A(M)`): the
character `γ = Ind_{HU₁}^M 1`, induced from `K = H·U₁ ≤ HU`, vanishes off the conjugates
of `K`, which lie in the normal `HU`. -/
theorem nineElevenGamma_support (data : TypesIIIIIIVSetup M) {U₁ : Subgroup G}
    [Fintype ↥M] [Invertible (Nat.card ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M) : ℂ)]
    (hU₁U : U₁ ≤ data.U) :
    (ClassFunction.induce (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
      (trivialClassFunction ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M))).support
      ⊆ (huSub data : Set ↥M) := by
  intro g hg
  have hconj := ClassFunction.support_induce_subset_conjugatesInto
    (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
    (trivialClassFunction ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)) hg
  rw [ClassFunction.mem_conjugatesInto] at hconj
  obtain ⟨x, hx⟩ := hconj
  have hxHU : x⁻¹ * g * x ∈ huSub data := hSubgroupOfM_sup_le_huSub data hU₁U hx
  have hgg : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
  rw [hgg]
  exact (huSub_normal data).conj_mem _ hxHU x

omit [Finite G] in
/-- `γ ∈ ℤ[Irr M]`: `Ind` of the (irreducible) trivial character is a virtual character. -/
theorem nineElevenGamma_mem_ZIrr (data : TypesIIIIIIVSetup M) (U₁ : Subgroup G)
    [Fintype ↥M] [Finite ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)]
    [Invertible (Nat.card ↥M : ℂ)]
    [Invertible (Nat.card ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M) : ℂ)] :
    ClassFunction.induce (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
      (trivialClassFunction ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)) ∈ ZIrr ↥M := by
  have : Fintype ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M) :=
    Fintype.ofFinite ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)
  exact ClassFunction.induce_mem_ZIrr _ trivialClassFunction_isIrreducible.mem_ZIrr

/-- **`γ(1) = q·a`** (Peterfalvi (9.11.4)): the degree of `γ = Ind_{HU₁}^M 1` is the index
`[M : HU₁] = [M : HU]·[HU : HU₁] = q·[U : U₁] = q·a`.  This is what cancels against the
degree `ψ₁(1) = qa` of the `𝒮₁`-member in `α = γ − ψ₁`, giving `α(1) = 0`. -/
theorem nineElevenGamma_apply_one (data : TypesIIIIIIVSetup M) {U₁ : Subgroup G}
    [Fintype ↥M] [Invertible (Nat.card ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M) : ℂ)]
    (hU₁U : U₁ ≤ data.U) {a : ℕ} (hU₁a : U₁.relIndex data.U = a) :
    ClassFunction.induce (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
      (trivialClassFunction ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)) (1 : ↥M)
      = ((data.q * a : ℕ) : ℂ) := by
  have := hSubgroupOfM_normal data
  have hKle := hSubgroupOfM_sup_le_huSub data hU₁U
  -- `|K| = |H|·|U₁|` and `|HU| = |H|·|U|`
  have hbot := hSubgroupOfM_inf_uSubgroupOfM_eq_bot data
  have hcardK : Nat.card ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)
      = Nat.card ↥data.H * Nat.card ↥U₁ := by
    rw [card_sup_of_normal_of_inf_bot hbot (Subgroup.subgroupOf_mono M hU₁U),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h_le_M data)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hU₁U.trans (u_le_M data))).toEquiv]
  have hcardHU : Nat.card ↥(huSub data) = Nat.card ↥data.H * Nat.card ↥data.U := by
    rw [← hSubgroupOfM_sup_uSubgroupOfM data, card_sup_of_normal_of_inf_bot hbot le_rfl,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h_le_M data)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (u_le_M data)).toEquiv]
  -- `a·|U₁| = |U|` from `[U : U₁] = a`
  have haU : a * Nat.card ↥U₁ = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card (U₁.subgroupOf data.U)
    rwa [show (U₁.subgroupOf data.U).index = U₁.relIndex data.U from rfl, hU₁a,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₁U).toEquiv] at h
  -- `[HU : K] = a`
  have hrel : (data.H.subgroupOf M ⊔ U₁.subgroupOf M).relIndex (huSub data) = a := by
    have h := Subgroup.index_mul_card
      ((data.H.subgroupOf M ⊔ U₁.subgroupOf M).subgroupOf (huSub data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv, hcardK, hcardHU,
      ← haU] at h
    have hpos : 0 < Nat.card ↥data.H * Nat.card ↥U₁ :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have h' : (data.H.subgroupOf M ⊔ U₁.subgroupOf M).relIndex (huSub data)
        * (Nat.card ↥data.H * Nat.card ↥U₁)
        = a * (Nat.card ↥data.H * Nat.card ↥U₁) := by
      rw [show (data.H.subgroupOf M ⊔ U₁.subgroupOf M).relIndex (huSub data)
          = ((data.H.subgroupOf M ⊔ U₁.subgroupOf M).subgroupOf (huSub data)).index
        from rfl, h]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  -- `[M : K] = [HU : K]·[M : HU] = a·q`
  have hindex : (data.H.subgroupOf M ⊔ U₁.subgroupOf M).index = a * data.q := by
    rw [← Subgroup.relIndex_mul_index hKle, hrel, huSub_index_eq_q]
  rw [ClassFunction.induce_apply_one, hindex, trivialClassFunction_apply]
  push_cast
  ring

omit [Finite G] in
/-- **`⟨γ, Ind_{HU}^M ζ⟩ = 0` for every `ζ ∈ 𝒳`** (Peterfalvi (9.11.4), *"Since
`H ⊆ Ker γ`, `γ` is orthogonal to `ψ₁`"*): the (9.11.4) orthogonality, through the
averaging-projector engine `inner_induce_trivial_induce_eq_zero` at `N = H`, `K = H·U₁`,
`D = HU` — the kernel-avoidance `H ⊄ Ker ζ` is the defining `𝒳`-membership. -/
theorem nineElevenGamma_inner_induceHU (data : TypesIIIIIIVSetup M) {U₁ : Subgroup G}
    [Fintype ↥M] [Finite ↥(huSub data)]
    [Finite ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M) : ℂ)]
    (hU₁U : U₁ ≤ data.U) {ζ : IrreducibleCharacter ↥(huSub data)} (hζ : ζ ∈ xiSet data) :
    ClassFunction.inner
      (ClassFunction.induce (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
        (trivialClassFunction ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)))
      (ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ)) = 0 := by
  have := hSubgroupOfM_normal data
  exact inner_induce_trivial_induce_eq_zero (N := data.H.subgroupOf M) le_sup_left
    (hSubgroupOfM_sup_le_huSub data hU₁U) ζ.2 hζ

/-- **The (9.11.4) Mackey norm, cleared form `‖γ‖²·u = a·u + (q−1)·a²`** (book:
`‖γ‖² = a + (q−1)a²/u`): from the conjugation count
`‖γ‖²·|K|² = |H|²·|U|·(|U₁| + (q−1)·|C|)` (`inner_induce_trivial_self_mul_card_sq` +
`sum_card_inf_conjSMul_eq`) and the dictionaries `|K| = |H|·|U₁|`, `a·|U₁| = |U|`,
`u·|C| = |U|`.  Inputs: `U′ ≤ U₁` (making `U₁ ⊴ U` — from the (9.11.1) equality
configuration `C = U′ ≤ U₁`) and the (9.11.2) TI-identity `hTI`
(the `NineElevenTwoTIWitness`). -/
theorem nineElevenGamma_inner_self_mul_u {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) {U₁ : Subgroup G} {a : ℕ}
    [Fintype ↥M] [Finite ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)]
    [Invertible (Nat.card ↥M : ℂ)]
    [Invertible (Nat.card ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M) : ℂ)]
    (hU₁U : U₁ ≤ data.U) (hUpU₁ : uprimeSub data ≤ U₁)
    (hU₁a : U₁.relIndex data.U = a)
    (hTI : ∀ w ∈ data.typeP.W1, w ≠ 1 →
      U₁ ⊓ MulAut.conj w • U₁ = cSub data chief) :
    ClassFunction.inner
        (ClassFunction.induce (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
          (trivialClassFunction ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)))
        (ClassFunction.induce (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
          (trivialClassFunction ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)))
        * (chars.u : ℂ)
      = ((a * chars.u + (data.q - 1) * a ^ 2 : ℕ) : ℂ) := by
  have := hSubgroupOfM_normal data
  have hbot := hSubgroupOfM_inf_uSubgroupOfM_eq_bot data
  -- the `↥M`-realized hypotheses of the fibred count
  have hU₁mU : U₁.subgroupOf M ≤ data.U.subgroupOf M := Subgroup.subgroupOf_mono M hU₁U
  have hU₁n : ∀ u ∈ data.U.subgroupOf M,
      MulAut.conj u • U₁.subgroupOf M = U₁.subgroupOf M := by
    intro u hu
    have hu' : (u : G) ∈ data.U := hu
    rw [← subgroupOf_pointwise_conj_smul,
      conj_smul_eq_self_of_derived_le hU₁U hUpU₁ hu']
  have hWnU : ∀ w ∈ data.typeP.W1.subgroupOf M,
      MulAut.conj w • data.U.subgroupOf M = data.U.subgroupOf M := by
    intro w hw
    have hw' : (w : G) ∈ data.typeP.W1 := hw
    rw [show (data.U : Subgroup G) = data.typeP.U from rfl,
      ← subgroupOf_pointwise_conj_smul, conj_smul_U_eq_self_of_mem_W1 data hw']
  have hTIm : ∀ w ∈ data.typeP.W1.subgroupOf M, w ≠ 1 →
      U₁.subgroupOf M ⊓ MulAut.conj w • U₁.subgroupOf M
        = (cSub data chief).subgroupOf M := by
    intro w hw hne
    have hw' : (w : G) ∈ data.typeP.W1 := hw
    have hne' : (w : G) ≠ 1 := by
      intro h1
      exact hne (Subtype.ext h1)
    rw [← subgroupOf_pointwise_conj_smul, Subgroup.subgroupOf, Subgroup.subgroupOf,
      ← Subgroup.comap_inf, hTI (w : G) hw' hne']
    rfl
  have hcompl : (data.H.subgroupOf M ⊔ data.U.subgroupOf M).IsComplement'
      (data.typeP.W1.subgroupOf M) := by
    rw [hSubgroupOfM_sup_uSubgroupOfM data]
    exact huSub_isComplement'_w1SubgroupOf data
  -- the conjugation count, with the `W₁`-cardinality converted to `q`
  have hq : Nat.card ↥(data.typeP.W1.subgroupOf M) = data.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv]
    rfl
  -- cardinality dictionaries
  have hcardK : Nat.card ↥(data.H.subgroupOf M ⊔ U₁.subgroupOf M)
      = Nat.card ↥data.H * Nat.card ↥U₁ := by
    rw [card_sup_of_normal_of_inf_bot hbot hU₁mU,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h_le_M data)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hU₁U.trans (u_le_M data))).toEquiv]
  have hcardH : Nat.card ↥(data.H.subgroupOf M) = Nat.card ↥data.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h_le_M data)).toEquiv
  have hcardU : Nat.card ↥(data.U.subgroupOf M) = Nat.card ↥data.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (u_le_M data)).toEquiv
  have hcardU₁ : Nat.card ↥(U₁.subgroupOf M) = Nat.card ↥U₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hU₁U.trans (u_le_M data))).toEquiv
  have hcardC : Nat.card ↥((cSub data chief).subgroupOf M)
      = Nat.card ↥(cSub data chief) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((cSub_le_U data chief).trans (u_le_M data))).toEquiv
  have hcount := sum_card_inf_conjSMul_eq (Γ := ↥M) hbot hU₁mU hU₁n hWnU hcompl hTIm
  rw [hq, hcardH, hcardU, hcardU₁, hcardC] at hcount
  have hnorm := inner_induce_trivial_self_mul_card_sq (Γ := ↥M)
    (data.H.subgroupOf M ⊔ U₁.subgroupOf M)
  rw [hcount, hcardK] at hnorm
  -- `a·|U₁| = |U|` and `u·|C| = |U|`
  have haU : a * Nat.card ↥U₁ = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card (U₁.subgroupOf data.U)
    rwa [show (U₁.subgroupOf data.U).index = U₁.relIndex data.U from rfl, hU₁a,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₁U).toEquiv] at h
  have huC : chars.u * Nat.card ↥(cSub data chief) = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cSub data chief).subgroupOf data.U)
    rwa [show ((cSub data chief).subgroupOf data.U).index
        = (cSub data chief).relIndex data.U from rfl, relIndex_cSub_U_eq_u chars,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cSub_le_U data chief)).toEquiv] at h
  -- the `ℂ`-arithmetic: clear `|H|²·|U₁|²` and substitute the dictionaries
  have hHne : ((Nat.card ↥data.H : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hU₁ne : ((Nat.card ↥U₁ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hfactor : (((Nat.card ↥data.H : ℕ) : ℂ) * ((Nat.card ↥data.H : ℕ) : ℂ))
      * (((Nat.card ↥U₁ : ℕ) : ℂ) * ((Nat.card ↥U₁ : ℕ) : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hHne hHne) (mul_ne_zero hU₁ne hU₁ne)
  have haU' : ((a : ℕ) : ℂ) * ((Nat.card ↥U₁ : ℕ) : ℂ)
      = ((Nat.card ↥data.U : ℕ) : ℂ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℂ)) haU
  have huC' : ((chars.u : ℕ) : ℂ) * ((Nat.card ↥(cSub data chief) : ℕ) : ℂ)
      = ((Nat.card ↥data.U : ℕ) : ℂ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℂ)) huC
  refine mul_left_cancel₀ hfactor ?_
  push_cast at hnorm ⊢
  linear_combination (chars.u : ℂ) * hnorm
    + (((data.q - 1 : ℕ) : ℂ) * ((Nat.card ↥data.H : ℕ) : ℂ) ^ 2
        * ((Nat.card ↥data.U : ℕ) : ℂ)) * huC'
    - ((chars.u : ℂ) * ((Nat.card ↥data.H : ℕ) : ℂ) ^ 2 * ((Nat.card ↥U₁ : ℕ) : ℂ)
        + ((data.q - 1 : ℕ) : ℂ) * ((Nat.card ↥data.H : ℕ) : ℂ) ^ 2
          * ((Nat.card ↥data.U : ℕ) : ℂ)
        + ((data.q - 1 : ℕ) : ℂ) * ((a : ℕ) : ℂ) * ((Nat.card ↥data.H : ℕ) : ℂ) ^ 2
          * ((Nat.card ↥U₁ : ℕ) : ℂ)) * haU'

/-- **The (9.11.2) TI-witness `Prop`** (issue 9083, Phase E): Peterfalvi (9.11.2), *"If
`w ∈ W₁^#`, then `U₁ ∩ U₁^w = C`"*, packaged with the standing facts about the book's
witness `U₁ = C_U(H₁)`: `C ≤ U₁ ≤ U` (`cSub_le_cuSubOf`, `cuSubOf_le_U`) and
`[U : U₁] = a` ((9.7.a), `relIndex_cuSubOf_U_eq_a`).  The per-`w` intersection identity is
the Phase-B pair dichotomy (`nineElevenTwo_relIndex_dichotomy`) transported along the
`W₁ ↔` Clifford-summand conjugation dictionary `C_U(H₁)^w = C_U(H₁^w)` (`Hpart_orbit`) —
the remaining (9.11.2) content for Phase E. -/
def NineElevenTwoTIWitness {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) : Prop :=
  ∃ U₁ : Subgroup G, cSub data chief ≤ U₁ ∧ U₁ ≤ data.U ∧
    U₁.relIndex data.U = caseA.a ∧
    ∀ w ∈ data.typeP.W1, w ≠ 1 → U₁ ⊓ MulAut.conj w • U₁ = cSub data chief

end NineElevenFourContext

end OddOrder.Peterfalvi.S11


