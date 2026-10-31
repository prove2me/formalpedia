-- Prove2me | Definitions.Def_ChapterGradedFriedrichs
-- name    : ChapterGradedFriedrichs
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-30T08:33:29.537867+00:00
-- url     : https://prove2.me/theorems/4525cabb-524e-42a7-b56e-8e4649d13f94
-- title:
--   The Lean 4 theorem `toL2_mem` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGradedFriedrichs.lean`): generated def bundle for ChapterGradedFriedrichs. See BookProof/ChapterGradedFriedrichs.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGradedFriedrichs.lean

import Definitions.Def_ChapterGradedFock
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFermionFock
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_symm
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_nonneg
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_one_particle
import Mathlib


/-!
# Chapter GradedFriedrichs — the analytic half of the graded second quantization

`BookProof.ChapterGradedFock` builds the graded Fock space `Γˢ ⊗ Γᵃ` and its
**algebraic** structure (the unified graded canonical relation, the `ℤ₂`
grading).  What `CONSOLIDATED_PLAN.md` §10.6.2 item 3 still asked for is the
**analytic** conclusion: that the total graded Hamiltonian

`dΓ(A, B) = dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)`

is a densely defined positive symmetric operator on `ℓ²(Conf × FConf)` itself —
not merely factorwise — and therefore has a positive self-adjoint (Friedrichs)
extension.  This chapter proves that.

## Deliverables

* A reusable **generic transport** of the algebraic model `γ →₀ ℂ` into
  `ℓ²(γ)`: `toL2`, `ainner` (the algebraic inner product), `algEquivL2`
  (the algebraic space *is* the finite-mode domain), `opOfAlg`, and the two
  criteria `IsSymAlg`/`IsPosAlg` transporting to `SymmetricOn` and to
  nonnegativity of the quadratic form, hence `algOp_friedrichs_extension`.
* The **slice calculus** for the tensor product: `sliceFst`, `sliceSnd`, the
  factorization `ainner_eq_sum_sliceFst` / `ainner_eq_sum_sliceSnd` of the inner
  product into a finite sum over the slices, and the intertwining
  `sliceFst_liftFst` / `sliceSnd_liftSnd`.
* **`isSymAlg_liftFst`, `isPosAlg_liftFst`, `isSymAlg_liftSnd`,
  `isPosAlg_liftSnd`** — symmetry and positivity of a one-factor operator are
  inherited by its lift to the tensor product.  This is what makes the graded
  statement genuinely two-dimensional rather than factorwise.
* **`gradedHamiltonian_friedrichs_extension`** — the headline: for a Hermitian
  positive bosonic one-particle matrix `A` and a Hermitian positive fermionic
  one `B`, the operator `dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)` on the finite-mode domain of
  `ℓ²(Conf × FConf)` has a positive self-adjoint extension.
* **`gradedSecondQuantization_friedrichs`** — the same conclusion phrased for
  arbitrary symmetric positive one-particle operators given in a Hilbert basis.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.GradedFriedrichs

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin
open BookProof.FockSecondQuantization BookProof.FermionFock BookProof.GradedFock

noncomputable section

/-! ## A generic transport `(γ →₀ ℂ) → ℓ²(γ)` -/

section Generic

variable {γ : Type*}

/-- A finitely supported function on `γ`, viewed inside `ℓ²(γ)`. -/
def toL2 (u : γ →₀ ℂ) : L2I γ :=
  ⟨fun g => u g, memLpTwo_of_finite_support u.finite_support⟩

@[simp] theorem toL2_apply (u : γ →₀ ℂ) (g : γ) :
    ((toL2 u : L2I γ) : γ → ℂ) g = u g := rfl

/-- The transport map is linear. -/
def toL2L : (γ →₀ ℂ) →ₗ[ℂ] L2I γ where
  toFun := toL2
  map_add' u v := by refine lp.ext (funext fun g => ?_); rfl
  map_smul' c u := by refine lp.ext (funext fun g => ?_); simp [toL2]

@[simp] theorem toL2L_apply (u : γ →₀ ℂ) : toL2L u = toL2 u := rfl

theorem toL2_mem (u : γ →₀ ℂ) : toL2 u ∈ lpFiniteModes γ := u.finite_support

theorem toL2_injective : Function.Injective (toL2 (γ := γ)) := by
  intro u v h
  refine Finsupp.ext fun g => ?_
  have := congrArg (fun f : L2I γ => (f : γ → ℂ) g) h
  simpa using this

/-- The **algebraic inner product**: the `ℓ²` inner product read on the
finitely supported model. -/
def ainner (u v : γ →₀ ℂ) : ℂ := inner ℂ (toL2 u) (toL2 v)

theorem ainner_eq_sum {u : γ →₀ ℂ} {s : Finset γ} (hs : u.support ⊆ s) (v : γ →₀ ℂ) :
    ainner u v = ∑ g ∈ s, (starRingEnd ℂ) (u g) * v g := by
  rw [ainner, lp.inner_eq_tsum]
  have hcoord : ∀ g : γ,
      (inner ℂ (((toL2 u : L2I γ) : γ → ℂ) g) (((toL2 v : L2I γ) : γ → ℂ) g) : ℂ)
        = (starRingEnd ℂ) (u g) * v g := by
    intro g; simp [RCLike.inner_apply, mul_comm]
  rw [tsum_congr hcoord]
  refine tsum_eq_sum fun g hg => ?_
  have hu : u g = 0 := by
    by_contra hc
    exact hg (hs (Finsupp.mem_support_iff.mpr hc))
  rw [hu, map_zero, zero_mul]

theorem toL2_add (u v : γ →₀ ℂ) : toL2 (u + v) = toL2 u + toL2 v := toL2L.map_add u v

theorem ainner_add_right (u v w : γ →₀ ℂ) : ainner u (v + w) = ainner u v + ainner u w := by
  rw [ainner, ainner, ainner, toL2_add, inner_add_right]

theorem ainner_add_left (u v w : γ →₀ ℂ) : ainner (u + v) w = ainner u w + ainner v w := by
  rw [ainner, ainner, ainner, toL2_add, inner_add_left]

/-- `T` is **formally symmetric** for the algebraic inner product. -/
def IsSymAlg (T : Module.End ℂ (γ →₀ ℂ)) : Prop := ∀ u v, ainner (T u) v = ainner u (T v)

/-- `T` is **formally positive** for the algebraic inner product. -/
def IsPosAlg (T : Module.End ℂ (γ →₀ ℂ)) : Prop := ∀ u, 0 ≤ (ainner u (T u)).re

theorem isSymAlg_add {T S : Module.End ℂ (γ →₀ ℂ)} (hT : IsSymAlg T) (hS : IsSymAlg S) :
    IsSymAlg (T + S) := by
  intro u v
  change ainner (T u + S u) v = ainner u (T v + S v)
  rw [ainner_add_left, ainner_add_right, hT, hS]

theorem isPosAlg_add {T S : Module.End ℂ (γ →₀ ℂ)} (hT : IsPosAlg T) (hS : IsPosAlg S) :
    IsPosAlg (T + S) := by
  intro u
  change 0 ≤ (ainner u (T u + S u)).re
  rw [ainner_add_right, Complex.add_re]
  exact add_nonneg (hT u) (hS u)

/-! ### The algebraic space is the finite-mode domain -/

/-- The finitely supported model **is** the finite-mode subspace of `ℓ²(γ)`. -/
def algEquivL2 : (γ →₀ ℂ) ≃ₗ[ℂ] lpFiniteModes γ := by
  classical
  refine LinearEquiv.ofBijective (toL2L.codRestrict (lpFiniteModes γ) toL2_mem) ⟨?_, ?_⟩
  · intro u v h
    exact toL2_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    refine ⟨Finsupp.onFinset hx.toFinset (fun g => (x : γ → ℂ) g) ?_, ?_⟩
    · intro g hg
      exact hx.mem_toFinset.mpr hg
    · exact Subtype.ext (lp.ext (funext fun _ => rfl))

@[simp] theorem coe_algEquivL2 (u : γ →₀ ℂ) :
    ((algEquivL2 u : lpFiniteModes γ) : L2I γ) = toL2 u := rfl

theorem coe_algEquivL2_symm (x : lpFiniteModes γ) :
    ((x : lpFiniteModes γ) : L2I γ) = toL2 (algEquivL2.symm x) := by
  rw [← coe_algEquivL2, LinearEquiv.apply_symm_apply]

/-- The operator on the finite-mode domain determined by an operator of the
algebraic model. -/
def opOfAlg (T : Module.End ℂ (γ →₀ ℂ)) : lpFiniteModes γ →ₗ[ℂ] L2I γ :=
  (lpFiniteModes γ).subtype.comp (algEquivL2.conj T)

theorem coe_opOfAlg (T : Module.End ℂ (γ →₀ ℂ)) (x : lpFiniteModes γ) :
    opOfAlg T x = toL2 (T (algEquivL2.symm x)) := by
  simp [opOfAlg, LinearEquiv.conj_apply, coe_algEquivL2]

theorem opOfAlg_symmetricOn {T : Module.End ℂ (γ →₀ ℂ)} (hT : IsSymAlg T) :
    SymmetricOn (lpFiniteModes γ) (opOfAlg T) := by
  intro x y
  rw [coe_opOfAlg, coe_opOfAlg, coe_algEquivL2_symm x, coe_algEquivL2_symm y]
  exact hT _ _

theorem opOfAlg_quadForm_nonneg {T : Module.End ℂ (γ →₀ ℂ)} (hT : IsPosAlg T)
    (x : lpFiniteModes γ) : 0 ≤ quadForm (opOfAlg T) x := by
  rw [quadForm, coe_opOfAlg, coe_algEquivL2_symm x]
  exact hT _

/-- **A formally symmetric, formally positive operator of the algebraic model
has a positive self-adjoint (Friedrichs) extension on `ℓ²(γ)`.** -/
theorem algOp_friedrichs_extension {T : Module.End ℂ (γ →₀ ℂ)}
    (hsym : IsSymAlg T) (hpos : IsPosAlg T) :
    ∃ (Dom : Submodule ℂ (L2I γ)) (A : Dom →ₗ[ℂ] L2I γ),
      IsPositiveSelfAdjointExtension (opOfAlg T) A :=
  friedrichs_extension_exists_complete
    ⟨lpFiniteModes γ, opOfAlg T, opOfAlg_symmetricOn hsym, opOfAlg_quadForm_nonneg hpos⟩
    lpFiniteModes_dense

end Generic

/-! ## The slice calculus of the tensor product -/

section Slices

variable {α β : Type*}

/-- The **first-factor slice** at `b`: `(sliceFst b u) a = u (a, b)`. -/
def sliceFst (b : β) : ((α × β) →₀ ℂ) →ₗ[ℂ] (α →₀ ℂ) :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    ((Finsupp.single p.2 (1 : ℂ) : β →₀ ℂ) b • (Finsupp.single p.1 (1 : ℂ) : α →₀ ℂ))

/-- The **second-factor slice** at `a`: `(sliceSnd a u) b = u (a, b)`. -/
def sliceSnd (a : α) : ((α × β) →₀ ℂ) →ₗ[ℂ] (β →₀ ℂ) :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    ((Finsupp.single p.1 (1 : ℂ) : α →₀ ℂ) a • (Finsupp.single p.2 (1 : ℂ) : β →₀ ℂ))

theorem sliceFst_apply (b : β) (u : (α × β) →₀ ℂ) (a : α) : sliceFst b u a = u (a, b) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]
  | single p c =>
    obtain ⟨a₀, b₀⟩ := p
    rw [sliceFst, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Prod.mk.injEq]
    by_cases hb : b₀ = b <;> by_cases ha : a₀ = a <;> simp [ha, hb]

theorem sliceSnd_apply (a : α) (u : (α × β) →₀ ℂ) (b : β) : sliceSnd a u b = u (a, b) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]
  | single p c =>
    obtain ⟨a₀, b₀⟩ := p
    rw [sliceSnd, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Prod.mk.injEq]
    by_cases hb : b₀ = b <;> by_cases ha : a₀ = a <;> simp [ha, hb]

theorem sliceFst_otimes (b : β) (v : α →₀ ℂ) (w : β →₀ ℂ) :
    sliceFst b (otimes v w) = (w b) • v := by
  refine Finsupp.ext fun a => ?_
  rw [sliceFst_apply, otimes_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem sliceSnd_otimes (a : α) (v : α →₀ ℂ) (w : β →₀ ℂ) :
    sliceSnd a (otimes v w) = (v a) • w := by
  refine Finsupp.ext fun b => ?_
  rw [sliceSnd_apply, otimes_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Slicing intertwines `T ⊗ 1` with `T`. -/
theorem sliceFst_liftFst (T : Module.End ℂ (α →₀ ℂ)) (b : β) (u : (α × β) →₀ ℂ) :
    sliceFst b (liftFst T u) = T (sliceFst b u) := by
  have h : (sliceFst (α := α) b).comp (liftFst (β := β) T)
      = T.comp (sliceFst (α := α) b) := by
    refine prod_linear_ext fun v w => ?_
    simp only [LinearMap.comp_apply, liftFst_otimes, sliceFst_otimes, map_smul]
  exact congrArg (fun f : ((α × β) →₀ ℂ) →ₗ[ℂ] (α →₀ ℂ) => f u) h

/-- Slicing intertwines `1 ⊗ S` with `S`. -/
theorem sliceSnd_liftSnd (S : Module.End ℂ (β →₀ ℂ)) (a : α) (u : (α × β) →₀ ℂ) :
    sliceSnd a (liftSnd S u) = S (sliceSnd a u) := by
  have h : (sliceSnd (β := β) a).comp (liftSnd (α := α) S)
      = S.comp (sliceSnd (β := β) a) := by
    refine prod_linear_ext fun v w => ?_
    simp only [LinearMap.comp_apply, liftSnd_otimes, sliceSnd_otimes, map_smul]
  exact congrArg (fun f : ((α × β) →₀ ℂ) →ₗ[ℂ] (β →₀ ℂ) => f u) h

theorem support_sliceFst_subset {u : (α × β) →₀ ℂ} {A : Finset α} {B : Finset β}
    (hu : u.support ⊆ A ×ˢ B) (b : β) : (sliceFst b u).support ⊆ A := by
  intro a ha
  have hne : u (a, b) ≠ 0 := by
    rw [← sliceFst_apply]
    exact Finsupp.mem_support_iff.mp ha
  exact (Finset.mem_product.mp (hu (Finsupp.mem_support_iff.mpr hne))).1

theorem support_sliceSnd_subset {u : (α × β) →₀ ℂ} {A : Finset α} {B : Finset β}
    (hu : u.support ⊆ A ×ˢ B) (a : α) : (sliceSnd a u).support ⊆ B := by
  intro b hb
  have hne : u (a, b) ≠ 0 := by
    rw [← sliceSnd_apply]
    exact Finsupp.mem_support_iff.mp hb
  exact (Finset.mem_product.mp (hu (Finsupp.mem_support_iff.mpr hne))).2

/-- The inner product of the product space is the sum over the second index of
the inner products of the first-factor slices. -/
theorem ainner_eq_sum_sliceFst {u v : (α × β) →₀ ℂ} {A : Finset α} {B : Finset β}
    (hu : u.support ⊆ A ×ˢ B) :
    ainner u v = ∑ b ∈ B, ainner (sliceFst b u) (sliceFst b v) := by
  classical
  rw [ainner_eq_sum hu v, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ainner_eq_sum (support_sliceFst_subset hu b)]
  exact Finset.sum_congr rfl fun a _ => by rw [sliceFst_apply, sliceFst_apply]

/-- The inner product of the product space is the sum over the first index of
the inner products of the second-factor slices. -/
theorem ainner_eq_sum_sliceSnd {u v : (α × β) →₀ ℂ} {A : Finset α} {B : Finset β}
    (hu : u.support ⊆ A ×ˢ B) :
    ainner u v = ∑ a ∈ A, ainner (sliceSnd a u) (sliceSnd a v) := by
  classical
  rw [ainner_eq_sum hu v]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ainner_eq_sum (support_sliceSnd_subset hu a)]
  exact Finset.sum_congr rfl fun b _ => by rw [sliceSnd_apply, sliceSnd_apply]

open Classical in
/-- A finset rectangle containing the supports of all the vectors involved. -/
def rect (s : Finset (α × β)) : Finset α × Finset β := (s.image Prod.fst, s.image Prod.snd)

open Classical in
theorem subset_rect {s : Finset (α × β)} : s ⊆ (rect s).1 ×ˢ (rect s).2 := by
  intro p hp
  exact Finset.mem_product.mpr
    ⟨Finset.mem_image_of_mem Prod.fst hp, Finset.mem_image_of_mem Prod.snd hp⟩

/-- **Symmetry is inherited by the lift to the first tensor factor.** -/
theorem isSymAlg_liftFst {T : Module.End ℂ (α →₀ ℂ)} (hT : IsSymAlg T) :
    IsSymAlg (liftFst (β := β) T) := by
  classical
  intro u v
  set s : Finset (α × β) :=
    (liftFst (β := β) T u).support ∪ u.support ∪ v.support ∪ (liftFst (β := β) T v).support
    with hs
  have hsub : ∀ w : (α × β) →₀ ℂ, w.support ⊆ s → w.support ⊆ (rect s).1 ×ˢ (rect s).2 :=
    fun w hw => hw.trans subset_rect
  have h1 : (liftFst (β := β) T u).support ⊆ s := by
    intro p hp; simp only [hs]; exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ hp))
  have h2 : u.support ⊆ s := by
    intro p hp; simp only [hs]; exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hp))
  rw [ainner_eq_sum_sliceFst (hsub _ h1), ainner_eq_sum_sliceFst (hsub _ h2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sliceFst_liftFst, sliceFst_liftFst, hT]

/-- **Positivity is inherited by the lift to the first tensor factor.** -/
theorem isPosAlg_liftFst {T : Module.End ℂ (α →₀ ℂ)} (hT : IsPosAlg T) :
    IsPosAlg (liftFst (β := β) T) := by
  classical
  intro u
  rw [ainner_eq_sum_sliceFst (u := u) (v := liftFst (β := β) T u)
    (subset_rect (s := u.support))]
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun b _ => ?_
  rw [sliceFst_liftFst]
  exact hT _

/-- **Symmetry is inherited by the lift to the second tensor factor.** -/
theorem isSymAlg_liftSnd {S : Module.End ℂ (β →₀ ℂ)} (hS : IsSymAlg S) :
    IsSymAlg (liftSnd (α := α) S) := by
  classical
  intro u v
  set s : Finset (α × β) :=
    (liftSnd (α := α) S u).support ∪ u.support ∪ v.support ∪ (liftSnd (α := α) S v).support
    with hs
  have hsub : ∀ w : (α × β) →₀ ℂ, w.support ⊆ s → w.support ⊆ (rect s).1 ×ˢ (rect s).2 :=
    fun w hw => hw.trans subset_rect
  have h1 : (liftSnd (α := α) S u).support ⊆ s := by
    intro p hp; simp only [hs]; exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ hp))
  have h2 : u.support ⊆ s := by
    intro p hp; simp only [hs]; exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hp))
  rw [ainner_eq_sum_sliceSnd (hsub _ h1), ainner_eq_sum_sliceSnd (hsub _ h2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sliceSnd_liftSnd, sliceSnd_liftSnd, hS]

/-- **Positivity is inherited by the lift to the second tensor factor.** -/
theorem isPosAlg_liftSnd {S : Module.End ℂ (β →₀ ℂ)} (hS : IsPosAlg S) :
    IsPosAlg (liftSnd (α := α) S) := by
  classical
  intro u
  rw [ainner_eq_sum_sliceSnd (u := u) (v := liftSnd (α := α) S u)
    (subset_rect (s := u.support))]
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [sliceSnd_liftSnd]
  exact hS _

end Slices

/-! ## The graded Hamiltonian `dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)` -/

theorem isSymAlg_dGamma {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    IsSymAlg (dGamma col) := fun u v => inner_dGamma_symm hherm u v

theorem isPosAlg_dGamma {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) :
    IsPosAlg (dGamma col) := fun u => inner_dGamma_nonneg hpos u

theorem isSymAlg_dGammaF {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    IsSymAlg (dGammaF col) := fun u v => inner_dGammaF_symm hherm u v

theorem isPosAlg_dGammaF {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) :
    IsPosAlg (dGammaF col) := fun u => inner_dGammaF_nonneg hpos u

/-- The **total graded second-quantized Hamiltonian** on the algebraic graded
Fock space: `dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)`. -/
def gradedHamiltonianAlg (colB colF : ℕ → (ℕ →₀ ℂ)) : Module.End ℂ GradedAlg :=
  liftFst (dGamma colB) + liftSnd (dGammaF colF)

/-- The **total graded second-quantized Hamiltonian** on the finite-mode domain
of `ℓ²(Conf × FConf) ≅ Γˢ ⊗ Γᵃ`. -/
def gradedHamiltonian (colB colF : ℕ → (ℕ →₀ ℂ)) : lpFiniteModes GConf →ₗ[ℂ] GFock :=
  opOfAlg (gradedHamiltonianAlg colB colF)

theorem isSymAlg_gradedHamiltonianAlg {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hb : IsHermCol colB) (hf : IsHermCol colF) :
    IsSymAlg (gradedHamiltonianAlg colB colF) :=
  isSymAlg_add (isSymAlg_liftFst (isSymAlg_dGamma hb)) (isSymAlg_liftSnd (isSymAlg_dGammaF hf))

theorem isPosAlg_gradedHamiltonianAlg {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hb : IsPosCol colB) (hf : IsPosCol colF) :
    IsPosAlg (gradedHamiltonianAlg colB colF) :=
  isPosAlg_add (isPosAlg_liftFst (isPosAlg_dGamma hb)) (isPosAlg_liftSnd (isPosAlg_dGammaF hf))

theorem gradedHamiltonian_symmetricOn {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hb : IsHermCol colB) (hf : IsHermCol colF) :
    SymmetricOn (lpFiniteModes GConf) (gradedHamiltonian colB colF) :=
  opOfAlg_symmetricOn (isSymAlg_gradedHamiltonianAlg hb hf)

theorem gradedHamiltonian_quadForm_nonneg {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hb : IsPosCol colB) (hf : IsPosCol colF) (x : lpFiniteModes GConf) :
    0 ≤ quadForm (gradedHamiltonian colB colF) x :=
  opOfAlg_quadForm_nonneg (isPosAlg_gradedHamiltonianAlg hb hf) x

/-- **The graded second-quantized Hamiltonian `dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)` has a
positive self-adjoint (Friedrichs) extension on `ℓ²(Conf × FConf)`.**  This is
the analytic conclusion on the graded space itself, not merely factorwise. -/
theorem gradedHamiltonian_friedrichs_extension {colB colF : ℕ → (ℕ →₀ ℂ)}
    (hbherm : IsHermCol colB) (hbpos : IsPosCol colB)
    (hfherm : IsHermCol colF) (hfpos : IsPosCol colF) :
    ∃ (Dom : Submodule ℂ GFock) (A : Dom →ₗ[ℂ] GFock),
      IsPositiveSelfAdjointExtension (gradedHamiltonian colB colF) A :=
  algOp_friedrichs_extension (isSymAlg_gradedHamiltonianAlg hbherm hfherm)
    (isPosAlg_gradedHamiltonianAlg hbpos hfpos)

/-- **Graded second quantization of a pair of arbitrary symmetric positive
one-particle operators.** -/
theorem gradedSecondQuantization_friedrichs {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (bB : HilbertBasis ℕ ℂ F) (bF : HilbertBasis ℕ ℂ G)
    (A : finiteModeDomain bB →ₗ[ℂ] finiteModeDomain bB)
    (B : finiteModeDomain bF →ₗ[ℂ] finiteModeDomain bF)
    (hA : SymmetricOn (finiteModeDomain bB) ((finiteModeDomain bB).subtype.comp A))
    (hAp : ∀ x, 0 ≤ quadForm ((finiteModeDomain bB).subtype.comp A) x)
    (hB : SymmetricOn (finiteModeDomain bF) ((finiteModeDomain bF).subtype.comp B))
    (hBp : ∀ x, 0 ≤ quadForm ((finiteModeDomain bF).subtype.comp B) x) :
    ∃ (Dom : Submodule ℂ GFock) (A' : Dom →ₗ[ℂ] GFock),
      IsPositiveSelfAdjointExtension
        (gradedHamiltonian (opCol bB A) (opCol bF B)) A' :=
  gradedHamiltonian_friedrichs_extension (isHermCol_opCol hA) (isPosCol_opCol hAp)
    (isHermCol_opCol hB) (isPosCol_opCol hBp)

/-! ## Non-vacuity: the total number operator `N_b ⊗ 1 + 1 ⊗ N_f` -/

/-- The identity one-particle matrix `A e_k = e_k`, whose second quantization is
the number operator. -/
def idCol : ℕ → (ℕ →₀ ℂ) := fun j => Finsupp.single j 1

theorem support_idCol (k : ℕ) : (idCol k).support = {k} :=
  Finsupp.support_single_ne_zero k one_ne_zero

theorem isHermCol_idCol : IsHermCol idCol := by
  intro j k
  by_cases h : j = k
  · subst h; simp [idCol]
  · simp [idCol, h, Ne.symm h]

theorem isPosCol_idCol : IsPosCol idCol := by
  intro S c
  have h : ∀ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (idCol k) j * c k
      = (starRingEnd ℂ) (c j) * c j := by
    intro j hj
    rw [Finset.sum_eq_single j]
    · simp [idCol]
    · intro k _ hkj
      simp [idCol, Ne.symm hkj]
    · intro hc; exact absurd hj hc
  rw [Finset.sum_congr rfl h, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (c j).re, sq_nonneg (c j).im]

theorem dGamma_idCol_one_particle (k : ℕ) :
    dGamma idCol (Finsupp.single (Finsupp.single k 1) 1)
      = Finsupp.single (Finsupp.single k 1) (1 : ℂ) := by
  rw [dGamma_one_particle, support_idCol, Finset.sum_singleton]
  simp [idCol]

/-- Local copy: the stub `Thm_BookProof_GradedFriedrichs_dGammaF_idCol_one_particle`
imports this bundle, so it cannot be imported back (import cycle); proved here
from `dGammaF_one_particle` exactly as the bosonic twin above. -/
theorem dGammaF_idCol_one_particle (k : ℕ) :
    dGammaF idCol (Finsupp.single ({k} : FConf) 1)
      = Finsupp.single ({k} : FConf) (1 : ℂ) := by
  rw [dGammaF_one_particle, support_idCol, Finset.sum_singleton]
  simp [idCol]

/-- **The graded Hamiltonian is not the zero operator**: on the state with one
boson in mode `k` and one fermion in mode `l` the total number operator
`N_b ⊗ 1 + 1 ⊗ N_f` has eigenvalue `2`. -/
theorem gradedNumber_one_particle (k l : ℕ) :
    gradedHamiltonianAlg idCol idCol
        (otimes (Finsupp.single (Finsupp.single k 1) 1) (Finsupp.single ({l} : FConf) 1))
      = (2 : ℂ) •
        otimes (Finsupp.single (Finsupp.single k 1) 1) (Finsupp.single ({l} : FConf) 1) := by
  change liftFst (dGamma idCol) (otimes _ _) + liftSnd (dGammaF idCol) (otimes _ _) = _
  rw [liftFst_otimes, liftSnd_otimes, dGamma_idCol_one_particle,
    dGammaF_idCol_one_particle, two_smul]

/-- **The total graded number operator `N_b ⊗ 1 + 1 ⊗ N_f` has a positive
self-adjoint (Friedrichs) extension on `ℓ²(Conf × FConf)`.**  Together with
`gradedNumber_one_particle` this shows the general theorem is not vacuous. -/
theorem gradedNumber_friedrichs_extension :
    ∃ (Dom : Submodule ℂ GFock) (A : Dom →ₗ[ℂ] GFock),
      IsPositiveSelfAdjointExtension (gradedHamiltonian idCol idCol) A :=
  gradedHamiltonian_friedrichs_extension isHermCol_idCol isPosCol_idCol
    isHermCol_idCol isPosCol_idCol

end

end BookProof.GradedFriedrichs


