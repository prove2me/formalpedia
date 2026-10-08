-- Prove2me | Definitions.Def_ChapterTensorPermutation
-- name    : ChapterTensorPermutation
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T14:47:24.788826+00:00
-- url     : https://prove2.me/theorems/bad1417f-36c3-46ba-b4d9-2d644d3af84d
-- title:
--   The Lean 4 theorem `span_purePow_eq_top` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterTensorPermutation.lean`): generated def bundle for ChapterTensorPermutation. See BookProof/ChapterTensorPermutation.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterTensorPermutation.lean

import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterA4
import Mathlib


/-!
# The symmetric group acting on a tensor power

`BookProof.TensorCore` presents the `n`-particle space `E^{⊗n}` in the nested form
`E ⊗ (E ⊗ (⋯ ⊗ ℂ))` (`IPSpace.pow`), and `BookProof.TwoParticleSector` treats the swap of the
two-particle space.  This module constructs the action of the **full symmetric group**
`Equiv.Perm (Fin n)` on `E^{⊗n}` by permutation of the factors, as a unitary representation in
the sense of `BookProof.GroupAverage.UnitaryRep`.

The construction is by recursion on `n`, out of two elementary isometries only:

* `swapFirst` — the exchange of the first two factors (associator ∘ commutor ∘ associator),
* `liftTail` — an operator applied to the last `n` factors of `E^{⊗(n+1)}`.

Every permutation operator is a composite of those, so it is a linear isometry equivalence by
construction, and — this is what the sector chapters use — every structure preserved by
`swapFirst` and by `liftTail` is automatically preserved by the whole action.

The recursion follows `Equiv.Perm.decomposeFin`: `σ` is `swap 0 (σ 0)` after the permutation
of the last `n` factors given by the second component of the decomposition.  That the
resulting family is multiplicative is proved from the formula on pure tensors,
`permOp_purePow`: `U_σ (x_0 ⊗ ⋯ ⊗ x_{n-1}) = x_{σ 0} ⊗ ⋯ ⊗ x_{σ (n-1)}`.

## Contents

* `purePow` — the pure tensor of a family `Fin n → E`, in the nested presentation;
  `span_purePow_eq_top` and `linearMap_ext_purePow` (pure tensors span, so a linear map is
  determined by its values on them).
* `swapFirst`, `liftTail`, `swap0`, `permOp` — the construction.
* `swapFirst_purePow`, `swap0_purePow`, **`permOp_purePow`** — the action on pure tensors.
* `permOp_one`, `permOp_mul` — the group law.
* **`permRep`** — the unitary representation of `Equiv.Perm (Fin n)` on `E^{⊗n}`, and
  **`signRep`** — its twist by the sign character, whose invariant sector is the
  antisymmetric one.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.TensorPerm

open scoped TensorProduct
open BookProof.TensorCore BookProof.GroupAverage

noncomputable section

/-! ## Pure tensors -/

variable (E : BookProof.TensorCore.IPSpace)

/-- The pure tensor `x₀ ⊗ x₁ ⊗ ⋯ ⊗ x_{n-1}` of a family of vectors, in the nested
presentation of `IPSpace.pow`. -/
def purePow : ∀ (n : ℕ), (Fin n → E.carrier) → (E.pow n).carrier
  | 0, _ => (1 : ℂ)
  | (n + 1), f => f 0 ⊗ₜ[ℂ] purePow n (Fin.tail f)

@[simp] theorem purePow_succ (n : ℕ) (f : Fin (n + 1) → E.carrier) :
    purePow E (n + 1) f = f 0 ⊗ₜ[ℂ] purePow E n (Fin.tail f) := rfl

/-- **Pure tensors span the tensor power.** -/
theorem span_purePow_eq_top (n : ℕ) :
    Submodule.span ℂ (Set.range (purePow E n)) = ⊤ := by
  induction n with
  | zero =>
      refine top_unique (fun x _ => ?_)
      have h1 : purePow E 0 (fun i => Fin.elim0 i) ∈ Set.range (purePow E 0) := ⟨_, rfl⟩
      have hmem := Submodule.smul_mem (Submodule.span ℂ (Set.range (purePow E 0)))
        (show ℂ from x) (Submodule.subset_span h1)
      have hx : (show ℂ from x) • purePow E 0 (fun i => Fin.elim0 i) = x := by
        change (show ℂ from x) * (1 : ℂ) = x
        rw [mul_one]
      rwa [hx] at hmem
  | succ n ih =>
      refine top_unique ?_
      rw [← TensorProduct.span_tmul_eq_top ℂ E.carrier (E.pow n).carrier, Submodule.span_le]
      rintro t ⟨x, y, rfl⟩
      simp only [SetLike.mem_coe]
      have hy : y ∈ Submodule.span ℂ (Set.range (purePow E n)) := by rw [ih]; trivial
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨g, rfl⟩ := hz
          exact Submodule.subset_span ⟨Fin.cons x g, by simp⟩
      | zero => simp
      | add a b _ _ ha hb =>
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
          rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem _ c ha

/-- A linear map out of a tensor power is determined by its values on pure tensors. -/
theorem linearMap_ext_purePow {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    {u v : (E.pow n).carrier →ₗ[ℂ] M}
    (h : ∀ f : Fin n → E.carrier, u (purePow E n f) = v (purePow E n f)) : u = v := by
  refine LinearMap.ext_on (span_purePow_eq_top E n) ?_
  rintro x ⟨f, rfl⟩
  exact h f





/-! ## The two elementary isometries -/

/-- The exchange of the first two factors of `X ⊗ (X ⊗ R)`. -/
def swapAux (X R : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] :
    X ⊗[ℂ] (X ⊗[ℂ] R) ≃ₗᵢ[ℂ] X ⊗[ℂ] (X ⊗[ℂ] R) :=
  (TensorProduct.assocIsometry ℂ X X R).symm.trans
    ((TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ X X)
        (LinearIsometryEquiv.refl ℂ R)).trans (TensorProduct.assocIsometry ℂ X X R))

@[simp] theorem swapAux_tmul {X R : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] (x y : X) (r : R) :
    swapAux X R (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] r)) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] r) := by
  simp [swapAux]

/-- The exchange of the first two factors of `E^{⊗(n+2)}`. -/
def swapFirst (n : ℕ) : (E.pow (n + 2)).carrier ≃ₗᵢ[ℂ] (E.pow (n + 2)).carrier :=
  swapAux E.carrier (E.pow n).carrier

@[simp] theorem swapFirst_tmul (n : ℕ) (x y : E.carrier) (r : (E.pow n).carrier) :
    swapFirst E n (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] r) : (E.pow (n + 2)).carrier) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] r) :=
  swapAux_tmul x y r

/-- An operator applied to the last `n` factors of `E^{⊗(n+1)}`. -/
def liftTail {n : ℕ} (u : (E.pow n).carrier ≃ₗᵢ[ℂ] (E.pow n).carrier) :
    (E.pow (n + 1)).carrier ≃ₗᵢ[ℂ] (E.pow (n + 1)).carrier :=
  TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ E.carrier) u

@[simp] theorem liftTail_tmul {n : ℕ} (u : (E.pow n).carrier ≃ₗᵢ[ℂ] (E.pow n).carrier)
    (x : E.carrier) (r : (E.pow n).carrier) :
    liftTail E u (x ⊗ₜ[ℂ] r : (E.pow (n + 1)).carrier) = x ⊗ₜ[ℂ] u r := rfl

/-! ## The permutation operators -/

/-- The exchange of the first factor with the `p`-th factor, as a composite of `swapFirst`
and `liftTail`. -/
def swap0 : ∀ (n : ℕ), Fin n → ((E.pow n).carrier ≃ₗᵢ[ℂ] (E.pow n).carrier)
  | 0, p => Fin.elim0 p
  | 1, _ => LinearIsometryEquiv.refl ℂ _
  | (n + 2), p =>
      Fin.cases (motive := fun _ => (E.pow (n + 2)).carrier ≃ₗᵢ[ℂ] (E.pow (n + 2)).carrier)
        (LinearIsometryEquiv.refl ℂ _)
        (fun j => (liftTail E (swap0 (n + 1) j)).trans
          ((swapFirst E n).trans (liftTail E (swap0 (n + 1) j)))) p

/-- The operator permuting the factors of `E^{⊗n}`.  On pure tensors it is
`x₀ ⊗ ⋯ ⊗ x_{n-1} ↦ x_{σ 0} ⊗ ⋯ ⊗ x_{σ (n-1)}` (`permOp_purePow`). -/
def permOp : ∀ (n : ℕ), Equiv.Perm (Fin n) → ((E.pow n).carrier ≃ₗᵢ[ℂ] (E.pow n).carrier)
  | 0, _ => LinearIsometryEquiv.refl ℂ _
  | (n + 1), σ =>
      (swap0 E (n + 1) (Equiv.Perm.decomposeFin σ).1).trans
        (liftTail E (permOp n (Equiv.Perm.decomposeFin σ).2))

/-! ## The equations of the two recursions -/

@[simp] theorem swap0_one (p : Fin 1) : swap0 E 1 p = LinearIsometryEquiv.refl ℂ _ := rfl

@[simp] theorem swap0_zero (n : ℕ) :
    swap0 E (n + 2) 0 = LinearIsometryEquiv.refl ℂ _ := rfl

theorem swap0_succ (n : ℕ) (j : Fin (n + 1)) :
    swap0 E (n + 2) j.succ = (liftTail E (swap0 E (n + 1) j)).trans
      ((swapFirst E n).trans (liftTail E (swap0 E (n + 1) j))) := by
  simp [swap0]



/-! ## The combinatorics of the recursion -/

/-- The permutation of `Fin (n+1)` fixing `0` and acting as `e` on the remaining places. -/
def permSucc {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

@[simp] theorem permSucc_zero {n : ℕ} (e : Equiv.Perm (Fin n)) : permSucc e 0 = 0 := by
  simp [permSucc]

@[simp] theorem permSucc_succ {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    permSucc e i.succ = (e i).succ := by
  simp [permSucc]

/-- The conjugation identity behind the recursion for `swap0`: exchanging the first factor
with the `(j+1)`-st is the exchange of the first two, conjugated by the exchange of the
second with the `(j+1)`-st. -/
theorem permSucc_swap_conj {n : ℕ} (j : Fin (n + 1)) (i : Fin (n + 2)) :
    permSucc (Equiv.swap 0 j) (Equiv.swap 0 1 (permSucc (Equiv.swap 0 j) i))
      = Equiv.swap 0 j.succ i := by
  refine Fin.cases ?_ ?_ i
  · have e1 : permSucc (Equiv.swap 0 j) (0 : Fin (n + 2)) = 0 := permSucc_zero _
    have e2 : Equiv.swap (0 : Fin (n + 2)) 1 0 = 1 := Equiv.swap_apply_left 0 1
    have e3 : permSucc (Equiv.swap 0 j) (1 : Fin (n + 2)) = j.succ := by
      rw [← Fin.succ_zero_eq_one, permSucc_succ, Equiv.swap_apply_left]
    rw [e1, e2, e3, Equiv.swap_apply_left]
  · intro k
    rw [permSucc_succ]
    rcases eq_or_ne k j with hkj | hkj
    · subst hkj
      have e1 : Equiv.swap (0 : Fin (n + 1)) k k = 0 := Equiv.swap_apply_right 0 k
      rw [e1, Fin.succ_zero_eq_one, Equiv.swap_apply_right, permSucc_zero,
        Equiv.swap_apply_right]
    · rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        have hj0 : j ≠ 0 := fun h => hkj h.symm
        have hjs0 : (j.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero j
        have hjs1 : (j.succ : Fin (n + 2)) ≠ 1 := by
          rw [← Fin.succ_zero_eq_one]
          exact fun h => hj0 (Fin.succ_injective _ h)
        have e1 : Equiv.swap (0 : Fin (n + 1)) j 0 = j := Equiv.swap_apply_left 0 j
        have e2 : Equiv.swap (0 : Fin (n + 2)) 1 j.succ = j.succ :=
          Equiv.swap_apply_of_ne_of_ne hjs0 hjs1
        have e3 : permSucc (Equiv.swap 0 j) (j.succ : Fin (n + 2)) = 1 := by
          rw [permSucc_succ, Equiv.swap_apply_right, Fin.succ_zero_eq_one]
        have e4 : Equiv.swap (0 : Fin (n + 2)) j.succ 1 = 1 := by
          refine Equiv.swap_apply_of_ne_of_ne ?_ (fun h => hjs1 h.symm)
          rw [← Fin.succ_zero_eq_one]
          exact Fin.succ_ne_zero 0
        rw [e1, e2, e3, Fin.succ_zero_eq_one, e4]
      · have hks1 : (k.succ : Fin (n + 2)) ≠ 1 := by
          rw [← Fin.succ_zero_eq_one]
          exact fun h => hk0 (Fin.succ_injective _ h)
        have e1 : Equiv.swap (0 : Fin (n + 1)) j k = k :=
          Equiv.swap_apply_of_ne_of_ne hk0 hkj
        have e2 : Equiv.swap (0 : Fin (n + 2)) 1 k.succ = k.succ :=
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k) hks1
        have e3 : Equiv.swap (0 : Fin (n + 2)) j.succ k.succ = k.succ :=
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k)
            (fun h => hkj (Fin.succ_injective _ h))
        rw [e1, e2, permSucc_succ, e1, e3]

/-- The decomposition identity behind the recursion for `permOp`. -/
theorem swap_decomposeFin {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Equiv.swap 0 (Equiv.Perm.decomposeFin σ).1
        (permSucc (Equiv.Perm.decomposeFin σ).2 i) = σ i := by
  have hσ : Equiv.Perm.decomposeFin.symm
      ((Equiv.Perm.decomposeFin σ).1, (Equiv.Perm.decomposeFin σ).2) = σ := by simp
  refine Fin.cases ?_ ?_ i
  · rw [permSucc_zero, Equiv.swap_apply_left]
    conv_rhs => rw [← hσ]
    rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  · intro k
    rw [permSucc_succ]
    conv_rhs => rw [← hσ]
    rw [Equiv.Perm.decomposeFin_symm_apply_succ]

/-! ## The action on pure tensors -/

theorem liftTail_purePow {n : ℕ} {u : (E.pow n).carrier ≃ₗᵢ[ℂ] (E.pow n).carrier}
    {e : Equiv.Perm (Fin n)}
    (hu : ∀ g : Fin n → E.carrier, u (purePow E n g) = purePow E n (g ∘ e))
    (f : Fin (n + 1) → E.carrier) :
    liftTail E u (purePow E (n + 1) f) = purePow E (n + 1) (f ∘ permSucc e) := by
  have htail : Fin.tail (f ∘ permSucc e) = Fin.tail f ∘ e := by
    funext j
    simp [Fin.tail]
  rw [purePow_succ, liftTail_tmul, hu, purePow_succ, htail]
  simp

theorem swapFirst_purePow (n : ℕ) (f : Fin (n + 2) → E.carrier) :
    swapFirst E n (purePow E (n + 2) f) = purePow E (n + 2) (f ∘ Equiv.swap 0 1) := by
  have hL : purePow E (n + 2) f
      = f 0 ⊗ₜ[ℂ] (f 1 ⊗ₜ[ℂ] purePow E n (Fin.tail (Fin.tail f))) := by
    rw [purePow_succ, purePow_succ]
    simp [Fin.tail]
  have hswap0 : (f ∘ Equiv.swap 0 1) 0 = f 1 := by simp
  have hswap1 : (f ∘ Equiv.swap 0 1) 1 = f 0 := by simp
  have htail : Fin.tail (Fin.tail (f ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail f) := by
    funext j
    have h0 : (j.succ.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero _
    have h1 : (j.succ.succ : Fin (n + 2)) ≠ 1 := by
      rw [← Fin.succ_zero_eq_one]
      exact fun h => Fin.succ_ne_zero j (Fin.succ_injective _ h)
    simp [Fin.tail, Equiv.swap_apply_of_ne_of_ne h0 h1]
  have htail0 : Fin.tail (f ∘ Equiv.swap 0 1) 0 = f 0 := by
    simp [Fin.tail]
  have hR : purePow E (n + 2) (f ∘ Equiv.swap 0 1)
      = f 1 ⊗ₜ[ℂ] (f 0 ⊗ₜ[ℂ] purePow E n (Fin.tail (Fin.tail f))) := by
    rw [purePow_succ, purePow_succ, htail, hswap0, htail0]
  rw [hL, hR, swapFirst_tmul]

theorem swap0_purePow : ∀ (n : ℕ) (p : Fin (n + 1)) (f : Fin (n + 1) → E.carrier),
    swap0 E (n + 1) p (purePow E (n + 1) f) = purePow E (n + 1) (f ∘ Equiv.swap 0 p) := by
  intro n
  induction n with
  | zero =>
      intro p f
      have hp : p = 0 := Fin.ext (Nat.lt_one_iff.mp p.isLt)
      subst hp
      simp [swap0, Equiv.swap_self]
  | succ n ih =>
      intro p f
      refine Fin.cases ?_ ?_ p
      · simp [swap0, Equiv.swap_self]
      · intro j
        rw [swap0_succ]
        have h1 : liftTail E (swap0 E (n + 1) j) (purePow E (n + 2) f)
            = purePow E (n + 2) (f ∘ permSucc (Equiv.swap 0 j)) :=
          liftTail_purePow E (ih j) f
        have h2 := swapFirst_purePow E n (f ∘ permSucc (Equiv.swap 0 j))
        have h3 := liftTail_purePow E (ih j)
          ((f ∘ permSucc (Equiv.swap 0 j)) ∘ Equiv.swap 0 1)
        change liftTail E (swap0 E (n + 1) j)
            ((swapFirst E n) (liftTail E (swap0 E (n + 1) j) (purePow E (n + 2) f))) = _
        rw [h1, h2, h3]
        congr 1
        funext i
        exact congrArg f (permSucc_swap_conj j i)

/-- **The permutation operator on pure tensors.** -/
theorem permOp_purePow : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → E.carrier),
    permOp E n σ (purePow E n f) = purePow E n (f ∘ σ) := by
  intro n
  induction n with
  | zero => intro σ f; rfl
  | succ n ih =>
      intro σ f
      change liftTail E (permOp E n (Equiv.Perm.decomposeFin σ).2)
          (swap0 E (n + 1) (Equiv.Perm.decomposeFin σ).1 (purePow E (n + 1) f)) = _
      rw [swap0_purePow E n (Equiv.Perm.decomposeFin σ).1 f,
        liftTail_purePow E (ih (Equiv.Perm.decomposeFin σ).2)]
      congr 1
      funext i
      exact congrArg f (swap_decomposeFin σ i)

/-! ## The group law -/

theorem permOp_one (n : ℕ) (x : (E.pow n).carrier) : permOp E n 1 x = x := by
  have h : ((permOp E n 1).toLinearEquiv.toLinearMap : (E.pow n).carrier →ₗ[ℂ] _)
      = LinearMap.id := by
    refine linearMap_ext_purePow E (fun f => ?_)
    change permOp E n 1 (purePow E n f) = purePow E n f
    rw [permOp_purePow]
    rfl
  exact LinearMap.congr_fun h x

theorem permOp_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (x : (E.pow n).carrier) :
    permOp E n (σ * τ) x = permOp E n τ (permOp E n σ x) := by
  have h : ((permOp E n (σ * τ)).toLinearEquiv.toLinearMap : (E.pow n).carrier →ₗ[ℂ] _)
      = (permOp E n τ).toLinearEquiv.toLinearMap ∘ₗ (permOp E n σ).toLinearEquiv.toLinearMap := by
    refine linearMap_ext_purePow E (fun f => ?_)
    change permOp E n (σ * τ) (purePow E n f) = permOp E n τ (permOp E n σ (purePow E n f))
    rw [permOp_purePow, permOp_purePow, permOp_purePow]
    rfl
  exact LinearMap.congr_fun h x

theorem permOp_inner (n : ℕ) (σ : Equiv.Perm (Fin n)) (x y : (E.pow n).carrier) :
    (inner ℂ (permOp E n σ x) (permOp E n σ y) : ℂ) = inner ℂ x y :=
  (permOp E n σ).inner_map_map x y

/-! ## The unitary representation of the symmetric group -/

/-- **The symmetric group acts on the `n`-fold tensor power by permutation of the factors.**
The invariant sector of this action is the symmetric (bosonic) part of `E^{⊗n}`. -/
def permRep (n : ℕ) : UnitaryRep (Equiv.Perm (Fin n)) ((E.pow n).carrier) where
  act σ := (permOp E n σ⁻¹).toLinearEquiv.toLinearMap
  act_one x := by simpa using permOp_one E n x
  act_mul g h x := by
    have h1 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
    change permOp E n (g * h)⁻¹ x = permOp E n g⁻¹ (permOp E n h⁻¹ x)
    rw [h1, permOp_mul]
  act_inner g x y := permOp_inner E n g⁻¹ x y

@[simp] theorem permRep_act (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (E.pow n).carrier) :
    (permRep E n).act σ x = permOp E n σ⁻¹ x := rfl

/-- **The sign twist of the permutation action.**  Its invariant sector is the antisymmetric
(fermionic) part of `E^{⊗n}`. -/
def signRep (n : ℕ) : UnitaryRep (Equiv.Perm (Fin n)) ((E.pow n).carrier) where
  act σ := ((Equiv.Perm.sign σ : ℤ) : ℂ) • (permOp E n σ⁻¹).toLinearEquiv.toLinearMap
  act_one x := by simp [permOp_one]
  act_mul g h x := by
    have h1 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
    change ((Equiv.Perm.sign (g * h) : ℤ) : ℂ) • permOp E n (g * h)⁻¹ x
        = ((Equiv.Perm.sign g : ℤ) : ℂ) •
            permOp E n g⁻¹ (((Equiv.Perm.sign h : ℤ) : ℂ) • permOp E n h⁻¹ x)
    rw [h1, permOp_mul, map_smul, smul_smul, map_mul]
    push_cast
    ring_nf
  act_inner g x y := by
    change (inner ℂ (((Equiv.Perm.sign g : ℤ) : ℂ) • permOp E n g⁻¹ x)
      (((Equiv.Perm.sign g : ℤ) : ℂ) • permOp E n g⁻¹ y) : ℂ) = inner ℂ x y
    rw [inner_smul_left, inner_smul_right, permOp_inner]
    have : ((Equiv.Perm.sign g : ℤ) : ℂ) = 1 ∨ ((Equiv.Perm.sign g : ℤ) : ℂ) = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [h]
    rcases this with h | h <;> simp [h]

@[simp] theorem signRep_act (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (E.pow n).carrier) :
    (signRep E n).act σ x = ((Equiv.Perm.sign σ : ℤ) : ℂ) • permOp E n σ⁻¹ x := rfl

end

end BookProof.TensorPerm


