-- Prove2me | Definitions.Def_ChapterMackeyInducedSystem
-- name    : ChapterMackeyInducedSystem
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-07T15:31:51.232964+00:00
-- url     : https://prove2.me/theorems/d35d4428-24c8-4035-a3ab-80b42c9541fa
-- title:
--   The Lean 4 theorem `cocycle_one` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMackeyInducedSystem.lean`): generated def bundle for ChapterMackeyInducedSystem. See BookProof/ChapterMackeyInducedSystem.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyInducedSystem.lean

import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_cocycle_mem_stabilizer







import Definitions.Def_ChapterMackeyImprimitivity
import Mathlib


/-!
# Mackey's imprimitivity theorem, the converse direction (book.tex, Note 33 / Note 84)

`BookProof.ChapterMackeyImprimitivity` proves one half of Mackey's theorem in the
transitive discrete case: every system of imprimitivity `(U, p)` of `G` over a finite
transitive `G`-space `X` is unitarily equivalent to the system induced by the
representation `L = U|_H` of the stabilizer `H = Stab(x₀)` on the fibre `ran p x₀`.

Note 84 of `book.tex` uses the statement as a **one-to-one correspondence** between systems
of imprimitivity based on the homogeneous space and representations of the little group.
This file supplies the missing half of that correspondence: for *every* unitary
representation `L` of the stabilizer `H` on a complex Hilbert space `K`, the induced data

  `(V g f) x = L (cocycle g x) (f (g⁻¹ • x))`,   `cocycle g x = (s x)⁻¹ g s (g⁻¹ • x)`,
  `(P y f) x = if x = y then f x else 0`

on the space of `K`-valued fields over `X` (with the `ℓ²` inner product, `PiLp 2`) really
**is** a system of imprimitivity in the sense of `ImprimitivitySystem` — and its fibre
representation over `x₀` is `L` again, so the two constructions are mutually inverse.

## Results

* `cocycle_one`, `cocycle_mul` — the cocycle identities
  `c 1 x = 1`, `c (g₁g₂) x = c g₁ x · c g₂ (g₁⁻¹ • x)`, which make the induced maps a
  representation;
* `indRepLin` — the induced operator of `g`, linear on the field space, with
  `indRepLin_one`, `indRepLin_comp` and `indRepLin_norm` (it is an isometry);
* `indRep` — the induced *unitary*, and `indRepHom`, the induced unitary representation of
  `G` by linear isometry equivalences of the field space;
* `indPvm` — the induced projection-valued measure (multiplication by indicators), a
  bounded operator;
* **`inducedSystem`** — the bundled `ImprimitivitySystem G X (FieldSpace X K)`: the induced
  data satisfy self-adjointness, idempotence, orthogonality, completeness and the
  covariance relation `V(g) P(A) V(g)⁻¹ = P(gA)`;
* **`inducedSystem_fibre`** and **`inducedSystem_stabilizer_rep`** — the fibre of the
  induced system over `x₀` consists of the fields supported at `x₀`, and (for the
  normalized section `s x₀ = 1`) the stabilizer acts on it by `L`: the induced system
  reproduces the representation it was induced from;
* **`mackey_correspondence`** — both halves together.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace
open Finset

namespace BookProof.ChapterMackeyInducedSystem

open BookProof.ChapterMackeyImprimitivity

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [DecidableEq X] [MulAction G X]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {x₀ : X}

/-- The space of `K`-valued fields on the finite base `X`, with the `ℓ²` inner product. -/
abbrev FieldSpace (X K : Type*) [Fintype X] [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  PiLp 2 (fun _ : X => K)

/-! ## The cocycle identities -/

omit [Fintype X] [DecidableEq X] in
theorem cocycle_one (s : X → G) (x : X) : cocycle s 1 x = 1 := by
  simp [cocycle]

omit [Fintype X] [DecidableEq X] in
theorem cocycle_mul (s : X → G) (g₁ g₂ : G) (x : X) :
    cocycle s (g₁ * g₂) x = cocycle s g₁ x * cocycle s g₂ (g₁⁻¹ • x) := by
  have hx : (g₁ * g₂)⁻¹ • x = g₂⁻¹ • (g₁⁻¹ • x) := by
    rw [mul_inv_rev, mul_smul]
  rw [cocycle, cocycle, cocycle, hx]
  group

/-! ## The induced representation -/

/-- The induced operator of `g` on the field space, as a linear map. -/
noncomputable def indRepLin (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) (g : G) : FieldSpace X K →ₗ[ℂ] FieldSpace X K where
  toFun f := WithLp.toLp 2 fun x =>
    L ⟨cocycle s g x, cocycle_mem_stabilizer hs g x⟩ (f (g⁻¹ • x))
  map_add' f h := by ext x; simp
  map_smul' a f := by ext x; simp

variable {L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)} {s : X → G}

omit [DecidableEq X] in
theorem indRepLin_apply (hs : ∀ x, s x • x₀ = x) (g : G) (f : FieldSpace X K) (x : X) :
    (indRepLin L s hs g f) x = L ⟨cocycle s g x, cocycle_mem_stabilizer hs g x⟩ (f (g⁻¹ • x)) :=
  rfl

omit [DecidableEq X] in
theorem indRepLin_one (hs : ∀ x, s x • x₀ = x) (f : FieldSpace X K) :
    indRepLin L s hs 1 f = f := by
  ext x
  rw [indRepLin_apply]
  have h1 : (⟨cocycle s 1 x, cocycle_mem_stabilizer hs 1 x⟩ :
      MulAction.stabilizer G x₀) = 1 := Subtype.ext (cocycle_one s x)
  rw [h1]
  simp

omit [DecidableEq X] in
theorem indRepLin_comp (hs : ∀ x, s x • x₀ = x) (g₁ g₂ : G) (f : FieldSpace X K) :
    indRepLin L s hs g₁ (indRepLin L s hs g₂ f) = indRepLin L s hs (g₁ * g₂) f := by
  ext x
  rw [indRepLin_apply, indRepLin_apply, indRepLin_apply]
  have hmul : (⟨cocycle s (g₁ * g₂) x, cocycle_mem_stabilizer hs (g₁ * g₂) x⟩ :
        MulAction.stabilizer G x₀) =
      (⟨cocycle s g₁ x, cocycle_mem_stabilizer hs g₁ x⟩ : MulAction.stabilizer G x₀) *
        ⟨cocycle s g₂ (g₁⁻¹ • x), cocycle_mem_stabilizer hs g₂ (g₁⁻¹ • x)⟩ :=
    Subtype.ext (cocycle_mul s g₁ g₂ x)
  rw [hmul, map_mul]
  have hx : (g₁ * g₂)⁻¹ • x = g₂⁻¹ • (g₁⁻¹ • x) := by rw [mul_inv_rev, mul_smul]
  rw [hx]
  rfl

omit [DecidableEq X] in
/-- The induced operators are isometries. -/
theorem indRepLin_norm (hs : ∀ x, s x • x₀ = x) (g : G) (f : FieldSpace X K) :
    ‖indRepLin L s hs g f‖ = ‖f‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  have hcoord : ∀ x : X, ‖(indRepLin L s hs g f) x‖ ^ 2 = ‖f (g⁻¹ • x)‖ ^ 2 := by
    intro x
    rw [indRepLin_apply, LinearIsometryEquiv.norm_map]
  simp only [hcoord]
  exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ (fun x => rfl)

variable (L s)

/-- The induced unitary of `g`. -/
noncomputable def indRep (hs : ∀ x, s x • x₀ = x) (g : G) :
    FieldSpace X K ≃ₗᵢ[ℂ] FieldSpace X K :=
  LinearIsometryEquiv.mk
    { toLinearMap := indRepLin L s hs g
      invFun := indRepLin L s hs g⁻¹
      left_inv := fun f => by
        change indRepLin L s hs g⁻¹ (indRepLin L s hs g f) = f
        rw [indRepLin_comp, inv_mul_cancel, indRepLin_one]
      right_inv := fun f => by
        change indRepLin L s hs g (indRepLin L s hs g⁻¹ f) = f
        rw [indRepLin_comp, mul_inv_cancel, indRepLin_one] }
    (indRepLin_norm hs g)

/-- The **induced unitary representation** of `G` on the space of fields. -/
noncomputable def indRepHom (hs : ∀ x, s x • x₀ = x) :
    G →* (FieldSpace X K ≃ₗᵢ[ℂ] FieldSpace X K) where
  toFun g := indRep L s hs g
  map_one' := by
    ext f x
    exact congrFun (congrArg WithLp.ofLp (indRepLin_one hs f)) x
  map_mul' g₁ g₂ := by
    ext f x
    exact congrFun (congrArg WithLp.ofLp (indRepLin_comp hs g₁ g₂ f).symm) x

variable {L s}

omit [DecidableEq X] in
theorem indRepHom_apply (hs : ∀ x, s x • x₀ = x) (g : G) (f : FieldSpace X K) (x : X) :
    (indRepHom L s hs g f) x =
      L ⟨cocycle s g x, cocycle_mem_stabilizer hs g x⟩ (f (g⁻¹ • x)) := rfl

/-! ## The induced projection-valued measure -/

variable (X K) in
/-- Multiplication by the indicator of `{y}`, as a linear map on the field space. -/
def indPvmLin (y : X) : FieldSpace X K →ₗ[ℂ] FieldSpace X K where
  toFun f := WithLp.toLp 2 fun x => if x = y then f x else 0
  map_add' f g := by ext x; by_cases h : x = y <;> simp [h]
  map_smul' a f := by ext x; by_cases h : x = y <;> simp [h]

theorem indPvmLin_apply (y : X) (f : FieldSpace X K) (x : X) :
    (indPvmLin X K y f) x = if x = y then f x else 0 := rfl

theorem indPvmLin_norm_le (y : X) (f : FieldSpace X K) : ‖indPvmLin X K y f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum ?_
  intro x _
  by_cases h : x = y
  · simp [indPvmLin_apply, h]
  · rw [indPvmLin_apply, if_neg h, norm_zero, zero_pow (two_ne_zero)]
    positivity

variable (X K) in
/-- The atoms of the induced projection-valued measure, as bounded operators. -/
noncomputable def indPvm (y : X) : FieldSpace X K →L[ℂ] FieldSpace X K :=
  LinearMap.mkContinuous (indPvmLin X K y) 1 (indPvmLin_norm_le y)

theorem indPvm_apply (y : X) (f : FieldSpace X K) (x : X) :
    (indPvm X K y f) x = if x = y then f x else 0 := rfl

/-! ## The induced system of imprimitivity -/

/-- **The converse half of Mackey's theorem.**  The data induced from a unitary
representation `L` of the stabilizer `H = Stab(x₀)` on `K` form a system of imprimitivity
of `G` over `X`. -/
noncomputable def inducedSystem (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) : ImprimitivitySystem G X (FieldSpace X K) where
  U := indRepHom L s hs
  p := indPvm X K
  selfAdjoint y u v := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x = y <;> simp [indPvm_apply, h]
  idem y f := by ext x; by_cases h : x = y <;> simp [indPvm_apply, h]
  orthogonal y z hyz f := by
    ext x
    by_cases h : x = y
    · subst h
      simp [indPvm_apply, hyz]
    · simp [indPvm_apply, h]
  complete f := by
    ext x
    have happ : ((∑ y : X, indPvm X K y f) : FieldSpace X K) x =
        ∑ y : X, ((indPvm X K y f : FieldSpace X K) x) := by
      simp
    rw [happ]
    simp [indPvm_apply]
  covariant g y f := by
    ext x
    rw [show ((indRepHom L s hs g) (indPvm X K y f)) x =
        L ⟨cocycle s g x, cocycle_mem_stabilizer hs g x⟩ ((indPvm X K y f) (g⁻¹ • x)) from rfl,
      show ((indPvm X K (g • y)) ((indRepHom L s hs g) f)) x =
        if x = g • y then ((indRepHom L s hs g) f) x else 0 from rfl,
      indRepHom_apply, indPvm_apply]
    by_cases h : x = g • y
    · have h' : g⁻¹ • x = y := by rw [h, inv_smul_smul]
      rw [if_pos h', if_pos h]
    · have h' : g⁻¹ • x ≠ y := by
        intro hc
        exact h (by rw [← hc, smul_inv_smul])
      rw [if_neg h', if_neg h, map_zero]

/-! ## The induced system reproduces `L` -/





/-! ## The correspondence -/



end BookProof.ChapterMackeyInducedSystem


