-- Prove2me | Definitions.Def_AlgebraicGeometry_MumfordTruncation
-- name    : AlgebraicGeometry_MumfordTruncation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/7422ac69-d4e3-5c5f-b3bc-0c95fc049220
-- title:
--   Kernel-of-coproduct truncation of a two-term complex
-- statement:
--   Over a commutative ring $R$, the namespace `TwoChartCech.KerCoprod` attaches to a pair of $R$-linear maps $d\colon C^0\to C^1$ and $g\colon P\to C^1$ with common target a new two-term complex mapping to $d$. Its degree-zero term is the submodule `K0 d g` $=\ker\bigl([d,g]\colon C^0\times P\to C^1\bigr)$ of $C^0\times P$, whose membership criterion `mem_K0_iff` reads $d(z_1)+g(z_2)=0$; its differential `dK d g` is the second projection restricted to this kernel, with target $P$. The comparison maps are `ι0 d g`, the first projection restricted to `K0 d g`, and `ι1 g`, defined to be $-g$ (recorded by `ι1_eq`). The theorem `comm` states that $\iota_0$ followed by $d$ equals $d_K$ followed by $\iota_1$, i.e. the square
--   $$\begin{array}{ccc}K^0&\xrightarrow{d_K}&P\\ \downarrow\iota_0&&\downarrow\iota_1\\ C^0&\xrightarrow{\ d\ }&C^1\end{array}$$
--   commutes, which is exactly the defining relation of $K^0$; `ι0_prod_dK` says that the pair $(\iota_0,d_K)$ assembled into a map to $C^0\times P$ is the inclusion of the submodule. Simplification lemmas evaluate the three maps on elements.
--
--   The namespace `TwoChartCech.Mumford` specialises this to one fixed choice of $g$, under the standing assumption that the cokernel $C^1/\operatorname{im} d$ is a finite $R$-module: `rank d` is a natural number $m$ for which a surjection `quot d` $\colon R^m\twoheadrightarrow C^1/\operatorname{im} d$ exists (`quot_surjective`), extracted from the finiteness hypothesis, and `lift d` $\colon R^m\to C^1$ is a lift of `quot d` through the quotient map, obtained from projectivity of $R^m$; `mkQ_comp_lift` and `mkQ_lift_apply` record that composing `lift d` with the projection $C^1\to C^1/\operatorname{im} d$ gives `quot d`. Consequently `surjective_coprod` asserts that $[d,\ \mathrm{lift}\,d]\colon C^0\times R^m\to C^1$, $(x,v)\mapsto d(x)+\mathrm{lift}(v)$, is surjective. The abbreviations `Mumford.K0 d`, `dK d`, `ι0 d`, `ι1 d` are the general construction evaluated at $g=$ `lift d`, together with the corresponding membership criterion, evaluation lemmas and the commuting square `Mumford.comm`. Note that `rank d`, `quot d` and `lift d` depend on choices made by the finiteness and projectivity statements, so they are a chosen presentation of the cokernel rather than canonical data.
--
--   **Relation to Mathlib.** Mathlib has no truncation construction of this kind; it is assembled here from Mathlib's `LinearMap.coprod`, kernels and quotients, the cardinality form of `Module.Finite` (`Module.Finite.exists_fin'`) and the projective lifting property `Module.projective_lifting_property`.
--
--   **Where it is used.** The construction is the truncation step used when a two-term complex with finitely generated cohomology is replaced by one whose degree-one term is finite free, so that ranks and base change can be controlled; it is imported by the modules of the tree that carry out such two-chart Čech computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_MumfordTruncation.lean

import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Module.Projective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v w w'

namespace TwoChartCech

namespace KerCoprod

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable {P : Type w'} [AddCommGroup P] [Module R P]
variable (d : C0 →ₗ[R] C1) (g : P →ₗ[R] C1)

abbrev K0 : Submodule R (C0 × P) := LinearMap.ker (d.coprod g)

theorem mem_K0_iff (z : C0 × P) : z ∈ K0 d g ↔ d z.1 + g z.2 = 0 := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply]

def dK : K0 d g →ₗ[R] P := (LinearMap.snd R C0 P) ∘ₗ (K0 d g).subtype

def ι0 : K0 d g →ₗ[R] C0 := (LinearMap.fst R C0 P) ∘ₗ (K0 d g).subtype

def ι1 : P →ₗ[R] C1 := -g

@[simp] theorem dK_apply (z : K0 d g) : dK d g z = (z : C0 × P).2 := rfl
@[simp] theorem ι0_apply (z : K0 d g) : ι0 d g z = (z : C0 × P).1 := rfl
@[simp] theorem ι1_apply (p : P) : ι1 g p = -g p := rfl
theorem ι1_eq : ι1 g = -g := rfl

theorem comm : d ∘ₗ ι0 d g = ι1 g ∘ₗ dK d g := by
  ext z
  have hz : d (z : C0 × P).1 + g (z : C0 × P).2 = 0 := (mem_K0_iff d g _).mp z.2
  simp only [LinearMap.comp_apply, ι0_apply, dK_apply, ι1_apply, eq_neg_iff_add_eq_zero]
  exact hz

theorem ι0_prod_dK : (ι0 d g).prod (dK d g) = (K0 d g).subtype := by
  ext z <;> rfl

end KerCoprod

namespace Mumford

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def rank : ℕ := (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose

def quot : (Fin (rank d) → R) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose

theorem quot_surjective : Function.Surjective (quot d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose_spec

def lift : (Fin (rank d) → R) →ₗ[R] C1 :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose

theorem mkQ_comp_lift : (LinearMap.range d).mkQ ∘ₗ lift d = quot d :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose_spec

theorem mkQ_lift_apply (v : Fin (rank d) → R) : (LinearMap.range d).mkQ (lift d v) = quot d v := by
  rw [← LinearMap.comp_apply, mkQ_comp_lift]

theorem surjective_coprod : Function.Surjective (d.coprod (lift d)) := by
  intro y
  obtain ⟨v, hv⟩ := quot_surjective d ((LinearMap.range d).mkQ y)
  have hy : y - lift d v ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← hv, mkQ_lift_apply, sub_self]
  obtain ⟨x, hx⟩ := hy
  exact ⟨(x, v), by simp only [LinearMap.coprod_apply, hx, sub_add_cancel]⟩

abbrev K0 : Submodule R (C0 × (Fin (rank d) → R)) := KerCoprod.K0 d (lift d)

theorem mem_K0_iff (z : C0 × (Fin (rank d) → R)) : z ∈ K0 d ↔ d z.1 + lift d z.2 = 0 :=
  KerCoprod.mem_K0_iff d (lift d) z

abbrev dK : K0 d →ₗ[R] (Fin (rank d) → R) := KerCoprod.dK d (lift d)

abbrev ι0 : K0 d →ₗ[R] C0 := KerCoprod.ι0 d (lift d)

abbrev ι1 : (Fin (rank d) → R) →ₗ[R] C1 := KerCoprod.ι1 (lift d)

@[simp] theorem dK_apply (z : K0 d) : dK d z = (z : C0 × (Fin (rank d) → R)).2 := rfl
@[simp] theorem ι0_apply (z : K0 d) : ι0 d z = (z : C0 × (Fin (rank d) → R)).1 := rfl
@[simp] theorem ι1_apply (v : Fin (rank d) → R) : ι1 d v = -lift d v := rfl
theorem ι1_eq : ι1 d = -lift d := rfl

theorem comm : d ∘ₗ ι0 d = ι1 d ∘ₗ dK d := KerCoprod.comm d (lift d)

theorem ι0_prod_dK : (ι0 d).prod (dK d) = (K0 d).subtype := KerCoprod.ι0_prod_dK d (lift d)

end Mumford

section Gates

example (x : ℤ) (v : Fin (Mumford.rank (0 : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (x, v) ∈ Mumford.K0 (0 : ℤ →ₗ[ℤ] ℤ) ↔ Mumford.lift (0 : ℤ →ₗ[ℤ] ℤ) v = 0 := by
  rw [Mumford.mem_K0_iff, LinearMap.zero_apply, zero_add]

example (v : Fin (Mumford.rank (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (-(Mumford.lift (LinearMap.id : ℤ →ₗ[ℤ] ℤ) v), v) ∈ Mumford.K0 (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  rw [Mumford.mem_K0_iff, LinearMap.id_apply, neg_add_cancel]

example (R : Type u) [CommRing R] :
    (0 : R →ₗ[R] R) ∘ₗ Mumford.ι0 (0 : R →ₗ[R] R) = Mumford.ι1 (0 : R →ₗ[R] R) ∘ₗ Mumford.dK (0 : R →ₗ[R] R) :=
  Mumford.comm 0

example (R : Type u) [CommRing R] (d : R →ₗ[R] R) (x : R) (p : PUnit.{u + 1}) :
    (x, p) ∈ KerCoprod.K0 d (0 : PUnit →ₗ[R] R) ↔ d x = 0 := by
  rw [KerCoprod.mem_K0_iff, LinearMap.zero_apply, add_zero]

end Gates

end TwoChartCech

end


