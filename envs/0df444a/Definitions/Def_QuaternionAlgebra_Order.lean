-- Prove2me | Definitions.Def_QuaternionAlgebra_Order
-- name    : QuaternionAlgebra_Order
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/de5de6a2-5303-51d6-a050-655879288b38
-- title:
--   Orders in rational quaternion algebras and optimal embeddings
-- statement:
--   Fix rationals $a,b$ and work inside the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$, i.e. the $\mathbb{Q}$-algebra with basis $1,i,j,k$ and $i^2=a$, $j^2=b$. The module sets up orders and embedding data as predicates on $\mathbb{Z}$-submodules of $B$, not on subrings. `IsOrder Λ`, for `Λ : Submodule ℤ ℍ[ℚ, a, b]`, is a structure in `Prop` with four fields: $1\in\Lambda$; $\Lambda$ is closed under the multiplication of $B$; the $\mathbb{Q}$-span of $\Lambda$ is all of $B$; and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module. Thus an order is a full $\mathbb{Z}$-lattice which is a subring. `IsUnitOf Λ u` says $u\in\Lambda$ and there is $v\in\Lambda$ with $uv=vu=1$.
--
--   For integers $t,n$, `IsQuadraticDatum t n α` is the equation $\alpha^2-t\alpha+n=0$ in $B$ (written with $\mathbb{Q}$-scalar actions on $\alpha$ and $1$), and `isQuadraticDatum_iff` records this equivalence. `EmbeddingDatum Λ t n` is the subtype (a `Type`, not a proposition) of those $\alpha$ lying in $\Lambda$ and satisfying that equation; equivalently, a ring map $\mathbb{Z}[X]/(X^2-tX+n)\to\Lambda$. `IsOptimalDatum Λ α` asserts that every $x\in\Lambda$ which lies in the $\mathbb{Q}$-span of $1$ and $\alpha$ already lies in the $\mathbb{Z}$-span of $1$ and $\alpha$, i.e. $\mathbb{Q}\langle 1,\alpha\rangle\cap\Lambda=\mathbb{Z}\langle 1,\alpha\rangle$. `HasEmbeddingConductor Λ α f` is the conjunction of: $f\cdot\bigl(\mathbb{Q}\langle 1,\alpha\rangle\cap\Lambda\bigr)\subseteq\mathbb{Z}\langle 1,\alpha\rangle$, and no $g$ with $0<g<f$ has this property; note that $f=0$ satisfies both clauses vacuously, so the predicate determines the conductor only among positive values. `EmbeddingDatum.HasConductor d f` is this applied to the underlying element of $d$. `UnitConj d d'` is the inverse-free relation $\alpha' u=u\alpha$ for some unit $u$ of $\Lambda$; `EmbeddingClassSet Λ t n` is the quotient `Quot` of `EmbeddingDatum Λ t n` by this relation (the quotient by the generated equivalence, so no proof that `UnitConj` is an equivalence is required), and `condEmbeddingCount Λ t n f` is the `Nat.card` of the set of classes admitting a representative of conductor $f$.
--
--   **Relation to Mathlib.** The ambient algebra `ℍ[ℚ, a, b]`, `Submodule ℤ` and `Submodule.FG` are Mathlib's; Mathlib has no notion of an order in a quaternion algebra, nor of quadratic/optimal embedding data or their unit-conjugacy class sets, so these are the project's own, formulated as predicates on $\mathbb{Z}$-submodules rather than on subrings.
--
--   **Where it is used.** These definitions provide the vocabulary for counting embeddings of quadratic orders into orders of rational quaternion algebras up to unit conjugacy, with the conductor recording the index of $\mathbb{Z}[\alpha]$ in $\mathbb{Q}(\alpha)\cap\Lambda$; such counts are the local input to trace computations on the quaternionic side of the Hecke-module comparisons.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_QuaternionAlgebra_Order.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace QuaternionAlgebra

open scoped Quaternion

variable {a b : ℚ}

structure IsOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop where

  one_mem : (1 : ℍ[ℚ, a, b]) ∈ Λ

  mul_mem : ∀ ⦃x y : ℍ[ℚ, a, b]⦄, x ∈ Λ → y ∈ Λ → x * y ∈ Λ

  spanTop : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤

  fg : Λ.FG

def IsUnitOf (Λ : Submodule ℤ ℍ[ℚ, a, b]) (u : ℍ[ℚ, a, b]) : Prop :=
  u ∈ Λ ∧ ∃ v ∈ Λ, u * v = 1 ∧ v * u = 1

def IsQuadraticDatum (t n : ℤ) (α : ℍ[ℚ, a, b]) : Prop :=
  α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0

def EmbeddingDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  {α : ℍ[ℚ, a, b] // α ∈ Λ ∧ IsQuadraticDatum t n α}

def IsOptimalDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) : Prop :=
  ∀ x ∈ Λ, (∃ c d : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + d • α) →
    ∃ p q : ℤ, x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α

def UnitConj {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ} (d d' : EmbeddingDatum Λ t n) : Prop :=
  ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ d'.1 * u = u * d.1

def HasEmbeddingConductor (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) : Prop :=
  (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
      ∃ p q : ℤ, (f : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α) ∧
    (∀ g : ℕ, 0 < g → g < f →
      ¬ (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
        ∃ p q : ℤ, (g : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α))

abbrev EmbeddingDatum.HasConductor {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ}
    (d : EmbeddingDatum Λ t n) (f : ℕ) : Prop :=
  HasEmbeddingConductor Λ d.1 f

def EmbeddingClassSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  Quot (UnitConj (Λ := Λ) (t := t) (n := n))

noncomputable def condEmbeddingCount (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) (f : ℕ) : ℕ :=
  Nat.card {c : EmbeddingClassSet Λ t n //
    ∃ d : EmbeddingDatum Λ t n, Quot.mk _ d = c ∧ d.HasConductor f}

theorem isQuadraticDatum_iff {t n : ℤ} {α : ℍ[ℚ, a, b]} :
    IsQuadraticDatum t n α ↔ α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0 :=
  Iff.rfl

end QuaternionAlgebra


