-- Prove2me | Definitions.Def_QuaternionAlgebra_QMPeriodLattice
-- name    : QuaternionAlgebra_QMPeriodLattice
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/b224dd5e-f4c2-59a5-b518-2402b0a25037
-- title:
--   Period map and period lattice of a rational quaternion algebra
-- statement:
--   Fix rationals $a,b$ and work with the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ in Mathlib's presentation, i.e. the $\mathbb{Q}$-algebra with basis $1,i,j,k$ and $i^2=a$, $j^2=b$, $k=ij=-ji$. Given a $\mathbb{Q}$-algebra homomorphism $\iota \colon \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ and a point $\tau$ of the upper half-plane, `qmPeriodMap` is the $\mathbb{Z}$-linear map $\mathbb{H}[\mathbb{Q},a,b] \to \mathbb{C}^2$ (target the function type `Fin 2 → ℂ`) sending $x$ to the matrix–vector product of the entrywise complexification of $\iota(x)$ with the column vector $(\tau,1)$; thus $x \mapsto \iota(x)\binom{\tau}{1}$, where $\tau$ is the complex number underlying the upper half-plane point. The accompanying lemma `qmPeriodMap_apply` records this defining formula for the bundled map.
--
--   Given in addition a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ — in the intended applications an order, or a one-sided ideal of an order — `qmPeriodLattice` is the $\mathbb{Z}$-submodule of $\mathbb{C}^2$ obtained as the image $\Lambda$ under `qmPeriodMap ι τ`. It is by construction a subgroup of $\mathbb{C}^2$, with no discreteness, rank or stability claim attached: nothing here asserts that it is a lattice, and no hypothesis such as $ab \neq 0$ or indefiniteness of the algebra is imposed on $\iota$ beyond its being a $\mathbb{Q}$-algebra map. The lemma `mem_qmPeriodLattice_iff` unfolds membership: a vector $v \in \mathbb{C}^2$ lies in `qmPeriodLattice ι Λ τ` exactly when $v = \iota(x)\binom{\tau}{1}$ for some $x \in \Lambda$.
--
--   **Relation to Mathlib.** Built on Mathlib's `QuaternionAlgebra` presentation $\mathbb{H}[\mathbb{Q},a,b]$, `UpperHalfPlane` and `Submodule.map`; Mathlib has no notion of the period map or period lattice attached to a splitting of a quaternion algebra, so these are the project's own definitions.
--
--   **Where it is used.** These are the analytic data out of which complex tori $\mathbb{C}^2/\Lambda_\tau$ with quaternionic multiplication are formed, the uniformisation underlying the Shimura curves and quaternionic automorphic forms used on the modularity side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_QuaternionAlgebra_QMPeriodLattice.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped Quaternion

namespace QuaternionAlgebra

variable {a b : ℚ}

def qmPeriodMap (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => ((ι x).map (algebraMap ℝ ℂ)).mulVec ![(τ : ℂ), 1]
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.map_add, Matrix.add_mulVec] }

@[simp]
theorem qmPeriodMap_apply (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane)
    (x : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ x = ((ι x).map (algebraMap ℝ ℂ)).mulVec ![(τ : ℂ), 1] :=
  rfl

def qmPeriodLattice (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (τ : UpperHalfPlane) : Submodule ℤ (Fin 2 → ℂ) :=
  Λ.map (qmPeriodMap ι τ)

theorem mem_qmPeriodLattice_iff (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (τ : UpperHalfPlane) (v : Fin 2 → ℂ) :
    v ∈ qmPeriodLattice ι Λ τ ↔ ∃ x ∈ Λ, qmPeriodMap ι τ x = v :=
  Submodule.mem_map

end QuaternionAlgebra

end


