-- Prove2me | Definitions.Def_SmaleDiffS4_Basic
-- name    : SmaleDiffS4_Basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T12:32:12.368987+00:00
-- url     : https://prove2.me/theorems/84d01d36-7eac-4927-8f7d-9902f19b3884
-- title:
--   $\mathrm{Diff}(D^n)$, $\mathrm{Diff}(S^n)$ with the $C^\infty$ topology, and $O(n)$
-- statement:
--   This file fixes the objects in terms of which the whole mission is stated.
--
--   1. $\mathrm{Diff}(D^n)$ (`DiffDisk n`): the group of smooth ($C^\infty$) diffeomorphisms $f$ of $\mathbb R^n$ such that $f(x)=x$ for every $x$ with $\|x\|\ge 1$. This is the standard model of the group of diffeomorphisms of the closed $n$-ball that are the identity on (a neighbourhood of) the boundary. Its base point is the identity.
--   2. $\mathrm{Diff}(S^n)$ (`DiffSphere n`): the group of all smooth diffeomorphisms of the round unit sphere $S^n\subset\mathbb R^{n+1}$, with Mathlib's standard smooth structure on the sphere; both orientation-preserving and orientation-reversing maps are included. Its base point is the identity.
--   3. $O(n)$ (`OrthGroup n`): the real orthogonal $n\times n$ matrices, with the subspace topology from the space of matrices.
--
--   Both diffeomorphism groups carry the $C^\infty$ topology. On $\mathrm{Diff}(D^n)$ a net $f_\alpha$ converges to $f$ exactly when, for every $k\ge 0$, the $k$-th derivatives $D^k f_\alpha$ converge to $D^k f$ uniformly on $\mathbb R^n$. On $\mathrm{Diff}(S^n)$ the same is required of the degree-one homogeneous extension
--   $$\tilde f(x)=\|x\|\, f\!\left(\frac{x}{\|x\|}\right)\qquad (x\neq 0),$$
--   with the derivatives evaluated at points of $S^n$. Because $\tilde f$ is homogeneous, this is the usual $C^\infty$ topology on maps $S^n\to S^n\subset\mathbb R^{n+1}$.
--
--   **Formalization Note** The topologies are defined as the initial topologies of the maps $f\mapsto (D^k f)_{k\in\mathbb N}$ into a product of spaces of functions with the topology of uniform convergence (`UniformFun`). The radial extension is given the junk value $0$ at the origin; this does not affect derivatives at points of the sphere.
-- source:
--   Open Problem Garden, 'What is the homotopy type of the group of diffeomorphisms of the 4-sphere?' (S. Smale; posted by rybu, 2009), http://www.openproblemgarden.org/op/what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere — problem statement: 'Diff(D^4) is the group of diffeomorphisms of the 4-ball which restrict to the identity on the boundary'; Diff(S^n) and O_{n+1} as in discussion paragraph 2.

import Mathlib

/-!
# Diffeomorphism groups of the disc and the sphere, with the C^∞ topology

Basic objects for the question "What is the homotopy type of the group of diffeomorphisms
of the 4-sphere?" (S. Smale; Open Problem Garden).

* `SmaleDiffS4.DiffDisk n` : diffeomorphisms of `ℝⁿ` that are the identity outside the open
  unit ball, i.e. diffeomorphisms of the closed unit disc `Dⁿ` agreeing with the identity
  (to infinite order) on the boundary sphere. This is the standard model of `Diff(Dⁿ rel ∂)`.
* `SmaleDiffS4.DiffSphere n` : all smooth (`C^∞`) diffeomorphisms of the round unit sphere
  `Sⁿ ⊆ ℝⁿ⁺¹` (orientation-preserving and orientation-reversing).
* `SmaleDiffS4.OrthGroup n` : the orthogonal group `O(n)` with its usual (matrix) topology.

Both diffeomorphism groups carry the (weak = strong, here) `C^∞` topology: uniform
convergence of all derivatives. For the sphere, derivatives are taken of the degree-one
homogeneous (radial) extension `x ↦ ‖x‖ • f (x / ‖x‖)` to `ℝⁿ⁺¹ \ {0}` and evaluated on the
sphere itself.
-/

open scoped ContDiff Manifold
open Metric

namespace SmaleDiffS4

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The group `Diff(Dⁿ rel ∂)`: smooth diffeomorphisms of `ℝⁿ` equal to the identity at
every point of norm `≥ 1`. -/
def DiffDisk (n : ℕ) : Type :=
  {f : Diffeomorph 𝓘(ℝ, E n) 𝓘(ℝ, E n) (E n) (E n) ∞ // ∀ x : E n, 1 ≤ ‖x‖ → f x = x}

/-- The `C^∞` jet map of a disc diffeomorphism: its `k`-th iterated derivative, for each `k`,
viewed as an element of the space of functions with the topology of uniform convergence. -/
noncomputable def diskJet (n : ℕ) (f : DiffDisk n) :
    (k : ℕ) → UniformFun (E n) (ContinuousMultilinearMap ℝ (fun _ : Fin k => E n) (E n)) :=
  fun k => UniformFun.ofFun (iteratedFDeriv ℝ k (f.1 : E n → E n))

/-- The `C^∞` topology on `Diff(Dⁿ rel ∂)`: uniform convergence of all derivatives. -/
noncomputable instance (n : ℕ) : TopologicalSpace (DiffDisk n) :=
  TopologicalSpace.induced (diskJet n) inferInstance

/-- The identity diffeomorphism, the base point of `Diff(Dⁿ rel ∂)`. -/
noncomputable instance (n : ℕ) : One (DiffDisk n) :=
  ⟨⟨Diffeomorph.refl 𝓘(ℝ, E n) (E n) ∞, fun _ _ => rfl⟩⟩

/-- The round unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, with Mathlib's standard smooth manifold structure. -/
abbrev Sph (n : ℕ) : Type := sphere (0 : E (n + 1)) 1

/-- The group `Diff(Sⁿ)` of all smooth diffeomorphisms of the round unit sphere. -/
def DiffSphere (n : ℕ) : Type :=
  Diffeomorph (𝓡 n) (𝓡 n) (Sph n) (Sph n) ∞

lemma smul_inv_norm_mem_sph {n : ℕ} {x : E (n + 1)} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ sphere (0 : E (n + 1)) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The degree-one homogeneous extension `x ↦ ‖x‖ • f (x / ‖x‖)` of a self-map of `Sⁿ` to
`ℝⁿ⁺¹` (with value `0` at the origin). -/
noncomputable def radialExt {n : ℕ} (f : Sph n → Sph n) : E (n + 1) → E (n + 1) :=
  fun x => if hx : x = 0 then 0 else ‖x‖ • (f ⟨‖x‖⁻¹ • x, smul_inv_norm_mem_sph hx⟩ : E (n + 1))

/-- The `C^∞` jet map of a sphere diffeomorphism: for each `k`, the `k`-th iterated derivative
of its radial extension, restricted to the sphere, with the topology of uniform convergence. -/
noncomputable def sphereJet (n : ℕ) (f : DiffSphere n) :
    (k : ℕ) → UniformFun (Sph n)
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => E (n + 1)) (E (n + 1))) :=
  fun k => UniformFun.ofFun fun x : Sph n =>
    iteratedFDeriv ℝ k
      (radialExt ⇑(show Diffeomorph (𝓡 n) (𝓡 n) (Sph n) (Sph n) ∞ from f))
      (x : E (n + 1))

/-- The `C^∞` topology on `Diff(Sⁿ)`. -/
noncomputable instance (n : ℕ) : TopologicalSpace (DiffSphere n) :=
  TopologicalSpace.induced (sphereJet n) inferInstance

/-- The identity diffeomorphism, the base point of `Diff(Sⁿ)`. -/
noncomputable instance (n : ℕ) : One (DiffSphere n) :=
  ⟨Diffeomorph.refl (𝓡 n) (Sph n) ∞⟩

/-- The orthogonal group `O(n)` of real `n × n` matrices, with the subspace topology. -/
abbrev OrthGroup (n : ℕ) : Type := Matrix.orthogonalGroup (Fin n) ℝ

end SmaleDiffS4


