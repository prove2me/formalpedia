-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Involution
-- name    : OAI_Geometry_Arnold_Involution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:21:46.758609+00:00
-- url     : https://prove2.me/theorems/a3bf0e93-1379-49a7-8b1b-84b90c2e3b89
-- title:
--   The coordinate involution of the quadric $Q_3\subset\mathbb{CP}^4$
-- statement:
--   Write $q(z)=\sum_{j=0}^4z_j^2$ and $|z|^2=\sum_j|z_j|^2$ for $z\in\mathbb{C}^5$. The quadric is $Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$. Its points are represented by unit isotropic vectors $z$, i.e. $|z|^2=1$ and $q(z)=0$, which form the unit quadric $S$, and $\pi:S\to Q_3$ is the projection $z\mapsto[z]$. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0$ and $\sum_jz_jv_j=0$. The form $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$ is the Fubini–Study form on horizontal vectors.
--
--   1. **The linear involution.** $\iota(z)=(z_0,-z_1,-z_2,-z_3,-z_4)$, a $\mathbb{C}$-linear automorphism of $\mathbb{C}^5$ with $\iota^2=\mathrm{id}$. It preserves both $q$ and $|z|^2$.
--   2. **Induced maps.** A $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^5$ maps nonzero vectors to nonzero vectors. If $D$ preserves the cone $q=0$, it induces the map $[z]\mapsto[Dz]$ of $Q_3$ to itself.
--   3. **The involution of $Q_3$.** The bijection $[z]\mapsto[\iota z]$ of $Q_3$, which is its own inverse.
--
--   This is the map $\varphi$ of the Arnold-type counterexample. It is shown to be Hamiltonian, and its fixed points on $Q_3$ are counted.
--
--   **Formalization Note** The involution is a self-equivalence `Q3 ≃ Q3`, built from `Projectivization.map`. $Q_3$ is the subtype of `Projectivization ℂ (Fin 5 → ℂ)` of classes with an isotropic representative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Involution.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Involution.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample

namespace Quadric

/-- The linear involution fixing the first coordinate. -/
def involutionLinear : CV ≃ₗ[ℂ] CV where
  toFun z j := if j = 0 then z j else -z j
  invFun z j := if j = 0 then z j else -z j
  left_inv z := by funext j; by_cases hj : j = 0 <;> simp [hj]
  right_inv z := by funext j; by_cases hj : j = 0 <;> simp [hj]
  map_add' z w := by funext j; by_cases hj : j = 0 <;> simp [hj, add_comm]
  map_smul' a z := by funext j; by_cases hj : j = 0 <;> simp [hj]

@[simp] lemma involutionLinear_apply (z : CV) (j : Fin 5) :
    involutionLinear z j = if j = 0 then z j else -z j := rfl

@[simp] lemma involutionLinear_twice (z : CV) :
    involutionLinear (involutionLinear z) = z := involutionLinear.left_inv z

@[simp] lemma involutionLinear_quadricPolynomial (z : CV) :
    quadricPolynomial (involutionLinear z) = quadricPolynomial z := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0 <;> simp [hj]

@[simp] lemma involutionLinear_normSquared (z : CV) :
    normSquared (involutionLinear z) = normSquared z := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 0 <;> simp [hj]

/-- An injective complex-linear symmetry of the cone acts on the actual
projective quadric, not on a substitute abstract model. -/
lemma linearEquiv_ne_zero (D : CV ≃ₗ[ℂ] CV) {z : CV} (hz : z ≠ 0) : D z ≠ 0 := by
  intro h
  exact hz (D.injective (by simpa using h))

def map (D : CV ≃ₗ[ℂ] CV)
    (hD : ∀ z, quadricPolynomial z = 0 → quadricPolynomial (D z) = 0) : Q3 → Q3 :=
  fun q ↦ ⟨Projectivization.map D.toLinearMap D.injective q.val, by
    obtain ⟨z, hz, hq, hpoly⟩ := q.property
    refine ⟨D z, linearEquiv_ne_zero D hz, ?_, hD z hpoly⟩
    rw [← hq]
    rfl⟩

/-- The Hamiltonian involution's underlying projective equivalence. -/
def involution : Q3 ≃ Q3 where
  toFun := map involutionLinear (fun z hz ↦ by simpa using hz)
  invFun := map involutionLinear (fun z hz ↦ by simpa using hz)
  left_inv q := by
    apply Subtype.ext
    obtain ⟨z, hz, hq, hp⟩ := q.property
    change Projectivization.map involutionLinear.toLinearMap involutionLinear.injective
      (Projectivization.map involutionLinear.toLinearMap involutionLinear.injective q.val) = q.val
    rw [← hq]
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, involutionLinear_twice]
  right_inv q := by
    apply Subtype.ext
    obtain ⟨z, hz, hq, hp⟩ := q.property
    change Projectivization.map involutionLinear.toLinearMap involutionLinear.injective
      (Projectivization.map involutionLinear.toLinearMap involutionLinear.injective q.val) = q.val
    rw [← hq]
    simp only [Projectivization.map_mk, LinearEquiv.coe_coe, involutionLinear_twice]

@[simp] theorem involution_sq (q : Q3) : involution (involution q) = q :=
  involution.left_inv q

end Quadric
end ArnoldCounterexample

end

end OAI


