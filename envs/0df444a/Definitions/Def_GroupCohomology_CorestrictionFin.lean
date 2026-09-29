-- Prove2me | Definitions.Def_GroupCohomology_CorestrictionFin
-- name    : GroupCohomology_CorestrictionFin
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/91e1cbe7-803f-5d9f-8a36-9dbf2db5200b
-- title:
--   Fin-indexed restriction and transfer on inhomogeneous cochains
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ a group, $H\le G$ a subgroup of finite index, $A$ a $k$-linear representation of $G$, and $\tau$ a transversal in the sense of the imported module: a section $\sigma\colon G/H\to G$ of the projection with $\sigma(\bar 1)=1$, from which one forms $\lambda(x)=x\,\sigma(\overline{x^{-1}})\in H$. Cochains are taken in Mathlib's model: an $n$-cochain is a function $(\mathrm{Fin}\ n\to G)\to A$.
--
--   Three items are defined. First, `IsSlotInvariant U u`, for a subgroup $U\le G$ and $u\colon(\mathrm{Fin}\ n\to G)\to X$, asserts slot-wise right invariance: $u(g\cdot s)=u(g)$ for all $g$ and all $s$ with $s_i\in U$ for every $i$ (the product being taken pointwise in each slot). Second, `resFin A n u` restricts an $n$-cochain of $G$ to one of $H$ by $h\mapsto u(i\mapsto h_i)$, reading the entries $h_i\in H$ inside $G$. Third, `corFin A τ n u` is the transfer of an $n$-cochain $u$ of $H$ with values in $A$: writing $p_j=\mathrm{Fin.partialProd}\,g$ for the partial products $p_0=1$, $p_{i+1}=g_0\cdots g_i$, one sets
--   $$(\mathrm{cor}_n u)(g)=\sum_{q\in G/H}\rho_A(\sigma(q))\,u\Big(i\mapsto \lambda(\sigma(q)^{-1}p_i)^{-1}\,\lambda(\sigma(q)^{-1}p_{i+1})\Big),$$
--   the sum being over the finite set $G/H$ (a `Fintype` structure on the quotient $G/H$ from the imported module is used). The accompanying lemma `corFin_apply` records this formula as the defining equation. Thus the construction is uniform in $n$ and depends on the chosen transversal; in degrees $1$ and $2$ it specialises to the pair-model maps `cor₁`, `cor₂` of the imported module.
--
--   **Relation to Mathlib.** Cochains are Mathlib's inhomogeneous model $(\mathrm{Fin}\ n\to G)\to A$ for `A : Rep k G`; the cochain-level transfer `corFin`, the restriction `resFin` written directly in that model, and the slot-invariance predicate are the project's own, as is the `Transversal` structure of the imported module.
--
--   **Where it is used.** These cochain-level maps underlie the transfer arguments used downstream: that corestriction is a cochain map, that it preserves slot-wise invariance under a normal subgroup of $G$ contained in $H$, and that $\mathrm{cor}\circ\mathrm{res}$ is multiplication by $[G:H]$ up to an explicit coboundary, whence injectivity of restriction on degree-three cohomology for subgroups of index invertible in $k$. This is the Sylow-type step in bounding the cohomological dimension of the relevant Galois groups, as needed in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_CorestrictionFin.lean

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace groupCohomology
namespace Cores

def IsSlotInvariant {G : Type*} [Group G] {X : Type*} {n : ℕ} (U : Subgroup G) (u : (Fin n → G) → X) : Prop :=
  ∀ g s : Fin n → G, (∀ i, s i ∈ U) → u (g * s) = u g

variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G}

def resFin (A : Rep.{0} k G) (n : ℕ) (u : (Fin n → G) → A) : (Fin n → H) → A :=
  fun h => u (fun i => (h i : G))

variable [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)

attribute [local instance] fintypeQuot

noncomputable def corFin (n : ℕ) (u : (Fin n → H) → A) : (Fin n → G) → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q)
    (u (fun i => (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹
                   * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ)))

lemma corFin_apply (n : ℕ) (u : (Fin n → H) → A) (g : Fin n → G) :
    corFin A τ n u g = ∑ q : G ⧸ H, A.ρ (τ.σ q)
      (u (fun i => (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹
                     * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ))) := rfl

end Cores
end groupCohomology


