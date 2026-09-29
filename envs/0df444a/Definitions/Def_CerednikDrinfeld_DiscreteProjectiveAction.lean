-- Prove2me | Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
-- name    : CerednikDrinfeld_DiscreteProjectiveAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/8f1b2f41-c845-5b60-8fdd-2cedeae0e919
-- title:
--   Valuative discreteness of a representation into PGL2​
-- statement:
--   The module introduces a single predicate, [`CerednikDrinfeld.Omega.IsDiscrete`](../def/CerednikDrinfeld_DiscreteProjectiveAction.html#L10), formulated for a field $K_0$, an extension field $K$ of $K_0$ (an algebra over $K_0$) carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, a group $G$, and a homomorphism $\rho \colon G \to \mathrm{PGL}_2(K_0)$. The predicate asserts: for every $\varepsilon \in \Gamma_0$ with $\varepsilon \neq 0$, the set of those $\gamma \in G$ for which there exists $g \in \mathrm{GL}_2(K_0)$ with
--
--   $[g] = \rho(\gamma)$ in $\mathrm{PGL}_2(K_0)$, $v(g_{ij}) \le 1$ for all $i,j$, and $v(\det g) \ge \varepsilon$,
--
--   is finite. Here the entries and the determinant of $g$, which lie in $K_0$, are transported into $K$ along the structure map $K_0 \to K$ before $v$ is applied, and $[g]$ denotes the image of $g$ under the projection $\mathrm{GL}_2(K_0) \to \mathrm{PGL}_2(K_0)$. Thus discreteness is expressed entirely through the valuation of $K$: an element of $G$ is counted when its image admits an integral representative matrix whose determinant is not too small in valuation, and for each fixed bound only finitely many elements of $G$ are counted. No topology on $G$, on $K_0$ or on $\mathrm{PGL}_2(K_0)$ enters, and the condition is imposed on $\rho$ itself, so it simultaneously constrains the kernel of $\rho$ and the image. The extension field $K$ together with its valuation is an explicit argument of the predicate.
--
--   **Relation to Mathlib.** Built on Mathlib's `Valued`, `GL (Fin 2) K₀` and the projective linear group `PGL(2, K₀)` with its quotient map `Matrix.ProjGenLinGroup.mk`; the discreteness condition itself, stated by valuations of integral representatives rather than by a group topology, is the project's own notion.
--
--   **Where it is used.** The predicate is the standing hypothesis on $\rho$ in the development of the Drinfeld upper half-plane $K \setminus K_0$ with its Möbius action of $\mathrm{PGL}_2(K_0)$, where it controls the infinite products [`CerednikDrinfeld.Omega.theta`](../def/CerednikDrinfeld_DrinfeldUpperHalfPlane.html#L165) built from cross-ratio factors and hence the automorphy properties of the resulting functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_DiscreteProjectiveAction.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

namespace CerednikDrinfeld
namespace Omega

def IsDiscrete {K₀ : Type*} [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) : Prop :=
  ∀ ε : Γ₀, ε ≠ 0 →
    {γ : G | ∃ g : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = ρ γ ∧
      (∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1) ∧
      ε ≤ Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)))}.Finite

end Omega
end CerednikDrinfeld


