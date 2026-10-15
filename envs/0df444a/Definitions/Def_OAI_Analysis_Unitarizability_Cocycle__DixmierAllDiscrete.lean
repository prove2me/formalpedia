-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:02:57.28328+00:00
-- url     : https://prove2.me/theorems/21b1dac6-01c9-470e-9f3e-f95d64c06249
-- title:
--   Conjugation and coboundaries for a homomorphism from a group into a ring
-- statement:
--   Let $G$ be a group, $R$ a ring and $U:G\to R$ a homomorphism into the multiplicative monoid of $R$, so that $U(gh)=U(g)U(h)$ and $U(1)=1$; in particular $U(g^{-1})$ is a two-sided inverse of $U(g)$. In the application $R$ is the algebra of bounded operators on a complex Hilbert space and $U$ is a representation.
--
--   1. **Conjugation.** For $g\in G$ and $T\in R$,
--   $$\operatorname{Ad}_U(g)\,T=U(g)\,T\,U(g^{-1}).$$
--   2. **Coboundary.** For $T\in R$, the map $\delta_UT:G\to R$,
--   $$(\delta_UT)(g)=T-U(g)\,T\,U(g^{-1}).$$
--
--   The file records $\operatorname{Ad}_U(1)T=T$ and $(\delta_UT)(1)=0$.
--
--   The coboundary satisfies the twisted cocycle identity $(\delta_UT)(gh)=(\delta_UT)(g)+\operatorname{Ad}_U(g)\bigl((\delta_UT)(h)\bigr)$, which is exactly the hypothesis under which the upper-triangular representation $g\mapsto\begin{pmatrix}U(g)&D(g)U(g)\\0&U(g)\end{pmatrix}$ is defined. Two coboundaries $\delta_UT$ and $\delta_UB$ agree at $g$ precisely when $T-B$ commutes with $U(g)$. In the construction for a non-amenable group, $U$ is a translation representation and $T$ is a sparse part of a translation-invariant operator, whose coboundary is uniformly bounded; a bounded cocycle that is not the coboundary of any bounded operator yields a uniformly bounded representation that is not similar to a unitary one.
--
--   **Formalization Note** `conjugate U g T` is `U g * T * U g⁻¹` and `coboundary U T g` is `T - conjugate U g T`, for `U : G →* R` and an arbitrary `Ring R`; `conjugate_one` and `coboundary_one` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Cocycle.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Cocycle.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete

namespace OAI

/-! Cocycle algebra in an arbitrary ring, specializing to bounded complex Hilbert-space operators. -/
namespace Dixmier
section Ring
variable {G R : Type*} [Group G] [Ring R]

def conjugate (U : G →* R) (g : G) (T : R) : R := U g * T * U g⁻¹

@[simp] theorem conjugate_one (U : G →* R) (T : R) : conjugate U 1 T = T := by
  simp [conjugate]

def coboundary (U : G →* R) (T : R) (g : G) : R := T - conjugate U g T

@[simp] theorem coboundary_one (U : G →* R) (T : R) : coboundary U T 1 = 0 := by
  simp [coboundary]

end Ring
end Dixmier

end OAI


