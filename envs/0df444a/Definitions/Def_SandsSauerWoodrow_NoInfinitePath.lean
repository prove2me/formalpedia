-- Prove2me | Definitions.Def_SandsSauerWoodrow_NoInfinitePath
-- name    : SandsSauerWoodrow_NoInfinitePath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-17T23:27:24.255559+00:00
-- url     : https://prove2.me/theorems/5277ccc5-526f-4990-ad76-d0e35ef0d3b9
-- title:
--   No infinite outward path for a relation
-- statement:
--   This definition supplies the finiteness-free hypothesis of Theorem 1 of Sands, Sauer and Woodrow (*On monochromatic paths in edge-coloured digraphs*, J. Combin. Theory Ser. B **33** (1982), 271–275, pp. 271–273) in the form the proof uses it.
--
--   Let $R$ be a relation on a set $V$ of vertices. Say that $R$ admits an **infinite outward path** when there is an injective sequence $x_0, x_1, x_2, \dots$ of vertices such that $x_n\,R\,x_{n+1}$ for every $n$, and that $R$ has **no infinite outward path** when no such sequence exists:
--
--   $$\neg\, \exists x : \mathbb{N} \to V,\ \bigl(\text{$x$ injective}\bigr) \wedge \forall n,\ x_n\,R\,x_{n+1}.$$
--
--   Injectivity is essential: the source's paths have pairwise distinct vertices, so a cycle, or a walk revisiting a vertex, is not an infinite outward path. Applied to the asymmetric part of reachability along a single colour, this is the condition the proof of the source theorem carries through its maximality argument; it is vacuous when $V$ is finite, where no injective sequence of vertices exists.
-- source:
--   Proof step of B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275, Theorem 1 (pp. 271-273). Formulation: J.-P. Chancelier, A formal proof of the Sands-Sauer-Woodrow theorem using the Rocq prover and mathcomp/ssreflect, arXiv:2604.21376, §5-§6.

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets

/-! The finiteness-free hypothesis of Sands-Sauer-Woodrow Theorem 1, in the form the proof
uses it: no infinite outward path for a relation (Chancelier, arXiv:2604.21376, §5). -/

universe u

namespace SandsSauerWoodrow

/-- A relation `R` on a set of vertices has no infinite outward path when there is no
injective sequence of vertices whose consecutive pairs are all related by `R`. Injectivity is
what makes the sequence a path rather than a walk, matching the source's convention that paths
have pairwise distinct vertices. -/
def NoInfinitePath {V : Type u} (R : V → V → Prop) : Prop :=
  ¬ ∃ x : ℕ → V, Function.Injective x ∧ ∀ n : ℕ, R (x n) (x (n + 1))

end SandsSauerWoodrow


