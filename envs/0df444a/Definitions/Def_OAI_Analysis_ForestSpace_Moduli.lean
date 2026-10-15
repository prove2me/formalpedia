-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Moduli
-- name    : OAI_Analysis_ForestSpace_Moduli
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:47:40.391915+00:00
-- url     : https://prove2.me/theorems/fc25cd9d-dfde-493f-8f7e-8ccde347f865
-- title:
--   The whole space as a closed finite-codimensional subspace
-- statement:
--   Let $E$ be a real normed space, and let $\mathrm{Cof}(E)$ be the family of closed finite-codimensional subspaces of $E$, that is, closed linear subspaces $F\subseteq E$ whose quotient $E/F$ is finite-dimensional. This file names one distinguished member of this family, the whole space itself:
--
--   $$
--   F_{\top}=E\in\mathrm{Cof}(E).
--   $$
--
--   It is closed, and its quotient $E/E=\{0\}$ is finite-dimensional, so its codimension is $0$.
--
--   The asymptotic moduli of a norm $N$ on $E$ are defined through suprema over $\mathrm{Cof}(E)$. For example, the one-sided asymptotic uniform convexity modulus is
--
--   $$
--   \bar\delta_N(t)=\inf_{N(x)=1}\ \sup_{F\in\mathrm{Cof}(E)}\ \inf_{y\in F,\ N(y)=1}\bigl(N(x+ty)-1\bigr),
--   $$
--
--   and the averaged modulus is built in the same way from $\tfrac12\bigl(N(x+ty)+N(x-ty)\bigr)-1$. The element $F_{\top}$ shows that the family indexing these suprema is nonempty. It also gives a concrete subspace whenever one is needed, for instance to bound such a supremum from below by its term at $F=E$.
--
--   **Formalization Note** `Cofinite E` is the subtype of `Submodule ℝ E` made of the submodules that are closed and have finite-dimensional quotient `E ⧸ F`. `cofiniteTop E` is the top submodule `⊤` together with these two facts. The moduli are written with `sSup` and `sInf` on the reals, where the supremum of the empty set is $0$. An explicit inhabitant of `Cofinite E` is therefore what allows the supremum over subspaces to be compared with its individual terms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Moduli.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Moduli.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section ModulusDefinitions
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def cofiniteTop : Cofinite E :=
  ⟨⊤, by simp, inferInstance⟩

end ModulusDefinitions

end

end ForestSpace

end OAI


