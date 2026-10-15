-- Prove2me | Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange
-- name    : OAI_Analysis_HilbertCrouzeix_NumericalRange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:02:31.728879+00:00
-- url     : https://prove2.me/theorems/124d2d2f-3be7-4f59-b11e-751241ee197f
-- title:
--   Sup-norm of a function over a set of complex numbers, with value $0$ on the empty set
-- statement:
--   Let $E$ be any set equipped with a norm function $\|\cdot\|:E\to\mathbb{R}$ (no further structure is required; typically $E$ is the space $M_m(\mathbb{C})$ of $m\times m$ complex matrices with the operator norm), let $S\subseteq\mathbb{C}$ and let $f:\mathbb{C}\to E$. The sup-norm of $f$ over $S$ used throughout this development is
--
--   $$
--   \|f\|_{S}=\begin{cases}\sup\{\|f(z)\| : z\in S\}, & S\neq\emptyset,\\ 0, & S=\emptyset.\end{cases}
--   $$
--
--   This module records the corresponding evaluation rule for the empty set: for every such $E$ and every function $f:\mathbb{C}\to E$,
--
--   $$
--   \|f\|_{\emptyset}=0 .
--   $$
--
--   The quantity $\|f\|_S$ is the right-hand side of the bounds of the form $\|F(A)\|\le 2\,\|F\|_{W(A)}$ considered for bounded operators $A$ on a complex Hilbert space, where $W(A)=\{\langle x,Ax\rangle:\|x\|=1\}$ is the numerical range of $A$. The rule above is what makes these bounds meaningful in the degenerate case of the zero space, where $W(A)$ is empty and the right-hand side is $0$.
--
--   **Formalization Note** The sup-norm is `normSup S f` from the shared definitions of this development, and the rule is the simp lemma `normSup_empty`. For nonempty $S$ the supremum is Lean's `sSup` on the real numbers, which by convention returns $0$ for a set that is not bounded above; for continuous $f$ on a compact set $S$ this convention plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HilbertCrouzeix/NumericalRange.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HilbertCrouzeix/NumericalRange.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HilbertCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HilbertCrouzeix

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

@[simp] theorem normSup_empty {E : Type*} [Norm E] (f : ℂ → E) :
    normSup ∅ f = 0 := by simp [normSup]

end Elementary

end HilbertCrouzeix

end

end OAI


