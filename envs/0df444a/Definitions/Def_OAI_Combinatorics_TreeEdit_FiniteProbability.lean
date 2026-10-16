-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
-- name    : OAI_Combinatorics_TreeEdit_FiniteProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:12:39.488993+00:00
-- url     : https://prove2.me/theorems/41a131a4-46dd-4e16-b639-e0822efe4d41
-- title:
--   Uniform mean and uniform probability on a finite set
-- statement:
--   This file sets up elementary probability for the uniform distribution on a finite set $A$.
--
--   1. **Uniform mean.** For $f:A\to\mathbb{R}$,
--
--      $$\mathbb{E}_{a\in A}\,f(a)=\frac{1}{|A|}\sum_{a\in A}f(a).$$
--
--   2. **Uniform probability.** For an event, that is, a predicate $E$ on $A$,
--
--      $$\Pr_{a\in A}[E(a)]=\mathbb{E}_{a\in A}\,\mathbf{1}_{E}(a)=\frac{|\{a\in A: E(a)\}|}{|A|},$$
--
--      where $\mathbf{1}_E(a)$ is $1$ if $E(a)$ holds and $0$ otherwise.
--
--   The random choices in the circle-phase tree construction for binary edit distance (random permutations selecting primes, random residues, uniformly random points of finite groups) are all uniform choices from finite sets, possibly finite products. These two notions are the basis on which the usual rules (linearity, monotonicity, union bounds, products over independent coordinates, existence of an outcome of positive probability) are proved without measure theory.
--
--   **Formalization Note** The Lean names are `mean` and `probability`. The predicate need not be decidable; the indicator is formed with classical logic. If $A$ is empty, Lean's convention $0^{-1}=0$ makes every mean and every probability equal to $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

noncomputable def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (Fintype.card A : ℝ)⁻¹ * ∑ a, f a

noncomputable def probability {A : Type*} [Fintype A] (E : A → Prop) : ℝ :=
  mean (fun a => if E a then 1 else 0)

end TreeEdit.FiniteProbability

end OAI


