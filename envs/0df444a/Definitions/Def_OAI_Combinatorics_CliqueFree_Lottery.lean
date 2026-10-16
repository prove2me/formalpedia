-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
-- name    : OAI_Combinatorics_CliqueFree_Lottery
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:43:41.208988+00:00
-- url     : https://prove2.me/theorems/13b6f0f5-7e42-477c-a349-dfaa21636c91
-- title:
--   Finite real lotteries: weighted outcome lists, expectations and rescaled pushforwards
-- statement:
--   A *lottery* over a type $\alpha$ is a finite list $L=\bigl((p_1,a_1),\dots,(p_n,a_n)\bigr)$ of pairs consisting of a real weight $p_i$ and an outcome $a_i\in\alpha$. Outcomes may repeat, and the weights are a priori arbitrary real numbers. The file defines:
--
--   1. **Expectation** of a function $f:\alpha\to\mathbb{R}$:
--
--      $$\mathbb{E}_L[f]=\sum_{i=1}^{n}p_i\,f(a_i),$$
--
--      so the empty lottery has expectation $0$ and prepending $(p,a)$ adds $p\,f(a)$.
--
--   2. **Positivity:** $L$ is positive if $p_i\ge 0$ for every entry.
--
--   3. **Total weight:** $|L|=\sum_{i}p_i=\mathbb{E}_L[1]$.
--
--   4. **Probability lottery:** $L$ is positive and $|L|=1$. Such an $L$ is a finitely supported probability distribution on $\alpha$, and $\mathbb{E}_L$ is the ordinary expectation.
--
--   5. **Transform:** for $p\in\mathbb{R}$ and $f:\alpha\to\beta$, the lottery
--
--      $$\bigl((p\,p_1,f(a_1)),\dots,(p\,p_n,f(a_n))\bigr)$$
--
--      over $\beta$, in which all weights are multiplied by $p$ and outcomes are pushed forward along $f$. Its expectations are $p\,\mathbb{E}_L[g\circ f]$ for $g:\beta\to\mathbb{R}$.
--
--   Lotteries give an elementary, measure-free model of finitely supported random variables. In the clique-free independence argument their outcomes are multiplier vectors $m:V\to\mathbb{R}$ on the vertex set of a graph, so that a probability lottery is a random reweighting of the vertices. Because concatenating lists adds expectations, concatenations of rescaled transforms describe mixtures of lotteries.
--
--   **Formalization Note** `Law α` is an abbreviation for `List (ℝ × α)`. The definitions are `expect`, `Positive`, `total`, `IsProb` and `transform`; `expect_nil`, `expect_cons` and `expect_singleton` are the corresponding simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Lottery.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Lottery.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence
universe u
namespace Lottery
variable {α β : Type u}

/-- A finite real lottery; list entries need not have distinct outcomes. -/
abbrev Law (α : Type u) := List (ℝ × α)

def expect (L : Law α) (f : α → ℝ) : ℝ := (L.map fun z ↦ z.1 * f z.2).sum

def Positive (L : Law α) : Prop := ∀ z ∈ L, 0 ≤ z.1

def total (L : Law α) : ℝ := expect L (fun _ ↦ 1)

def IsProb (L : Law α) : Prop := Positive L ∧ total L = 1

@[simp] lemma expect_nil (f : α → ℝ) : expect [] f = 0 := rfl
@[simp] lemma expect_cons (p : ℝ) (a : α) (L : Law α) (f : α → ℝ) :
    expect ((p,a)::L) f = p*f a + expect L f := rfl
@[simp] lemma expect_singleton (p : ℝ) (a : α) (f : α → ℝ) : expect [(p,a)] f = p*f a := by
  simp [expect]

def transform (p : ℝ) (f : α → β) (L : Law α) : Law β := L.map (fun z ↦ (p*z.1,f z.2))

end Lottery

end CliqueFreeIndependence

end

end OAI


