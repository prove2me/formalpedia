-- Prove2me | Definitions.Def_DRSubmodHull_Ppt
-- name    : DRSubmodHull_Ppt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:03.784885+00:00
-- url     : https://prove2.me/theorems/88269117-fff2-491a-8549-e5a0d5b91120
-- title:
--   The points $P(\mathcal S)$ of (9) and the deepest ascendant $i^\triangle(\mathcal S)$ of (7)
-- statement:
--   For $\mathcal S\subseteq\mathcal V$ and $i\in\mathcal V$, the **deepest ascendant** $i^\triangle(\mathcal S)$ is the element of $\mathcal S\cap R^-(i)$ of maximum depth, and $0$ if $\mathcal S\cap R^-(i)=\emptyset$ (eq. (7)). Since $R^-(i)$ is the directed path from the root to $i$, it is the element of $\mathcal S\cap R^-(i)$ of which all others are ascendants; $i^\triangle(\mathcal S)=i$ when $i\in\mathcal S$.
--
--   With $u_0=0$, the point $P(\mathcal S)\in\mathbb R^{\mathcal V}$ is (eq. (9))
--   $$
--   P(\mathcal S)_i=\begin{cases}\lfloor u_\psi\rfloor, & \text{if } i^\triangle(\mathcal S)=\psi\in\Psi \text{ and } \mathrm{ch}(\psi)\notin\mathcal S,\\ u_{i^\triangle(\mathcal S)}, & \text{otherwise.}\end{cases}
--   $$
--
--   The vertices of $\mathcal S$ and everything below them are raised to the largest values the box and MIR constraints allow; the others stay at their minimal values. These are the extreme points of $\mathcal{CZ}$ (Corollary 4.20) and the building blocks of the DR inequalities.
--
--   **Formalization Note** The index $0$ is `none : Option V`, and `uAt u none = 0`. The deepest ascendant is defined without a depth function, by the characterization above; in a directed rooted forest it exists whenever $\mathcal S\cap R^-(i)\ne\emptyset$ and is unique.
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, §4, p.8, eqs. (7) and (9)

import Mathlib
import Definitions.Def_DRSubmodHull_CZ

set_option autoImplicit false

open Classical

noncomputable section

namespace DRSubmodHull

/-- **The deepest ascendant `i△(𝒮)`** (arXiv:2211.07726v2, §4, p.8, eq. (7)):
`i△(𝒮) := arg max{depth(j) : j ∈ 𝒮 ∩ R⁻(i)}` if `𝒮 ∩ R⁻(i) ≠ ∅`, and `0` otherwise.

**Formalization Note.** The value `0` of the paper is `none`. Since `R⁻(i)` is the directed path
from the root to `i`, the element of `𝒮 ∩ R⁻(i)` of maximum depth is the `j ∈ 𝒮 ∩ R⁻(i)` of which
every element of `𝒮 ∩ R⁻(i)` is an ascendant; this characterization needs no depth function. In a
directed rooted forest such a `j` exists whenever `𝒮 ∩ R⁻(i) ≠ ∅` and is unique. Note `i△(𝒮) = i`
when `i ∈ 𝒮`. -/
def tri {V : Type*} (A : V → V → Prop) (S : Finset V) (i : V) : Option V :=
  if h : ∃ j ∈ S, Relation.ReflTransGen A j i ∧
      ∀ k ∈ S, Relation.ReflTransGen A k i → Relation.ReflTransGen A k j then
    some h.choose
  else none

/-- `u₀ = 0` (p.8): the upper bound of an `Option V`, with `none` (the paper's index `0`) giving `0`. -/
def uAt {V : Type*} (u : V → ℝ) : Option V → ℝ
  | some j => u j
  | none => 0

/-- **The points `P(𝒮)`** (arXiv:2211.07726v2, §4, p.8, eq. (9)): with `u₀ = 0`,
`P(𝒮)_i = ⌊u_ψ⌋` if `i△(𝒮) = ψ ∈ Ψ` and `ch(ψ) ∉ 𝒮`, and `P(𝒮)_i = u_{i△(𝒮)}` otherwise. -/
def Ppt {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) (S : Finset V) : V → ℝ :=
  fun i =>
    match tri A S i with
    | some ψ => if ψ ∈ Psi A N u ∧ child A ψ ∉ S then (Int.floor (u ψ) : ℝ) else u ψ
    | none => 0

end DRSubmodHull


