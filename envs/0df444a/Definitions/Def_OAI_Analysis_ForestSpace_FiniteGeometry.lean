-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
-- name    : OAI_Analysis_ForestSpace_FiniteGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:49:38.143775+00:00
-- url     : https://prove2.me/theorems/d73574ea-1e46-4fc7-905e-cf6b69aa70f0
-- title:
--   Ancestral intervals, gate masses and selected heads in a finite forest
-- statement:
--   Let $(V,\le)$ be a **finite** partially ordered set (a finite forest in the applications). Fix real functions $f,k:V\to\mathbb{R}$ (a head vector and a tail vector), a set $H\subseteq V$, a function $\sigma:V\to\mathbb{R}$ of signs, and a real parameter $s$. Recall that $g$ is a *gate* of $H$ if $g\notin H$ and all $v<g$ lie in $H$. The file defines the following objects.
--
--   1. **Half-open interval.** For $a,g\in V$, $[a,g)=\{v\in V: a\le v<g\}$.
--   2. **Closed interval.** For $g,w\in V$, $[g,w]=\{v\in V: g\le v\le w\}$. It is empty unless $g\le w$.
--   3. **Mass.** The mass of $k$ at $g$ is the largest absolute $k$-sum over a closed interval starting at $g$:
--   $$
--   m_k(g)=\max_{w\in V}\Bigl|\sum_{v\in[g,w]}k(v)\Bigr|.
--   $$
--   4. **Gate weight.** $\gamma_{H,k}(g)=m_k(g)^2$ if $g$ is a gate of $H$, and $\gamma_{H,k}(g)=0$ otherwise.
--   5. **Gate correction.** $c_{H,k,\sigma}(g)=\sigma(g)\,m_k(g)$ if $g$ is a gate of $H$, and $c_{H,k,\sigma}(g)=0$ otherwise.
--   6. **Large starts.** For $g\in V$,
--   $$
--   L_{f,k,s}(g)=\Bigl\{a\in V:\ a<g\ \text{ and }\ 2s\,m_k(g)\le\Bigl|\sum_{v\in[a,g)}f(v)\Bigr|\Bigr\}.
--   $$
--   These are the vertices strictly below $g$ from which the $f$-sum up to, but excluding, $g$ reaches the threshold $2s\,m_k(g)$.
--   7. **Selected start and selected head.** If $L_{f,k,s}(g)\neq\emptyset$, the selected start $a^*(g)$ is a maximal element of $L_{f,k,s}(g)$, fixed once and for all by choice, and the selected head is $h_{f,k,s}(g)=[a^*(g),g)$. If $L_{f,k,s}(g)=\emptyset$, the selected head is $h_{f,k,s}(g)=\emptyset$. In a forest order the vertices below $g$ form a chain, so $a^*(g)$ is then the large start closest to $g$.
--   8. **Opposite sign.** For $r\in\mathbb{R}$, $\operatorname{sgn}^-(r)=1$ if $r<0$ and $\operatorname{sgn}^-(r)=-1$ if $r\ge0$.
--
--   Each of $[a,g)$, $[g,w]$ and $L_{f,k,s}(g)$ comes with a lemma characterizing its members.
--
--   These are the finite combinatorial tools for the paired estimate, in which a head $f$ is supported on an ancestral set $H$ and a tail $k$ is supported off $H$. The mass $m_k(g)$ measures the largest partial sum of the tail starting at the gate $g$. The gate correction places a single coordinate of exactly that size, with a prescribed sign, at each gate. The selected head is the head interval that is split off when the $f$-sum just before $g$ is large compared with the mass. Choosing the correction sign opposite to the $f$-sum over the selected head makes the resulting head–tail cross terms nonpositive.
--
--   **Formalization Note** The definitions are `before a g`, `along g w`, `mass k g`, `gateWeight`, `correction`, `largeStarts`, `selectedStart`, `selectedHead` and `oppositeSign`. Here `mass k g` is a `Finset.sup'` over `univ`, which is nonempty because it contains `g`. `selectedStart` uses `Classical.choose` applied to `Finset.exists_maximal`, and `selectedHead` is a dependent if-then-else on nonemptiness. The hypothesis `Fintype V` is what lets these intervals and the maximum be formed as finite sets. `oppositeSign` needs no order. The convention $\operatorname{sgn}^-(0)=-1$ is arbitrary, since either sign works at $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/FiniteGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/FiniteGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteGeometry
variable {V : Type} [Fintype V] [PartialOrder V]

/-- The ancestral interval [a,g), ending immediately before g along its path. -/
noncomputable def before (a g : V) : Finset V := by
  classical
  exact univ.filter (fun v => a ≤ v ∧ v < g)

@[simp] theorem mem_before {a g v : V} : v ∈ before a g ↔ a ≤ v ∧ v < g := by
  classical
  simp [before]

/-- The closed ancestral interval [g,w]. -/
noncomputable def along (g w : V) : Finset V :=
  univ.filter (fun v => g ≤ v ∧ v ≤ w)

@[simp] theorem mem_along {g w v : V} : v ∈ along g w ↔ g ≤ v ∧ v ≤ w := by
  simp [along]

/-- Maximal initial-segment mass of a test inside the cone at g. -/
noncomputable def mass (k : V → ℝ) (g : V) : ℝ :=
  univ.sup' ⟨g, mem_univ g⟩ (fun w => |segSum k (along g w)|)

/-- Square mass at gates, and zero elsewhere. -/
noncomputable def gateWeight (H : Set V) (k : V → ℝ) (g : V) : ℝ :=
  if Gate H g then mass k g ^ 2 else 0

noncomputable def correction (H : Set V) (k σ : V → ℝ) (g : V) : ℝ :=
  if Gate H g then σ g * mass k g else 0

/-- Candidate starts of suffixes whose head sum reaches the gate threshold. -/
noncomputable def largeStarts (f k : V → ℝ) (s : ℝ) (g : V) : Finset V :=
  univ.filter (fun a => a < g ∧ 2 * s * mass k g ≤ |segSum f (before a g)|)

@[simp] theorem mem_largeStarts {f k : V → ℝ} {s : ℝ} {g a : V} :
    a ∈ largeStarts f k s g ↔ a < g ∧ 2 * s * mass k g ≤ |segSum f (before a g)| := by
  simp [largeStarts]

noncomputable def selectedStart (f k : V → ℝ) (s : ℝ) (g : V)
    (h : (largeStarts f k s g).Nonempty) : V :=
  Classical.choose ((largeStarts f k s g).exists_maximal h)

noncomputable def selectedHead (f k : V → ℝ) (s : ℝ) (g : V) : Finset V :=
  if h : (largeStarts f k s g).Nonempty then before (selectedStart f k s g h) g else ∅

end FiniteGeometry

section CrossTermAlgebra

/-- Opposite sign for the selected head sum; at zero either sign is harmless. -/
def oppositeSign (r : ℝ) : ℝ := if r < 0 then 1 else -1

end CrossTermAlgebra

end

end ForestSpace

end OAI


