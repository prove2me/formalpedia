-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
-- name    : OAI_Combinatorics_TreeEdit_CircleTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:20:46.033653+00:00
-- url     : https://prove2.me/theorems/9344ebc2-73d3-4c7a-ac90-64bad4ce4f16
-- title:
--   Random prime-period configurations and good shifts for the circle-phase tree
-- statement:
--   This file defines the random data of the circle-phase tree and the recursive notion of a *good shift*. Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ be the circle, and for $t\in\mathbb{T}$ let $\|t\|$ be the distance from $t$ to $0$, that is, from a representative of $t$ to the nearest integer. Fix a set $I$ (a pool of indices), a labelling $r:I\to\mathbb{N}$ (in applications, by distinct primes), natural numbers $g,s,L$, and a list $j:[g]\to I$, where $[n]=\{0,\dots,n-1\}$. Every internal node has $m=gs$ children.
--
--   1. **Grid point.** For $n\in\mathbb{N}$, $\pi(n)\in\mathbb{T}$ is the image of $1/n$, so that $a\,\pi(n)=a/n \bmod 1$.
--
--   2. **Groups of children.** Child $i\in[gs]$ belongs to group $\gamma(i)=\lfloor i/s\rfloor\in[g]$; the children form $g$ consecutive groups of $s$.
--
--   3. **Configurations.** For $h\in\mathbb{N}$ the configuration space $\mathcal{C}_h$ is defined by recursion: $\mathcal{C}_0$ has a single element, and
--
--      $$\mathcal{C}_{h+1}=\operatorname{Sym}(I)\times\bigl(\mathbb{Z}/L\mathbb{Z}\times\mathcal{C}_h\bigr)^{[gs]}.$$
--
--      Thus a configuration of a node of height $h+1$ is a permutation $\sigma$ of $I$ together with, for every child $i$, a residue $z_i\in\mathbb{Z}/L\mathbb{Z}$ and a configuration $C_i\in\mathcal{C}_h$ of the child's subtree. Each $\mathcal{C}_h$ is nonempty, and it is finite when $I$ is finite and $L\ge1$; the uniform distribution on this product makes all choices independent and uniform.
--
--   4. **Period.** The period of $\sigma$ is the product of the $g$ selected labels,
--
--      $$P_\sigma=\prod_{q\in[g]} r\bigl(\sigma(j(q))\bigr).$$
--
--   5. **Coefficients.** For child $i$, with selected label $\rho=r\bigl(\sigma(j(\gamma(i)))\bigr)$ and residue $z_i$ represented by its value in $\{0,\dots,L-1\}$,
--
--      $$c_i=1+(z_i \bmod \rho)\cdot\frac{P_\sigma}{\rho}\in\mathbb{N}.$$
--
--   6. **Good shifts.** For $\varepsilon\in\mathbb{R}$, goodness of $t\in\mathbb{T}$ at height $h$ with respect to $C\in\mathcal{C}_h$ is defined recursively. At height $0$, $t$ is good if and only if $\varepsilon\le\|t\|$. At height $h+1$, with $C=(\sigma,(z_i,C_i)_{i})$, $t$ is good if and only if for every $a\in\{0,1,\dots,P_\sigma-1\}$
--
--      $$gs\ \le\ 64\cdot\#\Bigl\{\,i\in[gs] : t+\frac{a\,c_i}{P_\sigma}\ \text{is good at height } h \text{ with respect to } C_i\Bigr\},$$
--
--      that is, at least a $1/64$ fraction of the children see a good shift.
--
--   When $j$ is injective and $\sigma$ is uniform, the labels $r(\sigma(j(0))),\dots,r(\sigma(j(g-1)))$ are a uniformly random ordered selection of $g$ distinct pool elements. Since $c_i/P_\sigma=1/P_\sigma+(z_i\bmod\rho)/\rho$, in row $a$ child $i$ receives the common drift $a/P_\sigma$ plus a step on the $\rho$-point grid of its own group, while $c_i\equiv1$ modulo the selected label of every other group. Goodness depends only on the shift $t$ and the configuration, not on base phases; it is the hypothesis under which the circle-tree words of a phase vector and of its translate by $t$ are far apart.
--
--   **Formalization Note** The Lean names are `point` (the image of `(n : ℝ)⁻¹`, so `point 0 = 0` by Lean's convention), `group` (defined through `finProdFinEquiv`), `Config I L m h` (with instances `configFintype`, which needs `NeZero L`, and `configNonempty`), `period`, `coefficient` and `Good ε r j h C t`; the norm $\|t\|$ is the norm of `UnitAddCircle`. In `Good` the row index ranges over `Fin (period r j C.1)`, so the condition is vacuous if the period is $0$, and the shift is the natural number $a c_i$ acting on `point (period r j C.1)`. In `coefficient` the quotient is natural-number division, exact because $\rho$ is one of the factors of $P_\sigma$. The plumbing lemma `product_positive` states that a finite product of positive naturals is positive. The data $I$, $r$, $j$ are arbitrary here; primality, positivity and injectivity are hypotheses of later results.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleTree.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleTree.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

noncomputable def point (n : ℕ) : UnitAddCircle := ↑((n : ℝ)⁻¹)

lemma product_positive {I : Type*} [Fintype I] (r : I → ℕ) (hr : ∀ i, 0 < r i) :
    0 < ∏ i, r i := Finset.prod_pos (fun i _ => hr i)

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

def group {g s : ℕ} (i : Fin (g * s)) : Fin g := (finProdFinEquiv.symm i).1

@[reducible] def Config (I : Type) (L m : ℕ) : ℕ → Type _
  | 0 => Unit
  | h + 1 => Equiv.Perm I × (Fin m → ZMod L × Config I L m h)

noncomputable instance configFintype {I : Type} [Fintype I] {L m : ℕ} [NeZero L] (h : ℕ) :
    Fintype (Config I L m h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ h ih => exact inferInstanceAs (Fintype (Equiv.Perm I × (Fin m → ZMod L × Config I L m h)))

instance configNonempty {I : Type} {L m : ℕ} (h : ℕ) : Nonempty (Config I L m h) := by
  induction h with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ h ih => exact inferInstanceAs (Nonempty (Equiv.Perm I × (Fin m → ZMod L × Config I L m h)))

noncomputable def period {I : Type} {g : ℕ} (r : I → ℕ) (j : Fin g → I) (σ : Equiv.Perm I) : ℕ :=
  ∏ i, r (σ (j i))

noncomputable def coefficient {I : Type} {g s L : ℕ} (r : I → ℕ) (j : Fin g → I)
    (σ : Equiv.Perm I) (z : ZMod L) (i : Fin (g * s)) : ℕ :=
  1 + (z.val % r (σ (j (group i)))) * (period r j σ / r (σ (j (group i))))

noncomputable def Good {I : Type} {g s L : ℕ} (ε : ℝ) (r : I → ℕ) (j : Fin g → I) :
    (h : ℕ) → Config I L (g * s) h → UnitAddCircle → Prop
  | 0, _, t => ε ≤ ‖t‖
  | h + 1, C, t => ∀ a : Fin (period r j C.1), g * s ≤ 64 *
    (Finset.univ.filter (fun i : Fin (g * s) =>
      Good ε r j h (C.2 i).2 (t + (a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)))).card

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

end OAI


