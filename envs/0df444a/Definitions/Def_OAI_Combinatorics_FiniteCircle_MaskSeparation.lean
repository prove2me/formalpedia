-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
-- name    : OAI_Combinatorics_FiniteCircle_MaskSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:42:13.793229+00:00
-- url     : https://prove2.me/theorems/7f5bbada-bab4-457c-8ae3-d65f24639391
-- title:
--   Mask phase homomorphisms and the recursive mask cost on $\mathbb{Z}/M$
-- statement:
--   Fix $h,M\in\mathbb{N}$ and a table $p(l,k)$ of natural numbers (level $l$, index $k<h$). A mask tag of level $l$ is a pair $(k,b)$ with $k<h$ and $0\le b<p(l,k)$; there are $N_l=\sum_{k<h}p(l,k)$ of them. When $p(l,k)\mid M$, write $\iota_{l,k}:\mathbb{Z}/p(l,k)\to\mathbb{Z}/M$ for the subcircle homomorphism $a\mapsto (M/p(l,k))\,a$. For $M\ge1$, the circle cost of $x\in\mathbb{Z}/M$ is $\operatorname{cc}(x)=|\tilde x|/M$, where $\tilde x$ is the representative of $x$ of least absolute value.
--
--   1. **Mask residues.** The group of mask residues of level $l$ is $\mathcal{R}_l=\prod_{k<h}\mathbb{Z}/p(l,k)$.
--   2. **Mask phase homomorphism.** If $p(l,k)\mid M$ for all $k<h$, then $\sigma_l:\mathcal{R}_l\to(\mathbb{Z}/M)^{\{\text{tags of level } l\}}$ is the group homomorphism
--   $$
--   \sigma_l(z)_{(k',b)}=\sum_{k<h}\iota_{l,k}(z_k)+b\,\iota_{l,k'}(z_{k'}).
--   $$
--   Taking $z_k=a\bmod p(l,k)$ reproduces the shift $\gamma_l(a,(k',b))=\sum_{k<h}\frac{M}{p(l,k)}(a\bmod p(l,k))+b\,\frac{M}{p(l,k')}(a\bmod p(l,k'))$ that the mask words apply to the block with tag $(k',b)$ in their $a$-th row.
--   3. **Mask cost.** Assume $p(l,k)\mid M$ and $p(l,k)>0$ for all levels $l$ and all $k<h$. The mask costs $c_l:\mathbb{Z}/M\to\mathbb{R}$ are defined by $c_0=\operatorname{cc}$ and
--   $$
--   c_{l+1}(x)=\min_{z\in\mathcal{R}_{l+1}}\ \frac{1}{N_{l+1}}\sum_{j}c_l\bigl(x+\sigma_{l+1}(z)_j\bigr),
--   $$
--   the sum running over the tags $j$ of level $l+1$. Each $c_l$ is a phase cost: nonnegative, zero at $0$, even and subadditive.
--
--   The mask cost of level $l$ measures how much a level-$l$ mask word must change when all of its phases are rotated by a common $\theta$: in the separation argument the deficit between a mask word and its rotated copy is bounded below by a constant multiple, depending on $l$, of the word length times $c_l(\theta)$. The minimum over $z$ reflects the freedom of an alignment to match each row with a row whose phases are shifted by a residue pattern.
--
--   **Formalization Note** `MaskResidues h p l` is the dependent product `(k : Fin h) → ZMod (p l k)`, `maskPhaseHom h p M l hd` is an additive monoid homomorphism taking the divisibility hypotheses of level $l$, and `maskCost h p M hd hn l` takes divisibility and positivity hypotheses for all levels; positivity makes each $\mathbb{Z}/p(l,k)$ a nonempty finite group, so the minimum is the finite infimum of `PhaseCost.step`. The circle cost is `circleCost`, which is $0$ when $M=0$ by Lean's division convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

abbrev MaskResidues (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) := (k : Fin h) → ZMod (p l k)

noncomputable def maskPhaseHom (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (hd : ∀ k : Fin h, p l k ∣ M) : MaskResidues h p l →+ (MaskTag h p l → ZMod M) where
  toFun z j := (∑ k, subcircle (hd k) (z k)) + j.2.val • subcircle (hd j.1) (z j.1)
  map_zero' := by funext j; simp
  map_add' z u := by
    funext j
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, nsmul_add]
    abel

noncomputable def maskCost (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k) :
    ℕ → PhaseCost (ZMod M)
  | 0 => circlePhaseCost M
  | l+1 => by
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    exact (maskCost h p M hd hn l).step (maskPhaseHom h p M (l+1) (hd _))

end FiniteCircle

end OAI


