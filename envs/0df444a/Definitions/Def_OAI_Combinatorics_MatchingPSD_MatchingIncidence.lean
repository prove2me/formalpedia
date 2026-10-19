-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
-- name    : OAI_Combinatorics_MatchingPSD_MatchingIncidence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:35:16.589495+00:00
-- url     : https://prove2.me/theorems/d545a219-3cef-4a06-97d3-21fc4bcb69c8
-- title:
--   Color tables of perfect matchings and the table relation between matchings and 3-colorings
-- statement:
--   A perfect matching of a vertex set $V$ is encoded as a pairing, a permutation $M$ of $V$ with $M(M(v)) = v$ and $M(v) \neq v$ for all $v$, whose edges are the sets $\{v, M(v)\}$; let $\mathcal{M}(V)$ be the set of pairings. Colors are taken from $\{0,1,2\}$, and an unordered pair of colors has one of six types $\tau(a,b) = \tau(b,a) \in \{0,\dots,5\}$, given by the symmetric table with rows $(0,1,2)$, $(1,3,4)$, $(2,4,5)$ (types $0,3,5$ are monochromatic, types $1,2,4$ are the pairs $\{0,1\},\{0,2\},\{1,2\}$). The module defines:
--
--   1. The finiteness of $\mathcal{M}(V)$ for finite $V$, and, for any $V$, the action of the symmetric group on $\mathcal{M}(V)$ by relabelling, $p \cdot M = p M p^{-1}$; it is a group action, $1 \cdot M = M$ and $(pq) \cdot M = p \cdot (q \cdot M)$.
--   2. For finite $V$, a pairing $M$ and a coloring $f : V \to \{0,1,2\}$, the **color table** of $M$ under $f$,
--   $$
--   \mathrm{tab}_M(f)(t) = \frac{1}{2}\, \bigl|\{ v \in V : \tau\bigl(f(v), f(M(v))\bigr) = t \}\bigr| \qquad (t \in \{0,\dots,5\}),
--   $$
--   the number of edges of $M$ whose endpoints carry a color pair of type $t$ (every edge is seen from both of its endpoints).
--   3. For a set $H$, the **standard pairing** of $H \times \{0,1\}$, which matches $(i, 0)$ with $(i, 1)$ for every $i \in H$.
--   4. For finite $H$ and a reference coloring $f_0 : H \times \{0,1\} \to \{0,1,2\}$, the **table relation** between pairings $M$ of $H \times \{0,1\}$ and colorings $z$ of $H \times \{0,1\}$ with the same color counts as $f_0$: $M$ and $z$ are related when $\mathrm{tab}_M(z) = T_{f_0}$, where $T_{f_0}(t) = \bigl|\{i \in H : \tau(f_0(i,0), f_0(i,1)) = t\}\bigr|$ is the table of $f_0$ with respect to the standard pairing.
--   5. For finite $H$, color counts $s : \{0,1,2\} \to \mathbb{N}$ and a permutation $p$ of $H \times \{0,1\}$, the permutation $z \mapsto z \circ p$ of the set of colorings of $H \times \{0,1\}$ with color counts $s$ (precomposition with a permutation preserves color counts).
--
--   The table relation is the bipartite incidence structure between matchings and colorings whose incidence operator is analysed spectrally to show that averages of a function of the matching over table classes are governed by its low-degree part. The two kinds of permutations act compatibly on the two sides of the relation, since $\mathrm{tab}_{p \cdot M}(z) = \mathrm{tab}_M(z \circ p)$.
--
--   **Formalization Note** The definitions are a `Fintype (Pairing V)` instance (via `Fintype.ofFinite`), the `MulAction (Equiv.Perm V) (Pairing V)` instance `relabelMulAction`, `Pairing.table`, `standardPairing`, `tableRelation` and `coloringPerm`. The table is computed with truncating natural-number division by $2$; the count being halved is always even, because $\tau$ is symmetric and $v \mapsto M(v)$ pairs up the counted vertices, so the division is exact.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatchingIncidence.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatchingIncidence.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

noncomputable instance : Fintype (Pairing V) := Fintype.ofFinite _

instance relabelMulAction : MulAction (Equiv.Perm V) (Pairing V) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

noncomputable def table (M : Pairing V) (f : V → Fin 3) (t : Fin 6) : ℕ :=
  histogram (fun v => threeEdgeType (f v, f (M.1 v))) t / 2

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

def standardPairing : Pairing (H × Bool) :=
  ⟨Equiv.prodCongr (Equiv.refl H) Equiv.boolNot,
    by rintro ⟨i,b⟩; cases b <;> rfl,
    by rintro ⟨i,b⟩ h; have he := congrArg Prod.snd h; cases b <;> contradiction⟩

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def tableRelation (f₀ : H × Bool → Fin 3) :
    Pairing (H × Bool) → Colorings (H × Bool) (Fin 3) (histogram f₀) → Prop :=
  fun M z => M.table z.1 = threeTable f₀

noncomputable def coloringPerm (s : Fin 3 → ℕ) (p : Equiv.Perm (H × Bool)) :
    Equiv.Perm (Colorings (H × Bool) (Fin 3) s) where
  toFun z := ⟨z.1 ∘ p, (histogram_comp_perm z.1 p).trans z.2⟩
  invFun z := ⟨z.1 ∘ p.symm, (histogram_comp_perm z.1 p.symm).trans z.2⟩
  left_inv z := by apply Subtype.ext; funext v; simp
  right_inv z := by apply Subtype.ext; funext v; simp

end MatchingIncidence
end MatchingSmoothing

end OAI


