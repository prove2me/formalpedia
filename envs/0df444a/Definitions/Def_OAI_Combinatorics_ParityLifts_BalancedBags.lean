-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
-- name    : OAI_Combinatorics_ParityLifts_BalancedBags
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:07:12.820983+00:00
-- url     : https://prove2.me/theorems/531151f5-0884-43fc-adb1-f48aca4db0f9
-- title:
--   Balanced stars around a bag, and label-mismatch tests
-- statement:
--   This file defines the local configuration from which a successful choice is extracted, and the label predicates used to test it.
--
--   Let $T_t$ be the template with main vertices $[t]=\{0,\dots,t-1\}$ and helper vertices, let $F$ be a graph on a finite set $W$, $a\colon F\to T_t$ a homomorphism, $b\colon V(T_t)\to\mathbb{F}_2$, and $w$ a weighted witness for $(a,b)$ with type masses $m_u(Y)=\sum_{x\in Y,\,a(x)=u}s(x)$.
--
--   1. **Regions.** For a labelling $\mathrm{reg}\colon W\to\{\bot\}\sqcup[n]$, the region of a label $\iota$ is its fibre $\mathrm{reg}^{-1}(\iota)$.
--   2. **Balanced stars.** A balanced star for $w$ consists of a number $n\in\mathbb{N}$, a labelling $\mathrm{reg}\colon W\to\{\bot\}\sqcup[n]$ and sets $S_0,\dots,S_{n-1}\subseteq W$ such that, with the bag $B=\mathrm{reg}^{-1}(\bot)$ and the outer sides $A_i=\mathrm{reg}^{-1}(i)$:
--      - $|B|\le t$, and $S_i\subseteq B$ with $|S_i|<t$ for every $i\in[n]$;
--      - for every $i\in[n]$, each vertex $y\notin A_i$ that is adjacent in $F$ to a vertex of $A_i$ lies in $S_i$;
--      - for every $i\in[n]$ and every main index $j\in[t]$ such that no vertex of $S_i$ has type $j$, the mass vanishes: $m_j(A_i)=0$.
--
--      Thus $W$ is partitioned into the bag $B$ and the outer sides $A_i$; each side is attached to $B$ only through a separator $S_i$ of fewer than $t$ vertices, and carries zero mass of every main type missing from $S_i$.
--   3. **Mismatch tests.** Let $C$ be a choice system on $t$ indices, with label maps $\lambda^{\mathrm L}_{ij}\colon D_i\to L_{ij}$ and $\lambda^{\mathrm R}_{ij}\colon D_j\to L_{ij}$ for $i<j$, and let $\varphi\colon F\to G_C$ be a homomorphism into its base graph. For a pair $p=(i,j)$ with $i<j$, a label $\alpha\in L_p$ and $x\in W$,
--   $$
--   \mathrm{lt}_{p,\alpha}(x)=\begin{cases}0&\text{if } \varphi(x)=(i,d) \text{ with } \lambda^{\mathrm L}_p(d)=\alpha,\\ 1&\text{otherwise,}\end{cases}\qquad \mathrm{rt}_{p,\alpha}(x)=\begin{cases}1&\text{if } \varphi(x)=(j,e) \text{ with } \lambda^{\mathrm R}_p(e)=\alpha,\\ 0&\text{otherwise.}\end{cases}
--   $$
--   For a helper $h=h_{ij;\ell}$ and $\alpha\in L_{ij}$, the helper test is $\mathrm{ht}_{h,\alpha}(x)=0$ if $\varphi(x)=(h,\alpha)$, and $\mathrm{ht}_{h,\alpha}(x)=1$ otherwise.
--
--   A balanced star models the star around a sink bag of a tree decomposition, together with the vertex partition it induces; the definition itself only records the axioms above. For the star parity (and $t\ge1$), results built on these definitions show that a balanced star exists whenever $F$ has a reduced cut decomposition with bags of size at most $t$, that its bag then consists of exactly one vertex of each main type, and that the base-graph images of these representatives form a successful choice. The mismatch tests drive the last step: on an edge $xy$ of $F$ with $x$ of type $i$ and $y$ of type $j$ the base graph forces the two labels to agree, so $\mathrm{lt}_{p,\alpha}(x)+\mathrm{rt}_{p,\alpha}(y)=1$, while the helper test couples the two predicates through the labels stored at helper vertices.
--
--   **Formalization Note** The labelling takes values in `Option (Fin regions)`, with `none` marking the bag, and `regionSet` gives its fibres. The structure is `BalancedStar w` with fields `regions`, `region`, `bag`, `bag_eq`, `size`, `separator`, `separator_sub`, `separator_small`, `boundary`, `zero_mass`; the parity function `b` is arbitrary in the definition. The tests are `leftTest`, `rightTest` and `helperTest`, defined through the partial label readouts of the base graph.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/BalancedBags.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/BalancedBags.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels

namespace OAI

namespace ParityWL

open scoped BigOperators

section BalancedBags

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t} {b : TemplateVertex t → Bit}

noncomputable def regionSet {n : ℕ} (region : W → Option (Fin n))
    (i : Option (Fin n)) : Finset W := Finset.univ.filter (fun x => region x = i)

/-- The star about a sink bag, with its vertex partition obtained from a tree
decomposition. -/
structure BalancedStar (w : WeightedWitness (template t) F a b) where
  regions : ℕ
  region : W → Option (Fin regions)
  bag : Finset W
  bag_eq : bag = regionSet region none
  size : bag.card ≤ t
  separator : Fin regions → Finset W
  separator_sub : ∀ i, separator i ⊆ bag
  separator_small : ∀ i, (separator i).card < t
  boundary : ∀ i, ∀ x ∈ regionSet region (some i), ∀ y,
    F.Adj x y → y ∉ regionSet region (some i) → y ∈ separator i
  zero_mass : ∀ i (j : Fin t),
    (∀ x ∈ separator i, a x ≠ .inl j) →
      w.mass (regionSet region (some i)) (.inl j) = 0

end BalancedBags

section MismatchPredicates

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t) {W : Type} {F : SimpleGraph W}
variable (φ : F →g baseGraph C)

noncomputable def leftTest (p : MainPair t) (α : C.Label p) (x : W) : Bit :=
  if leftLabelAt C p (φ x) = some α then 0 else 1

noncomputable def rightTest (p : MainPair t) (α : C.Label p) (x : W) : Bit :=
  if rightLabelAt C p (φ x) = some α then 1 else 0

noncomputable def helperTest (h : Helper t) (α : C.Label h.1.1) (x : W) : Bit :=
  if helperLabelAt C h (φ x) = some α then 0 else 1

end MismatchPredicates

end ParityWL

end OAI


