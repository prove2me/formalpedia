-- Prove2me | Definitions.Def_PolySwap_KMS_Dehn
-- name    : PolySwap_KMS_Dehn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:39:51.73801+00:00
-- url     : https://prove2.me/theorems/ed896834-e4dc-4dd3-ae8a-b75cfab06cbb
-- title:
--   Word length, area and Dehn functions of a presentation; coset complexes $CC(G;(H_i))$ and their multiplication-table presentation
-- statement:
--   Let $G$ be a group with a presentation $\langle S\mid R\rangle$, i.e. a map $S\to G$ whose words generate $G$ and whose relations are exactly the normal closure of $R\subseteq\mathrm{Free}(S)$. $|w|_S$ is the length of a word $w\in\mathrm{Free}(S)$. The **area** of a relation $w$ is the least $k$ with
--   $$w=u_1^{-1}\rho_1u_1\cdots u_k^{-1}\rho_ku_k\ \text{ in }\mathrm{Free}(S),\qquad\rho_i\in R\cup R^{-1},$$
--   and the **Dehn function** is $\mathrm{Dehn}_{S,R}(m)=\max\{\mathrm{Area}_R(w):w=1\text{ in }G,\ |w|_S\le m\}$.
--
--   The **coset complex** $CC(G;(H_i)_{i\in I})$ of a group with a family of subgroups has vertex set $\bigsqcup_iG/H_i$; $\{g_1H_{i_1},\dots,g_kH_{i_k}\}$ is a face iff the $i_j$ are distinct and $\bigcap_jg_jH_{i_j}\ne\emptyset$. It is pure of dimension $|I|-1$, with maximal faces the chambers $\{gH_i:i\in I\}$, and carries the uniform distribution on them. For a 1-connected coset complex $Y=CC(G;(H_i))$, $\mathrm{Dehn}_Y$ is the Dehn function of the presentation of $G$ whose generators are all nontrivial elements of the $H_i$ ($S=\bigcup_iH_i\setminus\{1\}$, Appendix B, p. 61) and whose relations are $\bigcup_iR_i$, $R_i$ the nontrivial relations of length at most 3 in the multiplication table of $H_i$.
--
--   **Formalization Note.** Words are elements of `FreeGroup S`, evaluated by `FreeGroup.lift ι`; `wordLength` is the reduced length `FreeGroup.norm` (formal inverses count as letters). `area` and `dehn` take values in `ℕ∞` (`area = ⊤` if $w$ is not a product of conjugates of relators). `cosetComplex G H` has vertex type `Σ i, G ⧸ H i` and is the empty complex for an infinite `G` (only finite groups are used). `CosetGen H` is the subtype of nontrivial elements lying in some `H i` (each element once): $S=\bigcup H_i\setminus\{1\}$, as Appendix B (p. 61) fixes it. `cosetWord H g` is the word of $g\in\bigcup H_i$: $[g]$ for $g\neq 1$, the empty word for $g=1$. `multTable H i` is the set of positive words $[a][b]$, $[a][b][c]$ with letters in `H i` whose product is $1$.
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.1 (p. 10, Definition 2.4, Remark 2.5), §2.5 (pp. 16–17, Definitions 2.22, 2.23), §2.6 (p. 20, Definition 2.35), Appendix B (pp. 61–62)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex

open Classical

noncomputable section

namespace PolySwap.KMS

/-!
# Word length, area, Dehn functions; coset complexes and their multiplication-table presentation

Dikstein, Oppenheim, Valentiner-Branth, *Polynomial Swap Coboundary Expansion with Applications
to LTCs and PCPs*, STOC 2027 submission (manuscript sha256 b9cb2095…), §2.1 (p. 10,
Definition 2.4, Remark 2.5, Garland weights), §2.5 (pp. 16–17, Definitions 2.22, 2.23),
§2.6 (p. 20, Definition 2.35) and Appendix B (pp. 61–62).

A presentation `⟨S | R⟩` of a group `G` is a map `ι : S → G` together with a set `R` of words
(elements of the free group `Free(S)`); words are evaluated in `G` by `FreeGroup.lift ι`.
-/

variable {G : Type*} [Group G] {S : Type*}

/-- `|w|_S` (Definition 2.22): the length of the (reduced) word `w ∈ Free(S)`. -/
def wordLength (w : FreeGroup S) : ℕ := w.norm

/-- `Area_R(w)` (p. 17): the least `k` such that `w = u₁⁻¹ρ₁u₁ ⋯ u_k⁻¹ρ_k u_k` in `Free(S)` with
`ρ_i ∈ R ∪ R⁻¹`; `⊤` if there is no such expression. -/
def area (R : Set (FreeGroup S)) (w : FreeGroup S) : ℕ∞ :=
  ⨅ (l : List (FreeGroup S × FreeGroup S))
    (_ : (∀ p ∈ l, p.2 ∈ R ∨ p.2⁻¹ ∈ R) ∧ w = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod),
    (l.length : ℕ∞)

/-- `Dehn_{S,R}(m) = max{Area_R(w) : w = 1 in G, |w|_S ≤ m}` (Definition 2.23), with values in
`ℕ∞`. -/
def dehn (ι : S → G) (R : Set (FreeGroup S)) (m : ℕ) : ℕ∞ :=
  ⨆ (w : FreeGroup S) (_ : FreeGroup.lift ι w = 1 ∧ wordLength w ≤ m), area R w

/-- `G = ⟨S | R⟩`: the words in `S` generate `G` and the relations of `G` are exactly the normal
closure of `R` in `Free(S)`. -/
def IsPresentation (ι : S → G) (R : Set (FreeGroup S)) : Prop :=
  Function.Surjective (FreeGroup.lift ι) ∧ (FreeGroup.lift ι).ker = Subgroup.normalClosure R

/-- The coset complex `CC(G; (H_i)_{i ∈ ι})` (Definition 2.4) of a finite group: vertex set
`⊔_i G/H_i`, and `{g₁H_{i₁}, …, g_kH_{i_k}}` is a face iff the `i_j` are distinct and
`⋂_j g_jH_{i_j} ≠ ∅`. Its maximal faces are the chambers `{gH_i : i ∈ ι}`, `g ∈ G`, and it carries
the uniform distribution on them (§2.1, p. 11). (For an infinite `G` the definition returns the
empty complex; it is only used for finite groups.) -/
def cosetComplex (G : Type*) [Group G] {ι : Type*} [Fintype ι] (H : ι → Subgroup G) :
    WComplex (Σ i, G ⧸ H i) where
  tops := if _h : Finite G then
      haveI := Fintype.ofFinite G
      Finset.univ.image (fun g : G => Finset.univ.image (fun i => (⟨i, (g : G ⧸ H i)⟩ : Σ i, G ⧸ H i)))
    else ∅
  wt _ := 1

/-- The generators of the coset-complex presentation (Definition 2.35): the nontrivial elements
of the subgroups `H_i`, `S = ⋃_i H_i \ {1}` (as Appendix B, p. 61, makes explicit). -/
abbrev CosetGen {ι : Type*} (H : ι → Subgroup G) : Type _ := {g : G // g ≠ 1 ∧ ∃ i, g ∈ H i}

/-- The word of `Free(S)` representing an element `g ∈ ⋃_i H_i`: the one-letter word `[g]` for
`g ≠ 1`, the empty word for `g = 1`. -/
def cosetWord {ι : Type*} (H : ι → Subgroup G) (g : G) (hg : ∃ i, g ∈ H i) :
    FreeGroup (CosetGen H) :=
  if h : g = 1 then 1 else FreeGroup.of ⟨g, h, hg⟩

/-- `R_i`: the nontrivial relations of length at most 3 in the multiplication table of `H_i`
(p. 20; Appendix B, p. 62): the positive words `[a][b]`, `[a][b][c]` with letters in
`H_i \ {1}` whose product is `1` in `G` (e.g. `[g][g⁻¹]` and `[a][b][(ab)⁻¹]`). -/
def multTable {ι : Type*} (H : ι → Subgroup G) (i : ι) : Set (FreeGroup (CosetGen H)) :=
  {w | ∃ l : List (CosetGen H), 1 ≤ l.length ∧ l.length ≤ 3 ∧ (∀ x ∈ l, x.1 ∈ H i) ∧
    (l.map Subtype.val).prod = 1 ∧ w = (l.map FreeGroup.of).prod}

/-- `⋃_i R_i`, the relations of the coset-complex presentation. -/
def cosetRel {ι : Type*} (H : ι → Subgroup G) : Set (FreeGroup (CosetGen H)) :=
  ⋃ i, multTable H i

/-- `Dehn_X` for `X = CC(G; (H_i))` (Definition 2.35): the Dehn function of the presentation of
`G` by the nontrivial elements of the `H_i` and the relations `⋃_i R_i`. -/
def cosetDehn {ι : Type*} (H : ι → Subgroup G) (m : ℕ) : ℕ∞ :=
  dehn (Subtype.val : CosetGen H → G) (cosetRel H) m

end PolySwap.KMS


