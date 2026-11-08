-- Prove2me | Definitions.Def_QuadraticRE_Auth
-- name    : QuadraticRE_Auth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:07:19.725766+00:00
-- url     : https://prove2.me/theorems/e834b52f-005c-49cc-b127-8b55573e5920
-- title:
--   Authorized sets (Definition 4.5) and child blocks
-- statement:
--   For $X\in\{A,C\}$, a set $S\subseteq[L]$ of leaves is **authorized** for $\mathrm{Sh}^j_X$ if there is a map $\mathrm{Rec}_S:\mathbb F_2^{|S|}\to\mathbb F_2$ with $\mathrm{Rec}_S(\mathrm{Sh}^j_X(s;\theta)[S])=s$ for every root bit $s$ and every mask vector $\theta$; $\mathrm{Auth}^j_X(S)$ is this property. For $S\subseteq[4^{j+1}]$ and a child $\nu$, $S_\nu\subseteq[4^j]$ is the set of selected leaves in child block $\nu$, numbered within that block.
--
--   Authorization is the combinatorial quantity on which the privacy error depends.
--
--   **Formalization Note** Defined from the sharing itself, not by the recursion of Lemma 4.8 or by linear algebra, so both are theorems. $\mathbb F_2^{|S|}$ is the type of functions on $S$. Child block $\nu$ (numbered $0,\dots,3$) holds the leaves $\nu4^j,\dots,(\nu+1)4^j-1$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Definition 4.5, pp.21–22; Lemma 4.8, p.26

import Mathlib
import Definitions.Def_QuadraticRE_Sh

namespace QuadraticRE

/-- Definition 4.5 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), pp.21–22: `S ⊆ [L]` is authorized for `Sh^j_X` if there is a map
`Rec_S : F₂^{|S|} → F₂` with `Rec_S(Sh^j_X(s; θ)[S]) = s` for every root bit `s` and every mask vector
`θ`. `Auth^j_X(S)` is this property.

**Formalization Note.** Defined from the sharing itself, not by the recursion of Lemma 4.8 and not by
linear algebra. `F₂^{|S|}` is the function type on the subtype of `S`. -/
def Auth (X : Scheme) (j : ℕ) (S : Finset (Fin (4 ^ j))) : Prop :=
  ∃ Rec : (S → F2) → F2, ∀ (s : F2) (θ : Fin (maskLen X j) → F2), Rec (S.restrict (Sh X j s θ)) = s

/-- Leaf number `i` of child block `ν` in a tree of depth `j + 1`. -/
def leafOf {j : ℕ} (ν : Fin 4) (i : Fin (4 ^ j)) : Fin (4 ^ (j + 1)) :=
  ⟨ν.val * 4 ^ j + i.val, by
    have hν := ν.isLt
    have hi := i.isLt
    have h1 : (ν.val + 1) * 4 ^ j ≤ 4 * 4 ^ j := Nat.mul_le_mul_right _ hν
    rw [pow_succ]
    nlinarith⟩

/-- `S_ν ⊆ [4^j]` of Lemma 4.8, p.26: "the indices of the selected leaves in child block `ν`, numbered
within that block". -/
def block {j : ℕ} (S : Finset (Fin (4 ^ (j + 1)))) (ν : Fin 4) : Finset (Fin (4 ^ j)) :=
  Finset.univ.filter (fun i => leafOf ν i ∈ S)

end QuadraticRE


