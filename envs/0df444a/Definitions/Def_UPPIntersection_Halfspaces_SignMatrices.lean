-- Prove2me | Definitions.Def_UPPIntersection_Halfspaces_SignMatrices
-- name    : UPPIntersection_Halfspaces_SignMatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:00.269413+00:00
-- url     : https://prove2.me/theorems/d6468159-e515-407d-a5a5-c64f002418d5
-- title:
--   Definition 1.1, Definition 6.1 — $HS_{M,d}$, $F\wedge F$ and Forster's average margin
-- statement:
--   Sign matrices take values in $\{-1,1\}$ with $-1$ meaning "true"; the conjunction $x\wedge y$ is $-1$ iff $x=y=-1$. A sign matrix is stored as a matrix of bits with $\mathsf{true}$ standing for $+1$, so that the published `signRank` (minimum rank of a real matrix $R$ with $A_{ab}R_{ab}>0$ everywhere) applies directly.
--
--   1. **Disjoint conjunction.** For $F$ with rows $A$ and columns $B$, $F\wedge F$ has rows $A^2$, columns $B^2$ and entries $(F\wedge F)((a_1,a_2),(b_1,b_2))=F(a_1,b_1)\wedge F(a_2,b_2)$.
--   2. **Bounded integer halfspaces (Definition 1.1).** For natural numbers $M,d$ let $G_{M,d}=\{-M,\dots,M\}^d$ and
--   $$HS_{M,d}(a,b)=\operatorname{sgn}\bigl(\langle a,b\rangle-\tfrac12\bigr),\qquad a,b\in G_{M,d},$$
--   so $HS_{M,d}(a,b)=-1$ iff $\langle a,b\rangle\le0$. The encoding length of a row is $n=d\,\lceil\log_2(2M+1)\rceil$.
--   3. **Average margin (Definition 6.1).** For a distribution $\mu$ on the columns,
--   $$m^{\mathrm{avg}}_\mu(A)=\sup_{r,\,u,\,v}\ \min_{a}\ \mathbb E_{b\sim\mu}\,|\langle u_a,v_b\rangle| ,$$
--   the supremum over all dimensions $r$ and all unit vectors $u_a,v_b\in\mathbb R^r$ with $A_{ab}\langle u_a,v_b\rangle>0$ for every $(a,b)$.
--
--   These are the matrices whose sign rank the paper bounds: Forster's theorem turns an average-margin upper bound into a sign-rank lower bound, and $HS_{M,d}\wedge HS_{M,d}$ is the explicit separating family.
--
--   **Formalization Note** The grid is `Fin d → Set.Icc (-M) M` over `ℤ`, including all zero vectors. Unit arrangements are the published `UnitRealization`. For nonempty finite matrices the set under the supremum is nonempty and bounded by 1, so the real `sSup` is a genuine supremum.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 3 (Definition 1.1 and footnote 2), p. 12 (§2 conventions for ∧), p. 27 (Definition 6.1); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_SignRankMargin_OREquality_Geometry

namespace UPPIntersection.Halfspaces

open SignRankMargin.OREquality

/-- The real value `±1` of a sign-matrix entry stored as a `Bool`: `true` is `+1` (logical
"false" in the source's convention) and `false` is `-1` (logical "true"). -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- The disjoint conjunction `F ∧ F` of a sign matrix: rows `(a₁, a₂)`, columns `(b₁, b₂)`, entry
`F(a₁,b₁) ∧ F(a₂,b₂)`, which is `-1` exactly when both entries are `-1`. In the `Bool` encoding
(`true = +1`) this is Boolean `||`. -/
def andSquare {X Y : Type} (F : Matrix X Y Bool) : Matrix (X × X) (Y × Y) Bool :=
  fun a b => F a.1 b.1 || F a.2 b.2

/-- The coordinate set `{-M, …, M}`. -/
abbrev Coord (M : ℕ) : Type := Set.Icc (-(M : ℤ)) (M : ℤ)

/-- The integer grid `{-M, …, M}^d`, the row and column set of `HS_{M,d}` (Definition 1.1). -/
abbrev Grid (M d : ℕ) : Type := Fin d → Coord M

/-- The bounded integer halfspace problem `HS_{M,d}(a,b) = sgn(⟨a,b⟩ - 1/2)` (Definition 1.1),
stored with `true = +1`: the entry is `true` iff `⟨a,b⟩ - 1/2 > 0`. -/
noncomputable def HS (M d : ℕ) : Matrix (Grid M d) (Grid M d) Bool :=
  fun a b => decide ((1 : ℝ) / 2 < ∑ i, ((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ))

/-- The number of bits `n = d · ⌈log₂(2M+1)⌉` used to encode one row (or column) of `HS_{M,d}`. -/
def encodingLength (M d : ℕ) : ℕ := d * Nat.clog 2 (2 * M + 1)

/-- Forster's **average margin** `m^{avg}_μ(A)` (Definition 6.1): the supremum, over all finite
dimensions `r` and all unit-vector arrangements `u_a, v_b ∈ ℝ^r` with `A_{ab}⟨u_a,v_b⟩ > 0` for all
`(a,b)`, of `min_a ∑_b μ(b) |⟨u_a, v_b⟩|`. Here `μ` is a distribution on the columns. -/
noncomputable def avgMargin {X Y : Type} [Fintype Y] (A : Matrix X Y Bool) (μ : Y → ℝ) : ℝ :=
  sSup {m : ℝ | ∃ (r : ℕ) (u : X → EuclideanSpace ℝ (Fin r)) (v : Y → EuclideanSpace ℝ (Fin r)),
    UnitRealization A r u v ∧ m = ⨅ a, ∑ b, μ b * |inner ℝ (u a) (v b)|}

end UPPIntersection.Halfspaces


