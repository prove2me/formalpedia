-- Prove2me | Definitions.Def_SubspaceConv_cosetSum
-- name    : SubspaceConv_cosetSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:13.053694+00:00
-- url     : https://prove2.me/theorems/c9d206f4-20cc-428d-92d8-75aa1aaefc55
-- title:
--   The coset operator $\mathsf A$ of §3.1
-- statement:
--   For tables $h_B:\mathbb F_q^d/B\to S$, one for each direction $B\le\mathbb F_q^d$ with $\dim B\le\ell$, define for each direction $D$ with $\dim D\le\ell$ and each coset $x+D$
--   $$(\mathsf Ah)_D(x+D)=\sum_{B\le D}\ \sum_{y+B\subseteq x+D}h_B(y+B).$$
--   By Lemma 1, $\mathsf A$ is the part of the zeta transform that sums crossing subspaces into crossing subspaces: $U(B,y+B)\le U(D,x+D)$ exactly when $B\le D$ and $y+B\subseteq x+D$.
--
--   **Formalization Note** Cosets are elements of the quotient module $\mathbb F^d/B$; the condition $y+B\subseteq x+D$ is the literal inclusion of the two cosets as subsets of $\mathbb F^d$. Values lie in any additive commutative monoid.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.1, p.11 (definition of A); §3.1–3.2, p.12 (dimension cutoffs)

import Mathlib
import Definitions.Def_SubspaceConv_SubLE

namespace SubspaceConv

open Classical in
/-- The coset operator `A` of §3.1: for tables `h_B : F^d / B → S` indexed by the directions
`B` of dimension at most `ℓ`,
`(A h)_D(x + D) = ∑_{B ≤ D} ∑_{y + B ⊆ x + D} h_B(y + B)` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.1, p.11, and the
cutoff of §3.1–3.2, p.12).

**Formalization Note** Directions `B, D` range over `SubLE F d ℓ` (dimension at most `ℓ`).
Cosets are elements of the quotient module `(Fin d → F) ⧸ B`; the condition `y + B ⊆ x + D` is
the literal inclusion of the cosets as subsets of `F^d` (preimages under the quotient maps).
Values lie in any additive commutative monoid `S`. -/
noncomputable def cosetSum {F : Type*} [Field F] [Fintype F] {d ℓ : ℕ} {S : Type*}
    [AddCommMonoid S] (h : (B : SubLE F d ℓ) → (Fin d → F) ⧸ B.1 → S)
    (D : SubLE F d ℓ) (c : (Fin d → F) ⧸ D.1) : S :=
  ∑ B : SubLE F d ℓ, if B.1 ≤ D.1 then
    ∑ c' : (Fin d → F) ⧸ B.1,
      (if (B.1.mkQ ⁻¹' {c'} ⊆ D.1.mkQ ⁻¹' {c}) then h B c' else 0)
  else 0

end SubspaceConv


