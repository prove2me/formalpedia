-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_LinPrimOn
-- name    : GroupIsoPoly_Supplement_LinPrimOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:24:22.453484+00:00
-- url     : https://prove2.me/theorems/103c6637-62e8-4554-8e23-994c45bb9f35
-- title:
--   Irreducible and linearly primitive actions on subquotients of $\mathbb F_p^d$
-- statement:
--   Let $S$ be a set of matrices in $\mathrm{GL}(d,p)$ and $L\le U$ subspaces of $\mathbb F_p^d$, both invariant under $S$; consider the induced action on $U/L$. Subspaces of $U/L$ are written as subspaces $W$ with $L\le W\le U$.
--
--   1. The action on $U/L$ is **irreducible** if $U/L\neq0$ and the only $S$-invariant $W$ with $L\le W\le U$ are $L$ and $U$.
--   2. A **block decomposition** of $U/L$ is a family $W_1,\dots,W_k$ ($k\ge1$) with $L<W_c\le U$, whose images form a direct sum $U/L=W_1/L\oplus\cdots\oplus W_k/L$, such that every $h\in S$ maps each $W_c$ onto some $W_{c'}$. A **linear imprimitivity system** is a block decomposition with $k\ge2$.
--   3. The action is **linearly primitive** if it is irreducible and has no linear imprimitivity system.
--
--   These are the paper's notions of §5.1 applied to induced actions on invariant subquotients, as Theorem 5.1 uses them for composition factors and their blocks.
--
--   **Formalization Note** $h(W)$ is the image of $W$ under the matrix $h$ (`gmap`). The direct-sum condition is $W_c\cap(L+\sum_{c'\neq c}W_{c'})=L$ together with $\sum_c W_c=U$; for subspaces containing $L$ this is independence in $U/L$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §5.1, p.41 (PDF p.45): irreducible, linear imprimitivity system, linearly primitive

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

variable {p d : ℕ}

/-- The image `h(U)` of a subspace `U ≤ F_p^d` under a matrix `h ∈ GL(d, p)`. -/
noncomputable def gmap [Fact p.Prime] (h : GL (Fin d) (ZMod p)) (U : Submodule (ZMod p) (Fin d → ZMod p)) :
    Submodule (ZMod p) (Fin d → ZMod p) :=
  U.map (Matrix.mulVecLin (h : Matrix (Fin d) (Fin d) (ZMod p)))

/-- **Irreducibility on a subquotient.** For subspaces `L ≤ U` of `F_p^d` invariant under a set `S` of
matrices, `IrredOn S L U` says that the induced action of `S` on `U/L` is irreducible: `U/L ≠ 0` and
the only `S`-invariant subspaces `W` with `L ≤ W ≤ U` are `L` and `U`.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), §5.1, p.41 (PDF p.45): "We say that H is irreducible if
there are no non-trivial invariant subspaces of H."

**Formalization Note.** Subspaces of `U/L` are represented by the subspaces `W` with `L ≤ W ≤ U`
(the correspondence theorem), and `W` is `S`-invariant when `h(W) ≤ W` for `h ∈ S`. -/
def IrredOn [Fact p.Prime] (S : Set (GL (Fin d) (ZMod p)))
    (L U : Submodule (ZMod p) (Fin d → ZMod p)) : Prop :=
  L < U ∧ ∀ W : Submodule (ZMod p) (Fin d → ZMod p), L ≤ W → W ≤ U →
    (∀ h ∈ S, gmap h W ≤ W) → W = L ∨ W = U

/-- **A block decomposition of a subquotient.** `IsBlockDecomp S L U W` says that the subspaces
`W 0, …, W (k-1)`, each with `L < W c ≤ U`, have images in `U/L` that form a direct-sum decomposition
`U/L = W₀/L ⊕ ⋯ ⊕ W_{k-1}/L` (each `W c / L ≠ 0`), and that every `h ∈ S` maps each `W c` onto some
`W c'`.

Qiao, Zhang, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §5.1, p.41 (PDF p.45): "A linear
imprimitivity system of H ≤ GL(d, p) is a direct sum decomposition F_p^d = U1 ⊕ · · · ⊕ Uk, with k ≥ 2
and Ui ≠ 0 for all i, such that for any h ∈ H and i ∈ [k], h(Ui) = Uj for some j ∈ [k]."

**Formalization Note.** Here `k ≥ 1` is allowed (a single block); a linear imprimitivity system is
the case `k ≥ 2`. Independence of the images in `U/L` is `W c ⊓ (L ⊔ ⨆_{c' ≠ c} W c') = L`, which for
subspaces containing `L` is the direct-sum condition in the quotient (for `k = 1` it is automatic). -/
def IsBlockDecomp [Fact p.Prime] (S : Set (GL (Fin d) (ZMod p)))
    (L U : Submodule (ZMod p) (Fin d → ZMod p)) {k : ℕ}
    (W : Fin k → Submodule (ZMod p) (Fin d → ZMod p)) : Prop :=
  1 ≤ k ∧ (∀ c, L < W c ∧ W c ≤ U) ∧ (⨆ c, W c) = U ∧
    (∀ c, W c ⊓ (L ⊔ ⨆ c' ∈ {c' : Fin k | c' ≠ c}, W c') = L) ∧
    ∀ h ∈ S, ∀ c, ∃ c', gmap h (W c) = W c'

/-- **Linear primitivity on a subquotient.** `LinPrimOn S L U` says that the action of `S` on `U/L`
is irreducible and has no linear imprimitivity system: there is no block decomposition of `U/L`
into `k ≥ 2` nonzero summands permuted by `S`.

Qiao, Zhang, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), §5.1, p.41 (PDF p.45): "An
irreducible action is linearly primitive if no such decomposition exists. We use “primitive” in this
linear sense for matrix actions." -/
def LinPrimOn [Fact p.Prime] (S : Set (GL (Fin d) (ZMod p)))
    (L U : Submodule (ZMod p) (Fin d → ZMod p)) : Prop :=
  IrredOn S L U ∧
    ¬ ∃ (k : ℕ) (W : Fin k → Submodule (ZMod p) (Fin d → ZMod p)), 2 ≤ k ∧ IsBlockDecomp S L U W

end Supplement

end GroupIsoPoly


