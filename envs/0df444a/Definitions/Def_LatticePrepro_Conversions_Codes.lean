-- Prove2me | Definitions.Def_LatticePrepro_Conversions_Codes
-- name    : LatticePrepro_Conversions_Codes
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:20:53.043742+00:00
-- url     : https://prove2.me/theorems/9fbeb92e-77ce-403c-8e8d-88c07ac49221
-- title:
--   Fixed codes with targets, Hamming distance to a code, and the code of a block-sparse linear system (Section 3, Appendix B.1)
-- statement:
--   These definitions set up the code side of the conversion from block-sparse linear systems (Definition 3.10) to the nearest codeword problem with preprocessing (Lemma 3.11).
--
--   1. **Code families** (`CodeFamily F X`). For a field $F$ and a set of instances $X$: a finite coordinate set $M$, a linear code $\mathcal C\subseteq F^M$ (an $F$-subspace, the same for every instance), and a target $t_x\in F^M$ for each instance $x\in X$.
--   2. **Distance to a code** (`CodeFamily.codeDist`, Definition 3.1). For $y\in F^M$ and a subspace $\mathcal C\subseteq F^M$,
--   $$\Delta(y,\mathcal C)=\min_{c\in\mathcal C}\Delta(y,c),$$
--   where $\Delta(y,c)$ is the Hamming distance, the number of coordinates in which $y$ and $c$ differ.
--   3. **Extension of scalars** (`CodeFamily.extend`). For a prime $p$, a code family over $\mathbb F_p$ and a field $F$ containing $\mathbb F_p$ (an $\mathbb F_p$-algebra): the code family over $F$ with the same coordinates, the code $\operatorname{span}_F\mathcal C\subseteq F^M$ spanned by the codewords of $\mathcal C$ read in $F^M$, and the same targets read in $F^M$.
--   4. **The code of a linear system** (`LinearSystemFamily.code`). Let $L$ be a linear-system family over $\mathbb F_p$: a fixed linear map $A$ on $\mathbb F_p^{\iota}$ for a finite column set $\iota$, right-hand sides $b_x$, and a partition of the columns into $D$ blocks. Its code is
--   $$\mathcal C_L=\ker A\times\{0\}=\{(u,u')\in\mathbb F_p^{\iota}\times\mathbb F_p^{\iota}:\ Au=0,\ u'=0\},$$
--   with coordinate set $\iota\sqcup\iota$.
--   5. **Its targets** (`LinearSystemFamily.codeTarget`). $y_x=(v_0,0)$ for a chosen solution $v_0$ of $Av=b_x$ if the system is solvable, and $y_x=(0,\mathbf 1)$ (all ones on the second copy) otherwise.
--   6. **Its blocks** (`LinearSystemFamily.codeBlk`). The coordinates $\iota\sqcup\iota$ are partitioned into blocks indexed by two copies of the block set; each copy of $\iota$ carries the block partition of the columns.
--
--   These are the code, targets and block structure of the proof of Lemma 3.11 (Appendix B.1): $y_x-\mathcal C_L$ is the set of solutions of $Av=b_x$ padded with zeros, which yields the gap (38), and extension of scalars carries the gap to any field of characteristic $p$. The same code and blocks are the starting point of the lattice reduction of Lemma 3.12.
--
--   **Formalization Note.** `codeDist` is a natural number, defined as the `sInf` of $\{\Delta(y,c): c\in\mathcal C\}$; this set is nonempty ($0\in\mathcal C$), so the infimum is attained and equals the paper's minimum. Codes are `Submodule F (M → F)`, and the coordinate set $M$ of a code family is a type with `Fintype` and `DecidableEq` instances. The solution $v_0$ is picked by classical choice, so `codeTarget` is noncomputable. The paper's block length $M=2n$ corresponds to the coordinate type `ι ⊕ ι`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definition 3.1 (\label{def:code-lattice-distances}) and the proof of Lemma 3.11 (\label{lem:block-system-codes}) in Appendix B.1 (\label{subsec:affine-code-proof}); Lean: LatticePrepro/Conversions/Codes.lean, LatticePrepro.CodeFamily, LatticePrepro.CodeFamily.codeDist, LatticePrepro.CodeFamily.extend, LatticePrepro.LinearSystemFamily.code, LatticePrepro.LinearSystemFamily.codeTarget, LatticePrepro.LinearSystemFamily.codeBlk

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem

/-!
# From linear systems to codes (Lemma 3.11, Appendix B.1)

Given a linear system family `A · v = b_x` over `𝔽_p` with columns `ι`, we build a fixed code
`𝒞 = ker A × {0} ⊆ 𝔽_p^{ι ⊕ ι}` and targets `y_x`: a solution `(v_0, 0)` of the system when one
exists, and `(0, 1)` otherwise. Then `y_x - 𝒞` is the set of solutions (padded by zeros), so

* YES instances have a binary vector `e` with `y_x - e ∈ 𝒞`, at most one nonzero entry per block
  and weight `≤ D`;
* NO instances have `dist(y_x, 𝒞) > g · D`.

The code is then extended by scalars to any finite field `F ⊇ 𝔽_p`, which preserves distances
to targets over `𝔽_p`.
-/

namespace LatticePrepro

/-- A fixed linear code with a target for every instance. -/
structure CodeFamily (F : Type) [Field F] (X : Type) where
  /-- Coordinates. -/
  M : Type
  [fintypeM : Fintype M]
  [decEqM : DecidableEq M]
  /-- The code. -/
  code : Submodule F (M → F)
  /-- The target for instance `x`. -/
  target : X → (M → F)

namespace CodeFamily

variable {F : Type} [Field F] {X : Type}

attribute [instance] fintypeM decEqM

/-- Hamming distance from a word to a code (Definition 3.1). -/
noncomputable def codeDist [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) : ℕ :=
  sInf {d | ∃ c ∈ C, hammingDist y c = d}

end CodeFamily

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The code `ker A × {0}` of Lemma 3.11. -/
def LinearSystemFamily.code : Submodule (ZMod p) (L.ι ⊕ L.ι → ZMod p) :=
  LinearMap.ker ((L.A.comp (LinearMap.funLeft (ZMod p) (ZMod p) Sum.inl)).prod
    (LinearMap.funLeft (ZMod p) (ZMod p) Sum.inr))

open Classical in
/-- The target `y_x` of Lemma 3.11. -/
noncomputable def LinearSystemFamily.codeTarget (x : X) : L.ι ⊕ L.ι → ZMod p :=
  if h : ∃ v, L.IsSolution x v then Sum.elim h.choose 0 else Sum.elim 0 1

/-- The block of a code coordinate. -/
def LinearSystemFamily.codeBlk : L.ι ⊕ L.ι → L.β ⊕ L.β := Sum.map L.blk L.blk

end OfSystem

section Extend

variable {p : ℕ} [Fact p.Prime] {X : Type} (F : Type) [Field F] [Algebra (ZMod p) F]

/-- The `F`-linear code spanned by a code over `𝔽_p`, with the targets mapped along
`algebraMap`. -/
noncomputable def CodeFamily.extend (C : CodeFamily (ZMod p) X) : CodeFamily F X where
  M := C.M
  code := Submodule.span F ((fun c : C.M → ZMod p => fun i => algebraMap (ZMod p) F (c i)) '' C.code)
  target := fun x i => algebraMap (ZMod p) F (C.target x i)

end Extend

end LatticePrepro


