-- Prove2me | Definitions.Def_LatticePrepro_Reduction_LinearSystem
-- name    : LatticePrepro_Reduction_LinearSystem
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:52.783537+00:00
-- url     : https://prove2.me/theorems/30996775-141c-466e-915d-b04ad49e587c
-- title:
--   Linear systems with a fixed matrix and the block-sparse linear-system problem (Definition 3.10)
-- statement:
--   Fix a field $F$ and a set $X$ of instances.
--
--   1. **`LinearSystemFamily F X`.** A family of linear systems $Av=b_x$ ($x\in X$) with a fixed matrix. It consists of:
--      - a finite set $\iota$ of columns and a finite set $\beta$ of blocks;
--      - a block map $\mathrm{blk}:\iota\to\beta$ such that every block contains exactly $b$ columns, where $b$ is the block size;
--      - an $F$-vector space $W$ of rows and an $F$-linear map $A:F^\iota\to W$, the fixed matrix;
--      - a right-hand side $b_x\in W$ for every instance $x$.
--
--      The number of blocks is $D=|\beta|$ (`numBlocks`).
--   2. **Solutions** (`IsSolution x v`): $v\in F^\iota$ with $Av=b_x$.
--   3. **YES instances** (`IsYes x`): some solution $v$ is binary ($v_i\in\{0,1\}$ for all $i$) and has at most one nonzero coordinate in each block.
--   4. **NO instances with gap $g$** (`IsNo g x`): every solution $v$ has Hamming weight $\operatorname{wt}(v)>g\cdot D$.
--   5. **Gap reductions** (`IsGapReduction Lang g`), for a language $\mathrm{Lang}\subseteq X$: every $x\in\mathrm{Lang}$ is a YES instance and every $x\notin\mathrm{Lang}$ is a NO instance with gap $g$, that is,
--   $$x\in\mathrm{Lang}\Rightarrow\exists\,v\in\{0,1\}^\iota:\ Av=b_x,\ \text{at most one nonzero per block};\qquad x\notin\mathrm{Lang}\Rightarrow\forall v\,\bigl(Av=b_x\Rightarrow\operatorname{wt}(v)>g\cdot D\bigr).$$
--
--   This formalizes the block-sparse linear-system problem with preprocessing, $(D,b,g)$-BSLSP (Definition 3.10). The matrix $A$ and its block partition are the fixed input and $b_x$ is the online input. `IsGapReduction` says that $x\mapsto b_x$ maps the language to YES instances and its complement to NO instances. It is the conclusion of Theorems 4.6 and 4.8 and the input of the code and lattice conversions (Lemmas 3.11 and 3.12).
--
--   **Formalization Note** The matrix is an abstract $F$-linear map into an arbitrary $F$-module $W$ rather than an $h\times n$ matrix, and $F$ is any field (the paper uses $\mathbb{F}_p$). The parameter conditions $D,b,g\ge1$ and $b>g$ of Definition 3.10 are not part of these definitions; where needed they are stated separately (for example in `GapReduction`). Computability of the reduction is not modelled. The `Fintype` and `DecidableEq` instances are fields of the structure.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definition 3.10 (\label{def:block-sparse-linear-system}); Lean: LatticePrepro/Reduction/LinearSystem.lean, LatticePrepro.LinearSystemFamily, LatticePrepro.LinearSystemFamily.numBlocks, LatticePrepro.LinearSystemFamily.IsSolution, LatticePrepro.LinearSystemFamily.IsYes, LatticePrepro.LinearSystemFamily.IsNo, LatticePrepro.LinearSystemFamily.IsGapReduction

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks

/-!
# Linear systems with a fixed matrix

A *linear system family* with a fixed matrix (cf. Section 3 of the paper) is a linear map
`A : (ι → F) →ₗ[F] W` together with a right-hand side `rhs x : W` for every instance `x`.
The columns `ι` are partitioned into blocks by `blk : ι → β`. The matrix `A` does not depend
on `x`; only `rhs x` does.

The *block-sparse linear-system problem with preprocessing* (Definition 3.10) asks to distinguish

* YES: `A v = rhs x` has a binary solution with at most one nonzero coordinate per block, from
* NO: every solution `v` of `A v = rhs x` has Hamming weight `> g · D`,

where `D = |β|` is the number of blocks and `g` the gap.
-/

namespace LatticePrepro

/-- A family of linear systems `A v = rhs x` with a fixed matrix and block-partitioned columns. -/
structure LinearSystemFamily (F : Type) [Field F] (X : Type) where
  /-- Column indices. -/
  ι : Type
  [fintypeι : Fintype ι]
  [decEqι : DecidableEq ι]
  /-- Block indices. -/
  β : Type
  [fintypeβ : Fintype β]
  [decEqβ : DecidableEq β]
  /-- The block partition of the columns. -/
  blk : ι → β
  /-- The block size. -/
  blockSize : ℕ
  card_fiber : ∀ s : β, (Finset.univ.filter fun i => blk i = s).card = blockSize
  /-- Codomain (rows). -/
  W : Type
  [addCommGroupW : AddCommGroup W]
  [moduleW : Module F W]
  /-- The fixed matrix. -/
  A : (ι → F) →ₗ[F] W
  /-- The right-hand side for instance `x`. -/
  rhs : X → W

namespace LinearSystemFamily

variable {F : Type} [Field F] {X : Type}

attribute [instance] fintypeι decEqι fintypeβ decEqβ addCommGroupW moduleW

variable (L : LinearSystemFamily F X)

/-- The number of blocks `D`. -/
abbrev numBlocks : ℕ := Fintype.card L.β

/-- Solutions of the system for instance `x`. -/
def IsSolution (x : X) (v : L.ι → F) : Prop := L.A v = L.rhs x

/-- YES instances of BSLSP: a binary block-sparse solution exists. -/
def IsYes [DecidableEq F] (x : X) : Prop :=
  ∃ v : L.ι → F, L.IsSolution x v ∧ IsBinary v ∧ AtMostOnePerBlock L.blk v

/-- NO instances of BSLSP with gap `g`: every solution has weight more than `g · D`. -/
def IsNo [DecidableEq F] (g : ℕ) (x : X) : Prop :=
  ∀ v : L.ι → F, L.IsSolution x v → g * L.numBlocks < hammingNorm v

/-- A reduction with gap `g` from a language `Lang` to the BSLSP promise problem. -/
def IsGapReduction [DecidableEq F] (Lang : Set X) (g : ℕ) : Prop :=
  (∀ x ∈ Lang, L.IsYes x) ∧ (∀ x ∉ Lang, L.IsNo g x)

end LinearSystemFamily

end LatticePrepro


