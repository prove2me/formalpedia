-- Prove2me | Definitions.Def_LatticePrepro_Explicit
-- name    : LatticePrepro_Explicit
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:14:12.190463+00:00
-- url     : https://prove2.me/theorems/a9cb223b-477c-4599-b050-760df0be383b
-- title:
--   Theorem 5.1 for the paper's construction: tables, the code and lattice built from them, and the gap property
-- statement:
--   These definitions name the code and the lattice that the paper constructs for Theorem 5.1, so that the theorem can be stated for them.
--
--   1. **Gap of a code family** (`CodeFamily.HasGap`). A code family with code $\mathcal C\subseteq F^{M}$ and targets $t_x$ has the gap for a radius $R$, a real $\varepsilon$, a language $\mathrm{Lang}$ and integers $n,C$ if $R\ge1$, $1\le M\le n^{C}$, $\Delta(t_x,\mathcal C)\le R$ for $x\in\mathrm{Lang}$, and $\Delta(t_x,\mathcal C)>M^{1-\varepsilon}\cdot R$ for $x\notin\mathrm{Lang}$.
--   2. **Gap of a lattice family** (`LatticeFamily.HasGap`). A lattice family with lattice $\Lambda\subseteq\mathbb Z^{M}$ and targets $t_x$ has the gap for a norm exponent $p$ (with $s=\min\{p,2\}$), a radius $R$, $\varepsilon$, $\mathrm{Lang}$ and $n,C$ if $R\ge1$, $1\le M\le n^{C}$, $N\cdot\mathbb Z^{M}\subseteq\Lambda$ for some integer $N>0$, $\operatorname{dist}_p(t_x,\Lambda)\le R$ for $x\in\mathrm{Lang}$, and $\operatorname{dist}_p(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R$ for $x\notin\mathrm{Lang}$.
--   3. **Change of instances** (`CodeFamily.comap`, `LatticeFamily.comap`). The same code or lattice, with the target of $y$ defined as the target of $f(y)$ for a map $f$ of instances.
--   4. **The code of a linear system over $F$** (`LinearSystemFamily.codeFamily`). For a linear-system family over $\mathbb F_p$ and a field $F$ of characteristic $p$: the code spanned over $F$ by $\ker A\times\{0\}$, with the targets of Lemma 3.11 read in $F$.
--   5. **The lattice and radius of a linear system** (`LinearSystemFamily.latticeFamily`, `latticeRadius`). For a norm exponent $p$: the Construction A lattice $\Lambda_A$ of the padded code if $p\le2$, and its blockwise Walsh–Hadamard transform $\Lambda_H$ if $p>2$ or $p=\infty$, with their targets. The radius is $\lceil D^{1/p}\rceil$ for $p\le2$, $\lceil(2^{k}D)^{1/p}\rceil$ for $2<p<\infty$, and $1$ for $p=\infty$, where $D$ is the number of blocks and $2^{k}$ the padded block size.
--   6. **Tables** (`QuadraticVerifier.Tables`). Let $V$ be a quadratic verifier over $\mathbb F_p$ with instance length $n$, $S$ assignment coordinates, $N$ evaluation tables and language $L(V)\subseteq\{0,1\}^n$. For a gap exponent $\delta<1$ put $m=\lceil\delta/(1-\delta)\rceil+1$ (`momentAxes`) and $g=(S+1)^{k}$ with $k$ = `gapExp p δ`. **Tables** for $V$ and $\delta$ consist of an integer $B\ge2$ with $8Ng\le B^{m}\le2^{m}\cdot8Ng$ and an explicit moment representation in the sense of Theorem A.8 with $m$ axes and representation bound $r=B^{m}$. They do not depend on the instance.
--   7. **The fixed linear system, code and lattice of the tables** (`Tables.system`, `Tables.codeFamily`, `Tables.latticeFamily`, `Tables.latticeRadius`). The system is $Av=b_x$ of Construction 4.5 for the tables. The code family, the lattice family and the radius are those of items 4 and 5 for this system.
--
--   Theorem 5.1 is then the statement that `Tables.codeFamily` and `Tables.latticeFamily` have the gap for the language of the verifier.
--
--   **Formalization Note.** `HasGap` has the same content as the fields of `CodeGap` and `LatticeGap`, but as a property of a given family instead of an existence statement. The existence form of this statement only asserts that some code or lattice with targets has the gap. Since the Lean statement does not require the targets to be computable, that form is satisfied by a construction unrelated to the paper, in which the target records whether $x$ is in the language. Here the code, the lattice and the targets are the ones the paper constructs. Polynomial-time computability of the code, the lattice and the targets is not formalized. The target uses a solution of $Av=b_x$ picked by classical choice, where the paper uses Gaussian elimination; the distance from the target to the code does not depend on the solution. The case distinction on $p\le2$ uses the classical decidability of the order on the reals.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 5.1 (\label{thm:approximation-hardness}) and its proof, with Construction 4.5 (\label{con:fixed-verifier}), Lemma 3.11 (\label{lem:block-system-codes}), Lemma 3.12 (\label{lem:block-system-lattices}), Theorem 4.8 (\label{thm:quantitative-affine-gap}) and Theorem A.8 (\label{thm:moment-representation-construction}); Lean: LatticePrepro/Explicit.lean, LatticePrepro.CodeFamily.HasGap, LatticePrepro.LatticeFamily.HasGap, LatticePrepro.CodeFamily.comap, LatticePrepro.LatticeFamily.comap, LatticePrepro.LinearSystemFamily.codeFamily, LatticePrepro.LinearSystemFamily.latticeFamily, LatticePrepro.LinearSystemFamily.latticeRadius, LatticePrepro.QuadraticVerifier.Tables, LatticePrepro.QuadraticVerifier.Tables.system, LatticePrepro.QuadraticVerifier.Tables.codeFamily, LatticePrepro.QuadraticVerifier.Tables.latticeFamily, LatticePrepro.QuadraticVerifier.Tables.latticeRadius

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT_Ext

/-!
# Theorem 5.1 for the paper's construction

The statements of `Main.lean` and `ThreeSAT.lean` assert that *some* fixed code or lattice with
targets has the gap of Theorem 5.1 (`Nonempty (CodeGap …)`, `Nonempty (LatticeGap …)`). The
paper's theorem also requires the code and the map `x ↦ t_x` to be computable in polynomial time.
That requirement is not expressed in Lean, and without it the existence statements say very
little: the target `t_x` is an arbitrary function of the instance, so one can take a code with
two coordinates and let the target record whether `x` is in the language.

This file states Theorem 5.1 for the code and the lattice that the paper constructs, so that
nothing is left to choose except data that does not depend on the instance.

* `QuadraticVerifier.Tables V δ` is that data for a verifier `V` and a gap exponent `δ`: a base
  `B` in the range of the proof of Theorem 4.8 and an explicit moment representation
  (Theorem A.8) with `momentAxes δ` axes and representation bound `B ^ momentAxes δ`.
* `Tables.system` is the fixed linear system `A v = b_x` of Construction 4.5 for these tables.
  The instance enters only through the right-hand side `b_x`, whose nonzero entries are the
  powers `θ_x^k` of the instance encoding.
* `Tables.codeFamily` is the code `ker A × {0}` with the targets of Lemma 3.11, extended to a
  field `F`, and `Tables.latticeFamily`, `Tables.latticeRadius` are the lattice, targets and
  radius of Lemma 3.12 (`LinearSystemFamily.latticeFamily`, `LinearSystemFamily.latticeRadius`).
* `CodeFamily.HasGap` and `LatticeFamily.HasGap` are the conclusions of Theorem 5.1 for a given
  family and radius.

The main statements are `Tables.codeFamily_hasGap` and `Tables.latticeFamily_hasGap` (the gap
holds for every choice of tables), `Tables.nonempty` (tables exist), and their instantiation
with the 3SAT verifier, `ThreeSAT.explicit_code_and_lattice_gaps`.

The targets are still not shown to be computable in polynomial time: `LinearSystemFamily.codeTarget`
picks a solution of `A v = b_x` by classical choice, where the paper uses Gaussian elimination.
The distance from the target to the code does not depend on which solution is picked.
-/

namespace LatticePrepro

/-! ### The conclusion of Theorem 5.1 for a given code or lattice -/

/-- The conclusion of Theorem 5.1 for a given code family `𝒞` and radius `R`: the block length
`M` satisfies `1 ≤ M ≤ n^C`, the radius is at least `1`, instances in `Lang` have
`dist(t_x, 𝒞) ≤ R`, and all other instances have `dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
structure CodeFamily.HasGap {F : Type} [Field F] [DecidableEq F] {X : Type} (𝒞 : CodeFamily F X)
    (R : ℕ) (ε : ℝ) (Lang : Set X) (n C : ℕ) : Prop where
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card 𝒞.M
  card_le : Fintype.card 𝒞.M ≤ n ^ C
  yes : ∀ x ∈ Lang, CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ R
  no : ∀ x ∉ Lang,
    (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * R < CodeFamily.codeDist (𝒞.target x) 𝒞.code

/-- The conclusion of Theorem 5.1 for a given lattice family `Λ`, norm exponent `pn` and radius
`R`: the dimension `M` satisfies `1 ≤ M ≤ n^C`, the radius is at least `1`, the lattice contains
`N · ℤ^M` for some `N > 0` (full rank), instances in `Lang` have `dist_p(t_x, Λ) ≤ R`, and all
other instances have `dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
structure LatticeFamily.HasGap {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (R : ℕ) (ε : ℝ)
    (Lang : Set X) (n C : ℕ) : Prop where
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card Λ.M
  card_le : Fintype.card Λ.M ≤ n ^ C
  full_rank : ∃ N : ℕ, 0 < N ∧ ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  yes : ∀ x ∈ Lang, Λ.latticeDist pn x ≤ R
  no : ∀ x ∉ Lang, (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * R < Λ.latticeDist pn x

/-- The same code, with the targets read along a map of instances. -/
def CodeFamily.comap {F : Type} [Field F] {X Y : Type} (𝒞 : CodeFamily F X) (f : Y → X) :
    CodeFamily F Y where
  M := 𝒞.M
  code := 𝒞.code
  target := fun y => 𝒞.target (f y)

/-- The same lattice, with the targets read along a map of instances. -/
def LatticeFamily.comap {X Y : Type} (Λ : LatticeFamily X) (f : Y → X) : LatticeFamily Y where
  M := Λ.M
  lattice := Λ.lattice
  target := fun y => Λ.target (f y)

/-! ### The code of Lemma 3.11, and the lattice and the radius of Lemma 3.12 -/

namespace LinearSystemFamily

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The code family of Lemma 3.11 over a field `F` of characteristic `p`: the code `ker A × {0}`
of the linear system, with the target `(v_x, 0)` for a solution `v_x` of `A v = b_x` if there is
one and `(0, 1)` otherwise, extended to `F`. -/
noncomputable def codeFamily (F : Type) [Field F] [Algebra (ZMod p) F] : CodeFamily F X :=
  CodeFamily.extend F L.toCodeFamily

/-- The lattice family of Lemma 3.12 for the norm exponent `pn`: Construction A on the padded
code for `p ≤ 2`, and its blockwise Walsh–Hadamard transform for `p > 2` and `p = ∞`. -/
noncomputable def latticeFamily : PNorm → LatticeFamily X
  | .fin q _ => if q ≤ 2 then L.latticeA else L.latticeH
  | .inf => L.latticeH

/-- The radius of Lemma 3.12 for the norm exponent `pn`, with `D` blocks and padded block size
`2^k`: `⌈D^{1/p}⌉` for `p ≤ 2`, `⌈(2^k · D)^{1/p}⌉` for `2 < p < ∞`, and `1` for `p = ∞`. -/
noncomputable def latticeRadius : PNorm → ℕ
  | .fin q _ =>
      if q ≤ 2 then ⌈(L.numBlocks : ℝ) ^ (1 / q)⌉₊
      else ⌈((2 ^ L.padK : ℝ) * L.numBlocks) ^ (1 / q)⌉₊
  | .inf => 1

end LinearSystemFamily

/-! ### The tables, and the code and lattice built from them -/

namespace QuadraticVerifier

variable {p : ℕ} [hp : Fact p.Prime]

/-- The data of the construction of Theorem 5.1 that does not depend on the instance, for a
verifier `V` with `S` assignment coordinates and `N` evaluation tables, and a gap exponent `δ`.
With `m = momentAxes δ` and the gap `g = (S + 1)^{gapExp p δ}`, it consists of a base `B ≥ 2`
with `8 N g ≤ B^m ≤ 2^m · 8 N g` (the choice in the proof of Theorem 4.8) and an explicit moment
representation with `m` axes and representation bound `B^m` (Theorem A.8). -/
structure Tables (V : QuadraticVerifier p) (δ : ℝ) where
  /-- The base. -/
  B : ℕ
  two_le_B : 2 ≤ B
  le_pow : 8 * Fintype.card V.TblIdx * (V.S + 1) ^ gapExp p δ ≤ B ^ momentAxes δ
  pow_le : B ^ momentAxes δ ≤
    2 ^ momentAxes δ * (8 * Fintype.card V.TblIdx * (V.S + 1) ^ gapExp p δ)
  /-- The explicit moment representation. -/
  E : ExplicitMomentRepresentation p V.S (momentAxes δ) B

namespace Tables

variable {V : QuadraticVerifier p} {δ : ℝ}

/-- The fixed linear system `A v = b_x` of Construction 4.5 for the tables `T`. The map `A` does
not depend on the instance `x`, and the right-hand side `b_x` is zero except for the powers
`θ_x^k` of the instance encoding in the translation equations. -/
noncomputable def system (T : V.Tables δ) : LinearSystemFamily (ZMod p) (Fin V.n → Bool) :=
  fixedSystem V T.E.R T.E.ε

/-- The code family of Theorem 5.1 for the tables `T` over a field `F` of characteristic `p`:
the code and the targets of Lemma 3.11 for the fixed linear system, extended to `F`. -/
noncomputable def codeFamily (T : V.Tables δ) (F : Type) [Field F] [Algebra (ZMod p) F] :
    CodeFamily F (Fin V.n → Bool) :=
  T.system.codeFamily F

/-- The lattice family of Theorem 5.1 for the tables `T` and the norm exponent `pn`: the lattice
and the targets of Lemma 3.12 for the fixed linear system. -/
noncomputable def latticeFamily (T : V.Tables δ) (pn : PNorm) : LatticeFamily (Fin V.n → Bool) :=
  T.system.latticeFamily pn

/-- The radius of Theorem 5.1 for lattices: the radius of Lemma 3.12 for the fixed linear
system. -/
noncomputable def latticeRadius (T : V.Tables δ) (pn : PNorm) : ℕ := T.system.latticeRadius pn

end Tables

end QuadraticVerifier

/-! ### Theorem 5.1 for 3SAT, for the paper's construction -/

end LatticePrepro


