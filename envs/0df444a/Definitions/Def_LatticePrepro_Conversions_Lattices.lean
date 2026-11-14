-- Prove2me | Definitions.Def_LatticePrepro_Conversions_Lattices
-- name    : LatticePrepro_Conversions_Lattices
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:21:38.275228+00:00
-- url     : https://prove2.me/theorems/d3b66619-8284-45a0-bcc1-522e27b99db5
-- title:
--   $\ell_p$ norms, fixed lattices with integer targets, and the lattice reduction structure (Section 3, Lemma 3.12)
-- statement:
--   These definitions fix the lattice-side notions and package the output of the lattice reduction (Lemma 3.12).
--
--   1. **Norm exponents** (`PNorm`): either a real number $p\ge1$ or $p=\infty$.
--   2. **$\ell_p$ norms** (`PNorm.norm`): for $v\in\mathbb R^M$, $\|v\|_p=\bigl(\sum_i|v_i|^p\bigr)^{1/p}$ for finite $p$, and $\|v\|_\infty=\sup_i|v_i|$.
--   3. **The exponent $s$** (`PNorm.s`): $s=\min\{p,2\}$, with $s=2$ for $p=\infty$.
--   4. **Lattice families** (`LatticeFamily X`): a finite coordinate set $M$, a lattice $\Lambda\subseteq\mathbb Z^M$ given as an additive subgroup ($\mathbb Z$-submodule) of $\mathbb Z^M$ that is the same for every instance, and an integer target $t_x\in\mathbb Z^M$ for every instance $x\in X$.
--   5. **Distances to integer vectors** (`LatticeFamily.toReal`, `LatticeFamily.dist`): integer vectors are read in $\mathbb R^M$, and the distance from the target of $x$ to $v\in\mathbb Z^M$ is $\|t_x-v\|_p$.
--   6. **Lattice reductions** (`LatticeReduction L g pn`). For a prime $\mathsf p$, a linear-system family $L$ over $\mathbb F_{\mathsf p}$ with $n$ columns in $D$ blocks, a gap $g\in\mathbb N$ and a norm exponent $p$: a lattice family $(\Lambda,(t_x))$ on $M$ coordinates, a radius $R\in\mathbb N$, a natural number $N$, and a residual weight $w(x,v)\in\mathbb N$ for each instance $x$ and each $v\in\mathbb Z^M$, such that
--      - $1\le R\le M$ and $2n\le M<4n$;
--      - $N>0$ and $N\cdot\mathbb Z^M\subseteq\Lambda$ (so $\Lambda$ has full rank);
--      - for every YES instance $x$ of $L$, some $v\in\Lambda$ has $\|t_x-v\|_p\le R$;
--      - for every instance $x$ and every $v\in\Lambda$, $w(x,v)\le16\cdot D\cdot\bigl(\|t_x-v\|_p/R\bigr)^{s}$;
--      - for every NO instance $x$ with gap $g$ and every $v\in\Lambda$, $w(x,v)>g\cdot D$.
--
--   The lattice and the radius depend only on $L$; only the targets depend on the instance, as in a preprocessing reduction. The residual weight is the quantity checked by the search test of Lemma 5.2.
--
--   **Formalization Note.** `PNorm` covers every real $p\ge1$ and $p=\infty$; the paper states Lemma 3.12 for rational $p$ and $p=\infty$, which matters only for computability. The sup norm is `⨆ i, |v i|`, and powers with real exponents are `Real.rpow`. The polynomial-time computability of the basis, targets, membership test and residual weight is not formalized: `weight` is an arbitrary function. Full rank is encoded by $N\cdot\mathbb Z^M\subseteq\Lambda$; `Lattices/Mathlib.lean` shows that this makes the real image of $\Lambda$ a Mathlib `IsZLattice`. Lean writes the prime as `p` and the norm exponent as `pn`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Section 3 (Preliminaries, \label{sec:preliminaries}) and Lemma 3.12 (\label{lem:block-system-lattices}); Lean: LatticePrepro/Conversions/Lattices.lean, LatticePrepro.PNorm, LatticePrepro.PNorm.norm, LatticePrepro.PNorm.s, LatticePrepro.LatticeFamily, LatticePrepro.LatticeFamily.toReal, LatticePrepro.LatticeFamily.dist, LatticePrepro.LatticeReduction

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard

/-!
# From codes to lattices (Lemma 3.12, Appendix B.2–B.3)

* `ℓ_p` norms on `M → ℝ` for `1 ≤ p < ∞` and `p = ∞` (`PNorm`).
* Construction A: `Λ_𝒞 = {v ∈ ℤ^M : v mod p ∈ 𝒞}` (Lemma B.1).
* The block Hadamard map (Lemma B.2): for `2 ≤ p ≤ ∞`, multiply lattice and target by a
  block-diagonal matrix of Sylvester–Hadamard matrices.
* The lattice reduction (Lemma 3.12, `LatticeReduction`, `exists_latticeReduction`): a fixed
  lattice `Λ`, an integer radius `R`, targets `t_x` and a residual weight such that YES instances
  have a lattice vector within distance `R` and NO instances have every lattice vector at distance
  more than `(g / 16)^{1/s} · R`, where `s = min {p, 2}`.
-/

namespace LatticePrepro

/-- A norm exponent: a real `p ≥ 1`, or `∞`. -/
inductive PNorm
  | fin (p : ℝ) (hp : 1 ≤ p)
  | inf

namespace PNorm

/-- The `ℓ_p` norm of a real vector. -/
noncomputable def norm {M : Type} [Fintype M] : PNorm → (M → ℝ) → ℝ
  | fin p _ => fun v => (∑ i, |v i| ^ p) ^ (1 / p)
  | inf => fun v => ⨆ i, |v i|

/-- The exponent `s = min {p, 2}` (`s = 2` for `p = ∞`). -/
noncomputable def s : PNorm → ℝ
  | fin p _ => min p 2
  | inf => 2

end PNorm

/-- A fixed lattice `Λ ⊆ ℤ^M` with an integer target for every instance. -/
structure LatticeFamily (X : Type) where
  /-- Coordinates. -/
  M : Type
  [fintypeM : Fintype M]
  [decEqM : DecidableEq M]
  /-- The lattice, as a `ℤ`-submodule of `ℤ^M`. -/
  lattice : Submodule ℤ (M → ℤ)
  /-- The target for instance `x`. -/
  target : X → (M → ℤ)

namespace LatticeFamily

attribute [instance] fintypeM decEqM

variable {X : Type} (Λ : LatticeFamily X)

/-- The real vector of an integer vector. -/
def toReal {M : Type} (v : M → ℤ) : M → ℝ := fun i => (v i : ℝ)

/-- Distance in `ℓ_p` from the target to a lattice vector. -/
noncomputable def dist (pn : PNorm) (x : X) (v : Λ.M → ℤ) : ℝ :=
  pn.norm (toReal (Λ.target x - v))

end LatticeFamily

/-! ### Padding the code to blocks of size a power of two -/

/-! ### Block-sparse binary vectors under the Hadamard map -/

/-! ### Real-number bounds for the radius -/

/-! ### The lattice reduction: statement -/

/-- The output of Lemma 3.12 for a linear system family `L`, a gap `g` and a norm exponent `pn`:
a fixed lattice `Λ ⊆ ℤ^M` with `2 n ≤ M < 4 n` (`n = |ι|`), containing `N · ℤ^M` for some
`N > 0` (full rank), an integer radius `1 ≤ R ≤ M`, and a *residual weight* `w = weight x v`
computable from a lattice vector `v`, such that

* YES instances have a lattice vector within `ℓ_p`-distance `R` of the target;
* `w ≤ 16 · D · (dist / R)^s` for every lattice vector, and `w > g · D` on NO instances.

The residual weight is the quantity tested in Lemma 5.2 (`Conversions/SearchTest.lean`). -/
structure LatticeReduction {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)
    (g : ℕ) (pn : PNorm) where
  /-- The fixed lattice and the targets. -/
  Λ : LatticeFamily X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  R_le_card : R ≤ Fintype.card Λ.M
  two_mul_card_le : 2 * Fintype.card L.ι ≤ Fintype.card Λ.M
  card_lt_four_mul : Fintype.card Λ.M < 4 * Fintype.card L.ι
  /-- The lattice contains `N · ℤ^M`. -/
  N : ℕ
  N_pos : 0 < N
  smul_mem : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  /-- The residual weight of a lattice vector. -/
  weight : X → (Λ.M → ℤ) → ℕ
  yes : ∀ x, L.IsYes x → ∃ v ∈ Λ.lattice, Λ.dist pn x v ≤ R
  weight_le : ∀ x, ∀ v ∈ Λ.lattice,
    (weight x v : ℝ) ≤ 16 * L.numBlocks * (Λ.dist pn x v / R) ^ pn.s
  lt_weight : ∀ x, L.IsNo g x → ∀ v ∈ Λ.lattice, g * L.numBlocks < weight x v

/-! ### The three cases of the lattice reduction -/

end LatticePrepro


