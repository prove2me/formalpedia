-- Prove2me | Definitions.Def_DetANN_TupleFamily
-- name    : DetANN_TupleFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:40.760503+00:00
-- url     : https://prove2.me/theorems/779c8791-32cf-4843-8989-64fc269808ee
-- title:
--   Tuple families, superblocks, local guarantees, and the averages of §5 and §7
-- statement:
--   Throughout, a **tuple family** is a map $S:\mathcal V\times\mathcal O\to[d]$ on finite nonempty sets $\mathcal V$ (tuples) and $\mathcal O$ (occurrences) with **uniform block frequencies**: every block $i\in[d]$ occurs $|\mathcal V||\mathcal O|/d$ times among the pairs $(v,o)$. Choose $(V,O)$ uniformly and put $I=S(V,O)$. For answers $x_v\in P$ and a point $x^\star\in P$ write $a_i=\mathbb E[x_V-x^\star\mid I=i]$, $a=\mathbb E[x_V-x^\star]$, $\mathcal V=\mathbb E\|x_V-x^\star-a_I\|_2^2$, $r=\|q-x^\star\|_2$, and $\|\mathcal A_vz\|_2^2=\sum_{o}\|A_{S(v,o)}z\|_2^2$ for the superblock of $v$ (repeated blocks counted with multiplicity). The **local guarantee** with factor $\alpha$ is $\|\mathcal A_v(q-x_v)\|_2\le\alpha\min_{y\in P}\|\mathcal A_v(q-y)\|_2$ for every $v$.
--
--   The definitions provide: the block counts $\#\{(v,o):S(v,o)=i\}$ and the uniform-frequency predicate; the superblock squared norm; the local guarantee; the conditional means $a_i$, the mean $a$, the within-block variance $\mathcal V$ and the between-block variance $\mathbb E_I\|a_I-a\|_2^2$.
--
--   The exhaustive family of §5 is $\mathcal V=[d]^s$, $\mathcal O=[s]$, $S(\omega,j)=\omega_j$; the walk family of §7 is $\mathcal V=[d]$, $\mathcal O$ the walks of length $\ell$, $S(v,w)$ the endpoint of $w$ from $v$. Stating the §5 and §7.3 estimates once for a general family covers both.
--
--   **Formalization Note** Expectations are finite uniform averages. The local guarantee is stated squared, $\|\mathcal A_v(q-x_v)\|_2^2\le\alpha^2\|\mathcal A_v(q-y)\|_2^2$ for all $y\in P$, which is equivalent for $\alpha\ge0$.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §4.1, p.8 (superblocks, (11)); §5, pp.9–13; §7.1–7.3, pp.17–18 ((25), the definitions of a_i, a, 𝒱)

import Mathlib

namespace DetANN

/-!
# Families of block tuples, superblocks, local guarantees, and the averages of §5 and §7

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §4.1 (p.8), §5 (pp.9–13), §7.1–7.3 (pp.17–18).

A tuple family is `S : Vtx → Occ → Fin d`: tuple `v` lists the blocks `S v o`, one per occurrence
`o`, with repetitions. The exhaustive family of §4 is `Vtx = [d]^s`, `Occ = [s]`, `S ω j = ω_j`; the
walk family of §7 is `Vtx = [d]`, `Occ` = walks of length `ℓ`, `S v w` = endpoint of `w` from `v`.

The paper's random choices are `V` uniform on `Vtx` and a uniformly random occurrence `O`, with
`I = S V O` the selected block (§5, p.9; §7.2, p.17). Every expectation below is the corresponding
finite average over `(V, O)` uniform on `Vtx × Occ`; a conditional expectation given `I = i` is the
average over the pairs with `S v o = i`.

**Formalization Note.**
* `UniformFreq S` is the paper's "uniform block frequencies": every block occurs equally often in the
  collection of tuples, so `I` is uniform on `[d]`.
* The superblock `𝒜_v z` is the concatenation of the `A_{S v o} z` over all occurrences, repeated
  blocks retained with multiplicity (p.8); only its squared norm `∑_o ‖A_{S v o} z‖²` is used.
* The local guarantee (11)/(25), `‖𝒜_v(q − x_v)‖ ≤ α min_{y ∈ P} ‖𝒜_v(q − y)‖`, is stated squared:
  `‖𝒜_v(q − x_v)‖² ≤ α² ‖𝒜_v(q − y)‖²` for all `y ∈ P`. For `α ≥ 0` and finite nonempty `P` the two
  forms are equivalent (both sides are nonnegative).
* A count that is `0` would make a conditional mean `0⁻¹ • 0 = 0`; the theorems assume uniform
  frequencies and nonempty `Vtx`, `Occ`, which make every count positive.
-/

variable {d : ℕ} {Vtx Occ : Type} [Fintype Vtx] [Fintype Occ]

/-- The number of occurrences of block `i` in the collection of tuples, `#{(v, o) : S v o = i}`. -/
def blockCount (S : Vtx → Occ → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun p : Vtx × Occ => S p.1 p.2 = i).card

/-- Uniform block frequencies: every block occurs `|Vtx|·|Occ|/d` times. -/
def UniformFreq (S : Vtx → Occ → Fin d) : Prop :=
  ∀ i : Fin d, blockCount S i * d = Fintype.card Vtx * Fintype.card Occ

/-- The squared norm of the superblock projection, `‖𝒜_v z‖² = ∑_o ‖A_{S v o} z‖²`. -/
noncomputable def superNormSq {b : ℕ}
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (S : Vtx → Occ → Fin d) (v : Vtx) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ o, ‖A (S v o) z‖ ^ 2

/-- The local approximation guarantee (11)/(25) with factor `α`, squared: for every tuple `v` and
every `y ∈ P`, `‖𝒜_v(q − x_v)‖² ≤ α² ‖𝒜_v(q − y)‖²`. -/
def LocalGuarantee {b : ℕ}
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (S : Vtx → Occ → Fin d) (P : Finset (EuclideanSpace ℝ (Fin d)))
    (q : EuclideanSpace ℝ (Fin d)) (x : Vtx → EuclideanSpace ℝ (Fin d)) (α : ℝ) : Prop :=
  ∀ v : Vtx, ∀ y ∈ P, superNormSq A S v (q - x v) ≤ α ^ 2 * superNormSq A S v (q - y)

/-- The conditional mean `a_i = E[x_V − x⋆ | I = i]`. -/
noncomputable def condMean (S : Vtx → Occ → Fin d) (x : Vtx → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  (blockCount S i : ℝ)⁻¹ •
    ∑ p ∈ Finset.univ.filter (fun p : Vtx × Occ => S p.1 p.2 = i), (x p.1 - xs)

/-- The unconditional mean `a = E[x_V − x⋆]`. -/
noncomputable def mean (x : Vtx → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (Fintype.card Vtx : ℝ)⁻¹ • ∑ v, (x v - xs)

/-- The within-block variance `𝒱 = E_{V,I} ‖x_V − x⋆ − a_I‖²`. -/
noncomputable def withinVar (S : Vtx → Occ → Fin d) (x : Vtx → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ)⁻¹ *
    ∑ p : Vtx × Occ, ‖x p.1 - xs - condMean S x xs (S p.1 p.2)‖ ^ 2

/-- The between-block variance `E_I ‖a_I − a‖²`. -/
noncomputable def betweenVar (S : Vtx → Occ → Fin d) (x : Vtx → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((Fintype.card Vtx * Fintype.card Occ : ℕ) : ℝ)⁻¹ *
    ∑ p : Vtx × Occ, ‖condMean S x xs (S p.1 p.2) - mean x xs‖ ^ 2

end DetANN


