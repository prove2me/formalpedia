-- Prove2me | Definitions.Def_NNPartTree_Supplement_CutInstance
-- name    : NNPartTree_Supplement_CutInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:10:10.447673+00:00
-- url     : https://prove2.me/theorems/6028dba2-b136-48b7-9913-e49bc13c35f0
-- title:
--   Rational instances of the balanced halfspace cut problem, their law, encoding, and the Yes/No cases of Theorem 2
-- statement:
--   An **instance** of the balanced halfspace cut problem of Theorem 2 consists of a dimension $d \in \mathbb{N}$, a number $m \in \mathbb{N}$ of pairs, and pairs $(x_1, y_1), \dots, (x_m, y_m) \in \mathbb{Q}^d \times \mathbb{Q}^d$, listed with repetitions allowed. Its **law** $\mathcal{D}$ is the uniform distribution over the multiset $\{(x_i, y_i)\}_{i=1}^m$, viewed in $\mathbb{R}^d \times \mathbb{R}^d$: each listed pair carries mass $1/m$.
--
--   The **encoding** of an instance is a binary string: $d$ and $m$ in self-delimiting binary, then, for $i = 1, \dots, m$, the $d$ coordinates of $x_i$ followed by the $d$ coordinates of $y_i$, each written as the sign and binary absolute value of its reduced numerator followed by its binary denominator.
--
--   With $\mathrm{err}_{\mathcal D}$, $\mathrm{bal}_{\mathcal D}$ and the class $\mathcal{P}_1$ of halfspaces $f(x) = \mathrm{sign}(\langle h, x\rangle - \theta)$ (convention $\mathrm{sign}(0) = 1$) of the base mission, the two cases of Theorem 2 are:
--
--   1. **Yes**: $m \ge 1$ and some $f \in \mathcal{P}_1$ has $\mathrm{bal}_{\mathcal D}(f) = 1/2$ and $\mathrm{err}_{\mathcal D}(f) = 0$;
--   2. **No$_{c,\beta}$**: $m \ge 1$ and every $f \in \mathcal{P}_1$ with $\mathrm{bal}_{\mathcal D}(f) \ge \beta$ has $\mathrm{err}_{\mathcal D}(f) \ge c\beta$.
--
--   These objects pose the distinguishing problem whose NP-hardness is Theorem 2.
--
--   **Formalization Note** The page speaks of pairs in $\mathbb{R}^d \times \mathbb{R}^d$. A polynomial-time reduction outputs finite strings, so the instances are rational; every rational instance is an instance of the printed problem. The guard $m \ge 1$ excludes only the empty list, on which the uniform distribution is undefined (the Lean law would be the zero measure). The rational encoders `encBin`/`encRat` are the published `QAlgorithms_ClassicalRationalEncoding`.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Theorem 2, p.11 (PDF p.11); Definition 3.1, p.10 (PDF p.10)

import Mathlib
import Definitions.Def_NNPartTree_Moments
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

set_option autoImplicit false

namespace NNPartTree.Supplement

open MeasureTheory QAlgorithms.LocalHamiltonian

/-- **Rational instances of the balanced halfspace cut problem** (Theorem 2, p.11, PDF p.11).
S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Theorem 2, p.11.

An instance consists of a dimension `d`, a number `m` of pairs, and the pairs
`(x₁, y₁), …, (x_m, y_m)` in `ℚᵈ × ℚᵈ`, listed with repetitions allowed.

**Formalization Note** The page says "given pairs in `ℝᵈ × ℝᵈ`". A Karp reduction outputs finite
strings, so the inputs of the decision problem are rational; every rational instance is an instance of
the printed problem. `d` and `m` are part of the instance and are unbounded. -/
structure CutInstance where
  /-- The dimension `d`. -/
  d : ℕ
  /-- The number `m` of pairs. -/
  m : ℕ
  /-- The pairs `(xᵢ, yᵢ)`, `i = 1, …, m`, with multiplicity. -/
  pts : Fin m → (Fin d → ℚ) × (Fin d → ℚ)

namespace CutInstance

/-- A rational vector as a point of `ℝᵈ = EuclideanSpace ℝ (Fin d)`. -/
noncomputable def toPt {d : ℕ} (v : Fin d → ℚ) : Pt d := WithLp.toLp 2 (fun i => (v i : ℝ))

/-- The law `D` of an instance: the uniform distribution over the multiset `{(xᵢ, yᵢ)}`, i.e. the
base `empirical` law of the list of pairs (each listed pair has mass `1/m`). -/
noncomputable def law (I : CutInstance) : Measure (Pt I.d × Pt I.d) :=
  empirical (fun i => (toPt (I.pts i).1, toPt (I.pts i).2))

/-- The binary encoding of an instance: `d` and `m` in self-delimiting binary (`encBin`), then for
`i = 1, …, m` the coordinates of `xᵢ` followed by those of `yᵢ`, each as a rational (`encRat`: sign
bit and binary absolute value of the reduced numerator, then the binary denominator). Its length is
linear in the bit size of the instance. -/
def enc (I : CutInstance) : List Bool :=
  encBin I.d ++ encBin I.m ++
    (List.finRange I.m).flatMap fun i =>
      (List.finRange I.d).flatMap (fun j => encRat ((I.pts i).1 j)) ++
        (List.finRange I.d).flatMap (fun j => encRat ((I.pts i).2 j))

/-- The **Yes** case of Theorem 2: `m ≥ 1` and some halfspace `f ∈ P₁` has `bal_D(f) = 1/2` and
`err_D(f) = 0`. -/
def Yes (I : CutInstance) : Prop :=
  1 ≤ I.m ∧ ∃ f : Pt I.d → ℝ, IsHalfspace f ∧ bal I.law f = 1 / 2 ∧ err I.law f = 0

/-- The **No** case of Theorem 2 with constant `c` and balance target `β`: `m ≥ 1` and every
halfspace `f ∈ P₁` with `bal_D(f) ≥ β` has `err_D(f) ≥ c β`. -/
def No (c β : ℝ) (I : CutInstance) : Prop :=
  1 ≤ I.m ∧ ∀ f : Pt I.d → ℝ, IsHalfspace f → β ≤ bal I.law f → c * β ≤ err I.law f

end CutInstance

end NNPartTree.Supplement


