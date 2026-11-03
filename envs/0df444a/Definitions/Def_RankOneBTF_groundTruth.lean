-- Prove2me | Definitions.Def_RankOneBTF_groundTruth
-- name    : RankOneBTF_groundTruth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:18.210379+00:00
-- url     : https://prove2.me/theorems/dfe871e8-b2fa-4201-a3cd-9f6317d5506e
-- title:
--   Binary tensors, the planted rank-one tensor $\bar W=\bar x\otimes\bar y\otimes\bar z$ and the uncorrupted entries $\mathcal T$
-- statement:
--   A **binary tensor** of size $n\times m\times l$ is an array $\mathcal G=(g_{ijk})\in\{0,1\}^{n\times m\times l}$, indexed by $i\in[n]$, $j\in[m]$, $k\in[l]$.
--
--   Given binary vectors $\bar x\in\{0,1\}^n$, $\bar y\in\{0,1\}^m$, $\bar z\in\{0,1\}^l$, the **ground truth rank-one tensor** is
--   $$
--   \bar{\mathcal W}=(\bar w_{ijk}):=\bar x\otimes\bar y\otimes\bar z,\qquad \bar w_{ijk}=\bar x_i\bar y_j\bar z_k .
--   $$
--   Relative to an input tensor $\mathcal G$, the **uncorrupted entries** form the set
--   $$
--   \mathcal T:=\{(i,j,k): g_{ijk}=\bar x_i\bar y_j\bar z_k\},
--   $$
--   and its complement $\mathcal F:=\{(i,j,k): g_{ijk}=1-\bar x_i\bar y_j\bar z_k\}$ is the set of corrupted entries. The sets $\mathcal P=\{\bar x_i=\bar y_j=\bar z_k=1\}$ and $\mathcal N$ (its complement) are written directly as conditions on $\bar x,\bar y,\bar z$. Finally $n_{\bar x}=|\{i:\bar x_i=1\}|$ denotes the number of ones of $\bar x$ (likewise $n_{\bar y}$, $n_{\bar z}$); the ratio of ones is $r_{\bar x}=n_{\bar x}/n$.
--
--   These are the basic objects of the whole mission: every LP, count and probability is built from them.
--
--   **Formalization Note** Binary entries are Booleans (`true` = 1, `false` = 0) and $[n]$ is `Fin n`, so the paper's index $i$ is the Lean index $i-1$. The count $n_{\bar x}$ is returned as a real number.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, pp.2–3 (binary tensor G, ground truth W̄ = x̄ ⊗ ȳ ⊗ z̄), p.5 (sets P, N, T, F), p.20 (n_x̄, n_ȳ, n_z̄)

import Mathlib

namespace RankOneBTF

/-- A binary `n × m × l` tensor, `G = (g_ijk) ∈ {0,1}^{n×m×l}` (Del Pia, Khajavirad,
*Rank-one Boolean tensor factorization and the multilinear polytope*, arXiv:2202.07053v3, §1,
p.2).

**Formalization Note** `true` encodes the entry `1` and `false` the entry `0`. The paper's
index sets `[n], [m], [l]` are `Fin n, Fin m, Fin l` (paper index `i` = Lean index `i − 1`). -/
abbrev BTensor (n m l : ℕ) : Type := Fin n → Fin m → Fin l → Bool

/-- The **ground truth rank-one tensor** `W̄ = (w̄_ijk) := x̄ ⊗ ȳ ⊗ z̄ ∈ {0,1}^{n×m×l}`, i.e.
`w̄_ijk = x̄_i ȳ_j z̄_k`, of binary vectors `x̄ ∈ {0,1}ⁿ, ȳ ∈ {0,1}ᵐ, z̄ ∈ {0,1}ˡ`
(arXiv:2202.07053v3, §1, p.3).

**Formalization Note** Binary vectors are `Bool`-valued; the product of `{0,1}` entries is the
Boolean conjunction. -/
def groundTruth {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) :
    BTensor n m l :=
  fun i j k => xb i && yb j && zb k

/-- Membership in the set `𝒯 := {(i,j,k) : g_ijk = x̄_i ȳ_j z̄_k}` of **uncorrupted** entries of
an input tensor `G` relative to the ground truth (arXiv:2202.07053v3, §2.2, p.5). Its
complement is `ℱ := {(i,j,k) : g_ijk = 1 − x̄_i ȳ_j z̄_k}`, the corrupted entries.

The sets `𝒫 = {x̄_i = ȳ_j = z̄_k = 1}` and `𝒩 = {x̄_i = 0 ∨ ȳ_j = 0 ∨ z̄_k = 0}` of p.5 are
written directly as conditions on `x̄, ȳ, z̄` wherever they are used. -/
def IsT {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) : Prop :=
  G i j k = groundTruth xb yb zb i j k

instance {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (i : Fin n) (j : Fin m) (k : Fin l) :
    Decidable (IsT xb yb zb G i j k) :=
  inferInstanceAs (Decidable (G i j k = _))

/-- The number of ones of a binary vector, e.g. `n_x̄ = |{i : x̄_i = 1}|` (arXiv:2202.07053v3,
p.20: "we denote by n_x̄, n_ȳ, and n_z̄ the number of ones in binary vectors x̄, ȳ, z̄"); the
ratio `r_x̄` of p.3 is `n_x̄ / n`.

**Formalization Note** Returned as a real number, since it enters real formulas. -/
def numOnes {n : ℕ} (v : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter fun i => v i = true).card : ℝ)

end RankOneBTF


