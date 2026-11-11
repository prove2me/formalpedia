-- Prove2me | Definitions.Def_QNatProofs_KeyedFam
-- name    : QNatProofs_KeyedFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:50.059724+00:00
-- url     : https://prove2.me/theorems/d49a8944-3346-4452-a290-1668cac52c3a
-- title:
--   Keyed function families, classical subexponential security, and the derived family of Fact 3.2
-- statement:
--   A **keyed function family** $\mathcal G=\{G_{m,k}:\{0,1\}^m\to\{0,1\}^m\}_{m\in\mathbb N,k\in\mathcal K_m}$ has a nonempty finite key set $\mathcal K_m$ for each $m$, with keys drawn uniformly.
--
--   $\mathcal G$ is **classically subexponentially secure** (Definition 3.2) if there is $a\in(0,1)$ such that every classical oracle algorithm $B$ satisfies, for all sufficiently large $m$: if $B$ runs in time at most $2^{m^a}$ then
--   $$
--   \Big|\Pr_{k\leftarrow\mathcal K_m}[B^{G_{m,k}}=1]-\Pr_{U_m}[B^{U_m}=1]\Big|\le 2^{-m^a},\tag{24}
--   $$
--   where $U_m:\{0,1\}^m\to\{0,1\}^m$ is a uniformly random function. The input of $B$ is $1^m$ followed by any auxiliary string of length at most $m$.
--
--   The **derived family of Fact 3.2** is
--   $$
--   F_{n,\lambda,k}(x):=G_{m,k}(0^{m-n}x)_{1,\dots,R},\qquad m=(n+R+\lambda)^{\lceil 1/a\rceil+1},
--   $$
--   for $x\in\{0,1\}^n$ and $k\in\mathcal K_m$.
--
--   This is the cryptographic assumption of the main theorem and the PRF used to build the PRAL family.
--
--   **Formalization Note** The two efficiency clauses of Definition 3.2 (keys sampled and functions evaluated in time $\mathrm{poly}(m)$) are not part of the structure; no statement of the mission uses them. "For all sufficiently large $m$" may depend on the algorithm $B$.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 3.2, (24), p.16; Fact 3.2, p.16

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QNatProofs_OracleAlg

set_option autoImplicit false

namespace QNatProofs

open Filter

/-- A **keyed function family** `𝒢 = {G_{m,k} : {0,1}^m → {0,1}^m}_{m ∈ ℕ, k ∈ 𝒦_m}` (Li, Parham,
arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 3.2, p.16), with a nonempty finite key
set `𝒦_m` for each `m`; keys are drawn uniformly.

**Formalization Note** The efficiency clauses of Definition 3.2 (uniform keys sampled and the
functions evaluated in time `poly(m)`) are not part of this structure; no statement of the mission
uses them. -/
structure KeyedFam where
  /-- The key set `𝒦_m`. -/
  K : ℕ → Type
  /-- Each key set is finite. -/
  [fintypeK : ∀ m, Fintype (K m)]
  /-- Each key set is nonempty. -/
  [nonemptyK : ∀ m, Nonempty (K m)]
  /-- The functions `G_{m,k}`. -/
  G : (m : ℕ) → K m → (Fin m → Bool) → (Fin m → Bool)

attribute [instance] KeyedFam.fintypeK KeyedFam.nonemptyK

/-- **Classical subexponential security with exponent `a`** (Li, Parham, arXiv:2610.06826 (held copy
sha256 b604fa11…), Definition 3.2, (24), p.16): every classical oracle algorithm `B`, for all
sufficiently large `m`, if it runs in time at most `2^{m^a}` then
`|Pr_{k←𝒦_m}[B^{G_{m,k}} = 1] − Pr_{U_m}[B^{U_m} = 1]| ≤ 2^{-m^a}`, with `U_m` a uniformly random
function `{0,1}^m → {0,1}^m`.

**Formalization Note** `B` is a uniform oracle algorithm (`OracleAlg`); its input is `1^m`
followed by any auxiliary string `z` of length at most `m`, and the bound must hold for every such
`z`. The threshold for "sufficiently large `m`" may depend on `B` (∀ B, ∀ᶠ m). The running time is
bounded against every oracle `{0,1}^m → {0,1}^m` (`OracleAlg.TimeBounded m m`). -/
def KeyedFam.IsSecureWithExp (G : KeyedFam) (a : ℝ) : Prop :=
  ∀ B : OracleAlg, ∀ᶠ m in atTop, ∀ z : List Bool, z.length ≤ m →
    B.TimeBounded m m (QAlgorithms.Complexity.encNat m ++ z) ((2 : ℝ) ^ ((m : ℝ) ^ a)) →
      oracleAdv B (QAlgorithms.Complexity.encNat m ++ z) (G.G m) ≤ (2 : ℝ) ^ (-((m : ℝ) ^ a))

/-- **Classically subexponentially secure PRF family** (Definition 3.2, p.16): secure with some
exponent `a ∈ (0, 1)`. -/
def KeyedFam.IsClassicalSubexpSecure (G : KeyedFam) : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1 ∧ G.IsSecureWithExp a

/-- The PRF input length `m = (n + R + λ)^{⌈1/a⌉ + 1}` of Fact 3.2 (p.16). -/
noncomputable def prfLen (a : ℝ) (n R lam : ℕ) : ℕ :=
  (n + R + lam) ^ (⌈1 / a⌉₊ + 1)

/-- **The derived family of Fact 3.2** (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…),
p.16): `F_{n,λ,k}(x) := G_{m,k}(0^{m−n} x)_{1,…,R}` with `m = (n + R + λ)^{⌈1/a⌉+1}`, for
`x ∈ {0,1}ⁿ` and `k ∈ 𝒦_m`.

**Formalization Note** The padded input `0^{m−n}x` has bit `i` equal to `x_{i−(m−n)}` for
`i ≥ m − n` and `0` otherwise; output bit `j < R` is bit `j` of `G_{m,k}(0^{m−n}x)`. Both index
conditions always hold because `n, R ≤ m` (`m ≥ n + R + λ ≥ max(n, R)` when `n + R + λ ≥ 1`; for
`n = R = 0` there is nothing to read). -/
def prfTape (G : KeyedFam) (m n R : ℕ) (k : G.K m) (x : Fin n → Bool) : Fin R → Bool :=
  fun j =>
    if hj : j.val < m then
      G.G m k (fun i => if h : m - n ≤ i.val then x ⟨i.val - (m - n), by omega⟩ else false)
        ⟨j.val, hj⟩
    else false

end QNatProofs


