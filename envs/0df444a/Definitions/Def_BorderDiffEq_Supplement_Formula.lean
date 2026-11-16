-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_Formula
-- name    : BorderDiffEq_Supplement_Formula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:48:48.229585+00:00
-- url     : https://prove2.me/theorems/1c34f16f-6019-496d-b684-257fef1ca198
-- title:
--   Arithmetic formulas with unbounded fan-in; depth and size
-- statement:
--   An **arithmetic formula** over a commutative ring $K$ in variables $(x_i)_{i\in\sigma}$ is a rooted tree whose leaves are labelled by variables $x_i$ or constants $c\in K$ and whose internal nodes are **sum gates** and **product gates** of arbitrary fan-in. It computes a polynomial in $K[x]$ in the obvious way. Its **size** is the number of nodes (gates and leaves) and its **depth** is the number of gate layers on a longest root-to-leaf path, so a leaf has depth $0$ and a $\Sigma\Pi\Sigma\Pi\Sigma\Pi$ formula has depth $6$.
--
--   Depth-six formulas are the output model of the debordering theorems for sums of powers of low-degree polynomials (Theorems 2.4 and 6.2) and of the reconstruction algorithm (Theorem 2.7).
--
--   **Formalization Note** A gate of fan-in $m$ stores its children as a function on `Fin m`. `eval`, `size`, `depth` are defined by recursion; `map` replaces the constant leaves through a function (used to instantiate a formula whose constants are register indices). Formulas over $F$ have constants in $F$ and no division gates.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.2.1, p.8 (Theorem 2.4) and §6.2.2, p.50 ("a ΣΠΣΠΣΠ formula for f, that is, a formula of depth six")

import Mathlib

namespace BorderDiffEq.Supplement

/-- **Arithmetic formulas with unbounded fan-in, and their depth and size**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §2.2.1, p.8 (Theorem 2.4, "a formula of
depth six"), and p.50 ("a ΣΠΣΠΣΠ formula for f, that is, a formula of depth six")): a formula is a
tree whose leaves are variables `xᵢ` or constants `c ∈ K`, and whose internal nodes are sum gates
and product gates of arbitrary fan-in.

**Formalization Note.** A gate of fan-in `m` stores its `m` children as a function `Fin m → _`.
`eval` is the polynomial computed, `size` the number of nodes (gates and leaves), `depth` the
number of gate layers on the longest root–leaf path (a leaf has depth `0`; a ΣΠΣΠΣΠ formula has
depth `6`). The constants of a formula over `F` lie in `F`; there are no division gates.
`map` replaces the constant leaves through a function, which is how a formula with symbolic
constants is instantiated. `code` writes a formula as a list of natural numbers (a prefix code:
a tag, then the data of the node, then the codes of its children), given codes of the constants
and of the variables; it is used to state that a formula is computed by an algorithm. -/
inductive Formula (K : Type) (σ : Type) : Type where
  /-- the leaf `xᵢ` -/
  | var : σ → Formula K σ
  /-- the constant leaf `c` -/
  | const : K → Formula K σ
  /-- a sum gate with `m` children -/
  | add : (m : ℕ) → (Fin m → Formula K σ) → Formula K σ
  /-- a product gate with `m` children -/
  | mul : (m : ℕ) → (Fin m → Formula K σ) → Formula K σ

namespace Formula

variable {K L σ : Type}

/-- The polynomial computed by the formula. -/
noncomputable def eval [CommRing K] : Formula K σ → MvPolynomial σ K
  | var i => MvPolynomial.X i
  | const c => MvPolynomial.C c
  | add _ g => ∑ i, eval (g i)
  | mul _ g => ∏ i, eval (g i)

/-- The size: the number of nodes (gates and leaves). -/
def size : Formula K σ → ℕ
  | var _ => 1
  | const _ => 1
  | add _ g => 1 + ∑ i, size (g i)
  | mul _ g => 1 + ∑ i, size (g i)

/-- The depth: the number of gate layers on a longest root–leaf path. -/
def depth : Formula K σ → ℕ
  | var _ => 0
  | const _ => 0
  | add _ g => 1 + Finset.univ.sup fun i => depth (g i)
  | mul _ g => 1 + Finset.univ.sup fun i => depth (g i)

/-- Replace every constant leaf `c` by `φ c` (the tree shape is unchanged). -/
def map (φ : K → L) : Formula K σ → Formula L σ
  | var i => var i
  | const c => const (φ c)
  | add m g => add m fun i => map φ (g i)
  | mul m g => mul m fun i => map φ (g i)

/-- A prefix code of the formula as a list of natural numbers: `var i ↦ [0, v i]`,
`const c ↦ [1, c' c]`, a sum gate `↦ [2, m]` and a product gate `↦ [3, m]`, each followed by the
codes of its `m` children in order. -/
def code (c' : K → ℕ) (v : σ → ℕ) : Formula K σ → List ℕ
  | var i => [0, v i]
  | const c => [1, c' c]
  | add m g => [2, m] ++ (List.ofFn fun i => code c' v (g i)).flatten
  | mul m g => [3, m] ++ (List.ofFn fun i => code c' v (g i)).flatten

end Formula

end BorderDiffEq.Supplement


