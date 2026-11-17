-- Prove2me | Definitions.Def_QaryCVP_Supplement_svpBasics
-- name    : QaryCVP_Supplement_svpBasics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:12:34.493723+00:00
-- url     : https://prove2.me/theorems/ac2c92d6-20e1-49e4-b597-6d9399e3fbd1
-- title:
--   Shortest nonzero vectors of $\Lambda$, the SVP input word, the SVP success event, the exact density test $\delta\le\delta_0$ and the ball counts $|B_d(u)|$
-- statement:
--   For $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ with q-ary lattice $\Lambda=\{x\in\mathbb Z^n: Hx\equiv0_m\}$, a vector $x$ is a **solution of SVP** (Definition 2.7) if $x\in\Lambda\setminus\{0^n\}$ and
--
--   $$\|x\|=\min_{a\in\Lambda\setminus\{0^n\}}\|a\|.$$
--
--   The module also fixes:
--
--   1. the **input word** of an SVP instance: $n,m,q$ followed by the $mn$ entries of $H$ row by row, as canonical representatives in $[0,q)$;
--   2. for a program $P$ of the randomized log-cost RAM, the property that on input $H$ it halts on every coin tape with output a nonzero vector of $\Lambda$, and the **success event**: the set of coin tapes on which the output is a shortest nonzero vector; $H$ is *good* for $P$ with error $\varepsilon$ if this event is measurable and has probability at least $1-\varepsilon$;
--   3. the unit vector $e_1$;
--   4. the **exact density test** $\delta\le\delta_0$ for rational $\delta_0\ge0$: $q^m\le2^{\delta_0 n}$, decided as $q^{m\cdot\mathrm{den}\,\delta_0}\le2^{\mathrm{num}\,\delta_0\cdot n}$;
--   5. $|B_d(u)|$, the number of integer points $z\in\mathbb Z^d$ with $\|z\|^2\le u$ (Definition A.1).
--
--   These are the objects of every SVP statement of the supplement.
--
--   **Formalization Note** Shortest is stated squared against every nonzero $a\in\Lambda$; the minimum exists because $\Lambda\supseteq q\mathbb Z^n$ is discrete.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Definition 2.7, p.13; Algorithm 4, p.48; density test, p.50; Definition A.1, p.59

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_encInst

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace QaryCVP.Supplement

/-- `x` is a solution of SVP for `H` (Definition 2.7, p.13): `x ∈ Λ ∖ {0ⁿ}` and
`‖x‖ = min_{a ∈ Λ∖{0ⁿ}} ‖a‖`.
Kim, Kwon, Lee, Lee, *Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary
Lattices*, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Definition 2.7, p.13.

**Formalization Note.** Stated squared, against every nonzero `a ∈ Λ` (as the base states γ-CVP,
R7). The minimum exists because `Λ ⊇ qZⁿ` is discrete, so this is the same condition. -/
def IsShortestNonzero {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (x : Fin n → ℤ) : Prop :=
  x ∈ qaryLattice H ∧ x ≠ 0 ∧ ∀ a ∈ qaryLattice H, a ≠ 0 → sqNormZ x ≤ sqNormZ a

/-- The input word of an SVP instance `H` (R9 without a target): `n, m, q`, then the `mn` entries of
`H` row by row as canonical representatives in `[0, q)` (Algorithm 4, p.48: "Input:
`H ∈ (Z/qZ)^{m×n}`"). -/
def encSVP {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) : List ℚ :=
  [(n : ℚ), (m : ℚ), (q : ℚ)] ++ encMat H

/-- On input `H`, the program `P` halts on **every** coin tape with output a nonzero vector of `Λ`
(Theorem 5.7, p.53: "always returns a nonzero vector of Λ"; Theorem 5.9, p.57: "Every execution
returns a nonzero lattice vector"). -/
def AlwaysNonzero (P : Program) {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) : Prop :=
  ∀ τ : ℕ → Bool, ∃ x : Fin n → ℤ, x ∈ qaryLattice H ∧ x ≠ 0 ∧
    callOutput P (Config.init (encSVP H)) τ = some (encZVec x)

/-- The SVP success event of `P` on a fixed `H`: the coin tapes on which the run on `H` halts with
output a shortest nonzero vector of `Λ`. -/
def svpGood (P : Program) {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) : Set (ℕ → Bool) :=
  {τ | ∃ x : Fin n → ℤ, IsShortestNonzero H x ∧
      callOutput P (Config.init (encSVP H)) τ = some (encZVec x)}

/-- `H` is good for the SVP program `P`: the success event is measurable and has probability at
least `1 − ε` under fair coins, with `H` held fixed. -/
def GoodMatrixSVP (P : Program) {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (ε : ℝ) : Prop :=
  MeasurableSet (svpGood P H) ∧ 1 - ε ≤ (coinTape (svpGood P H)).toReal

/-- The first standard unit vector `e₁ ∈ Zⁿ` (0-based index `0`). -/
def unitVec1 (n : ℕ) : Fin n → ℤ := fun i => if i.val = 0 then 1 else 0

/-- The exact density test `δ ≤ δ₀` for a rational `δ₀ ≥ 0` (p.50): `qᵐ ≤ 2^{δ₀ n}`, decided "by
exact integer arithmetic after raising both sides to the power of the denominator of `δ₀`", i.e.
`q^{m·den δ₀} ≤ 2^{num δ₀ · n}`. -/
def DensityLeQ (δ0 : ℚ) (q m n : ℕ) : Prop :=
  q ^ (m * δ0.den) ≤ 2 ^ (δ0.num.toNat * n)

/-- `|B_d(u)|`, the number of integer points `z ∈ Z^d` with `‖z‖² ≤ u` (Definition A.1, p.59).

**Formalization Note.** For an integer radius `u`, every such point has `|zᵢ| ≤ u`, so the points are
counted inside the box `[−u, u]^d`. -/
noncomputable def ballCount (d u : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(u : ℤ)) u).filter
    (fun z => ∑ i, (z i) ^ 2 ≤ (u : ℤ))).card

end QaryCVP.Supplement


