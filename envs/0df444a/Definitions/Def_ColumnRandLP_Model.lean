-- Prove2me | Definitions.Def_ColumnRandLP_Model
-- name    : ColumnRandLP_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:07.496429+00:00
-- url     : https://prove2.me/theorems/cc205184-c048-4bc9-8338-445c11576123
-- title:
--   Column-randomized LP $P_J$, distributional counterpart $P_{\mathrm{distr}}$, sampling law $\xi^{\otimes K}$ and the sparsification $x'$
-- statement:
--   Fix an $m\times n$ matrix $A$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ and a probability distribution $\xi=(\xi_1,\dots,\xi_n)$ on $[n]$.
--
--   1. **Sample.** A sample is an ordered tuple $J=(j_1,\dots,j_K)\in[n]^K$; repeated indices are allowed. Its law is $\xi^{\otimes K}$: the $K$ indices are drawn independently, each equal to $j$ with probability $\xi_j$.
--   2. **Column-randomized LP.** $A_J=[A_{j_1},\dots,A_{j_K}]$ and $c_J=(c_{j_1},\dots,c_{j_K})$, and
--   $$
--   P_J:\quad \min\{c_J^T\tilde x \mid A_J\tilde x=b,\ \tilde x\ge 0\},
--   $$
--   with optimal value $v(P_J)$.
--   3. **Distributional counterpart.** For a constant $C$,
--   $$
--   P_{\mathrm{distr}}:\quad \min\{c^Tx \mid Ax=b,\ 0\le x\le C\cdot\xi\},
--   $$
--   with optimal value $v(P_{\mathrm{distr}})$; $x^{*0}$ denotes an optimal solution.
--   4. **Sparsification.** For a vector $x^{*0}$ and a sample $J$,
--   $$
--   x'=\frac1K\sum_{k=1}^K\frac{x^{*0}_{j_k}}{\xi_{j_k}}\,e_{j_k},\qquad b'=Ax'.
--   $$
--
--   The optimality gap of a problem $P''$ whose feasible solutions embed in $F(P)$ is $\Delta v(P'')=v(P'')-v(P)$. Theorem 1 compares $\Delta v(P_J)$ with $\Delta v(P_{\mathrm{distr}})$, and the vectors $x'$, $b'$ drive its proof.
--
--   **Formalization Note** $J$ is `Fin K → Fin n`; `Fin n` has the discrete σ-algebra and the law of one index is $\sum_j\xi_j\delta_j$, so the law of $J$ is the product measure `Measure.pi`. Optimal values are real infima (see `ColumnRandLP.StandardLP`). In $x'$, Lean's convention $x/0=0$ is harmless: an optimal $x^{*0}$ of $P_{\mathrm{distr}}$ has $x^{*0}_j=0$ whenever $\xi_j=0$.
-- source:
--   Akchen–Mišić, Column-Randomized Linear Programs: Performance Guarantees and Applications, arXiv:2007.10461v5, Definition 1, (3), p.6; Algorithm 1, (4), p.7; Theorem 1, (5a)–(5c), p.7; proof of Proposition EC.3, p.ec7 (x*⁰, x′, b′)

import Mathlib
import Definitions.Def_ColumnRandLP_StandardLP

open Matrix MeasureTheory

namespace ColumnRandLP

/-- The sampled constraint matrix `A_J = [A_{j₁}, …, A_{j_K}]` (Akchen–Mišić,
arXiv:2007.10461v5, Definition 1, p.6, and Algorithm 1, step 2, p.7).

**Formalization Note** The sample `J = (j₁, …, j_K)` is an ordered tuple `Fin K → Fin n`;
repeated indices are allowed (then `A_J` has repeated columns), as in Definition 1. -/
def sampleMat {m n K : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (J : Fin K → Fin n) :
    Matrix (Fin m) (Fin K) ℝ :=
  fun i k => A i (J k)

/-- The sampled cost vector `c_J = [c_{j₁}, …, c_{j_K}]` (Akchen–Mišić, arXiv:2007.10461v5,
Definition 1, p.6, and Algorithm 1, step 2, p.7). -/
def sampleCost {n K : ℕ} (c : Fin n → ℝ) (J : Fin K → Fin n) : Fin K → ℝ :=
  fun k => c (J k)

/-- `v(P_J)`, the optimal value of the column-randomized linear program
`P_J : min {c_Jᵀ x̃ | A_J x̃ = b, x̃ ≥ 0}` (Akchen–Mišić, arXiv:2007.10461v5, Definition 1, (3),
p.6; (4), p.7). Meaningful when `P_J` is feasible (it is then bounded below by `v(P)`, since
its solutions embed in `F(P)`); see the note on `lpValue`. -/
noncomputable def vJ {m n K : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (J : Fin K → Fin n) : ℝ :=
  lpValue (sampleMat A J) b (sampleCost c J)

/-- Feasible set of the distributional counterpart
`P_distr : min {cᵀx | Ax = b, 0 ≤ x ≤ C·ξ}` (Akchen–Mišić, arXiv:2007.10461v5, Theorem 1,
(5a)–(5c), p.7). -/
def distrFeasSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (C : ℝ)
    (ξ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x = b ∧ 0 ≤ x ∧ x ≤ C • ξ}

/-- `v(P_distr)`, the optimal value of the distributional counterpart (Akchen–Mišić,
arXiv:2007.10461v5, Theorem 1, (5a)–(5c), p.7).

**Formalization Note** Real `sInf`; the feasible set is bounded (`0 ≤ x ≤ Cξ`), so this is the
true minimum as soon as `P_distr` is feasible, which every statement using it assumes. -/
noncomputable def vDistr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (C : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  sInf ((fun x => c ⬝ᵥ x) '' distrFeasSet A b C ξ)

/-- `x` is an optimal solution `x*⁰` of the distributional counterpart `P_distr`
(Akchen–Mišić, arXiv:2007.10461v5, proof of Proposition EC.3, p.ec7). -/
def IsDistrOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (C : ℝ) (ξ : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ distrFeasSet A b C ξ ∧ ∀ y ∈ distrFeasSet A b C ξ, c ⬝ᵥ x ≤ c ⬝ᵥ y

/-- The law of one sampled index: the distribution `ξ` on `[n]`, as the measure
`∑_j ξ_j δ_j` on `Fin n` (Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6: "ξ_j is the probability
that index j is selected by ρ").

**Formalization Note** `Fin n` carries Mathlib's discrete σ-algebra (`⊤`), so every set of
indices is measurable. It is a probability measure when `ξ ≥ 0` and `∑_j ξ_j = 1`, which every
statement assumes. -/
noncomputable def xiMeasure {n : ℕ} (ξ : Fin n → ℝ) : Measure (Fin n) :=
  ∑ j, ENNReal.ofReal (ξ j) • Measure.dirac j

/-- The law `ξ^{⊗K}` of the sample `J = (j₁, …, j_K)`: `K` indices drawn independently and
identically according to `ξ` (Akchen–Mišić, arXiv:2007.10461v5, §3.1, p.6: "ρ samples each index
independently and identically according to ξ").

**Formalization Note** The `K`-fold product measure on `Fin K → Fin n` (discrete σ-algebra).
"With probability at least `1 − δ` over the sample `J`" is
`ENNReal.ofReal (1 - δ) ≤ sampleMeasure ξ K S` for the event `S`. -/
noncomputable def sampleMeasure {n : ℕ} (ξ : Fin n → ℝ) (K : ℕ) : Measure (Fin K → Fin n) :=
  Measure.pi (fun _ : Fin K => xiMeasure ξ)

/-- The importance-weighted sparsification
`x′ = (1/K) ∑_{k=1}^K (x*⁰_{j_k} / ξ_{j_k}) e_{j_k}` of a vector `x0` along the sample `J`
(Akchen–Mišić, arXiv:2007.10461v5, proof of Proposition EC.3, p.ec7). The vector `b′ = A x′`
of the same proof is `A *ᵥ xprime ξ x0 J`.

**Formalization Note** Lean's `x / 0 = 0`; the paper's `x*⁰` satisfies `x*⁰_j = 0` whenever
`ξ_j = 0` (because `x*⁰ ≤ Cξ`), and such an index is drawn with probability `0`, so this
convention changes nothing. -/
noncomputable def xprime {n K : ℕ} (ξ : Fin n → ℝ) (x0 : Fin n → ℝ) (J : Fin K → Fin n) :
    Fin n → ℝ :=
  (1 / (K : ℝ)) • ∑ k, (x0 (J k) / ξ (J k)) • (Pi.single (J k) (1 : ℝ) : Fin n → ℝ)

end ColumnRandLP


