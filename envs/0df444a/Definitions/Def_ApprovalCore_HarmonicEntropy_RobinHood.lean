-- Prove2me | Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood
-- name    : ApprovalCore_HarmonicEntropy_RobinHood
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:30:36.637539+00:00
-- url     : https://prove2.me/theorems/592ba1b3-f44a-4c8a-a984-2506c50e21c7
-- title:
--   The Robin Hood operator $\Phi^\ell$, its water level, and harmonic entropy $F$ with its truncation $F_L$
-- statement:
--   For $d \in \mathbb N$ let $\Delta_d = \{x \in \mathbb R^d_{\ge 0} : \sum_{j=1}^d x_j = 1\}$ be the probability simplex; $x$ is **strictly positive** if every $x_j > 0$, and $(a)_+ = \max\{a, 0\}$.
--
--   **Water level and Robin Hood operator.** For $x \in \Delta_d$ and an integer $\ell \ge 1$, the **water level** $t_\ell \in [0,1]$ is the unique solution of
--   $$\ell \cdot t_\ell = \sum_{j=1}^d (x_j - t_\ell)_+ ,$$
--   and the **Robin Hood operator** $\Phi^\ell : \Delta_d \to \Delta_{d+\ell}$ is
--   $$\Phi^\ell(x) = \big(\min\{x_1, t_\ell\}, \dots, \min\{x_d, t_\ell\}, \underbrace{t_\ell, \dots, t_\ell}_{\ell\ \text{times}}\big),$$
--   with $\Phi^0(x) = x$ and $\Phi = \Phi^1$ (the paper writes the $\ell$-step operator with a superscript; it is defined directly, not as an iterate). Applying $\Phi$ $M$ times gives a vector on $d + M$ coordinates, which the paper also writes $\Phi^M(x)$; Lemma B.1 shows the two agree. The water level of $x$ with $\ell \ge 0$ steps is $t_\ell(x) := \|\Phi^\ell(x)\|_\infty$.
--
--   **Harmonic entropy.** With harmonic numbers $H_t = \sum_{j=1}^t 1/j$, $H_0 = 0$, harmonic entropy of a strictly positive $x \in \Delta_d$ is defined recursively by
--   $$F(x) = \begin{cases} H_{d-1} & \text{if } x = (\tfrac1d, \dots, \tfrac1d),\\ F(\Phi(x)) - \|x\|_\infty & \text{otherwise,}\end{cases}$$
--   which terminates because finitely many applications of $\Phi$ make $x$ uniform. For a distribution with zero coordinates, $F(x) := F(x')$ with $x'$ the vector obtained by deleting the zero coordinates. The truncation of the series representation (6) is
--   $$F_L(x) = \sum_{\ell=0}^{L-1}\Big(\frac{1}{\ell+1} - \|\Phi^\ell(x)\|_\infty\Big).$$
--
--   **Formalization Note.** Vectors are `Fin d → ℝ` (0-based); $\Delta_d$ is Mathlib's `stdSimplex ℝ (Fin d)` and $\|\cdot\|_\infty$ is Mathlib's sup norm `‖·‖`. The water level `waterLevel ℓ x` is the infimum of the solution set of $\ell t = \sum_j (x_j - t)_+$ in $[0,1]$, which is the unique solution on $\Delta_d$ for $\ell \ge 1$ (footnote 4); formulas (4)/(5) are the milestone Lemma 5.1, not the definition. `robinHood ℓ x` is $\Phi^\ell(x)$ on `Fin (d + ℓ)` with the $\ell$ new coordinates after the $d$ old ones; `phiIter M x` is $M$ applications of $\Phi$ (equal to `robinHood M x` on $\Delta_d$ by Lemma B.1, which is not used to define anything). Unfolding the recursion, `harmonicEntropyPos x` $= H_{d+L-1} - \sum_{\ell < L}\|\texttt{phiIter}\ \ell\ x\|_\infty$ with $L$ the least count such that `phiIter L x` is uniform; if no iterate is uniform (impossible for strictly positive $x$, §5.1) the value is a junk $0$. `deleteZeros` keeps the nonzero coordinates in increasing index order; `harmonicEntropy x` is `harmonicEntropyPos (deleteZeros x)`. Outside $\Delta_d$ all these are junk values that no statement uses.
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), §2 p. 3; §5.1 pp. 8–9 and footnote 4; §5.2 pp. 10–11 (definition of F and F_L)

import Mathlib

namespace ApprovalCore.HarmonicEntropy

/-!
# The Robin Hood operator and harmonic entropy

Becker, Greger, Peters, *Existence of the Core in Approval-Based Committee Elections*,
STOC 2027 submission (manuscript sha256 7cc237dc…), §2 p. 3 (`[t]`, `(a)+`, `∆d`),
§5.1 pp. 8–9 (Robin Hood operator, water level, footnote 4), §5.2 pp. 10–11 (harmonic
entropy `F`, its truncation `F_L`).

Distributions on `d` coordinates are vectors `x : Fin d → ℝ`; `∆d` is Mathlib's
`stdSimplex ℝ (Fin d)` (nonnegative coordinates summing to `1`). Coordinates are 0-based.
`‖y‖` on `Fin d → ℝ` is Mathlib's sup norm `max_j |y j|`, i.e. the paper's `∥y∥∞`.
-/

/-- The positive part `(a)+ = max{a, 0}` (p. 3). -/
noncomputable def posPart (a : ℝ) : ℝ := max a 0

/-- The water level `tℓ` of `x` for `ℓ ≥ 1` new coordinates (p. 9 and footnote 4): the
solution `t ∈ [0, 1]` of `ℓ · t = ∑_{j} (x_j − t)+`, which is unique for `x ∈ ∆d` and
`ℓ ≥ 1` (footnote 4). It is written as the infimum of the solution set in `[0, 1]`; on
`∆d` with `ℓ ≥ 1` that set is a singleton, so this is the paper's `tℓ`. -/
noncomputable def waterLevel {d : ℕ} (ℓ : ℕ) (x : Fin d → ℝ) : ℝ :=
  sInf {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ (ℓ : ℝ) * t = ∑ j, posPart (x j - t)}

/-- The Robin Hood operator `Φ^ℓ : ∆d → ∆(d+ℓ)` (p. 8; the paper writes the ℓ-step operator
with a superscript, defined directly, not as an iterate): for `ℓ ≥ 1`,
`Φ^ℓ(x) = (min{x₁, tℓ}, …, min{x_d, tℓ}, tℓ, …, tℓ)` with `ℓ` new coordinates equal to the
water level `tℓ`, placed after the `d` old ones; `Φ^0(x) = x` (p. 9). -/
noncomputable def robinHood {d : ℕ} : (ℓ : ℕ) → (Fin d → ℝ) → (Fin (d + ℓ) → ℝ)
  | 0, x => x
  | ℓ + 1, x =>
      Fin.append (fun j : Fin d => min (x j) (waterLevel (ℓ + 1) x))
        (fun _ : Fin (ℓ + 1) => waterLevel (ℓ + 1) x)

/-- `Φ = Φ^1` (p. 9). -/
noncomputable def Phi {d : ℕ} (x : Fin d → ℝ) : Fin (d + 1) → ℝ := robinHood 1 x

/-- `M` applications of the single-coordinate operator `Φ` (p. 9), the iterate
`Φ ∘ ⋯ ∘ Φ`: `phiIter 0 x = x`, `phiIter (M+1) x = Φ(phiIter M x) ∈ ∆(d+M+1)`. (The paper
also writes this `Φ^M(x)`; it equals the `M`-step operator by Lemma B.1.) -/
noncomputable def phiIter {d : ℕ} : (M : ℕ) → (Fin d → ℝ) → (Fin (d + M) → ℝ)
  | 0, x => x
  | M + 1, x => Phi (phiIter M x)

/-- `x` is the uniform distribution `(1/d, …, 1/d)`. -/
def IsUniform {d : ℕ} (x : Fin d → ℝ) : Prop := ∀ j, x j = 1 / (d : ℝ)

/-- `x` is strictly positive: `x_j > 0` for all `j` (p. 4). -/
def StrictlyPositive {d : ℕ} (x : Fin d → ℝ) : Prop := ∀ j, 0 < x j

/-- The harmonic number `H_t = ∑_{j=1}^t 1/j`, `H₀ = 0` (p. 6), as a real number
(Mathlib's `harmonic`). -/
noncomputable def H (t : ℕ) : ℝ := (harmonic t : ℝ)

/-- Harmonic entropy of a strictly positive distribution (p. 10), defined by the paper's
recursion `F(x) = H_{d−1}` if `x` is uniform and `F(x) = F(Φ(x)) − ∥x∥∞` otherwise.
The recursion terminates because `L` applications of `Φ` make `x` uniform for some `L` (§5.1, a milestone):
with `L` the least such iterate count, unfolding the recursion `L` times gives
`F(x) = H_{d+L−1} − ∑_{ℓ<L} ∥Φ(⋯Φ(x))∥∞` (`ℓ` applications of `Φ` in the `ℓ`-th term).
If no iterate is uniform (impossible for a strictly positive distribution, by §5.1) the
value is the junk `0`. -/
noncomputable def harmonicEntropyPos {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  haveI := Classical.propDecidable
  if h : ∃ L : ℕ, IsUniform (phiIter L x) then
    H (d + Nat.find h - 1) - ∑ ℓ ∈ Finset.range (Nat.find h), ‖phiIter ℓ x‖
  else 0

/-- The positive (non-zero) coordinates of `x`, in increasing order (zero coordinates
deleted, p. 10). -/
noncomputable def deleteZeros {d : ℕ} (x : Fin d → ℝ) :
    Fin (Finset.univ.filter (fun j => x j ≠ 0)).card → ℝ :=
  fun i => x ((Finset.univ.filter (fun j => x j ≠ 0)).orderEmbOfFin rfl i)

/-- Harmonic entropy `F` (p. 10): `F(x) := F(x′)` where `x′` is `x` with its zero
coordinates deleted, and `F` on strictly positive distributions is
`harmonicEntropyPos`. -/
noncomputable def harmonicEntropy {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  harmonicEntropyPos (deleteZeros x)

/-- The truncation `F_L(x) = ∑_{ℓ=0}^{L−1} (1/(ℓ+1) − ∥Φ^ℓ(x)∥∞)` of the series (6)
(p. 11), with `Φ^ℓ` the Robin Hood operator with `ℓ` steps (`Φ^0(x) = x`). -/
noncomputable def harmonicEntropyTrunc {d : ℕ} (L : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.range L, (1 / ((ℓ : ℝ) + 1) - ‖robinHood ℓ x‖)

end ApprovalCore.HarmonicEntropy


