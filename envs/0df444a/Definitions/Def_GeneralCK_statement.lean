-- Prove2me | Definitions.Def_GeneralCK_statement
-- name    : GeneralCK_statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T15:42:11.664324+00:00
-- url     : https://prove2.me/theorems/ad9fa566-34ec-43ec-851a-3c192a23cd49
-- title:
--   Mutual information of a Boolean function through a binary symmetric channel (Courtade-Kumar setup)
-- statement:
--   The measure-theory-free finite model of a Boolean function observed through a binary symmetric channel, as used in the Courtade–Kumar / Most Informative Boolean Function problem. Everything is a finite sum over the cube, so no probability space is needed.
--
--   **The cube.** $\mathrm{Cube}\ n$ is the Boolean cube $\{0,1\}^n$, realised as the functions $\mathrm{Fin}\ n \to \mathrm{Bool}$.
--
--   **Binary entropy, in bits.** For $p \in \mathbb{R}$,
--   $$H(p) \;=\; \frac{h_{2}^{\mathrm{nat}}(p)}{\log 2}, \qquad h_{2}^{\mathrm{nat}}(p) \;=\; p\log \tfrac1p + (1-p)\log\tfrac1{1-p},$$
--   using Mathlib's `Real.binEntropy` (which already takes the continuous values $0$ at $p = 0$ and $p = 1$). Thus $H(1/2) = 1$ and $H$ is measured in bits.
--
--   **The channel.** Let $X$ be uniform on $\{0,1\}^n$ and let $Y$ be obtained from $X$ by flipping each coordinate independently with crossover probability $p$ (so $p$ is a crossover probability, *not* a correlation). The transition kernel is
--   $$\mathrm{noiseKernel}\ p\ x\ y \;=\; \Pr[Y = y \mid X = x] \;=\; \prod_{i} \begin{cases} 1-p, & x_i = y_i,\ p, & x_i \ne y_i.\end{cases}$$
--
--   **Joint masses.** For a Boolean function $f : \{0,1\}^n \to \{0,1\}$, $b \in \{0,1\}$ and $y \in \{0,1\}^n$,
--   $$\mathrm{jointMass}\ f\ p\ b\ y \;=\; \Pr[f(X) = b,\ Y = y] \;=\; 2^{-n}\sum_{x} \mathbf{1}[f(x) = b]\ \mathrm{noiseKernel}\ p\ x\ y .$$
--
--   **Shannon entropy of a finite mass vector, in bits.** For a finite type $\alpha$ and $q : \alpha \to \mathbb{R}$,
--   $$\mathrm{entropy}\ q \;=\; \frac{1}{\log 2}\sum_{a} \bigl(-q(a)\log q(a)\bigr),$$
--   written with Mathlib's `Real.negMulLog`. It is applied below only to probability masses.
--
--   **Mutual information, in bits.** With the two marginals of the joint mass,
--   $$I(f(X); Y) \;=\; \mathrm{entropy}\bigl(b \mapsto \textstyle\sum_y \mathrm{jointMass}\ f\ p\ b\ y\bigr) + \mathrm{entropy}\bigl(y \mapsto \textstyle\sum_b \mathrm{jointMass}\ f\ p\ b\ y\bigr) - \mathrm{entropy}\bigl((b,y) \mapsto \mathrm{jointMass}\ f\ p\ b\ y\bigr),$$
--   i.e. $H(f(X)) + H(Y) - H(f(X), Y)$.
--
--   **The target proposition.** `GeneralCourtadeKumar` is the proposition — a definition, not an asserted theorem — that the inequality holds in full generality: for every dimension $n$ (including $n = 0$), every Boolean function $f$ on the cube, and every crossover probability $p \in [0,1]$ (including $0$, $1/2$ and $1$),
--   $$I(f(X); Y) \;\le\; 1 - H(p).$$
--
--   This is the statement a human reviewer has to check; the accompanying theorem asserts it.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/b821c742246c47508fb5d85b283c4760799f995f/browse/GeneralCK/Statement.lean#L1-L63 (the 63-line review target of the Lean 4 formalization); paper: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026), Section 1

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace GeneralCK

/-- The Boolean cube `{0,1}^n`, as functions `Fin n → Bool`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Binary entropy in bits, including the continuous endpoint values. -/
noncomputable def H (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- Independent coordinate bit flips. `p` is crossover, not correlation. -/
noncomputable def noiseKernel {n : ℕ} (p : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - p else p

/-- The joint mass of `(f(X),Y)` for uniform `X` and binary symmetric noise. -/
noncomputable def jointMass {n : ℕ} (f : Cube n → Bool) (p : ℝ)
    (b : Bool) (y : Cube n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, if f x = b then noiseKernel p x y else 0

/-- Finite Shannon entropy in bits. Used below only for probability masses. -/
noncomputable def entropy {α : Type*} [Fintype α] (q : α → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (q a)) / Real.log 2

/-- Mutual information from joint and marginal finite masses. -/
noncomputable def mutualInformation {n : ℕ} (f : Cube n → Bool) (p : ℝ) : ℝ :=
  entropy (fun b => ∑ y, jointMass f p b y) +
  entropy (fun y => ∑ b, jointMass f p b y) -
  entropy (fun byPair : Bool × Cube n => jointMass f p byPair.1 byPair.2)

/-- Review target: all dimensions (including zero), all Boolean functions,
all crossover probabilities (including zero, one half, and one).
This is a proposition definition, not an asserted theorem. -/
def GeneralCourtadeKumar : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
    0 ≤ p → p ≤ 1 → mutualInformation f p ≤ 1 - H p

end GeneralCK


