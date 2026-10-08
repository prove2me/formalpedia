-- Prove2me | Definitions.Def_LogSobolevMC_Metropolis_Chains
-- name    : LogSobolevMC_Metropolis_Chains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:15.637987+00:00
-- url     : https://prove2.me/theorems/86a8024d-2fd1-4511-9a70-b1d3d415a697
-- title:
--   Example 1.1, p. 698; Examples 3.1–3.3, pp. 715–719 — the binomial distribution, the base walk, the Metropolis chain (1.9), the two-point chain, the hypercube walk and the Ehrenfest chain
-- statement:
--   The concrete chains of the paper's running example. Fix $n\ge 1$ and let $\mathcal X=\{0,1,\dots,n\}$.
--
--   1. The **binomial distribution** $\pi(x)=2^{-n}\binom{n}{x}$ on $\mathcal X$.
--   2. The **base chain** $K$, nearest-neighbour random walk held at the ends: $K(x,x+1)=K(x,x-1)=1/2$ for $1\le x\le n-1$, $K(0,1)=K(0,0)=K(n,n-1)=K(n,n)=1/2$, and $K(x,y)=0$ otherwise.
--   3. The **Metropolis chain** $M$ obtained from $K$ and $\pi$ by the standard Metropolis construction: for $y\neq x$, $$M(x,y)=K(x,y)\min\Big\{1,\frac{\pi(y)}{\pi(x)}\Big\},\qquad M(x,x)=1-\sum_{y\neq x}M(x,y).$$ This is the chain displayed in (1.9).
--   4. The **two-point chain** on $\{-1,1\}$ with $K(-1,1)=K(1,-1)=1$ (Example 3.1).
--   5. The **hypercube walk** on $\{-1,1\}^n$: $K(x,y)=1/n$ if $x$ and $y$ differ at exactly one coordinate, and $0$ otherwise (Example 3.2).
--   6. The **number of ones** $x\mapsto\#\{i: x_i=1\}$ from $\{-1,1\}^n$ to $\mathcal X$, and the **Ehrenfest chain** $P(x,x+1)=(n-x)/n$ for $0\le x\le n-1$, $P(x,x-1)=x/n$ for $1\le x\le n$, $P(x,y)=0$ otherwise (Example 3.3).
--
--   These objects carry the paper's main application, Theorem 1.1: the Metropolis chain for the binomial distribution reaches stationarity after order $n\log n$ steps, proved by comparing $M$ with the Ehrenfest chain, which is a projection of the hypercube walk, which is a product of two-point chains.
--
--   **Formalization Note** $\{0,\dots,n\}$ is `Fin (n + 1)` and $\{-1,1\}$ is `Fin 2` with $0\mapsto -1$, $1\mapsto 1$; the hypercube is `Fin n → Fin 2`. The Metropolis chain is the published `MarkovMixing.metropolis` (LPW §3.2.1) applied to the base chain and $\pi$; the six cases of (1.9) are stated as a theorem (Example 1.1). The definitions are meant for $n\ge 1$; at $n=0$ the base chain row sums to $1/2$ and the hypercube and Ehrenfest kernels divide by $0$, and every theorem of the mission assumes $n\ge 1$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 698, Example 1.1 and (1.9); p. 715, Example 3.1; p. 717, Example 3.2; pp. 718–719, Example 3.3

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mcmc

namespace LogSobolevMC.Metropolis

noncomputable section

open scoped BigOperators

/-- The binomial distribution `π(x) = 2⁻ⁿ C(n, x)` on `{0, 1, …, n}` = `Fin (n + 1)`
(Example 1.1, p. 698). -/
def binomPi (n : ℕ) : Fin (n + 1) → ℝ :=
  fun x => ((n.choose (x : ℕ) : ℕ) : ℝ) / 2 ^ n

/-- The base chain of Example 1.1 (p. 698), nearest-neighbour random walk on
`{0, 1, …, n}` = `Fin (n + 1)`, held at the ends:
`K(x, x + 1) = K(x, x − 1) = 1/2` for `1 ≤ x ≤ n − 1`, and
`K(0, 1) = K(0, 0) = K(n, n − 1) = K(n, n) = 1/2`; all other entries are `0`. -/
def baseWalk (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun x y =>
    if (y : ℕ) = (x : ℕ) + 1 ∨ (y : ℕ) + 1 = (x : ℕ) then 1 / 2
    else if x = y ∧ ((x : ℕ) = 0 ∨ (x : ℕ) = n) then 1 / 2
    else 0

/-- The Metropolis chain `M` of Example 1.1, (1.9), p. 698: the standard Metropolis
construction (`MarkovMixing.metropolis`: a proposal `x → y ≠ x` of the base chain is
accepted with probability `min(1, π(y)/π(x))`, the rejected mass stays at `x`) applied
to `baseWalk n` and the binomial distribution `binomPi n`. -/
def binomMetropolis (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  MarkovMixing.metropolis (baseWalk n) (binomPi n)

/-- The two-point chain of Example 3.1 (p. 715) on `{−1, 1}`, encoded as `Fin 2`
(`0 ↦ −1`, `1 ↦ 1`): `K(−1, 1) = K(1, −1) = 1`, `K(−1, −1) = K(1, 1) = 0`. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => if a = b then 0 else 1

/-- The hypercube chain of Example 3.2 (p. 717) on `{−1, 1}ⁿ` = `Fin n → Fin 2`:
`K(x, y) = 1/n` if `x, y` differ at exactly one coordinate, and `0` otherwise. -/
def hypercube (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℝ :=
  fun x y => if (Finset.univ.filter fun i => x i ≠ y i).card = 1 then 1 / (n : ℝ) else 0

/-- The number of coordinates of `x ∈ {−1, 1}ⁿ` equal to `1` (encoded as `(1 : Fin 2)`),
as an element of `{0, 1, …, n}` = `Fin (n + 1)` (Example 3.3, pp. 718–719). -/
def ones (n : ℕ) (x : Fin n → Fin 2) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => x i = 1).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

/-- The Ehrenfest chain of Example 3.3 (p. 719) on `{0, 1, …, n}` = `Fin (n + 1)`:
`P(x, x + 1) = (n − x)/n` for `0 ≤ x ≤ n − 1`, `P(x, x − 1) = x/n` for `1 ≤ x ≤ n`,
and `P(x, y) = 0` otherwise. -/
def ehrenfest (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun x y =>
    if (y : ℕ) = (x : ℕ) + 1 then ((n : ℝ) - ((x : ℕ) : ℝ)) / n
    else if (y : ℕ) + 1 = (x : ℕ) then ((x : ℕ) : ℝ) / n
    else 0

end

end LogSobolevMC.Metropolis


