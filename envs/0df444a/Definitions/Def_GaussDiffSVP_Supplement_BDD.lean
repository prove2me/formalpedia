-- Prove2me | Definitions.Def_GaussDiffSVP_Supplement_BDD
-- name    : GaussDiffSVP_Supplement_BDD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:46:57.652354+00:00
-- url     : https://prove2.me/theorems/df7d3954-1f21-4d70-b9c2-ef258443518c
-- title:
--   Second successive minimum and the $r$-BDD data structure
-- statement:
--   The **second successive minimum** $\lambda_2(L)$ is the least $r$ such that the closed ball of radius $r$ contains two linearly independent vectors of $L$ ($\lambda_2=\infty$ in rank one).
--
--   An **$r$-BDD data structure** with preprocessing $P$, query work $D$, space $S$ and success probability $p$ is a pair of randomized programs, a preprocessing $\mathrm{Pre}$ and a query $Q$, such that for every $n\ge1$ and every nonsingular $B\in\mathbb Q^{n\times n}$ (bit length $\ell$):
--
--   1. $\mathrm{Pre}$ on $B$ halts on every coin tape with an advice word, within bit time $P(n)(\ell+1)^K$ and bit space $S(n)(\ell+1)^K$;
--   2. for every advice $A$ that $\mathrm{Pre}$ can output and every rational target $t$ (bit length $\ell_t$), inside or outside the promise, $Q$ on $(A,t)$ halts on every coin tape within bit time $D(n)(\ell+\ell_t+1)^K$ and bit space $S(n)(\ell+\ell_t+1)^K$;
--   3. with probability at least $p(n)$ the advice is **good**: the reply of $Q$ to every rational target is independent of the coins (the advice determines a function), and for every rational target $t$ with $\operatorname{dist}(t,L)\le r\lambda_1(L)$ the reply is the coefficient vector of a nearest lattice point.
--
--   Theorem 12.1 constructs such a structure; Theorems 12.3 and 12.4 assume one with $0<r<1/2$ and $p=9/10$.
--
--   **Formalization Note** The promise is closed ($\le r\lambda_1$). Polynomial input and target factors are the factors $(\ell+1)^K$, $(\ell+\ell_t+1)^K$. $\lambda_2$ takes values in $[0,\infty]$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.1, p.59; §12.3, p.59 (the r-BDD interface); Theorem 12.3, p.59 (λ₂)

import Mathlib
import Definitions.Def_CosetTreeSVP_SVP_Algo

open MeasureTheory TwMSOCount.Main
open scoped ENNReal NNReal

namespace GaussDiffSVP.Supplement

open CosetTreeSVP.SVP

/-- The second successive minimum `λ₂(L)`: the infimum of the radii `r ≥ 0` such that the closed
ball of radius `r` contains two linearly independent lattice vectors (Gao–Han–Hu, *Gaussian
Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.3, p.59).

**Formalization Note.** The value is in `ℝ≥0∞`: on a lattice of rank one there are no two linearly
independent vectors and `λ₂ = ∞` (so the promise `λ₂ ≥ gλ₁` holds there, as the paper's "Rank one
is immediate", p.104, presumes); it never collapses to `0`. -/
noncomputable def lam2 {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (r : ℝ≥0) (_ : ∃ u ∈ L, ∃ v ∈ L, LinearIndependent ℝ ![u, v] ∧ ‖u‖ ≤ r ∧ ‖v‖ ≤ r),
    (r : ℝ≥0∞)

/-- Good advice of an `r`-BDD data structure (Gao–Han–Hu, Theorem 12.1, p.59, and §12.3, p.59):
"the same advice determines a function that returns the exact nearest lattice point for every
rational target at distance at most `rλ₁(L)`". With advice word `A`, the query program `Q` on the
word `A ++ t`:

1. returns the same reply on every coin tape, for every rational target `t` (the advice determines a
   function of the target);
2. for every rational target `t` with `dist(t, L) ≤ rλ₁(L)`, returns on every coin tape the integer
   coefficient vector of a closest lattice vector (`CosetTreeSVP.SVP.IsClosest`).

**Formalization Note.** The distance promise is closed (`≤`), as printed; the published
`CosetTreeSVP.SVP.AdviceGood` (strict `<`, radius `n^{−1/3}`) is a different notion. -/
def BDDAdviceGood (r : ℝ) (Q : Program) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (A : List ℚ) :
    Prop :=
  (∀ (t : Fin n → ℚ) (τ τ' : ℕ → Bool),
      callOutput Q (Config.init (A ++ encQVec t)) τ = callOutput Q (Config.init (A ++ encQVec t)) τ') ∧
    ∀ t : Fin n → ℚ,
      Metric.infDist (qVec t) (latQ B : Set (EuclideanSpace ℝ (Fin n))) ≤
          r * SuperlatSVP.lam1 (latQ B) →
        ∀ τ : ℕ → Bool, ∃ x : Fin n → ℤ, IsClosest B t x ∧
          callOutput Q (Config.init (A ++ encQVec t)) τ = some (SuperlatSVP.encIntVec x)

/-- The event that the preprocessing `Pre` on the basis `B` halts with good advice. -/
def bddPreSuccess (r : ℝ) (Pre Q : Program) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) :
    Set (ℕ → Bool) :=
  {τ | ∃ A : List ℚ, callOutput Pre (Config.init (SuperlatSVP.encBasis B)) τ = some A ∧
    BDDAdviceGood r Q B A}

/-- An `r`-BDD data structure (interface) with preprocessing `P`, query work `D` and space `S`, and
good-advice probability `p` (Gao–Han–Hu, Theorem 12.1, p.59; §12.3, p.59: "Assume an r-BDD interface
with 0 < r < 1/2, preprocessing P, query work D, and space S. With probability at least 9/10 its
advice determines a function correct on all promised rational targets. The function has a fixed
resource bound even outside the promise."). For every `n ≥ 1` and every nonsingular `B ∈ ℚ^{n×n}`,
with `ℓ` the bit length of `B` and `ℓ_t` that of a target `t`:

1. on every coin tape the preprocessing `Pre` on `B` halts within bit time `P(n)(ℓ+1)^K` and bit
   space `S(n)(ℓ+1)^K`;
2. for every advice word `A` that `Pre` outputs on some coin tape and **every** rational target `t`
   (inside or outside the promise), on every coin tape the query `Q` on `A ++ t` halts within bit
   time `D(n)(ℓ+ℓ_t+1)^K` and bit space `S(n)(ℓ+ℓ_t+1)^K`;
3. the event that `Pre` outputs good advice (`BDDAdviceGood`) is measurable and has probability at
   least `p(n)` under fair coins.

**Formalization Note.** Polynomial input and target encoding factors, suppressed by the paper,
are the factors `(ℓ+1)^K` and `(ℓ+ℓ_t+1)^K` with one exponent `K`; the query's space bound covers the
advice it reads. The machine is the published `TwMSOCount.Main` RAM. -/
def IsBDDInterface (r : ℝ) (Pre Q : Program) (P D S : ℕ → ℝ) (K : ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
    (∀ τ : ℕ → Bool, ∃ s : RunStats,
        runStats Pre τ (Config.init (SuperlatSVP.encBasis B)) = some s ∧
        (s.time : ℝ) ≤ P n * ((SuperlatSVP.inputBits B : ℝ) + 1) ^ K ∧
        (s.space : ℝ) ≤ S n * ((SuperlatSVP.inputBits B : ℝ) + 1) ^ K) ∧
    (∀ (τ : ℕ → Bool) (A : List ℚ),
      callOutput Pre (Config.init (SuperlatSVP.encBasis B)) τ = some A →
      ∀ (t : Fin n → ℚ) (τ' : ℕ → Bool), ∃ s : RunStats,
        runStats Q τ' (Config.init (A ++ encQVec t)) = some s ∧
        (s.time : ℝ) ≤
          D n * ((SuperlatSVP.inputBits B : ℝ) + wordBits (encQVec t) + 1) ^ K ∧
        (s.space : ℝ) ≤
          S n * ((SuperlatSVP.inputBits B : ℝ) + wordBits (encQVec t) + 1) ^ K) ∧
    MeasurableSet (bddPreSuccess r Pre Q B) ∧
    ENNReal.ofReal (p n) ≤ coinTape (bddPreSuccess r Pre Q B)

end GaussDiffSVP.Supplement


