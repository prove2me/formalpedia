-- Prove2me | Definitions.Def_FreeOrderEPTAS_santaClaus
-- name    : FreeOrderEPTAS_santaClaus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:18.093547+00:00
-- url     : https://prove2.me/theorems/b1c6513d-90b3-46d0-a1d5-7154b3f8c0c4
-- title:
--   The Santa Claus algorithm as a program
-- statement:
--   The algorithm of Theorem 2.1 at accuracy $\varepsilon$, as an instrumented program:
--
--   1. set $\epsilon=\varepsilon/2$, $\xi=\epsilon/2$ and $\delta=2^{-r}$;
--   2. compute the types and the classes;
--   3. enumerate every guess vector: per $(i,t)$ a pair $(N^\downarrow,N^\uparrow)$, either $(v,v)$ with $0\le v\le2/\delta$ or $(1/\delta,g_k)$ with $g_k=\lceil(1-\xi)^{-k}\rceil$, $0\le k\le\lceil\log n/\log(1/(1-\xi))\rceil$; and per small triple a value $S^\downarrow\in\{0,\epsilon/T,\dots,\lfloor T/\epsilon\rfloor\epsilon/T\}$;
--   4. for each guess, until one succeeds: solve (LP); on a solution, round it; verify (I)–(III) and $\sum_j\ell_{ijd}X_{ij}\ge1-\varepsilon$.
--
--   The result is the first $X$ that passes, or nothing.
--
--   This replaces the "guessing" of the paper by enumeration and verification. Running at $\varepsilon/2$ turns the $2\epsilon$ of Lemma 2.3 into the $\epsilon$ of Theorem 2.1.
--
--   **Formalization Note** Every step is charged at its site: `opn k` for a straight-line block, with the count written at the site, and `foldP`/`foldProd` for loops. Randomness enters only through `callRnd`. `check` is a Boolean test of bounded loops.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §§2.2–2.5, pp.9–12

import Mathlib
import Definitions.Def_FreeOrderEPTAS_IPFeasible
import Definitions.Def_FreeOrderEPTAS_IsLPSolver
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_delta

namespace FreeOrderEPTAS

variable {m D n : ℕ}

/-- The options for one pair `(i, t)` as pairs `(N↓, N↑)` (§2.3, arXiv:2007.13121v3, p.10):
`(v, v)` for `0 ≤ v ≤ 2/δ`, and `(1/δ, g_k)` for `0 ≤ k ≤ ⌈log n / log(1/(1 - ξ))⌉`, where
`g_k = ⌈(1 - ξ)^{-k}⌉` is the explicit grid for `N↑` (the source leaves it unspecified), and `1/δ = 2^r`. -/
noncomputable def nGrid (ξ : ℝ) (r n : ℕ) : List (ℕ × ℕ) :=
  ((List.range (2 * 2 ^ r + 1)).map fun v => (v, v)) ++
    (List.range (⌈Real.log n / Real.log (1 / (1 - ξ))⌉₊ + 1)).map fun k =>
      (2 ^ r, ⌈((1 - ξ) ^ k)⁻¹⌉₊)

/-- The options for one small triple: the possible values `0, ϵ/T, 2ϵ/T, …, ⌊T/ϵ⌋ ϵ/T` of
`⌊min{S, 1}⌋_{ϵ/T}`. The cap at `1` makes their number independent of `n`. -/
noncomputable def sGrid (ϵ : ℝ) (T : ℕ) : List ℝ :=
  (List.range (⌊(T : ℝ) / ϵ⌋₊ + 1)).map fun k => (k : ℝ) * (ϵ / T)

/-- The options per triple `(i, d, t)` in lexicographic order: `sGrid` on a small triple, and
the single value `0` on any other, where `S↓` plays no role. -/
noncomputable def sChoices (I : SCInstance m D n) (ϵ δ : ℝ) : List (List ℝ) :=
  (List.finRange m).flatMap fun i => (List.finRange D).flatMap fun d =>
    (List.finRange (numTypes I ϵ δ)).map fun t =>
      if d ∈ I.A i ∧ typeOf I ϵ δ t i d = 0 then sGrid ϵ (numTypes I ϵ δ) else [0]

/-- The entry for pair `(i, t)` of a guess list. -/
def nAt {T : ℕ} (g : List (ℕ × ℕ)) (i : Fin m) (t : Fin T) : ℕ × ℕ :=
  g.getD (i.val * T + t.val) (0, 0)

/-- The entry for triple `(i, d, t)` of a guess list. -/
noncomputable def sAt {T : ℕ} (g : List ℝ) (i : Fin m) (d : Fin D) (t : Fin T) : ℝ :=
  g.getD ((i.val * D + d.val) * T + t.val) 0

/-- The verification of a rounded `X`: constraints (II), (III), and `∑_j ℓ_ijd X_ij ≥ c` on every
`i`, `d ∈ A_i`. Bounded loops with Boolean tests; no quantified proposition is decided. -/
noncomputable def check (I : SCInstance m D n) (c : ℝ) (X : Assignment m n) : Bool :=
  (List.finRange n).all (fun j => decide (((List.finRange m).filter fun i => X i j).length ≤ 1)) &&
    (List.finRange m).all (fun i =>
      decide (((List.finRange n).filter fun j => X i j).length ≤ I.k i) &&
        (List.finRange D).all fun d =>
          !decide (d ∈ I.A i) ||
            decide (c ≤ ((List.finRange n).map fun j => I.ℓ i j d * bit (X i j)).sum))

/-- The algorithm of §§2.2–2.5 (arXiv:2007.13121v3, pp.9–12) for Theorem 2.1, at accuracy `ε`.

1. Internally `ϵ = ε/2` and `ξ = ϵ/2`, and `δ = 2^{-r}` is `delta ϵ m D`.
2. Compute the types and classes.
3. Enumerate every guess vector `(N↓, N↑, S↓)` in lexicographic order.
4. For each, until one succeeds: build (LP) and solve it; on a solution, round it (`X_ij` is
   `Y_{(i,ρ(j)),j}`, the same array), and verify (I)–(III) and `∑_j ℓ_ijd X_ij ≥ 1 - ε`.

The result is the first `X` that passes, or `none`. Charges: the types take at most 11 operations
per `(j, i, d)` (membership read, `ℓ` read, `seg` in 7, write, dispatch); the classes compare each
job with at most `n` type vectors of `m D` coordinates; each grid entry takes at most 3 operations;
verification takes at most 4 operations per `(i, j, d)`. -/
noncomputable def santaClaus (ε : ℝ) (I : SCInstance m D n) (lp : LPSolver) (rnd : Rounding) :
    Prog (Option (Assignment m n)) := do
  let ϵ ← opn 1 (ε / 2)
  let ξ ← opn 1 (ϵ / 2)
  let r ← opn 8 (calib ϵ m D)
  let δ ← opn (r + 1) ((1 / 2 : ℝ) ^ r)
  tick (11 * (n + 1) * (m + 1) * (D + 1))
  tick (4 * (n + 1) * (n + 1) * (m + 1) * (D + 1))
  let T := numTypes I ϵ δ
  let NG := nGrid ξ r n
  tick (r + 6 + 3 * NG.length)
  let SC := sChoices I ϵ δ
  tick (3 * ((m + 1) * (D + 1) * (T + 1) * ((sGrid ϵ T).length + 1)) + 6)
  foldProd (List.replicate (m * T) NG) (fun (b : Option (Assignment m n)) gN =>
    foldProd SC (fun (b : Option (Assignment m n)) gS =>
      match b with
      | some X => pure (some X)
      | none => do
        let P := mkLP I ϵ δ ξ (fun i t => (nAt gN i t).1) (fun i t => (nAt gN i t).2)
          (fun i d t => sAt gS i d t)
        match ← callLP lp P with
        | none => pure none
        | some y => do
          let X : Assignment m n ← callRnd rnd P y
          tick (4 * (m + 1) * (n + 1) * (D + 1))
          pure (if check I (1 - ε) X then some X else none)) b) none

end FreeOrderEPTAS


