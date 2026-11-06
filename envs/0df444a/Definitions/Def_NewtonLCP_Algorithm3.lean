-- Prove2me | Definitions.Def_NewtonLCP_Algorithm3
-- name    : NewtonLCP_Algorithm3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:29.821619+00:00
-- url     : https://prove2.me/theorems/a41dec6f-3842-4e7c-9b0c-742c7c9d8631
-- title:
--   Algorithm 3 (full version) with Newton-solve and LP-call counters
-- statement:
--   Algorithm 3 takes rational $(M,q)$, constants $C_1,C_2$, a parameter choice $\beta,\delta$ obeying (54) and an LP oracle, and runs:
--
--   1. Call LPSolve on $Mx+q=s$, $x,s\ge0_n$; if infeasible, return "LCP$(M,q)$ is infeasible".
--   2. Set $\Delta=2^{C_1\,\mathrm{length}(M,q)}$, $T=2^{C_2\,n\,\mathrm{length}(M)}$, the embedded system $(\widehat M,\hat q)$ and the starting point $(\hat x^0,\hat s^0,\hat\mu^0)$ of (52).
--   3. For $\kappa=1,2,4,\dots$ while $\kappa\le T$: set $\mu_1=1/(16384n^3\Delta^2(\kappa+1)^2)$ and run FixedKappaNewton on the embedded system with $\beta_{2n}(\kappa),\delta_{2n}(\kappa)$. If it returns "$\widehat M\notin\mathcal P_\star$", return "$M\notin\mathcal P_\star$". If it returns a point $((x,\tilde x),(s,\tilde s),\mu)$, let $I=\{i:x_i\le\sqrt{2n\mu}\}$, $J=\{j:s_j\le\sqrt{2n\mu}\}$ and call LPSolve with these $I,J$; if it returns $(x',s')$, return it. Otherwise double $\kappa$.
--   4. Return "$M\notin\mathcal P_\star$".
--
--   The run reports its outcome together with the total number of Newton linear-system solves and of LP calls.
--
--   **Formalization Note** Data are cast to real numbers and all arithmetic is exact. The $\kappa$-loop visits $\kappa=2^j$, $j=0,\dots,C_2n\,\mathrm{length}(M)$. An exhausted inner fuel is passed on as a separate outcome; it does not occur for admissible parameters.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Algorithm 3, lines 15–31, p.32; §8.2, p.31

import Mathlib
import Definitions.Def_NewtonLCP_Encoding
import Definitions.Def_NewtonLCP_Embedding
import Definitions.Def_NewtonLCP_LPOracle
import Definitions.Def_NewtonLCP_FixedKappaNewton

open Matrix

namespace NewtonLCP

/-!
# Algorithm 3, with Newton-solve and LP-call counters

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Algorithm 3, lines 15–31, p.32; §8.2, p.31.

Line 15 calls `LPSolve(Mx + q = s, x, s ≥ 0ₙ)`; line 16 returns "Infeasible" if it is infeasible.
Line 17 sets `∆ = 2^{C₁ length(M, q)}`, line 18 `T = 2^{C₂ n length(M)}`, lines 19–20 the
embedded system `(M̂, q̂)` and the point `(x̂⁰, ŝ⁰, µ̂⁰)` of (52). Line 21 sets `κ = 1`; while
`κ ≤ T` (line 22): `µ₁ = 1/(16384n³∆²(κ+1)²)` (line 23); `R = FixedKappaNewton(M̂, q̂, x̂⁰, ŝ⁰,
µ̂⁰, µ₁, κ)` (line 24); if `R` is "`M̂ ∉ P⋆`" return "`M ∉ P⋆`" (line 25); if `R` is a point
`((x, x̃), (s, s̃), µ)` (line 26), `I = {i : xᵢ ≤ √(2nµ)}`, `J = {i : sᵢ ≤ √(2nµ)}` (line 27),
`U = LPSolve(Mx + q = s, x, s ≥ 0ₙ, x_I = 0_I, s_J = 0_J)` (line 28), and if `U = (x', s')`
return it (line 29); `κ ← 2κ` (line 30). Line 31 returns "`M ∉ P⋆`".

**Formalization Note.**
* Input `M, q` are rational and are cast to `ℝ`; all arithmetic is exact real arithmetic.
* `C₁, C₂` are the "appropriately chosen constants" of lines 17–18, and `β δ : ℕ → ℝ → ℝ` the
  parameter choice of (54); FixedKappaNewton on the `2n`-dimensional embedded system (index
  `Fin n ⊕ Fin n`) uses `β_{2n}(κ), δ_{2n}(κ)` (p.32, "`N²(β_{2n}(κ))`").
* The `κ`-loop visits `κ = 2ʲ` for `j = 0, 1, …`; `κ ≤ T = 2^{C₂ n length(M)}` iff
  `j ≤ C₂ n length(M)`, so the loop has at most `C₂ n length(M) + 1` rounds.
* `LPSolve` is an oracle `O : LPOracle n` for the fixed `(M, q)`.
* The result is `(outcome, solves, lps)`: `solves` adds the Newton solves of every
  FixedKappaNewton call, `lps` counts the oracle calls of lines 15 and 28. The algorithm never
  reads them.
* An exhausted inner fuel (never reached for valid parameters; see FixedKappaNewton) is passed
  on as `outOfFuel`.
-/

/-- Outcomes of Algorithm 3: a complementary solution `(x, s)`, "LCP(M, q) is infeasible",
"`M ∉ P⋆`", or an exhausted inner fuel. -/
inductive Out (n : ℕ) where
  | solution (x s : Fin n → ℝ)
  | infeasible
  | notPStar
  | outOfFuel

open Classical in
/-- The `κ`-loop of lines 21–31: `r` rounds left, current guess `κ = 2ʲ`, counters `sv`, `lp`. -/
noncomputable def a3Loop (n : ℕ) (β δ : ℕ → ℝ → ℝ) (O : LPOracle n)
    (M : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (Δ : ℝ) :
    ℕ → ℕ → ℕ → ℕ → Out n × ℕ × ℕ
  | 0, _, sv, lp => (Out.notPStar, sv, lp)
  | r + 1, j, sv, lp =>
    let κ : ℝ := 2 ^ j
    let mu1 : ℝ := 1 / (16384 * (n : ℝ) ^ 3 * Δ ^ 2 * (κ + 1) ^ 2)
    match fixedKappaNewton (embedM M) (embedQ M q Δ) (embedX0 M q Δ) (embedS0 M q Δ)
        (embedMu0 n Δ) mu1 (β (2 * n) κ) (δ (2 * n) κ) with
    | (FKOut.notPStar, c) => (Out.notPStar, sv + c, lp)
    | (FKOut.outOfFuel, c) => (Out.outOfFuel, sv + c, lp)
    | (FKOut.kappaTooSmall, c) => a3Loop n β δ O M q Δ r (j + 1) (sv + c) lp
    | (FKOut.point xh sh mu, c) =>
      let I := Finset.univ.filter (fun i => xh (Sum.inl i) ≤ Real.sqrt (2 * n * mu))
      let J := Finset.univ.filter (fun i => sh (Sum.inl i) ≤ Real.sqrt (2 * n * mu))
      match O I J with
      | some (x', s') => (Out.solution x' s', sv + c, lp + 1)
      | none => a3Loop n β δ O M q Δ r (j + 1) (sv + c) (lp + 1)

/-- Algorithm 3 on rational input `(M, q)` with constants `C₁, C₂`, parameter choice `β, δ`
and LP oracle `O`: returns `(outcome, Newton solves, LP calls)`. -/
noncomputable def algorithm3 (C₁ C₂ : ℕ) (β δ : ℕ → ℝ → ℝ) {n : ℕ} (O : LPOracle n)
    (M : Matrix (Fin n) (Fin n) ℚ) (q : Fin n → ℚ) : Out n × ℕ × ℕ :=
  match O ∅ ∅ with
  | none => (Out.infeasible, 0, 1)
  | some _ =>
    a3Loop n β δ O (M.map ((↑) : ℚ → ℝ)) (fun i => (q i : ℝ)) ((2 : ℝ) ^ (C₁ * encLen M q))
      (C₂ * n * encLenM M + 1) 0 0 1

end NewtonLCP


