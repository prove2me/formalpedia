-- Prove2me | Definitions.Def_IncrementalER_Supplement_theorem51Spec
-- name    : IncrementalER_Supplement_theorem51Spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:49:19.164638+00:00
-- url     : https://prove2.me/theorems/7fc17fcb-dfb1-447a-b6c6-f34388864cc2
-- title:
--   Adaptive leverage-degree oracle interface (Theorem 5.1)
-- statement:
--   This definition formalizes preprocessing and online leverage-degree queries on the randomized exact-real RAM. A query consists of a vertex $v$ and a membership-oracle pointer for a terminal set $U$ with $S_0\subseteq U$ and $v\in U\setminus S_0$; the pointer is represented by random-access membership bits, so every membership read and every other instruction is charged.
--
--   An adaptive strategy may choose each query from the full preceding query-answer transcript. One event covers all polynomially many queries and requires the one-sided estimate
--   $$
--   \ell_U^G(v)\le\widehat\ell_U^G(v)\le(1+\varepsilon)\ell_U^G(v),
--   $$
--   together with the separate initialization and per-query work bounds.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 5.1, p.29

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem21Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-!
# Adaptive membership-oracle interface for Theorem 5.1

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, STOC 2027 submission
(manuscript sha256 a0415fd5…), Theorem 5.1, p.29.
-/

abbrev LeverageQuery (n : ℕ) := Fin n × Finset (Fin n)
abbrev LeverageTranscript (n : ℕ) := List (LeverageQuery n × ℝ)
abbrev AdaptiveQueryStrategy (n : ℕ) := LeverageTranscript n → LeverageQuery n

/-- An adversary always supplies a legal membership-oracle query. -/
def ValidAdaptiveStrategy {n : ℕ} (S₀ : Finset (Fin n))
    (A : AdaptiveQueryStrategy n) : Prop :=
  ∀ tr, S₀ ⊆ (A tr).2 ∧ (A tr).1 ∈ (A tr).2 \ S₀

/-- Preprocessing input contains the graph, `k`, `epsilon`, and the common hitting set `S₀`. -/
noncomputable def oraclePreRun (Pre : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k epsilon : ℝ) (S₀ : Finset (Fin n))
    (fuel : ℕ) (omega : ℕ → Bool) : PNormReg.State :=
  let words : List ℤ := [4, (n : ℤ), (S₀.card : ℤ)] ++
    S₀.toList.map fun v => ((v : ℕ) : ℤ)
  PNormReg.run Pre (loadWords (graphState N es k) words [epsilon, k]) omega fuel

/-- Query layout for the membership-oracle pointer: after the tag, `n` and `v`, the next `n`
integer cells are the characteristic function of `U`.  A membership call is therefore an indirect
integer-memory load and is charged one machine instruction. -/
noncomputable def leverageQueryState {n : ℕ} (s : PNormReg.State)
    (q : LeverageQuery n) : PNormReg.State :=
  loadWords s
    ([5, (n : ℤ), (((q.1 : Fin n) : ℕ) : ℤ)] ++
      (List.ofFn fun v : Fin n => if v ∈ q.2 then (1 : ℤ) else 0)) []

/-- The one-sided leverage estimate is returned in real cell `-100`. -/
noncomputable def leverageAnswer (s : PNormReg.State) : ℝ := s.core.mem (-100)

/-- Run `t` adaptively selected queries after preprocessing.  The strategy sees the full preceding
query/answer transcript but never the current or future random bits. -/
noncomputable def adaptiveOracleRun (Pre Qry : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k epsilon : ℝ) (S₀ : Finset (Fin n))
    (A : AdaptiveQueryStrategy n) (preFuel queryFuel : ℕ) (omega : ℕ → Bool) :
    (t : ℕ) → PNormReg.State × LeverageTranscript n
  | 0 => (oraclePreRun Pre N es k epsilon S₀ preFuel omega, [])
  | t + 1 =>
      let prev := adaptiveOracleRun Pre Qry N es k epsilon S₀ A preFuel queryFuel omega t
      let q := A prev.2
      let st := PNormReg.run Qry (leverageQueryState prev.1 q) omega queryFuel
      (st, prev.2 ++ [(q, leverageAnswer st)])

/-- Work spent by adaptive query `j`, excluding preprocessing and all earlier queries. -/
noncomputable def adaptiveQueryWork (Pre Qry : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k epsilon : ℝ) (S₀ : Finset (Fin n))
    (A : AdaptiveQueryStrategy n) (preFuel queryFuel : ℕ) (omega : ℕ → Bool) (j : ℕ) : ℕ :=
  (adaptiveOracleRun Pre Qry N es k epsilon S₀ A preFuel queryFuel omega (j + 1)).1.work -
    (adaptiveOracleRun Pre Qry N es k epsilon S₀ A preFuel queryFuel omega j).1.work

/-- Full specification of Theorem 5.1.  `k` and `epsilon` remain inputs.  One probability event
covers every query of every legal adaptive strategy of polynomial length. -/
def theorem51Spec (Pre Qry : PNormReg.Program) (C : ℝ) (r p : ℕ) (c kappa : ℝ) : Prop :=
  PNormReg.Admissible Pre ∧ PNormReg.Admissible Qry ∧ 0 < C ∧
  ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, 1 ≤ n → n ≤ N →
    ∀ es : List (IncrementalER.Edge n), ValidGraph es →
    QuasiPolyCapacity C r N es → ∀ k : ℝ, 1 < k →
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
    ∀ S₀ : Finset (Fin n), IsKHittingSet (edgeCond es) S₀ k C r N →
      (S₀.card : ℝ) ≤ softBound C r N (es.length / k) →
      let preWork := softBound C r N (es.length * (1 + k + epsilon⁻¹) ^ p)
      let queryWork := softBound C r N ((1 + k + epsilon⁻¹) ^ p)
      let preFuel := ⌊preWork⌋₊
      let queryFuel := ⌊queryWork⌋₊
      ∀ qcount : ℕ, (qcount : ℝ) ≤ (N : ℝ) ^ kappa →
      ∀ A : AdaptiveQueryStrategy n, ValidAdaptiveStrategy S₀ A →
        PNormReg.coinTape {omega |
          let pre := (adaptiveOracleRun Pre Qry N es k epsilon S₀ A preFuel queryFuel omega 0).1
          ¬ (pre.halted = true ∧ (pre.work : ℝ) ≤ preWork ∧
            ∀ j < qcount,
              let prev := adaptiveOracleRun Pre Qry N es k epsilon S₀ A preFuel queryFuel omega j
              let next := adaptiveOracleRun Pre Qry N es k epsilon S₀ A preFuel queryFuel omega (j + 1)
              let q := A prev.2
              next.1.halted = true ∧ (adaptiveQueryWork Pre Qry N es k epsilon S₀ A
                preFuel queryFuel omega j : ℝ) ≤ queryWork ∧
              IncrementalER.levDegT (edgeCond es) q.2 q.1 ≤ leverageAnswer next.1 ∧
              leverageAnswer next.1 ≤
                (1 + epsilon) * IncrementalER.levDegT (edgeCond es) q.2 q.1)} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-c))

end IncrementalER.Supplement


