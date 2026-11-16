-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_WidthMachine
-- name    : IntervalMaxCutEPTAS_Scheme_Supplement_WidthMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:13.399454+00:00
-- url     : https://prove2.me/theorems/19973502-d3f9-41ab-906f-65dc79f7b73d
-- title:
--   Accuracy, explicit width and costed sparsification output
-- statement:
--   The accuracy exponent and the expression width in the proof of Theorem 1.2 are fixed by
--
--   $$b(\varepsilon)=\lceil\log_2(28/\varepsilon)\rceil,\qquad W(b)=3(20b2^b+1)^2+(b+1)(2^{b+1}+1)^2+1.$$
--
--   A sparse interval output is a spanning subgraph on the original vertex set, admits a real interval representation and loses at most $\varepsilon m$ original edges. Lemma 6.3 receives $n,b,K,J$ followed by the published serialization of the supplied structure. Theorem 1.2 receives the published representation-and-accuracy input. Its output includes the actual edited graph for a ranking of the input with a good shift, and the width-$W(b)$ expression for that same graph in the fixed packet format. Time and space are conclusions of the theorems, not assumed fields of a model. These definitions separate correctness from the execution semantics supplied by Light.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §6.2–§6.3, PDF p. 25 (printed p. 24)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Endpoints
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Expressions

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

open Classical

/-- The exact width supplied by §6.3, with 1/σ = 2^b. -/
def explicitWidth (b : ℕ) : ℕ :=
  3 * (20 * b * 2 ^ b + 1) ^ 2 + (b + 1) * (2 ^ (b + 1) + 1) ^ 2 + 1

noncomputable def accuracyExponent (ε : ℝ) : ℕ := ⌈Real.logb 2 (28 / ε)⌉₊

def IsInterval {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ I : Rep ℝ n, I.graph = G

/-- Loss is relative to the original m, on the same vertex set. -/
def SparseInterval {n : ℕ} (I : Rep ℝ n) (ε : ℝ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  G ≤ I.graph ∧ IsInterval G ∧
    (((I.graph.edgeFinset \ G.edgeFinset).card : ℕ) : ℝ) ≤ ε * I.graph.edgeFinset.card

/-- Lemma 6.3 receives the supplied structure, including rank endpoints and fixed shift only
through the already published structList layout. -/
noncomputable def encodeExpression {n : ℕ} (P : Setup n) (K J : ℕ) : List ℤ :=
  [(n : ℤ), (P.b : ℤ), (K : ℤ), (J : ℤ)] ++ structList P

/-- Theorem 1.2 returns the actual H of a valid rank construction of the input, and an expression
for that very H. The real-accuracy existence clause is stated separately in the theorem. -/
def ReportsSparse {n : ℕ} (I : Rep ℝ n) (ε : ℝ) (S : ℕ)
    (s : Light.State) : Prop :=
  ∃ (ρ : RankRep n) (θ : ℕ),
    IsRankingOf I ρ ∧ θ < 2 * bigM n ∧
    let P : Setup n := ⟨ρ, accuracyExponent ε, θ⟩
    GoodShift P ∧ SparseInterval I ε (H P) ∧
      ReportsExpression (H P) (explicitWidth P.b) S s

end IntervalMaxCutEPTAS.Scheme.Supplement


