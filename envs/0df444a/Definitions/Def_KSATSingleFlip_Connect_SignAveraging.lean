-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_SignAveraging
-- name    : KSATSingleFlip_Connect_SignAveraging
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T06:18:35.992204+00:00
-- url     : https://prove2.me/theorems/21422ed1-bceb-4ed2-b00a-228a22e58703
-- title:
--   Fixed-scope clauses and sign averaging
-- statement:
--   Fixed-scope signed clauses, the appended formula, the event that each clause forces a designated variable, agreement on a boundary, and uniform solution mass conditioned on boundary agreement. Each clause uses an independently sampled uniform sign function; unused signs do not change its law.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, Lemma 3.4, printed p. 16 (PDF p. 18), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

noncomputable section
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-! Literal-sign resampling for Lemma 3.4 of Wang, Yin, Yu and Zhang,
STOC 2027 submission #737, printed p. 16. -/

/-- A signed clause with a fixed variable scope. Signs outside the scope are
ignored, so a uniform full sign function induces independent uniform signs on
the specified scope. -/
def scopedSignedClause {n : ℕ} (scope : Finset (Fin n)) (sign : Fin n → Bool) : GClause (Fin n) :=
  fun v => if v ∈ scope then some (sign v) else none

/-- The formula obtained by appending the resampled clauses in their order. -/
def signExtendedFormula {n r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (signs : Fin r → Fin n → Bool) : GFormula (Fin n) :=
  Φ0 ++ List.ofFn (fun i => scopedSignedClause (scopes i) (signs i))

/-- Assignments for which each resampled clause forces its designated variable. -/
def allResampledClausesForce {n r : ℕ} (scopes : Fin r → Finset (Fin n))
    (signs : Fin r → Fin n → Bool) (designated : Fin r → Fin n) (σ : Fin n → Bool) : Prop :=
  ∀ i, Forces σ (scopedSignedClause (scopes i) (signs i)) (designated i)

/-- Agreement with a prescribed assignment on a finite set of variables. -/
def agreesOn {n : ℕ} (B : Finset (Fin n)) (τ σ : Fin n → Bool) : Prop :=
  ∀ v ∈ B, σ v = τ v

/-- The uniform solution mass of A conditioned on agreement with τ on B.
The denominator is nonzero under the hypothesis of Lemma 3.4. -/
def conditionalSolutionMass {n : ℕ} (Φ : GFormula (Fin n)) (A : Finset (Fin n → Bool))
    (B : Finset (Fin n)) (τ : Fin n → Bool) : ℝ :=
  (((sols Φ ∩ A).filter (agreesOn B τ)).card : ℝ) /
    (((sols Φ).filter (agreesOn B τ)).card : ℝ)

end KSATSingleFlip.Connect


