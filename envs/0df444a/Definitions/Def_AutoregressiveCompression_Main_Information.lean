-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Information
-- name    : AutoregressiveCompression_Main_Information
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:27.412213+00:00
-- url     : https://prove2.me/theorems/f49988d7-1d49-4abd-868e-3e3fa40af642
-- title:
--   Finite probability, information quantities in bits, and independent samples
-- statement:
--   Let P and Q be probability mass functions on a finite set Ω. Their probabilities are arbitrary real numbers. This interface defines finite expectation, Shannon entropy in bits, total variation distance, cross entropy, KL divergence in bits, and conditional entropy. It also constructs the law of m independent observations, with the unique empty block at m = 0.
--
--   The entropy is the published finite Shannon entropy applied to the real masses of a Mathlib PMF. Total variation is one half of the sum of absolute mass differences. The information quantities satisfy the source formulas
--
--   $$H(P)=-\sum_xP(x)\log_2P(x),\qquad \operatorname{KL}_2(P\Vert Q)=\sum_xP(x)\log_2\frac{P(x)}{Q(x)}.$$
--
--   KL divergence and cross entropy are explicitly positive infinity when P assigns positive probability to an atom to which Q assigns zero probability. Zero-mass terms contribute zero. Conditional entropy is the marginal-weighted sum of fiber entropies; a zero-mass fiber contributes zero. No algorithm is given access to these probability tables by this interface.
--
--   These definitions establish mathematical semantics only. They do not define efficient learning, compression, estimation, or testing, and do not assert any of the paper's reductions.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Section 4.1, printed pp.14–15 / PDF pp.16–17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_FuchsVdGraaf_entropy

/-!
Finite-law semantics for Hirahara–Nanashima, STOC 2027 submission #793
(October 2026), §4.1, printed pp.14–15 / PDF pp.16–17.

This file is foundational work only: it defines no computational task and asserts
no reduction. Probability laws are Mathlib PMFs, with unrestricted real masses.
-/

noncomputable section

namespace AutoregressiveCompression.Main

open scoped BigOperators Classical

/-- The real mass of a PMF. PMF masses are finite, so this loses no infinity. -/
def mass {Ω : Type} (P : PMF Ω) (x : Ω) : ℝ := (P x).toReal

/-- Finite expectation; no Bochner integral default is involved. -/
def expectation {Ω : Type} [Fintype Ω] (P : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, mass P x * f x

/-- Shannon entropy in bits, using the published general entropy definition. -/
def entropy {Ω : Type} [Fintype Ω] (P : PMF Ω) : ℝ :=
  FuchsVdGraaf.entropy (mass P)

/-- Statistical distance, with the source's factor one half. -/
def totalVariation {Ω : Type} [Fintype Ω] (P Q : PMF Ω) : ℝ :=
  (∑ x, |mass P x - mass Q x|) / 2

/-- KL in bits. A missing positive-mass target atom gives genuine positive
infinity, before any real division or logarithm is evaluated. Individual finite
summands can be negative; they are summed in ℝ before embedding into EReal. -/
def klBits {Ω : Type} [Fintype Ω] (P Q : PMF Ω) : EReal :=
  if ∃ x, P x ≠ 0 ∧ Q x = 0 then ⊤
  else ((∑ x, if P x = 0 then 0
    else mass P x * Real.logb 2 (mass P x / mass Q x) : ℝ) : EReal)

/-- Cross entropy in bits, with the same explicit support-mismatch branch. -/
def crossEntropy {Ω : Type} [Fintype Ω] (P Q : PMF Ω) : EReal :=
  if ∃ x, P x ≠ 0 ∧ Q x = 0 then ⊤
  else ((∑ x, if P x = 0 then 0
    else mass P x * Real.logb 2 (1 / mass Q x) : ℝ) : EReal)

/-- Exactly m independent samples, including the unique empty block. -/
def iid {Ω : Type} (P : PMF Ω) : (m : ℕ) → PMF (Fin m → Ω)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | m + 1 => P.bind fun x => (iid P m).map (Fin.cons x)

/-- Probability of an event on a finite space. -/
def eventProbability {Ω : Type} [Fintype Ω] (P : PMF Ω)
    (A : Ω → Prop) : ℝ :=
  expectation P (fun x => if A x then 1 else 0)

/-- Conditional entropy as marginal-weighted fiber entropy. The zero-mass
fibers contribute zero without normalizing the zero measure. -/
def conditionalEntropy {S A : Type} [Fintype S] [Fintype A]
    (P : PMF (S × A)) : ℝ :=
  ∑ s, let w := ∑ a, mass P (s, a)
    if w = 0 then 0 else
      w * FuchsVdGraaf.entropy (fun a => mass P (s, a) / w)

end AutoregressiveCompression.Main


