-- Prove2me | Definitions.Def_CommThresholdPR_StrongConverse_FiniteInfo
-- name    : CommThresholdPR_StrongConverse_FiniteInfo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:35.479367+00:00
-- url     : https://prove2.me/theorems/12296c9f-e266-4274-82bd-0c2b02d7a732
-- title:
--   Finite probability, conditioning, entropy, information and divergence
-- statement:
--   For a probability law $P$ on a finite carrier, $P(E)$ is the sum of its masses on $E$. Conditioning filters and renormalizes a positive-probability event; at a null event the original law is the arbitrary normalized fallback. Shannon entropy, conditional entropy and conditional mutual information use base-two logarithms, with $0\log 0=0$.
--
--   The divergence retains its extended value and total variation is half the sum of absolute mass differences:
--   $$D(Q\|P)=\sum_z Q(z)\log_2\frac{Q(z)}{P(z)},\qquad \operatorname{TV}(Q,P)=\frac12\sum_z|Q(z)-P(z)|.$$
--   A positive $Q$ mass against zero $P$ mass gives $+\infty$. The input/output record and the local-output-factorization predicate are shared interfaces, not hypotheses about all laws. Binary entropy uses the published Wilde definition. These finite quantities are reusable independently of communication protocols.
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), §§2.3–2.4, pp. 8–9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

noncomputable section

namespace CommThresholdPR.StrongConverse
open scoped BigOperators

/-- Finite-law probabilities and information, in bits (§2.3, pp. 8–9).
Conditioning on a null event returns the original law; it is never used as a
positive-probability conditional row. No full-support assumption is imposed. -/
def prob {Ω : Type} [Fintype Ω] (p : PMF Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ z, if E z then (p z).toReal else 0

def condition {Ω : Type} (p : PMF Ω) (E : Ω → Prop) : PMF Ω := by
  classical
  exact if h : ∃ z, E z ∧ z ∈ p.support then p.filter {z | E z} h else p

def cprob {Ω : Type} [Fintype Ω] (p : PMF Ω) (E C : Ω → Prop) : ℝ :=
  prob p (fun z => E z ∧ C z) / prob p C

def entropy {Ω Z : Type} [Fintype Z] (p : PMF Ω) (f : Ω → Z) : ℝ :=
  -∑ z, ((p.map f) z).toReal * Real.logb 2 (((p.map f) z).toReal)

def condEntropy {Ω Z W : Type} [Fintype Z] [Fintype W]
    (p : PMF Ω) (f : Ω → Z) (w : Ω → W) : ℝ :=
  entropy p (fun z => (f z, w z)) - entropy p w

def cmi {Ω X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (p : PMF Ω) (x : Ω → X) (y : Ω → Y) (z : Ω → Z) : ℝ :=
  condEntropy p x z - condEntropy p x (fun a => (z a, y a))

def tv {Ω : Type} [Fintype Ω] (p q : PMF Ω) : ℝ :=
  (∑ z, |(p z).toReal - (q z).toReal|) / 2

/-- The extended value is retained at every support mismatch. -/
def divergence {Ω : Type} [Fintype Ω] (q p : PMF Ω) : EReal := by
  classical
  exact if ∃ z, q z ≠ 0 ∧ p z = 0 then ⊤ else
    ((∑ z, (q z).toReal * Real.logb 2 ((q z).toReal / (p z).toReal) : ℝ) : EReal)

/-- An input/output law with a finite auxiliary variable. -/
structure Record (X Y A B V : Type) where
  x : X
  y : Y
  a : A
  b : B
  v : V
  deriving Fintype

def localOutputs {X Y A B V : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] [Fintype V] (p : PMF (Record X Y A B V)) : Prop :=
  ∀ x y v, 0 < prob p (fun z => z.x = x ∧ z.y = y ∧ z.v = v) →
    ∀ a b, cprob p (fun z => z.a = a ∧ z.b = b)
      (fun z => z.x = x ∧ z.y = y ∧ z.v = v) =
    cprob p (fun z => z.a = a) (fun z => z.x = x ∧ z.v = v) *
    cprob p (fun z => z.b = b) (fun z => z.y = y ∧ z.v = v)

def infoSum {X Y A B V : Type} [Fintype X] [Fintype Y]
    [Fintype V] (p : PMF (Record X Y A B V)) : ℝ :=
  cmi p Record.x Record.v Record.y + cmi p Record.y Record.v Record.x

end CommThresholdPR.StrongConverse


