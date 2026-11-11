-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_DenseCSP
-- name    : QuantumSepPoly_Frobenius_DenseCSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:29.457727+00:00
-- url     : https://prove2.me/theorems/f52fa6a8-c7ac-4396-b597-0b2bee873329
-- title:
--   Ordered Max-k-CSP instances with repeated indices
-- statement:
--   An instance consists of $n$ variables over a finite nonempty alphabet, a nonempty finite set $C\subseteq[n]^k$ of ordered constraints, and a real table $P_t$ for each tuple. Predicate range in $[0,1]$ is a separate property. Repeated indices are allowed.
--   $$\operatorname{val}_I(z)=|C|^{-1}\sum_{t\in C}P_t(z_{t_1},\ldots,z_{t_k}),\qquad\operatorname{OPT}(I)=\max_z\operatorname{val}_I(z).$$
--   Density means $C=[n]^k$. A real supremum represents the finite attained maximum on every theorem's nonempty alphabet. The separate range property lets the reduction prove its predicate bounds rather than assuming them.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 18 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Mathlib

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- Definition 5.1, p.18: ordered constraints, including all repeated indices.
The payoff bound is a separate predicate, so construction correctness is not assumed. -/
structure MaxCSP (n k : ℕ) (Ω : Type*) where
  constraints : Finset (Fin k → Fin n)
  nonempty : constraints.Nonempty
  predicate : (Fin k → Fin n) → (Fin k → Ω) → ℝ

def CSPBounded {n k : ℕ} {Ω : Type*} (I : MaxCSP n k Ω) : Prop :=
  ∀ t ∈ I.constraints, ∀ z, I.predicate t z ∈ Set.Icc (0 : ℝ) 1

def CSPDense {n k : ℕ} {Ω : Type*} (I : MaxCSP n k Ω) : Prop :=
  I.constraints = Finset.univ

def cspValue {n k : ℕ} {Ω : Type*} (I : MaxCSP n k Ω) (z : Fin n → Ω) : ℝ :=
  (∑ t ∈ I.constraints, I.predicate t (fun i => z (t i))) / I.constraints.card

def cspOPT {n k : ℕ} {Ω : Type*} (I : MaxCSP n k Ω) : ℝ :=
  sSup (Set.range (cspValue I))

end QuantumSepPoly.Frobenius


