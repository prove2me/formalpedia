-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Parameters
-- name    : QuantumSepPoly_Frobenius_Supplement_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:47:56.167088+00:00
-- url     : https://prove2.me/theorems/630ee487-3f0b-4035-9cea-fa0bf4b00c9d
-- title:
--   Reduction constants and sampling budget
-- statement:
--   For the source constant query bound $q$ and expander degree $c$, set
--   $$|\Omega|=2^q,\quad\delta=\max(q,c+1),\quad\xi=\frac1{4cq(c+1)},\quad\beta=\frac{\xi^4}{100\cdot2^{90}|\Omega|^{12}\delta^8}.$$
--   Admissible fixed choices have $t\ge1$, rational $\varepsilon>0$ and $(1-\beta)^t\le t\varepsilon\le(1-\eta)/4$. Define $k=\lceil\max(\sqrt N,64|\Omega|,4|\Omega|\log_2(1/\varepsilon))\rceil$, $s=\lceil(N|\Omega|)^{10k}\varepsilon^{-2}\rceil$, and the global cutoff $200s(N|\Omega|)^{4k}p$. These are computed formulas; no unspecified function named poly or soft-O is used as a time bound.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 26, 28–29 (PDF p. 26, 28–29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_CNF

noncomputable section

namespace QuantumSepPoly.Frobenius.Supplement
/-- Scalar parameters computed in §§6.1–6.2. -/
def alphabetSize (q : ℕ) : ℕ := 2^q
def degreeBound (q c : ℕ) : ℕ := max q (c+1)
def soundnessGap (q c : ℕ) : ℝ := 1/(4*(c : ℝ)*q*(c+1))
def blockGap (A δ : ℕ) (ξ : ℝ) : ℝ := ξ^4 / (100*2^90*(A : ℝ)^12*(δ : ℝ)^8)
def registerCount (N A : ℕ) (ε : ℚ) : ℕ :=
  Nat.ceil (max (Real.sqrt N) (max (64*(A : ℝ)) (4*(A : ℝ)*Real.logb 2 (1/(ε : ℝ)))))
def sampleCount (N A k : ℕ) (ε : ℚ) : ℕ :=
  Nat.ceil (((N*A : ℕ) : ℝ)^(10*k)*(ε : ℝ)^(-2 : ℤ))
def samplerBudget (N A k s : ℕ) (p : ℝ) : ℝ := 200*s*((N*A : ℕ) : ℝ)^(4*k)*p

def Admissible (η : ℝ) (A δ : ℕ) (ξ : ℝ) (t : ℕ) (ε : ℚ) : Prop :=
  1 ≤ t ∧ 0 < ε ∧ (1-blockGap A δ ξ)^t ≤ t*(ε : ℝ) ∧
    t*(ε : ℝ) ≤ (1-η)/4
end QuantumSepPoly.Frobenius.Supplement


