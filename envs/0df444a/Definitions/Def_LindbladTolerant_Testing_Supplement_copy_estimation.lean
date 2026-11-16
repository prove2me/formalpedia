-- Prove2me | Definitions.Def_LindbladTolerant_Testing_Supplement_copy_estimation
-- name    : LindbladTolerant_Testing_Supplement_copy_estimation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:12:46.451781+00:00
-- url     : https://prove2.me/theorems/7cb4d709-f9a3-441d-9133-222576ac1ce0
-- title:
--   Independent-copy input $\sigma^{\otimes N}$ and uniformly $\delta$-accurate copy estimators
-- statement:
--   This file fixes the access model for estimating the jump-state functional from independent copies (Section 4, Eq. (46), and Section 4.3).
--
--   1. **N-copy input.** For a finite index set $I$, a matrix $x$ on $I$ and an integer $N\ge0$, the matrix $x^{\otimes N}$ on $I^N$ has entries
--   $$
--   (x^{\otimes N})_{i,j}=\prod_{m=1}^{N}x_{i_m,j_m}.
--   $$
--   For $N=0$ the index set is the one-point set of empty tuples and $x^{\otimes0}$ is the scalar $1$. For a jump state $\sigma$ on system $\otimes$ reference this is the state of $N$ independent copies.
--
--   2. **Copy estimators.** An estimator that uses at most $N$ copies is a quantum instrument acting on the whole input $(SR)^{\otimes N}$, with a Borel real outcome $\hat h$ (the estimate) and any finite outcome-dependent quantum output. The probability that $\hat h$ lies in a Borel set $B$ on input $\rho$ is the Born probability $\int_B \operatorname{Tr}\mathcal M_o(\rho)\,d\mu(o)$ of the published instrument model. All ancillas, adaptive operations and collective measurements on the $N$ copies, together with internal randomness, are part of the instrument; unused copies are discarded by it.
--
--   3. **Uniform accuracy.** Fix $k$ and $\delta$. The instrument is *$\delta$-accurate with probability $2/3$ on the class* if for every $n$-qubit Lindblad generator $\mathcal L$ that admits a representation with traceless jump operators each supported on at most $k$ qubits, and whose canonical jump rate $\Gamma=\operatorname{Tr}C$ is positive (equivalently, whose canonical dissipator is nonzero), the jump state $\sigma=C/\Gamma$ satisfies
--   $$
--   \Pr\bigl[\,|\hat h-h(\sigma)|\le\delta\,\bigr]\ \ge\ \tfrac23\qquad\text{on input }\sigma^{\otimes N},
--   $$
--   where $h(\sigma)=\operatorname{Tr}(\sigma^2)+\tfrac12\bigl(d\operatorname{Tr}(\sigma_R^2)-1\bigr)$, $d=2^n$, is the jump-state functional of the base mission.
--
--   These objects state the copy lower bound (Theorem 4.5). The predicate is the estimator's success condition only; it says nothing about the number of copies.
--
--   **Formalization Note** The matrix model, Lindblad model, jump state, functional and quantum instruments are the published base definitions, reused unchanged. Probabilities are compared in $\mathbb R_{\ge0}^\infty$, as the instrument law is a measure.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, STOC 2027 submission #238 (October 2026), Optimal Tolerant Testing of Lindbladian Dissipation, SHA-256 d5f3c8d172d2da31a25deb28abf000f92655ed8e1a5a4c07bbd67d8676f759e8; p.18 (PDF p.18) Section 4, Eq. (46); p.24 (PDF p.24) Theorem 4.5; p.25 (PDF p.25) proof of Theorem 4.5 (N copies supplied at the start).

import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladTolerant_Testing_quantum_instruments

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Matrix

namespace LindbladTolerant.Testing.Supplement

open LindbladTolerant.Testing

/-- p.25: the N-copy input `x^{⊗N}` on `I^N`, entrywise the product of the N
one-copy entries. For `N = 0` the index type is the singleton empty tuple and
the matrix is the scalar `1`. No purity or density property is assumed. -/
def copies {I : Type*} (N : ℕ) (x : Op I) : Op (Fin N → I) :=
  fun i j => ∏ m, x (i m) (j m)

/-- p.18 Eq.(46), p.24: the fixed independent-copy estimator `a`, a quantum
instrument on the full N-copy input with an arbitrary Borel real outcome `ĥ`,
is δ-accurate with probability at least 2/3 on every jump state of a nonzero
canonical dissipator with locality at most `k` (positive canonical rate). The
probability is the actual Born law `instrumentLaw` of the instrument on
`σ^{⊗N}`. Nothing about the number of copies is assumed. -/
def CopyEstimates {n N : ℕ} {O : ℝ → Type} [∀ o, Fintype (O o)] [∀ o, DecidableEq (O o)]
    (k : ℕ) (delta : ℝ)
    (a : QuantumInstrument (Fin N → Qubits n × Qubits n) O) : Prop :=
  ∀ g : Super (Qubits n) (Qubits n), LocalGenerator k g → ∀ hp : 0 < rate g,
    (2/3 : ℝ≥0∞) ≤ instrumentLaw a (copies N (jumpState g hp))
      {h : ℝ | |h - functional (jumpState g hp)| ≤ delta}

end LindbladTolerant.Testing.Supplement


