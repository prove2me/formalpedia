-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_iidProb
-- name    : RouzeFranca_LearnGibbs_iidProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:41.992305+00:00
-- url     : https://prove2.me/theorems/be06c87d-dcff-42da-89c2-f4f18ff7bcad
-- title:
--   Single-copy POVMs, Born probabilities and the law of $N$ independent measurements
-- statement:
--   1. A **POVM** with $K$ outcomes on $n$ qubits is a family $M_1,\dots,M_K$ of positive semidefinite operators with $\sum_x M_x=I$.
--   2. Applying $M$ to a state $\rho$ produces outcome $x$ with the **Born probability** $p_\rho(x)=\operatorname{tr}[M_x\rho]$.
--   3. Applying $M$ independently to each of $N$ copies of $\rho$ produces outcomes $x=(x_1,\dots,x_N)$; the probability of an event $P$ is
--   $$
--   \Pr_{\rho,N}[P]=\sum_{x\,:\,P(x)}\ \prod_{j=1}^N\operatorname{tr}[M_{x_j}\rho].
--   $$
--
--   This is the sampling model of the learning theorems: a learner measures each copy of the unknown state with one fixed measurement (randomized measurements such as random Pauli bases are included, the random choice being part of the outcome) and then computes an estimate from the $N$ outcomes.
--
--   **Formalization Note** A finite sum, with no measure theory. Joint measurements on $\rho^{\otimes N}$ are not part of this model. Born probabilities are real parts of traces.
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, App. C, p. 26

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs

open Matrix
open scoped ComplexOrder

namespace RouzeFranca.LearnGibbs

/-- A POVM with `K` outcomes on `n` qubits: positive semidefinite effects summing to the
identity.

Rouzé, Stilck França, arXiv:2107.03333v4, App. C, p. 26 (measurements on copies of `σ(λ)`, "by
measuring in 1-qubit random bases").

**Formalization Note.** Any single-copy measurement, including randomized ones (the random
choice of basis is part of the outcome). -/
def IsPOVM {n K : ℕ} (M : Fin K → Mat n) : Prop :=
  (∀ x, (M x).PosSemidef) ∧ ∑ x, M x = 1

/-- The Born-rule probability `tr[M_x ρ]` of outcome `x` when the POVM `M` is applied to `ρ`.

Rouzé, Stilck França, arXiv:2107.03333v4, App. C, p. 26. Real part of the trace, which is real
and in `[0, 1]` for a POVM and a state. -/
noncomputable def bornProb {n K : ℕ} (M : Fin K → Mat n) (ρ : Mat n) (x : Fin K) : ℝ :=
  (trace (M x * ρ)).re

open Classical in
/-- The probability of the event `P` on the outcomes `x = (x₁, …, x_N)` when the single-copy POVM
`M` is applied independently to each of `N` copies of `ρ`:
`∑_{x : P x} ∏_j tr[M_{x_j} ρ]`.

Rouzé, Stilck França, arXiv:2107.03333v4, App. C, p. 26 ("using O(4^k log(mδ^{-1})ϵ^{-2}) copies
of σ(λ)"; Theorem C.1 (Fast learning of Gibbs states), "samples of σ(λ) are sufficient").

**Formalization Note.** A finite sum: no measure theory. The outcomes of the `N` copies are
i.i.d. with the Born law; joint (entangled) measurements on `ρ^{⊗N}` are not modelled. -/
noncomputable def iidProb {n K : ℕ} (M : Fin K → Mat n) (ρ : Mat n) (N : ℕ)
    (P : (Fin N → Fin K) → Prop) : ℝ :=
  ∑ x : Fin N → Fin K, (∏ j, bornProb M ρ (x j)) * (if P x then 1 else 0)

end RouzeFranca.LearnGibbs


