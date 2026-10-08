-- Prove2me | Definitions.Def_CompOT_EntropicLimit_Defs
-- name    : CompOT_EntropicLimit_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:08.24098+00:00
-- url     : https://prove2.me/theorems/b2ed4a3d-789f-4df8-8bb4-7a4b1e0db120
-- title:
--   (2.10), (2.11), (4.1), (4.2), (4.3), (4.6), pp. 370–428 — couplings, entropy H(P), the entropic problem, max-entropy optimal plans, Gibbs kernel and KL
-- statement:
--   Fix sizes $n, m$ and index rows by $i \in \{1,\dots,n\}$, columns by $j \in \{1,\dots,m\}$. For vectors $a \in \mathbb R^n$, $b \in \mathbb R^m$ and a cost matrix $C \in \mathbb R^{n\times m}$ this file defines the entropic objects of §4.1 of Peyré–Cuturi, using the coupling and cost objects supplied by the shared Assignment definitions.
--
--   1. **Couplings** (2.10): $U(a,b) = \{P \in \mathbb R_+^{n\times m} : P\mathbb 1_m = a,\ P^\top \mathbb 1_n = b\}$, the nonnegative matrices with row sums $a$ and column sums $b$.
--   2. **Frobenius pairing**: $\langle C, P\rangle = \sum_{i,j} C_{i,j}P_{i,j}$.
--   3. **Optimal coupling** for the Kantorovich problem (2.11): $P \in U(a,b)$ with $\langle C,P\rangle \le \langle C,Q\rangle$ for every $Q \in U(a,b)$; its cost is $L_C(a,b)$.
--   4. **Discrete entropy** (4.1):
--   $$\mathbf H(P) = -\sum_{i,j} P_{i,j}\big(\log P_{i,j} - 1\big),$$
--   with $0\log 0 = 0$.
--   5. **Entropic objective** (4.2): $\langle C,P\rangle - \varepsilon \mathbf H(P)$, and **entropic optimality**: $P \in U(a,b)$ minimizes this objective over $U(a,b)$; the minimum value is $L^\varepsilon_C(a,b)$.
--   6. **Maximal-entropy optimal coupling** (4.3): an optimal coupling of (2.11) whose entropy is at least that of every other optimal coupling, i.e. a minimizer of $-\mathbf H$ over the optimal set.
--   7. **Gibbs kernel**: $K_{i,j} = e^{-C_{i,j}/\varepsilon}$.
--   8. **Kullback–Leibler divergence between matrices** (4.6):
--   $$\mathrm{KL}(P\,|\,K) = \sum_{i,j} P_{i,j}\log\frac{P_{i,j}}{K_{i,j}} - P_{i,j} + K_{i,j}.$$
--
--   These are the objects of the entropic regularization of discrete optimal transport and are used by every statement of this mission.
--
--   **Formalization Note** Indices are 0-based (`Fin n`). The book states the convention $\mathbf H(a) = -\infty$ when an entry is $0$ or negative; it is not used: entries equal to $0$ contribute $0$ (via `Real.negMulLog`), which is what the continuity of $\mathbf H$ in the proof of Proposition 4.1 requires. Optimality is encoded as predicates (minimizer over $U(a,b)$) instead of a real infimum, so no junk value of an empty infimum enters. In $\mathrm{KL}$ a term with $P_{i,j}=0$ contributes $K_{i,j}$; $\mathrm{KL}$ is only applied to couplings and the positive Gibbs kernel.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (2.10)–(2.11), pp. 370–371; (4.1)–(4.3), pp. 425–426; (4.6) and Gibbs kernel, p. 428

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.EntropicLimit

/-- The discrete entropy (4.1), `H(P) = -∑_{i,j} P_{i,j}(log P_{i,j} - 1)`, with the
convention `0 log 0 = 0` (`Real.negMulLog x = -x log x`). -/
noncomputable def entropy {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, (Real.negMulLog (P i j) + P i j)

/-- The objective of the entropic problem (4.2): `⟨P,C⟩ - ε H(P)`. -/
noncomputable def entObjective {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  CompOT.Assignment.frob C P - ε * entropy P

/-- `P` is a minimizer of the entropic problem (4.2) over `U(a,b)`. -/
def IsEntropicOptimal {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  P ∈ CompOT.Assignment.couplings a b ∧ ∀ Q ∈ CompOT.Assignment.couplings a b, entObjective C ε P ≤ entObjective C ε Q

/-- `P` is a solution of (4.3): an optimal coupling of (2.11) whose entropy is maximal
among all optimal CompOT.Assignment.couplings (equivalently, a minimizer of `-H` over the optimal set). -/
def IsMaxEntropyOptimal {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  CompOT.Assignment.IsOptimalCoupling C a b P ∧ ∀ Q, CompOT.Assignment.IsOptimalCoupling C a b Q → entropy Q ≤ entropy P

/-- The Gibbs kernel `K_{i,j} = exp(-C_{i,j}/ε)` (p. 428). -/
noncomputable def gibbs {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => Real.exp (-C i j / ε)

/-- The Kullback–Leibler divergence between matrices (4.6),
`KL(P|K) = ∑_{i,j} P_{i,j} log(P_{i,j}/K_{i,j}) - P_{i,j} + K_{i,j}`
(a term with `P_{i,j} = 0` contributes `K_{i,j}`, i.e. `0 log 0 = 0`). -/
noncomputable def klMat {n m : ℕ} (P K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, (P i j * Real.log (P i j / K i j) - P i j + K i j)

end CompOT.EntropicLimit


