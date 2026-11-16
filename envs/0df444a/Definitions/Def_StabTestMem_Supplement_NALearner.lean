-- Prove2me | Definitions.Def_StabTestMem_Supplement_NALearner
-- name    : StabTestMem_Supplement_NALearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:39:36.164131+00:00
-- url     : https://prove2.me/theorems/e93016d4-e48d-45e1-b068-ed64bb6864c3
-- title:
--   Non-adaptive learners with precommitted randomness
-- statement:
--   A **non-adaptive learner** with $k$ qubits of memory and $t$ copies, with outputs in a set $\mathcal O$, consists of
--
--   1. a finite probability distribution $\mu$ on seeds $r$ (the random choices, such as random Clifford branches, made before any copy is touched);
--   2. for each seed $r$, a non-adaptive protocol $P_r$ with $k$ qubits of memory and $t$ rounds;
--   3. for each seed $r$, a post-processing map $\mathrm{out}_r$ from complete transcripts to $\mathcal O$.
--
--   When every copy is $\rho$, the probability that the output lies in a set $E\subseteq\mathcal O$ is
--   $$\Pr_{L,\rho}[\mathrm{out}\in E]=\sum_r\mu(r)\,\Pr_{P_r,\rho}\big[\{x:\mathrm{out}_r(x)\in E\}\big].$$
--
--   This is the class of learners of Theorems 1.2 and 6.6. The paper's protocol precommits to random Cliffords and applies the same Clifford to every copy of a branch; with a single history-independent protocol that shared choice could not be made, so the seed is part of the learner. A fixed deterministic schedule is the case of a single seed.
--
--   **Formalization Note** Seeds are indexed by `Fin m`; the protocols are the published `StabTestMem.MemProtocol` with `StabTestMem.Supplement.IsNonAdaptive`.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §6.1, pp. 52 and 55; Theorem 1.2, p. 5; Theorem 6.6, p. 56

import Definitions.Def_StabTestMem_Supplement_IsNonAdaptive
import Definitions.Def_StabTestMem_Supplement_eventProb

namespace StabTestMem.Supplement

open QAlgorithms

/-- **A non-adaptive learner with `k` qubits of memory, `t` copies and precommitted randomness.**
Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*,
arXiv:2607.02444 (version of 2 Nov 2026), §6.1, pp. 52 and 55: "We precommit to R = O(log(1/δ))
independent uniformly random Cliffords C_1, …, C_R … The learner need not know during the
measurement stage which branch succeeds: it runs the same precommitted schedule for every branch,
and selects a successful branch later by classical postprocessing"; "All Clifford choices and all
measurements are fixed before any outcomes are observed"; Theorems 1.2 (p. 5) and 6.6 (p. 56).

Fields:
* `m`, `μ`: a finite probability distribution on seeds `r : Fin m` (the precommitted random
  choices, drawn before any copy is touched);
* `P r`: for each seed a protocol of the published `StabTestMem.MemProtocol n k t X`
  (Definition 3.7) that is non-adaptive (`P_na`);
* `out r`: the classical post-processing, the output computed from the seed and the full
  transcript.

**Formalization Note.** A deterministic non-adaptive protocol is the case `m = 1`. The seed is
shared by all rounds; this is what lets the same random Clifford `C_j` act on every copy of
branch `j`, which a history-independent instrument cannot do on its own. -/
structure NALearner (n k t : ℕ) (X : Type) [Fintype X] (Out : Type) where
  /-- Number of seeds. -/
  m : ℕ
  /-- Law of the seed. -/
  μ : Fin m → ℝ
  μ_nonneg : ∀ r, 0 ≤ μ r
  μ_sum : ∑ r, μ r = 1
  /-- The protocol run under seed `r`. -/
  P : Fin m → MemProtocol n k t X
  P_na : ∀ r, IsNonAdaptive (P r)
  /-- The output under seed `r` and transcript `x`. -/
  out : Fin m → (Fin t → X) → Out

namespace NALearner

variable {n k t : ℕ} {X : Type} [Fintype X] {Out : Type}

/-- **Probability that the output lies in `E`** when every copy is `ρ`:
`Σ_r μ(r) · Pr_{x ∼ P_r(ρ^{⊗t})}[out_r(x) ∈ E]`, with the transcript law of the published
`MemProtocol.weight` (Lemma 3.10, p. 23) through `StabTestMem.Supplement.eventProb`. -/
noncomputable def prob (L : NALearner n k t X Out) (ρ : Matrix (Qubits n) (Qubits n) ℂ)
    (E : Out → Prop) : ℝ :=
  ∑ r, L.μ r * eventProb (L.P r) ρ (fun x => E (L.out r x))

end NALearner

end StabTestMem.Supplement


