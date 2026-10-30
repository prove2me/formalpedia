-- Prove2me | Definitions.Def_BBPSSW_Distill_AchievableRate
-- name    : BBPSSW_Distill_AchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:46:00.97849+00:00
-- url     : https://prove2.me/theorems/9250b675-a460-4e02-9e20-be0e0cc4f39d
-- title:
--   Achievable singlet-distillation rate
-- statement:
--   Let $M$ be a two-spin state shared by Alice and Bob. A rate $r\ge0$ is **achievable** from $M$ if there are output sizes $m_n$ and, for every $n$, a protocol $\Lambda_n$ of local operations and two-way classical communication (finitely many rounds) taking $n$ copies $M^{\otimes n}$ to a state of $m_n$ pairs, such that
--
--   1. $m_n/n\to r$, and
--   2. the fidelity of the output with $m_n$ perfect singlets tends to one:
--
--   $$\big\langle(\Psi^-)^{\otimes m_n}\big|\,\Lambda_n(M^{\otimes n})\,\big|(\Psi^-)^{\otimes m_n}\big\rangle\to1 .$$
--
--   **Formalization Note** The protocols are the published class `FiniteLOCC`: compositions of complete (trace-preserving) local Kraus instruments of Alice or Bob, with any intermediate local dimensions and an outcome-dependent continuation, branches summed. Protocols are deterministic: there is no renormalization by a success probability.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Abstract, p. 1 ("the yield D(M) of pure singlets (|Ψ−⟩) distillable from mixed states M"); p. 2 ("local operations and two-way classical communication")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_pairsState
import Definitions.Def_BBPSSW_Distill_pairsVec

open QAlgorithms.Papers.Independent.Information100.P21 (QQ quad FiniteLOCC)
open Filter Topology
open scoped NNReal

namespace BBPSSW.Distill

/-- **An achievable singlet-distillation rate.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Abstract, p. 1 ("the yield D(M) of pure singlets (|Ψ−⟩) distillable from mixed states
M"; "by applying local operations to a supply of not-too-impure entangled states … can
prepare a smaller number of entangled pairs of arbitrarily high purity (e.g. near-perfect
singlets)"), and p. 2 ("local operations and two-way classical communication").

`r ≥ 0` is achievable from the two-qubit state `M` if there are output sizes `m n` and, for
every `n`, a protocol `Λ n` built from local operations and two-way classical communication
(`FiniteLOCC`) taking `n` copies `M^{⊗n}` (Alice holding the first spin of each pair) to a
state of `m n` pairs, such that
1. the yield converges: `m n / n → r`, and
2. the output fidelity with `m n` perfect singlets tends to one:
   `⟨Ψ⁻^{⊗ m n}| Λ n (M^{⊗n}) |Ψ⁻^{⊗ m n}⟩ → 1`.

**Formalization Note.** `FiniteLOCC` (`…Information100.P21.FiniteLOCC`) is the inductive class
of finite-round adaptive LOCC maps: complete (trace-preserving) local Kraus instruments by
Alice or Bob, any intermediate local dimensions, with the continuation chosen per outcome and
the branches summed. Protocols are deterministic (no renormalization by a success
probability). `M^{⊗n}` is `pairsState (fun _ => M)` and `Ψ⁻^{⊗m}` is
`pairsVec (fun _ => bellVec .psiMinus)`; `quad` is Re ⟨v|ρ|v⟩. -/
def AchievableRate (M : Matrix QQ QQ ℂ) (r : ℝ≥0) : Prop :=
  ∃ m : ℕ → ℕ, ∃ Λ : (n : ℕ) →
      QAlgorithms.Superop (Fin (2 ^ n) × Fin (2 ^ n)) (Fin (2 ^ m n) × Fin (2 ^ m n)),
    (∀ n, FiniteLOCC (Λ n)) ∧
    Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 (r : ℝ)) ∧
    Tendsto (fun n : ℕ => quad (Λ n (pairsState fun _ : Fin n => M))
      (pairsVec fun _ : Fin (m n) => bellVec .psiMinus)) atTop (𝓝 1)

end BBPSSW.Distill


