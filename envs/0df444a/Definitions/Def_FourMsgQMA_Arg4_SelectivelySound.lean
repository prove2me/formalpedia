-- Prove2me | Definitions.Def_FourMsgQMA_Arg4_SelectivelySound
-- name    : FourMsgQMA_Arg4_SelectivelySound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:37:25.488809+00:00
-- url     : https://prove2.me/theorems/93144a32-2f1c-4dc4-aa90-c09f83f9b58a
-- title:
--   Negligible selective circuit batch soundness (Definition 3.6)
-- statement:
--   An argument $\Pi$ is **negligibly selectively sound** for $L$ if the following holds for every polynomial bound $B$, every sequence of admissible instances $u_\lambda=(C_\lambda,X_\lambda)$ with $X_\lambda\in L^{C_\lambda}_{\mathrm{no}}$ and $|u_\lambda|\le B(\lambda)$, and every QPT adversary $A$. The function
--   $$
--   \lambda\ \mapsto\ \Pr\big[b=1:\ v_0\leftarrow\mathrm{Pre}(u_\lambda);\ (q_1,v_1)\leftarrow V_1;\ (a_1,\zeta_1)\leftarrow A_1(u_\lambda,\zeta_\lambda,q_1);\ (q_2,v_2)\leftarrow V_2;\ (a_2,\zeta_2)\leftarrow A_2(\zeta_1,q_2);\ b=\mathrm{Dec}(v_2,a_2)\big]
--   $$
--   is negligible.
--
--   This is Definition 3.6 with soundness error $s=0$: "Negligible soundness means $s=0$" (Definition 3.4). The policy and full batch are fixed before preprocessing.
--
--   **Formalization Note** QPT adversaries are the published `TightPQRepetition.Main.IsQPT` families (nonuniform, polynomial size, one quantum advice state whose residual registers pass between the stages); they may hardwire $u_\lambda$. The negligible function is chosen after $B$, the sequence and the adversary.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Definition 3.6, p.13 (PDF 15); Definition 3.4, p.12; §3.1, p.9

import Mathlib
import Definitions.Def_FourMsgQMA_Arg4

namespace FourMsgQMA

open QAlgorithms.Complexity TightPQRepetition.Main

/-- Negligible selective circuit batch soundness, Definition 3.6 (p.13, PDF 15) with `s = 0`
(Definition 3.4, p.12: "Negligible soundness means `s = 0`"). For every polynomial bound `B`, every
sequence of admissible instances `u_λ = (C_λ, X_λ)` with `X_λ ∈ L^{C_λ}_no` and `|u_λ| ≤ B(λ)`,
fixed before all verifier coins, and every QPT adversary `Adv` (a nonuniform polynomial-size
quantum circuit family with quantum advice, which may hardwire `u_λ`), the probability that the
verifier accepts in the four-message experiment is negligible.

**Formalization Note** The adversary class is the published `TightPQRepetition.Main.IsQPT`
(§3.1, p.9: "a nonuniform polynomial-size quantum circuit family with one polynomial-size quantum
advice state"; its stages pass the same residual registers forward). The negligible function is
chosen after the bound, the sequence and the adversary (`∀ B ∀ u ∀ Adv ∃ ν`, p.9). -/
def Arg4.SelectivelySound (A : Arg4) (L : PromiseProblem) : Prop :=
  ∀ B : ℕ → ℕ, PolyBound B → ∀ u : ℕ → Inst, (∀ lam, u lam ∈ noSet L ∧ (u lam).size ≤ B lam) →
    ∀ Adv : ℕ → Strategy, IsQPT Adv →
      Negligible fun lam => (Adv lam).acceptProb (A.verifierSeq u) lam

end FourMsgQMA


