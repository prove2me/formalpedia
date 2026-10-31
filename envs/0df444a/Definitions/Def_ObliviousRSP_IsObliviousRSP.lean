-- Prove2me | Definitions.Def_ObliviousRSP_IsObliviousRSP
-- name    : ObliviousRSP_IsObliviousRSP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:36.741012+00:00
-- url     : https://prove2.me/theorems/9402481b-6594-4174-91d6-a695f2158699
-- title:
--   Faithful forward-only RSP protocol oblivious to Bob
-- statement:
--   Fix finite index sets $\iota$ (the input space $\mathbb C^d$) and $\sigma$ (each half of the shared state $|\Phi_{d'}\rangle$), a message set $M$, and for every message $m$ a finite index set $K_m$ (Bob's extra output). A **faithful remote state preparation protocol oblivious to Bob** for an ensemble $S$ consists of
--
--   - Alice's measurements $E_\psi = (E_{\psi,m})_{m\in M}$ on her half, depending on the state $\psi$ she wants to prepare;
--   - Bob's recovery isometries $V_m:\mathbb C^\sigma\to\mathbb C^\iota\otimes\mathbb C^{K_m}$, depending on the message only;
--   - message probabilities $p_m$ and extra output states $b_m$ on $\mathbb C^{K_m}$, both independent of $\psi$,
--
--   such that
--
--   1. $E_\psi$ is a POVM for every $\psi\in S$;
--   2. every $V_m$ is an isometry, $V_m^\dagger V_m = I$;
--   3. $p_m\ge 0$ and $b_m$ is a density matrix for every $m$;
--   4. for every $\psi\in S$ and every message $m$, with $\varphi = |\psi\rangle\langle\psi|$ and Bob's unnormalized conditional state $\sigma_{\psi m} = \operatorname{Tr}_1[(E_{\psi,m}\otimes I)|\Phi_{d'}\rangle\langle\Phi_{d'}|]$,
--   $$
--   V_m\,\sigma_{\psi m}\,V_m^\dagger = p_m\,(\varphi\otimes b_m).
--   $$
--
--   Condition 4 says that Bob's output is exactly $\varphi\otimes b_m$ with probability $p_m$ (faithful: exact and deterministic), and that the joint law of the message and of Bob's extra output does not depend on $\varphi$ (oblivious to Bob, in the form the paper derives on p.3). Only forward classical communication is used: Bob's operation depends on the message alone.
--
--   **Formalization Note** The paper's recovery is a unitary $U_m$ on Bob's half and a pure ancilla $|0\rangle$; here it is any isometry $V_m$, which covers $U_m(\cdot\otimes|0\rangle)$. Alice's general operation $\mathcal E_\varphi$ enters through its POVM (the paper's reduction, p.2). The message set is an arbitrary type, and the probabilities $p_m$ are forced to be the outcome probabilities by condition 4 (take traces).
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, pp.2–3, Figs. 1–2, definitions of faithful and oblivious (p.2) and the oblivious condition (p.3)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, pp.2–3 (Figs. 1–2 and the oblivious condition): a faithful remote state preparation
protocol for the ensemble `S` that uses only forward classical communication and the shared state
`|Φ_{d′}⟩`, and is oblivious to Bob.

Data: `E ψ` is Alice's `φ`-dependent POVM on her half (outcome = the classical message `m`);
`V m : ℂ^σ → ℂ^ι ⊗ ℂ^{K m}` is Bob's recovery isometry, depending on `m` but not on `φ`
(the paper's `U_m(· ⊗ |0⟩)`); `p m` is the probability of message `m` and `b m` Bob's extra
output state `b_m^{(out)}`, both independent of `φ` (the paper's consequence of obliviousness to
Bob, p.3). Conditions:
1. `E ψ` is a POVM for every `ψ ∈ S`;
2. every `V m` is an isometry, `V_m† V_m = I`;
3. `p m ≥ 0` and `b m` is a density matrix;
4. faithful and oblivious: for every `ψ ∈ S` and message `m`, Bob's (unnormalized) output
   after `V m` is `V_m (p_m ρ_φm) V_m† = p_m · (φ ⊗ b_m)` with `φ = |ψ⟩⟨ψ|`.

**Formalization Note.** Registers: input `ι` (dimension `d`), each half of the shared state
`σ` (dimension `d′`), Bob's extra output `K m`; `V m` maps into `ι × K m` with the copy of
`φ` first. Bob's general recovery operation is replaced by its isometric (Stinespring) form, which
covers the paper's unitary `U_m` with a pure ancilla `|0⟩`. The message set `M` is an arbitrary
type. The state of Bob's half is the unnormalized `bobState (E ψ m) = p_m ρ_φm`. -/
structure IsObliviousRSP {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    (S : Set (ι → ℂ)) (E : (ι → ℂ) → M → Matrix σ σ ℂ) (V : (m : M) → Matrix (ι × K m) σ ℂ)
    (p : M → ℝ) (b : (m : M) → Matrix (K m) (K m) ℂ) : Prop where
  povm : ∀ ψ ∈ S, IsPOVM (E ψ)
  isometry : ∀ m, (V m)ᴴ * V m = 1
  prob_nonneg : ∀ m, 0 ≤ p m
  extra_state : ∀ m, WildeQIT.IsDensityOperator (b m)
  faithful_oblivious : ∀ ψ ∈ S, ∀ m,
    V m * bobState (E ψ m) * (V m)ᴴ = (p m : ℂ) • (pureState ψ ⊗ₖ b m)

end ObliviousRSP


