-- Prove2me | Definitions.Def_CompPermOracle_Alg
-- name    : CompPermOracle_Alg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:32.867197+00:00
-- url     : https://prove2.me/theorems/015177cf-61ad-48a5-bb1c-e2d1fb9fb83f
-- title:
--   Quantum algorithms with forward and inverse queries: real, purified and compressed experiments
-- statement:
--   A **query algorithm** with workspace $W$ acts on the accessible registers: a direction bit $d$, an input over $[N]$, an answer over $[N]\cup\{\bot\}$ and the workspace. It consists of a unit initial state, a unitary $U_j$ on the accessible registers after the oracle step number $j$, and a set of accepting basis states. Three experiments run such an algorithm for $q$ queries.
--
--   1. Against a permutation $\varphi$: each oracle step applies $\tilde O_\varphi$ to (input, answer) if $d=0$, and $\tilde O_{\varphi^{-1}}$ if $d=1$. Then $\Pr_{\varphi\sim S_N}[1\leftarrow A]$ is the average over $\varphi$ of the probability of an accepting outcome.
--   2. Purified: the joint state starts in $\mathrm{init}\otimes|S_N\rangle$, and each oracle step is $P$ if $d=0$, $P^{-1}$ if $d=1$.
--   3. Compressed: the joint state starts in $\mathrm{init}\otimes|\emptyset\rangle$, and each oracle step is $\mathrm{cpO}$ if $d=0$, $\mathrm{cpO}^{-1}$ if $d=1$. Then $\Pr[1\leftarrow A^{\mathrm{cpO}}]$ is the probability of an accepting accessible outcome.
--
--   In the last two, $U_j$ acts as $U_j\otimes I$: the oracle register is not accessible.
--
--   **Formalization Note** The oracle $\mathcal O$ in the source's display (13) is read as the swap oracle $\tilde O$ of Definition 3.1. The query count is a parameter of the run, not of the algorithm: a run with $q$ queries ignores $U_j$ for $j\ge q$. Mid-circuit measurements are deferred into the unitaries, and a fixed forward/inverse schedule is the case where the algorithm sets $d$ classically.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Corollary 4.3, p.12; Remark 3.3, p.6; Definitions 3.4, 3.6, pp.7–8

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO

namespace CompPermOracle

/-- The accessible basis states of a query algorithm: a direction bit (`false` = forward,
`true` = inverse), an input over `[N]`, an answer over `[N] ∪ {⊥}`, and a workspace over `W`. -/
abbrev Acc (N : ℕ) (W : Type) := Bool × Fin N × Ans N × W

/-- A quantum algorithm with forward and inverse oracle access and a decision bit (Carolan, Majenz,
arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Corollary 4.3, p.12).

**Formalization Note.** An algorithm is a unit initial state on the accessible registers, a unitary
`U j` on the accessible registers after each oracle step, and a set of accepting basis states. The
number of queries `q` is a separate parameter: a run with `q` queries uses `U 0, …, U (q-1)` and
ignores the rest. Each oracle step is coherently controlled on the direction bit, so a fixed
schedule of forward and inverse queries is the case where the direction is set classically. The
workspace `W` is any finite type, so a measurement of the decision bit in the computational basis
is no restriction, and mid-circuit measurements are deferred into the unitaries. The oracle register
is not accessible: `U j` acts as `U j ⊗ I` on it. -/
structure Alg (N : ℕ) (W : Type) [Fintype W] where
  /-- The initial state on the accessible registers. -/
  init : Hil (Acc N W)
  /-- The initial state is a unit vector. -/
  norm_init : ‖init‖ = 1
  /-- The unitary applied after the oracle step number `j` (counted from 0). -/
  U : ℕ → Hil (Acc N W) ≃ₗᵢ[ℂ] Hil (Acc N W)
  /-- The basis states on which the algorithm outputs 1. -/
  accept : Finset (Acc N W)

variable {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- The inter-query unitary as a bounded operator. -/
noncomputable def Alg.Uop (A : Alg N W) (j : ℕ) : Hil (Acc N W) →L[ℂ] Hil (Acc N W) :=
  (A.U j).toLinearIsometry.toContinuousLinearMap

/-- One oracle step against the permutation `φ`: the swap oracle `Õ_φ` on (input, answer) if the
direction bit is `false`, and `Õ_{φ⁻¹}` if it is `true`, with the workspace untouched
(arXiv:2609.28469, Definition 3.1, p.6). -/
noncomputable def realStep (φ : Equiv.Perm (Fin N)) (ψ : Hil (Acc N W)) : Hil (Acc N W) :=
  WithLp.toLp 2 fun c =>
    (if c.1 then swapOracleInv φ else swapOracle φ)
      (WithLp.toLp 2 fun p : Fin N × Ans N => ψ (c.1, p.1, p.2, c.2.2.2)) (c.2.1, c.2.2.1)

/-- The state of the algorithm against `φ` after `j` queries and the unitaries that follow them. -/
noncomputable def realState (A : Alg N W) (φ : Equiv.Perm (Fin N)) : ℕ → Hil (Acc N W)
  | 0 => A.init
  | j + 1 => A.Uop j (realStep φ (realState A φ j))

/-- The probability that the algorithm outputs 1 after `q` queries against `φ`. -/
noncomputable def realAccept (A : Alg N W) (q : ℕ) (φ : Equiv.Perm (Fin N)) : ℝ :=
  ∑ c ∈ A.accept, ‖realState A φ q c‖ ^ 2

/-- `Pr_{φ∼S_N}[1 ← A^{Õ_φ, Õ_{φ⁻¹}}]` for `q` queries (arXiv:2609.28469, eq. (13), p.12).

**Formalization Note.** The oracle `𝒪` in display (13) is read as the swap oracle `Õ` of
Definition 3.1: the same algorithm must run against `cpO`, which acts on `𝒜` by swaps, and §3.1
says "We will work exclusively with swap oracles". -/
noncomputable def idealAccept (A : Alg N W) (q : ℕ) : ℝ :=
  ((N.factorial : ℝ))⁻¹ * ∑ φ : Equiv.Perm (Fin N), realAccept A q φ

/-- One oracle step on (accessible registers) ⊗ (oracle register `R`): the controlled operator `O d`
acts on (input, answer, `R`), with `d` the direction bit, and the workspace is untouched. -/
noncomputable def oracleStep {R : Type} [Fintype R]
    (O : Bool → Hil (Fin N × (Ans N × R)) →L[ℂ] Hil (Fin N × (Ans N × R)))
    (ψ : Hil (Acc N W × R)) : Hil (Acc N W × R) :=
  WithLp.toLp 2 fun c =>
    O c.1.1 (WithLp.toLp 2 fun p : Fin N × (Ans N × R) =>
        ψ ((c.1.1, p.1, p.2.1, c.1.2.2.2), p.2.2))
      (c.1.2.1, c.1.2.2.1, c.2)

/-- The state on (accessible registers) ⊗ `R` from the start vector `ψ₀`, after `j` oracle steps
with the operators `O`, each followed by `U ⊗ I_R`. -/
noncomputable def oracleRun {R : Type} [Fintype R] [DecidableEq R] (A : Alg N W)
    (O : Bool → Hil (Fin N × (Ans N × R)) →L[ℂ] Hil (Fin N × (Ans N × R)))
    (ψ₀ : Hil (Acc N W × R)) : ℕ → Hil (Acc N W × R)
  | 0 => ψ₀
  | j + 1 => opTensor (A.Uop j) (1 : Hil R →L[ℂ] Hil R) (oracleStep O (oracleRun A O ψ₀ j))

/-- The purified state after `j` queries: it starts in `init ⊗ |S_N⟩`, and each oracle step is the
direction-controlled `P` / `P⁻¹` (arXiv:2609.28469, Remark 3.3, p.6). -/
noncomputable def purifiedState (A : Alg N W) (j : ℕ) : Hil (Acc N W × Equiv.Perm (Fin N)) :=
  oracleRun A (fun d => if d then purPInvCtl else purPCtl) (ketTensor A.init (uniformPerm N)) j

/-- The compressed state after `j` queries: it starts in `init ⊗ |∅⟩`, and each oracle step is the
direction-controlled `cpO` / `cpO⁻¹` (arXiv:2609.28469, Definitions 3.4 and 3.6, pp.7–8). -/
noncomputable def compressedState (A : Alg N W) (j : ℕ) : Hil (Acc N W × PartialPerm N) :=
  oracleRun A (fun d => if d then cpOInvCtl else cpOCtl) (ketTensor A.init (ket ⊥)) j

/-- `Pr[1 ← A^{cpO}]` for `q` queries: the accessible registers are measured and the database is
ignored (arXiv:2609.28469, eq. (13), p.12). -/
noncomputable def compressedAccept (A : Alg N W) (q : ℕ) : ℝ :=
  ∑ c ∈ A.accept, ∑ f : PartialPerm N, ‖compressedState A q (c, f)‖ ^ 2

/-- The vector on the oracle register `R` that a joint state attaches to the accessible basis state
`c`. A joint state lies in `ℋ(Acc) ⊗ S` exactly when all these vectors lie in `S`. -/
noncomputable def regSlice {C R : Type} (ψ : Hil (C × R)) (c : C) : Hil R :=
  WithLp.toLp 2 fun r => ψ (c, r)

end CompPermOracle


