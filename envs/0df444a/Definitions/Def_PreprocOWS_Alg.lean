-- Prove2me | Definitions.Def_PreprocOWS_Alg
-- name    : PreprocOWS_Alg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:55.870202+00:00
-- url     : https://prove2.me/theorems/b5390edf-5b2e-4949-8e70-191e5dc42be3
-- title:
--   $T$-query algorithm: query map, unitaries $U_1,\dots,U_T$, measurement $\{\Pi_k\}$
-- statement:
--   An algorithm in the 1OWS game acts on the computational basis
--   $$
--   \Omega=[2^S]\times[N]\times[2^w],
--   $$
--   the advice register $\mathsf A$ ($S$ qubits), the challenge register $\mathsf X$ (dimension $N$) and the workspace $\mathsf W$ ($w$ qubits); $|0^w\rangle$ is the all-zero workspace state. A **$T$-query algorithm** consists of
--
--   1. a query map $q:\Omega\to\{\bot\}\cup([K]\times[N])$: on basis state $s$ the oracle is queried at $q(s)$, and $q(s)=\bot$ means no query on $s$;
--   2. unitaries $U_1,\dots,U_T$ on $\mathbb C^{\Omega}$, $U_i$ applied before the $i$-th query;
--   3. matrices $\Pi_k$, $k\in[K]$, the final measurement (the algorithm outputs the guess $k$).
--
--   The family $\{\Pi_k\}$ is a **projective measurement** when every $\Pi_k$ is Hermitian and idempotent and $\sum_k\Pi_k=I$. For an operator $O$ the layered product is $(OU)^T=O\,U_T\cdots O\,U_1$ (the identity for $T=0$).
--
--   This is the quantum oracle algorithm of §3.1, with the phase query used for $\pm1$-valued oracles.
--
--   **Formalization Note** The paper fixes one unitary $U$ between queries ("without loss of generality … the same $U$") and a phase query on a designated query register; distinct $U_i$ and an arbitrary query map include both. A final unitary $U_{T+1}$ is absorbed into the measurement ($U_{T+1}^\dagger\Pi_kU_{T+1}$ is again projective). Only the oracle is random: $q$, $U_i$, $\Pi_k$ are fixed before $R$.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §3.1, p.11 (PDF p.14); Definition 5.1, p.16 (PDF p.19); §5.1, p.17 (PDF p.20)

import Mathlib
open Matrix

namespace PreprocOWS

/-- The computational basis `Ω = [2^S] × [N] × [2^w]` of an algorithm in the 1OWS game: the advice
register A (`S` qubits), the challenge register X (dimension `N`) and the workspace W (`w` qubits),
Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, p.17 (PDF p.20).

**Formalization Note.** The registers are ordered A ⊗ X ⊗ W (the page writes
`|ψ_{R,k}⟩|φ_R⟩|0^w⟩_W`; the order of tensor factors is immaterial). -/
abbrev Ω (S N w : ℕ) : Type := Fin (2 ^ S) × Fin N × Fin (2 ^ w)

/-- The all-zero basis state `|0^w⟩` of the `w`-qubit workspace (arXiv:2610.02101, §5.1, p.17). -/
def wsZero (w : ℕ) : Fin (2 ^ w) := ⟨0, Nat.two_pow_pos w⟩

/-- A **`T`-query algorithm** in the 1OWS game of arXiv:2610.02101 (Definition 5.1, p.16; §3.1, p.11;
§5.1, p.17): a query map, `T` intermediate unitaries and a final `K`-outcome measurement.

* `q s ∈ Option ([K] × [N])` is the oracle input read on basis state `s`; `none` means the query does
  nothing on `s`. A query applies `O_R |s⟩ = R(q(s)) |s⟩`, with `R(none) := 1` (`phaseOracle`).
* `U i` is the unitary applied before the `(i+1)`-st query; the run is `O_R U_T ⋯ O_R U_1`.
* `proj k` is the measurement operator `Π_k` for the guess `k`.

**Formalization Note.** The paper uses one unitary `U` between queries ("without loss of generality …
the same U", §3.1) and a phase query on a designated query register; distinct `U_i` and a general query
map `q` include both. A final unitary `U_{T+1}` is absorbed into the measurement. Only the oracle `R`
is random: `q`, `U`, `proj` are fixed before `R`. -/
structure Alg (S T K N w : ℕ) where
  q : Ω S N w → Option (Fin K × Fin N)
  U : Fin T → Matrix.unitaryGroup (Ω S N w) ℂ
  proj : Fin K → Matrix (Ω S N w) (Ω S N w) ℂ

/-- `{Π_k}_{k ∈ [K]}` is a **projective measurement**: every `Π_k` is Hermitian and idempotent and
`∑_k Π_k = I` (arXiv:2610.02101, §5.1, p.17; §5.3, p.20: "∑_k Π_k = I"). -/
def IsProjMeas {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (P : Fin K → Matrix ι ι ℂ) : Prop :=
  (∀ k, (P k).IsHermitian ∧ P k * P k = P k) ∧ ∑ k, P k = 1

/-- The layered product `O U_T ⋯ O U_2 O U_1` (written `(O U)^T` on the page, arXiv:2610.02101,
§5.1, p.17): `U 0` is applied first. For `T = 0` it is the identity. -/
def layeredRun {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℕ} (O : Matrix ι ι ℂ)
    (U : Fin T → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((List.ofFn fun i : Fin T => O * U i).reverse).prod

end PreprocOWS


