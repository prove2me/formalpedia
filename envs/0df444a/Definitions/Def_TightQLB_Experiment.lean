-- Prove2me | Definitions.Def_TightQLB_Experiment
-- name    : TightQLB_Experiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:13.707198+00:00
-- url     : https://prove2.me/theorems/90462601-de65-4c42-ad7c-f137658273ec
-- title:
--   Definition 3.1 — the experiment, Eve\'s states $\rho^\omega_z$ and the expected score $B(\mathcal A)$
-- statement:
--   An **experiment** with $q$ queries consists of a device with a finite register $A=(\mathsf C\times\mathsf Q)\times W$ and an adversary, Eve, with a finite register $E$, together with
--
--   1. a density matrix $\rho_{AE}$ on $A\otimes E$, which does not depend on the oracle;
--   2. oracle-independent CPTP maps $\Phi_0,\dots,\Phi_q$ on $A$;
--   3. a POVM $\{M_z\}_{z\in\{0,1\}^n}$ on $A$.
--
--   For an oracle $\omega$ the device applies $\Phi_0$, then alternately a controlled query and the next map, so $q$ queries occur in all. Nothing acts on $E$. Eve's subnormalized state on the event $Z=z$ is $\rho^\omega_z=\operatorname{Tr}_A[(M_z\otimes I_E)\rho_{\mathrm{final}}]$, and $\Pr[Z=z\mid\omega]=\operatorname{Tr}\rho^\omega_z$. In the Fourier ensemble the expected score is
--
--   $$
--   B(\mathcal A)=\mathbb E_f\sum_z\Pr[Z=z\mid f]\,Np_f(z).
--   $$
--
--   This is the class of devices over which the main theorem quantifies.
--
--   **Formalization Note** The paper states Definition 3.1 operationally, with a classical record, paths along which at most $q$ queries occur, and record-selected registers. This module uses the channel form that the proof of Lemma 3.2, Steps 1–2, gives every such experiment: a round is one CPTP map, the record-controlled swaps move the selected registers into $\mathsf C\times\mathsf Q$, and a control qubit in $|0\rangle$ switches a query off. Conversely a CPTP map is an ancilla, a unitary and an ignored register, and a POVM is a measurement of an ancilla, so the class is the same. `Q` and the oracle matrix `O` are arbitrary, which covers both ensembles; `score` is the Fourier case. `ρ₀`, `Φ` and `M` are structure fields, fixed before the oracle. CPTP is the published `AKNMixed.FQP.IsQuantumOperation`.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.2, Definition 3.1, p. 15 (PDF p. 18); §3.1, Eq. (12), p. 14 (PDF p. 17)

import Mathlib
import Definitions.Def_TightQLB_Fourier
import Definitions.Def_TightQLB_Query
import Definitions.Def_AKNMixed_FQP_IsQuantumOperation
import Definitions.Def_WildeQIT_partialTrace
open QAlgorithms
open scoped ComplexOrder Matrix

namespace TightQLB

/-!
# The experiment (Definition 3.1) and its expected score

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.2, Definition 3.1,
p.15 (PDF p.18); the expected score, Eq. (12), p.14 (PDF p.17).

A device with a finite register `A` and an adversary Eve with a finite register `E` start in a joint
state `ρ_AE` that does not depend on the oracle. The device alternates oracle-independent operations
on `A` with at most `q` queries to the value oracle, possibly controlled by a qubit of `A`, and
outputs `Z ∈ {0,1}^n`. Nothing acts on `E`. The expected score is
`B(A) = E_f Σ_z Pr[Z = z | f] · N p_f(z)`.

**Formalization Note.**
* *Definition 3.1 in channel form.* The device's register is `A = Reg Q W` (a control qubit `C`, the
  query register `Q` and a finite workspace `W`). The experiment is a density matrix `ρ₀` on `A × E`,
  `q + 1` oracle-independent CPTP maps `Φ 0, …, Φ q` on `A`, exactly `q` controlled queries `O^c` on
  `C × Q` between consecutive maps, and a final POVM `{M_z}` on `A`. This is the form the proof
  of Lemma 3.2, Steps 1–2 (PDF pp.19–20), gives every experiment of Definition 3.1: a round's
  operations with the recording of their outcomes are one CPTP map, the record-controlled swaps move
  the selected registers into `C × Q`, and a control qubit in `|0⟩` switches a query off (so a
  path with fewer than `q` queries is covered, as is an uncontrolled query, `C = |1⟩`). Conversely a
  CPTP map is an ancilla, a unitary and an ignored register, and a POVM is a measurement of an ancilla,
  both allowed by Definition 3.1. The class is the same.
* The oracle enters only through its matrix `O` on `Q`, an argument of `state`; every field (`ρ₀`,
  `Φ`, `M`) is fixed before the oracle. `Q` and `O` are arbitrary, which covers both ensembles of
  Definition 3.1; the score (12) is defined for the Fourier ensemble, `Q = Qubits n × Bool` and
  `O = valueOracle fb`.
* "CPTP" is the published `AKNMixed.FQP.IsQuantumOperation`: linear, trace preserving on every
  matrix, and completely positive (`PeresTerno.IsCompletelyPositive`). Input and output space coincide;
  adjoining ancillas is covered by taking the workspace large enough from the start.
* Rounds act as `Φ t ⊗ id_E` (`PeresTerno.ampliate`), queries as `O^c ⊗ I_W ⊗ I_E`: nothing acts
  on `E`.
* Eve's subnormalized state on the event `Z = z` is `ρ^ω_z = Tr_A[(M_z ⊗ I_E) ρ_final]`
  (`WildeQIT.partialTraceLeft`), which equals `Tr_A[(√M_z ⊗ I) ρ_final (√M_z ⊗ I)]` by cyclicity of
  the trace on `A`; `Pr[Z = z | ω]` is the real part of its trace.
* `state O 0 = (Φ 0 ⊗ id) ρ₀` and `state O (t + 1) = (Φ (t+1) ⊗ id)(Q ρ Q†)` with `Q` the query:
  `Φ 0` acts first and each later round follows one query.
-/

/-- Definition 3.1, p.15 (PDF p.18), in channel form: an experiment with outputs in `{0,1}^n`, `q`
query slots on the query register `Q`, device workspace `W` and Eve register `E`. -/
structure Experiment (n q : ℕ) (Q W E : Type) [Fintype Q] [DecidableEq Q] [Fintype W]
    [DecidableEq W] [Fintype E] [DecidableEq E] where
  /-- The oracle-independent joint initial state `ρ_AE`. -/
  ρ₀ : Matrix (Reg Q W × E) (Reg Q W × E) ℂ
  /-- `ρ_AE` is a density matrix. -/
  ρ₀_density : PeresTerno.IsDensityMatrix ρ₀
  /-- The oracle-independent operations of the `q + 1` rounds, each on `A`. -/
  Φ : Fin (q + 1) → Matrix (Reg Q W) (Reg Q W) ℂ → Matrix (Reg Q W) (Reg Q W) ℂ
  /-- Each round is a CPTP map. -/
  Φ_cptp : ∀ t, AKNMixed.FQP.IsQuantumOperation (Φ t)
  /-- The output measurement, a POVM on `A` indexed by the output `z ∈ {0,1}^n`. -/
  M : Qubits n → Matrix (Reg Q W) (Reg Q W) ℂ
  /-- Its elements are positive semidefinite. -/
  M_psd : ∀ z, (M z).PosSemidef
  /-- They sum to the identity. -/
  M_sum : ∑ z, M z = 1

namespace Experiment

variable {n q : ℕ} {Q W E : Type} [Fintype Q] [DecidableEq Q] [Fintype W] [DecidableEq W]
  [Fintype E] [DecidableEq E]

/-- The state of `A × E` after round `t` (after `t` queries and the round that follows them), for the
oracle matrix `O`. -/
noncomputable def state (A : Experiment n q Q W E) (O : Matrix Q Q ℂ) :
    Fin (q + 1) → Matrix (Reg Q W × E) (Reg Q W × E) ℂ :=
  Fin.induction (PeresTerno.ampliate (A.Φ 0) A.ρ₀)
    (fun t ρ => PeresTerno.ampliate (A.Φ t.succ)
      (Matrix.kronecker (queryOn O W) (1 : Matrix E E ℂ) * ρ *
        (Matrix.kronecker (queryOn O W) (1 : Matrix E E ℂ))ᴴ))

/-- The final state of `A × E`. -/
noncomputable def finalState (A : Experiment n q Q W E) (O : Matrix Q Q ℂ) :
    Matrix (Reg Q W × E) (Reg Q W × E) ℂ :=
  A.state O (Fin.last q)

/-- §3.2, p.15 (PDF p.18): Eve's subnormalized state `ρ^ω_z = Tr_A[(M_z ⊗ I_E) ρ_final]` on the event
`Z = z`. -/
noncomputable def eveState (A : Experiment n q Q W E) (O : Matrix Q Q ℂ) (z : Qubits n) :
    Matrix E E ℂ :=
  WildeQIT.partialTraceLeft (Matrix.kronecker (A.M z) (1 : Matrix E E ℂ) * A.finalState O)

/-- `Pr[Z = z | ω]`, the trace of `ρ^ω_z`. -/
noncomputable def outProb (A : Experiment n q Q W E) (O : Matrix Q Q ℂ) (z : Qubits n) : ℝ :=
  (A.eveState O z).trace.re

/-- Eq. (12), p.14 (PDF p.17): the expected score `B(A) = E_f Σ_z Pr[Z = z | f] · N p_f(z)` in the
Fourier ensemble (query register `X × T`, oracle `O_f`). -/
noncomputable def score {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (A : Experiment n q (Qubits n × Bool) W E) : ℝ :=
  avgF (fun fb => ∑ z, A.outProb (valueOracle fb) z * ((2 : ℝ) ^ n * idealDist fb z))

end Experiment

end TightQLB


