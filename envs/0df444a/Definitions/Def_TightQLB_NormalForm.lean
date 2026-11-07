-- Prove2me | Definitions.Def_TightQLB_NormalForm
-- name    : TightQLB_NormalForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:24.685055+00:00
-- url     : https://prove2.me/theorems/ec88faa8-475b-4171-b6e9-dc8f80c0e72b
-- title:
--   Lemma 3.2 (a)–(d) — a fixed sequence of controlled queries, $V_\omega=U_qO^{\mathrm c}_\omega\cdots U_1O^{\mathrm c}_\omega U_0$
-- statement:
--   An experiment in **normal form** consists of a register $A'=(\mathsf C\times\mathsf Q)\times W$, a unit vector $\psi_0\in A'\otimes E$, oracle-independent unitaries $U_0,\dots,U_q$ on $A'$, and orthogonal projections $\{\Pi_z\}_{z\in\{0,1\}^n}$ on $A'$ with $\sum_z\Pi_z=I$. With
--
--   $$
--   V_\omega=U_qO^{\mathrm c}_\omega U_{q-1}O^{\mathrm c}_\omega\cdots U_1O^{\mathrm c}_\omega U_0,
--   $$
--
--   the final state is $\Psi(\omega)=(V_\omega\otimes I_E)\psi_0$ and its output-$z$ branch is $\Psi_z(\omega)=(\Pi_z\otimes I_E)\Psi(\omega)$. In the Fourier ensemble the score reads $B=\mathbb E_f\sum_zNp_f(z)\|\Psi_z(f)\|^2$.
--
--   Lemma 3.2 reduces every experiment to this form, which is the form used in all later proofs.
--
--   **Formalization Note** `V O t` is the partial product $U_tO^{\mathrm c}\cdots O^{\mathrm c}U_0$, with $U_0$ acting first. The projections are the field `proj`. All fields are fixed before the oracle, which enters only through its matrix `O`.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.2, Lemma 3.2 (a)–(d) and Eqs. (14)–(17), pp. 15–17 (PDF pp. 18–20)

import Mathlib
import Definitions.Def_TightQLB_Fourier
import Definitions.Def_TightQLB_Query
open QAlgorithms

namespace TightQLB

/-!
# The normal form of Lemma 3.2: a fixed sequence of controlled queries

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.2, Lemma 3.2 (a)–(d) and
Eqs. (14)–(17), pp.15–17 (PDF pp.18–20).

A register `A′` containing the query register and a control qubit, a unit vector `ψ₀ ∈ A′ ⊗ E`,
oracle-independent unitaries `U₀, …, U_q` on `A′`, and orthogonal projections `{Π_z}` on `A′` with
`Σ_z Π_z = I`. With `V_f = U_q O^c_f U_{q−1} ⋯ U₁ O^c_f U₀`, the final state is `Ψ(f) = (V_f ⊗ I_E)ψ₀`,
its output-`z` branch is `Ψ_z(f) = (Π_z ⊗ I_E)Ψ(f)`, and the score reads
`B = E_f Σ_z N p_f(z) ‖Ψ_z(f)‖²` (17).

**Formalization Note.** `A′ = Reg Q W = (C × Q) × W`, with an arbitrary query register `Q`. The
fields do not depend on the oracle, which enters only through its matrix `O` on `Q`.
`V O t = U_t O^c U_{t−1} ⋯ O^c U₀` (`U₀` acts first), so `V O (Fin.last q)` is `V_ω` of (15). The
projections are written `proj z`. The score (17) is defined for the Fourier ensemble,
`Q = Qubits n × Bool` and `O = valueOracle fb`.
-/

/-- Lemma 3.2 (a)–(d), p.15 (PDF p.18): an experiment with a fixed sequence of `q` controlled
queries. -/
structure NormalForm (n q : ℕ) (Q W E : Type) [Fintype Q] [DecidableEq Q] [Fintype W]
    [DecidableEq W] [Fintype E] [DecidableEq E] where
  /-- The initial unit vector `ψ₀ ∈ A′ ⊗ E`. -/
  ψ₀ : EuclideanSpace ℂ (Reg Q W × E)
  /-- `ψ₀` is a unit vector. -/
  ψ₀_unit : ‖ψ₀‖ = 1
  /-- The oracle-independent unitaries `U₀, …, U_q` on `A′`. -/
  U : Fin (q + 1) → Matrix.unitaryGroup (Reg Q W) ℂ
  /-- The output projections `Π_z` on `A′`. -/
  proj : Qubits n → Matrix (Reg Q W) (Reg Q W) ℂ
  /-- Each `Π_z` is Hermitian. -/
  proj_herm : ∀ z, (proj z).IsHermitian
  /-- Each `Π_z` is idempotent. -/
  proj_idem : ∀ z, proj z * proj z = proj z
  /-- `Σ_z Π_z = I`. -/
  proj_sum : ∑ z, proj z = 1

namespace NormalForm

variable {n q : ℕ} {Q W E : Type} [Fintype Q] [DecidableEq Q] [Fintype W] [DecidableEq W]
  [Fintype E] [DecidableEq E]

/-- Eq. (15), p.16 (PDF p.19): `V O t = U_t O^c U_{t−1} ⋯ U₁ O^c U₀`. -/
noncomputable def V (B : NormalForm n q Q W E) (O : Matrix Q Q ℂ) :
    Fin (q + 1) → Matrix (Reg Q W) (Reg Q W) ℂ :=
  Fin.induction (B.U 0 : Matrix (Reg Q W) (Reg Q W) ℂ)
    (fun t M => (B.U t.succ : Matrix (Reg Q W) (Reg Q W) ℂ) * queryOn O W * M)

/-- §4.1, p.23 (PDF p.26): the state `Ψ_t(ω) = (V_t ⊗ I_E) ψ₀` after `t` queries and `U_t`. -/
noncomputable def stateVec (B : NormalForm n q Q W E) (O : Matrix Q Q ℂ) (t : Fin (q + 1)) :
    EuclideanSpace ℂ (Reg Q W × E) :=
  act (Matrix.kronecker (B.V O t) (1 : Matrix E E ℂ)) B.ψ₀

/-- §3.2, p.17 (PDF p.20): the output-`z` branch `Ψ_z(ω) = (Π_z V_ω ⊗ I_E) ψ₀`. -/
noncomputable def branch (B : NormalForm n q Q W E) (O : Matrix Q Q ℂ) (z : Qubits n) :
    EuclideanSpace ℂ (Reg Q W × E) :=
  act (Matrix.kronecker (B.proj z * B.V O (Fin.last q)) (1 : Matrix E E ℂ)) B.ψ₀

/-- Eq. (17), p.17 (PDF p.20): `B(A) = E_f Σ_z N p_f(z) ‖Ψ_z(f)‖²`. -/
noncomputable def score {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (B : NormalForm n q (Qubits n × Bool) W E) : ℝ :=
  avgF (fun fb => ∑ z, (2 : ℝ) ^ n * idealDist fb z * ‖B.branch (valueOracle fb) z‖ ^ 2)

end NormalForm

end TightQLB


