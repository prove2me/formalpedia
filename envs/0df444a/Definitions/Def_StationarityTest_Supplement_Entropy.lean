-- Prove2me | Definitions.Def_StationarityTest_Supplement_Entropy
-- name    : StationarityTest_Supplement_Entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:46:02.798658+00:00
-- url     : https://prove2.me/theorems/6297aaec-94dc-4848-b1c8-1a2a3f6a2aa8
-- title:
--   Reduced states $\sigma_A$ on sets of sites, von Neumann entropy $S$ (nats) and mutual information $I(A:\bar A)_\sigma$
-- statement:
--   Consider $n$ sites, each made of $q$ qubits, with Hilbert space $\bigotimes_{i\in[n]}\mathbb C^{2^q}$ and computational basis the bit strings on all $nq$ qubits. For a set of sites $A\subseteq[n]$ with complement $\bar A=[n]\setminus A$, a basis string splits as a pair $(a,e)$ of its bits on $A$ and on $\bar A$.
--
--   1. The **reduced state** of an operator $\sigma$ on $A$ is the partial trace over $\bar A$:
--   $$
--   (\sigma_A)_{a,a'}=\sum_{e}\sigma_{(a,e),(a',e)} .
--   $$
--   2. The **von Neumann entropy** of a density matrix $\rho$ is
--   $$
--   S(\rho)=-\operatorname{tr}[\rho\log\rho],
--   $$
--   with the natural logarithm and the convention $0\log 0=0$.
--   3. The **quantum mutual information** between $A$ and its complement in $\sigma$ is
--   $$
--   I(A:\bar A)_\sigma:=S(\sigma_A)+S(\sigma_{\bar A})-S(\sigma).
--   $$
--
--   These are the quantities of the thermal area law (Theorem 1.12, footnote 4 on p.8).
--
--   **Formalization Note** The subsystem $A$ has basis $A\to\{0,1\}^q$; $S$ is computed as $\operatorname{Re}\operatorname{tr} f(\rho)$ for $f(x)=-x\log x$ through Mathlib's continuous functional calculus. The natural logarithm is the paper's: its proof expands $D(\alpha\|\rho_G)=-S+\beta\operatorname{tr}[G\alpha]+\log\operatorname{tr}e^{-\beta G}$ (268).
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 1.12 and footnote 4, p.8; Lemma B.2, (268)–(269), p.61

import Definitions.Def_StationarityTest_Pauli

open Matrix

namespace StationarityTest.Supplement

/-!
# Reduced states on sets of sites, von Neumann entropy and mutual information

T. Bergamaschi, *The stationarity test: a framework for learning quantum many-body systems from
their thermal states*, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 1.12 and footnote 4,
p.8; Lemma B.2 and (268)–(269), p.61.

**Formalization Note.** The system is `n` sites (`Fin n`) of `q` qubits, with Hilbert space the
functions on `QAlgorithms.Qubits (n * q)` (qubit `j` of site `i` is wire `finProdFinEquiv (i, j)`,
as in `StationarityTest.Pauli`). For a set of sites `A ⊆ [n]`, the subsystem `A` has computational
basis `A → Fin q → Bool`, and `σ_A = tr_{Ā}[σ]` is the partial trace over the sites of
`Ā = [n] \ A`: `(σ_A)_{a a'} = Σ_e σ_{(a,e),(a',e)}`. The entropy is the von Neumann entropy
`S(ρ) = −tr ρ log ρ` with the natural logarithm (the paper's (268) expands
`D(α‖ρ_G) = −S + β tr[Gα] + log tr e^{−βG}`, which holds only for the natural logarithm),
computed with Mathlib's continuous functional calculus; `0 log 0 = 0` because `Real.log 0 = 0`.
The mutual information is footnote 4: `I(A : Ā)_σ := S(σ_A) + S(σ_Ā) − S(σ)`.
-/

variable {n q : ℕ}

/-- The computational-basis string of all `n * q` qubits whose sites in `A` read `a` and whose
sites in `Aᶜ` read `e`. -/
def glue (A : Finset (Fin n)) (a : ↥A → Fin q → Bool) (e : ↥(Aᶜ) → Fin q → Bool) :
    QAlgorithms.Qubits (n * q) :=
  fun w =>
    if h : (finProdFinEquiv.symm w).1 ∈ A then a ⟨(finProdFinEquiv.symm w).1, h⟩ (finProdFinEquiv.symm w).2
    else e ⟨(finProdFinEquiv.symm w).1, Finset.mem_compl.mpr h⟩ (finProdFinEquiv.symm w).2

/-- The reduced state `σ_A = tr_{Ā}[σ]` on the sites of `A`: the partial trace over the sites of
the complement `Ā = [n] \ A`. -/
noncomputable def reducedState (A : Finset (Fin n)) (σ : Op n q) :
    Matrix (↥A → Fin q → Bool) (↥A → Fin q → Bool) ℂ :=
  Matrix.of fun a a' => ∑ e : ↥(Aᶜ) → Fin q → Bool, σ (glue A a e) (glue A a' e)

/-- The von Neumann entropy `S(ρ) = −tr[ρ log ρ]` in nats (natural logarithm), as
`Re tr f(ρ)` with `f(x) = −x log x` applied by the continuous functional calculus. -/
noncomputable def vnEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => -(x * Real.log x)) ρ).trace.re

/-- Footnote 4, p.8: the quantum mutual information `I(A : Ā)_σ := S(σ_A) + S(σ_Ā) − S(σ)`
between a set of sites `A` and its complement `Ā = [n] \ A`. -/
noncomputable def mutualInfo (A : Finset (Fin n)) (σ : Op n q) : ℝ :=
  vnEntropy (reducedState A σ) + vnEntropy (reducedState Aᶜ σ) - vnEntropy σ

end StationarityTest.Supplement


