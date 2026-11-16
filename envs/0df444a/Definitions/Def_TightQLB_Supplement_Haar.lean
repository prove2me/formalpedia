-- Prove2me | Definitions.Def_TightQLB_Supplement_Haar
-- name    : TightQLB_Supplement_Haar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:17:55.12838+00:00
-- url     : https://prove2.me/theorems/7771f514-e3d2-4c4e-85c3-299c636ecdf3
-- title:
--   The Haar ensemble, the canonical oracle $O_\phi$, experiments with $s$ supplied copies, $\beta_N$, $\Lambda_{s,q}$ and $H_N$
-- statement:
--   Fix $n\ge1$ and $N=2^n$, and identify $[N]$ with $\{0,1\}^n$. In the **Haar ensemble** the oracle hides a uniformly random unit vector $|\phi\rangle=\sum_x\alpha_x|x\rangle$ of $\mathbb C^N$ (a unit vector, not a ray: the global phase matters), and the ideal distribution is $p_\phi(x)=|\alpha_x|^2$. The query register is $Q=\mathbb C|\bot\rangle\oplus\mathbb C^N$ and the **canonical oracle** is
--
--   $$
--   O_\phi=I-|\bot\rangle\langle\bot|+|\bot\rangle\langle\phi|+|\phi\rangle\langle\bot|-|\phi\rangle\langle\phi| ,
--   $$
--
--   the reflection $I-2|\eta_\phi\rangle\langle\eta_\phi|$ with $|\eta_\phi\rangle=(|\bot\rangle-|\phi\rangle)/\sqrt2$, which swaps $|\bot\rangle$ and $|\phi\rangle$.
--
--   The module also defines:
--
--   1. the expected score $B(\mathcal A)=\mathbb E_\phi\sum_z\Pr[Z=z\mid\phi]\,N|\alpha_z|^2$ of an experiment of Definition 3.1 with the canonical oracle;
--   2. an **experiment with $s$ supplied copies**: the device registers additionally hold $s$ registers $\mathbb C^N$ prepared in $|\phi\rangle^{\otimes s}$, tensored with an oracle-independent joint state $\sigma_0$ of the rest of the device and Eve's register; it then runs $q+1$ oracle-independent CPTP rounds with $q$ controlled canonical queries in between and a final POVM; Eve's conditional states, the output probabilities and the score are as in Definition 3.1;
--   3. the **normal form with copies**: an oracle-independent unit vector $\psi_0$, oracle-independent unitaries $U_0,\dots,U_q$, and the final state $\Psi(\phi)=(V_\phi\otimes I_E)(|\phi\rangle^{\otimes s}\otimes\psi_0)$ with $V_\phi=U_qO^c_\phi U_{q-1}\cdots O^c_\phi U_0$;
--   4. the ideal score $\beta_N=2N/(N+1)$, the constant $c_0=54$, the harmonic number $H_N=\sum_{j=1}^N1/j$, and
--   $$
--   \Lambda_{s,q}=\sqrt{\frac{s(s-1)}{N+s-1}}+\frac{c_0}{\sqrt N}\sum_{t=0}^{q-1}\sqrt{s+2t+1}.
--   $$
--
--   These objects state the Haar lower bounds (Theorems 5.6, 5.25), the heavy-output bounds (Theorem 6.12) and the Haar randomness theorem (Theorem 7.9).
--
--   **Formalization Note** The Haar law is the published `QAlgorithms.TwoBasisCertification.haarTargetLaw` (the standard Gaussian on $\mathbb C^N$ normalized). $Q$ is `Option (Qubits n)` with `none` $=\bot$. Experiments reuse the published registers, controlled query `queryOn`, CPTP maps and partial trace of the base mission; the copy registers are `Fin s → Qubits n`, part of the device workspace. $c_0=54$ is the value the paper's proof gives (p. 44).
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, Eqs. (10)–(13), pp. 13–14 (PDF pp. 16–17); §3.2, p. 15 (PDF p. 18); §5, pp. 29–30 (PDF pp. 32–33); Theorem 5.6, p. 34 (PDF p. 37); p. 44 (PDF p. 47); Lemma 5.24, p. 45 (PDF p. 48)

import Mathlib
import Definitions.Def_TightQLB_Experiment
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates
open QAlgorithms MeasureTheory
open scoped ComplexOrder Matrix

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# The Haar ensemble, the canonical oracle, and experiments with supplied copies

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, Eqs. (10)–(13),
pp.13–14 (PDF pp.16–17); §3.2, Definition 3.1 and the paragraph after it, p.15 (PDF p.18); §5,
pp.29–30 (PDF pp.32–33); Theorem 5.6, p.34 (PDF p.37); Lemma 5.24, p.45 (PDF p.48).

"The oracle hides a uniformly random unit vector `|ϕ⟩ = Σ_x α_x|x⟩` in `C^N`, and the ideal
distribution is `p_ϕ(x) = |α_x|²`. The ensemble is a distribution on unit vectors rather than on
rays." The query register is `Q = C|⊥⟩ ⊕ C^N` and the canonical oracle is
`O_ϕ = I − |⊥⟩⟨⊥| + |⊥⟩⟨ϕ| + |ϕ⟩⟨⊥| − |ϕ⟩⟨ϕ|` (11). "In Section 5 the device may in addition
receive `s` copies of `|ϕ⟩` in registers of `A` before its first query."

**Formalization Note.**
* `[N]` is identified with `{0,1}^n = Qubits n` (§3.1), `N = 2^n` is `(2 : ℝ) ^ n`.
* The Haar law on unit vectors of `C^N` is the published
  `QAlgorithms.TwoBasisCertification.haarTargetLaw n`: the standard Gaussian on `C^N` pushed forward
  by normalization (the null vector, a null set, goes to `|0ⁿ⟩`). It is a law on unit vectors, not
  on rays, as §3.1 requires.
* `Q = C|⊥⟩ ⊕ C^N` is `Option (Qubits n)`, with `none = ⊥`.
* An experiment with `s` supplied copies is Definition 3.1 in the channel form of the published
  `TightQLB.Experiment`, with the copy registers `(C^N)^{⊗s} = Fin s → Qubits n` adjoined to the
  device workspace; the initial state is `|ϕ⟩⟨ϕ|^{⊗s} ⊗ σ₀` with `σ₀` an oracle-independent density
  matrix. With `s = 0` the copy register is a single point and this is the published experiment.
-/

/-- The Haar law on unit vectors of `C^N`, `N = 2^n` (§3.1, p.13, PDF p.16): the published
`haarTargetLaw`. -/
noncomputable abbrev haar (n : ℕ) : Measure (EuclideanSpace ℂ (Qubits n)) :=
  QAlgorithms.TwoBasisCertification.haarTargetLaw n

/-- The ideal distribution `p_ϕ(x) = |α_x|²` (§3.1, p.13, PDF p.16). -/
noncomputable def pOf {n : ℕ} (ϕ : EuclideanSpace ℂ (Qubits n)) (x : Qubits n) : ℝ :=
  ‖ϕ x‖ ^ 2

/-- Eq. (11), p.14 (PDF p.17): the canonical oracle
`O_ϕ = I − |⊥⟩⟨⊥| + |⊥⟩⟨ϕ| + |ϕ⟩⟨⊥| − |ϕ⟩⟨ϕ|` on `Q = C|⊥⟩ ⊕ C^N` (`none = ⊥`). -/
noncomputable def canonOracle {ι : Type} [DecidableEq ι] (ϕ : EuclideanSpace ℂ ι) :
    Matrix (Option ι) (Option ι) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | none, none => 0
    | none, some y => star (ϕ y)
    | some x, none => ϕ x
    | some x, some y => (if x = y then 1 else 0) - ϕ x * star (ϕ y)

/-- §5, p.29 (PDF p.32): the ideal score of the Haar ensemble, `β_N = 2N/(N + 1)`. -/
noncomputable def betaN (n : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ n / ((2 : ℝ) ^ n + 1)

/-- p.44 (PDF p.47): "The proof gives `c₀ = 54`" — the absolute constant of Theorems 5.6 and 5.21. -/
noncomputable def c0 : ℝ := 54

/-- Theorem 5.6, p.34 (PDF p.37):
`Λ_{s,q} = √(s(s − 1)/(N + s − 1)) + (c₀/√N) Σ_{t=0}^{q−1} √(s + 2t + 1)`, with `c₀ = 54`. -/
noncomputable def Lam (n s q : ℕ) : ℝ :=
  Real.sqrt ((s : ℝ) * ((s : ℝ) - 1) / ((2 : ℝ) ^ n + s - 1)) +
    c0 / Real.sqrt ((2 : ℝ) ^ n) * ∑ t ∈ Finset.range q, Real.sqrt ((s : ℝ) + 2 * t + 1)

/-- Lemma 5.24, p.45 (PDF p.48): the harmonic number `H_N = Σ_{j=1}^N 1/j`, `N = 2^n`. -/
noncomputable def harmonicN (n : ℕ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 (2 ^ n) : Finset ℕ), (1 : ℝ) / (j : ℝ)

/-- Eq. (12), p.14 (PDF p.17), in the Haar ensemble with the canonical oracle and no supplied
copies: `B(A) = E_ϕ Σ_z Pr[Z = z | ϕ] · N|α_z|²` for the published experiment with query register
`Q = Option (Qubits n)` and oracle `O_ϕ`. -/
noncomputable def haarScore {n q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E]
    [DecidableEq E] (A : Experiment n q (Option (Qubits n)) W E) : ℝ :=
  ∫ ϕ, ∑ z, A.outProb (canonOracle ϕ) z * ((2 : ℝ) ^ n * pOf ϕ z) ∂(haar n)

/-- The workspace of a device holding `s` copy registers `C^N` next to a finite workspace `W`. -/
abbrev CopyW (n s : ℕ) (W : Type) := (Fin s → Qubits n) × W

/-- `|ϕ⟩^{⊗s}`: the amplitude of `|x₁, …, x_s⟩` is `α_{x₁} ⋯ α_{x_s}` (proof of Lemma 5.1, p.30,
PDF p.33). -/
noncomputable def copiesAmp {n s : ℕ} (ϕ : EuclideanSpace ℂ (Qubits n)) (x : Fin s → Qubits n) :
    ℂ :=
  ∏ k, ϕ (x k)

/-- Definition 3.1 (p.15, PDF p.18) with the canonical oracle and `s` copies of `|ϕ⟩` supplied in
device registers before the first query, in the channel form of `TightQLB.Experiment`. The device
register is `Reg Q (CopyW n s W) = (C × Q) × ((C^N)^{⊗s} × W)` with `Q = Option (Qubits n)`. -/
structure CopyExperiment (n q s : ℕ) (W E : Type) [Fintype W] [DecidableEq W] [Fintype E]
    [DecidableEq E] where
  /-- The oracle-independent joint state of `C × Q × W` and Eve's `E`. -/
  σ₀ : Matrix (Reg (Option (Qubits n)) W × E) (Reg (Option (Qubits n)) W × E) ℂ
  /-- `σ₀` is a density matrix. -/
  σ₀_density : PeresTerno.IsDensityMatrix σ₀
  /-- The oracle-independent operations of the `q + 1` rounds on the device register. -/
  Φ : Fin (q + 1) → Matrix (Reg (Option (Qubits n)) (CopyW n s W))
    (Reg (Option (Qubits n)) (CopyW n s W)) ℂ →
    Matrix (Reg (Option (Qubits n)) (CopyW n s W)) (Reg (Option (Qubits n)) (CopyW n s W)) ℂ
  /-- Each round is a CPTP map. -/
  Φ_cptp : ∀ t, AKNMixed.FQP.IsQuantumOperation (Φ t)
  /-- The output POVM on the device register. -/
  M : Qubits n → Matrix (Reg (Option (Qubits n)) (CopyW n s W))
    (Reg (Option (Qubits n)) (CopyW n s W)) ℂ
  /-- Its elements are positive semidefinite. -/
  M_psd : ∀ z, (M z).PosSemidef
  /-- They sum to the identity. -/
  M_sum : ∑ z, M z = 1

namespace CopyExperiment

variable {n q s : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]

/-- The initial state `|ϕ⟩⟨ϕ|^{⊗s} ⊗ σ₀` of `A × E`, the copies sitting in the copy registers. -/
noncomputable def initState (A : CopyExperiment n q s W E) (ϕ : EuclideanSpace ℂ (Qubits n)) :
    Matrix (Reg (Option (Qubits n)) (CopyW n s W) × E)
      (Reg (Option (Qubits n)) (CopyW n s W) × E) ℂ :=
  fun i j => copiesAmp ϕ i.1.2.1 * star (copiesAmp ϕ j.1.2.1) *
    A.σ₀ ((i.1.1, i.1.2.2), i.2) ((j.1.1, j.1.2.2), j.2)

/-- The state of `A × E` after round `t`, exactly as `TightQLB.Experiment.state`, for the oracle
`O_ϕ`. -/
noncomputable def state (A : CopyExperiment n q s W E) (ϕ : EuclideanSpace ℂ (Qubits n)) :
    Fin (q + 1) → Matrix (Reg (Option (Qubits n)) (CopyW n s W) × E)
      (Reg (Option (Qubits n)) (CopyW n s W) × E) ℂ :=
  Fin.induction (PeresTerno.ampliate (A.Φ 0) (A.initState ϕ))
    (fun t ρ => PeresTerno.ampliate (A.Φ t.succ)
      (Matrix.kronecker (queryOn (canonOracle ϕ) (CopyW n s W)) (1 : Matrix E E ℂ) * ρ *
        (Matrix.kronecker (queryOn (canonOracle ϕ) (CopyW n s W)) (1 : Matrix E E ℂ))ᴴ))

/-- Eve's subnormalized state `ρ^ϕ_z = Tr_A[(M_z ⊗ I_E) ρ_final]` on the event `Z = z`. -/
noncomputable def eveState (A : CopyExperiment n q s W E) (ϕ : EuclideanSpace ℂ (Qubits n))
    (z : Qubits n) : Matrix E E ℂ :=
  WildeQIT.partialTraceLeft
    (Matrix.kronecker (A.M z) (1 : Matrix E E ℂ) * A.state ϕ (Fin.last q))

/-- `Pr[Z = z | ϕ]`. -/
noncomputable def outProb (A : CopyExperiment n q s W E) (ϕ : EuclideanSpace ℂ (Qubits n))
    (z : Qubits n) : ℝ :=
  (A.eveState ϕ z).trace.re

/-- Eq. (12): the expected score `B(A) = E_ϕ Σ_z Pr[Z = z | ϕ] · N|α_z|²`. -/
noncomputable def score (A : CopyExperiment n q s W E) : ℝ :=
  ∫ ϕ, ∑ z, A.outProb ϕ z * ((2 : ℝ) ^ n * pOf ϕ z) ∂(haar n)

end CopyExperiment

/-- The normal form of Lemma 3.2 with `s` supplied copies (p.15, PDF p.18: "Lemma 3.2 applies to
this variant, with `ψ₀` replaced by the oracle-dependent vector `|ϕ⟩^{⊗s} ⊗ ψ₀`"; §5, p.30, PDF
p.33): an oracle-independent unit vector `ψ₀` of `C × Q × W` and `E`, and oracle-independent
unitaries `U₀, …, U_q` on the device register `(C × Q) × ((C^N)^{⊗s} × W)`. -/
structure CopyNormalForm (n q s : ℕ) (W E : Type) [Fintype W] [DecidableEq W] [Fintype E]
    [DecidableEq E] where
  /-- The oracle-independent unit vector `ψ₀`. -/
  ψ₀ : EuclideanSpace ℂ (Reg (Option (Qubits n)) W × E)
  /-- `ψ₀` is a unit vector. -/
  ψ₀_unit : ‖ψ₀‖ = 1
  /-- The oracle-independent unitaries. -/
  U : Fin (q + 1) → Matrix.unitaryGroup (Reg (Option (Qubits n)) (CopyW n s W)) ℂ

namespace CopyNormalForm

variable {n q s : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]

/-- Eq. (15): `V_ϕ = U_q O^c_ϕ U_{q−1} ⋯ U₁ O^c_ϕ U₀` (as `TightQLB.NormalForm.V`). -/
noncomputable def V (B : CopyNormalForm n q s W E) (ϕ : EuclideanSpace ℂ (Qubits n)) :
    Matrix (Reg (Option (Qubits n)) (CopyW n s W)) (Reg (Option (Qubits n)) (CopyW n s W)) ℂ :=
  Fin.induction (B.U 0 : Matrix _ _ ℂ)
    (fun t M => (B.U t.succ : Matrix _ _ ℂ) * queryOn (canonOracle ϕ) (CopyW n s W) * M)
    (Fin.last q)

/-- The initial vector `|ϕ⟩^{⊗s} ⊗ ψ₀`. -/
noncomputable def initVec (B : CopyNormalForm n q s W E) (ϕ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Reg (Option (Qubits n)) (CopyW n s W) × E) :=
  WithLp.toLp 2 (fun i => copiesAmp ϕ i.1.2.1 * B.ψ₀ ((i.1.1, i.1.2.2), i.2))

/-- §5, p.30 (PDF p.33): the final state `Ψ(ϕ) = (V_ϕ ⊗ I_E)(|ϕ⟩^{⊗s} ⊗ ψ₀)`. -/
noncomputable def finalState (B : CopyNormalForm n q s W E) (ϕ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Reg (Option (Qubits n)) (CopyW n s W) × E) :=
  act (Matrix.kronecker (B.V ϕ) (1 : Matrix E E ℂ)) (B.initVec ϕ)

end CopyNormalForm

end TightQLB.Supplement


