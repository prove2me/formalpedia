-- Prove2me | Definitions.Def_OptQJunta_SamplerAlg
-- name    : OptQJunta_SamplerAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:38.709774+00:00
-- url     : https://prove2.me/theorems/7b00a9f4-1de2-42bf-b952-dfa06ec58e16
-- title:
--   Query circuits to a reversible sampler $A$ and $A^\dagger$; sampler distribution; Union Size Testing (Problem 3.1)
-- statement:
--   Let $A$ be a unitary on a finite-dimensional space $\mathbb C^V$. A **$T$-query circuit** to $A$ fixes, for each of its $T$ query slots, whether it calls $A$ or $A^\dagger$ (controlled versions are not supplied), applies that call to the $V$ register tensored with the identity on a finite workspace, and interleaves oracle-independent unitaries $U_0,\dots,U_T$; a **query algorithm** adds an oracle-independent unit start state and reads its output from the final measurement. A **known orthogonal projector** is a Hermitian idempotent matrix, and $p=\|\Pi A|0\rangle\|^2$.
--
--   A **reversible sampler** (§2.5.5) for a distribution $\mathcal D$ on $2^{[n]}$ is a unitary $A$ with
--
--   $$
--   A|0\rangle=\sum_{X\subseteq[n]}|X\rangle|\varphi_X\rangle,\qquad\|\varphi_X\|^2=\mathcal D(X).
--   $$
--
--   **Union Size Testing** (Problem 3.1) asks to distinguish (YES) some $T$ with $|T|\le k$ has $\Pr_{X\sim\mathcal D}[X\subseteq T]=1$ from (NO) every $T$ with $|T|\le k$ has $\Pr[X\not\subseteq T]\ge\delta$.
--
--   These objects state the reversible union-size tester (Theorem 3.19), amplitude amplification (Lemma 2.31) and amplitude estimation (Lemma 2.33).
--
--   **Formalization Note** The sampler's space is `Finset (Fin n) × Aux` (a subset is identified with its incidence string; `Aux` holds the auxiliary outputs), and its all-zero state is the basis state $(\varnothing,a_0)$; $\mathcal D$ is computed from $A$. The YES case is stated as $\mathcal D(X)=0$ for every $X\not\subseteq T$. The call pattern is fixed in advance; an adaptive choice of $A$ or $A^\dagger$ costs at most a factor $2$ to simulate.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.5.5, p.24; Problem 3.1, p.26; Lemmas 2.31, 2.33, pp.24–25

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace OptQJunta

open QAlgorithms

/-- A query circuit to a unitary `A` on a finite-dimensional space `ℂ^V` and its inverse `A†`
(Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256
a97d09a4…, §2.5.5, p.24: "One query is one ordinary call to `A` or to `A†`. Controlled versions of
`A` and `A†` are not supplied"). The circuit acts on `V × W`, `W` a finite workspace; slot `i` calls
`A` (`dir i = false`) or `A†` (`dir i = true`) on the `V` register, and the oracle-independent
unitaries `U_0, …, U_T` are interleaved.

**Formalization Note** The call pattern `dir` is fixed in advance. An adaptive choice between `A` and
`A†` is simulated by the alternating pattern at twice the cost (route the unused call to a fresh
garbage register), so fixing it loses no algorithm up to a factor `2`. -/
structure SamplerCirc (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (T : ℕ) where
  /-- Slot `i` calls `A†` if `dir i`, else `A`. -/
  dir : Fin T → Bool
  /-- The oracle-independent unitaries `U_0, …, U_T`. -/
  U : Fin (T + 1) → Matrix.unitaryGroup (V × W) ℂ

namespace SamplerCirc

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] {T : ℕ}

/-- The call `A` (if `b = false`) or `A†` (if `b = true`). -/
def call (A : Matrix V V ℂ) (b : Bool) : Matrix V V ℂ :=
  if b then A.conjTranspose else A

/-- The output `U_T (A^{(†)} ⊗ I_W) U_{T−1} ⋯ U_1 (A^{(†)} ⊗ I_W) U_0 ψ` of the circuit on input `ψ`. -/
noncomputable def run (C : SamplerCirc V W T) (A : Matrix V V ℂ) (ψ : EuclideanSpace ℂ (V × W)) :
    EuclideanSpace ℂ (V × W) :=
  (Fin.induction (motive := fun _ => EuclideanSpace ℂ (V × W)) (act (C.U 0 : Matrix _ _ ℂ) ψ)
    (fun i φ => act (C.U i.succ : Matrix _ _ ℂ)
      (act (Matrix.kronecker (call A (C.dir i)) (1 : Matrix W W ℂ)) φ))) (Fin.last T)

end SamplerCirc

/-- A query algorithm to a reversible sampler (Bao–Gao–Yao preprint, version of November 3, 2026,
sha256 a97d09a4…, §2.5 and §2.5.5, pp.22–24): a `SamplerCirc` with an oracle-independent unit start
state; its output is a function of the final computational-basis measurement.

**Formalization Note** Measurements and randomness are deferred (as for Boolean queries). -/
structure SamplerAlg (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (T : ℕ) extends SamplerCirc V W T where
  /-- The oracle-independent start state. -/
  start : EuclideanSpace ℂ (V × W)
  /-- It is a unit vector. -/
  start_unit : ‖start‖ = 1

namespace SamplerAlg

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] {T : ℕ}

/-- The final state on the sampler `A`. -/
noncomputable def finalState (M : SamplerAlg V W T) (A : Matrix V V ℂ) :
    EuclideanSpace ℂ (V × W) :=
  M.toSamplerCirc.run A M.start

/-- The probability that the algorithm outputs `b` on the sampler `A`. -/
noncomputable def outputProb {β : Type} [DecidableEq β] (M : SamplerAlg V W T) (A : Matrix V V ℂ)
    (out : V × W → β) (b : β) : ℝ :=
  probEvent (M.finalState A) fun z => out z = b

end SamplerAlg

/-- A known orthogonal projector: a Hermitian idempotent matrix (Bao–Gao–Yao preprint, version of
November 3, 2026, sha256 a97d09a4…, Lemmas 2.31 and 2.33, pp.24–25). -/
def IsOrthProj {V : Type} [Fintype V] [DecidableEq V] (P : Matrix V V ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- `p = ‖Π A |0⟩‖²`, the success probability of measuring the projector `Π` on `A|0⟩`, where `|0⟩`
is the basis state `v₀` (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…,
Lemmas 2.31 and 2.33, pp.24–25). -/
noncomputable def ampProb {V : Type} [Fintype V] [DecidableEq V] (P A : Matrix V V ℂ) (v₀ : V) : ℝ :=
  ‖act P (act A (ket v₀))‖ ^ 2

/-- The distribution `𝒟` on `2^{[n]}` of a reversible sampler (Bao–Gao–Yao preprint, version of
November 3, 2026, sha256 a97d09a4…, §2.5.5, p.24): `A|0⟩ = Σ_X |X⟩|φ_X⟩` and `𝒟(X) = ‖φ_X‖²`.

**Formalization Note** The sampler's space is `Finset (Fin n) × Aux` (a subset is identified with its
incidence string; `Aux` holds the auxiliary outputs), and its all-zero state `|0⟩` is the basis state
`(∅, a₀)`. -/
noncomputable def samplerDist {n : ℕ} {Aux : Type} [Fintype Aux] [DecidableEq Aux] (a₀ : Aux)
    (A : Matrix (Finset (Fin n) × Aux) (Finset (Fin n) × Aux) ℂ) (X : Finset (Fin n)) : ℝ :=
  ∑ a : Aux, ‖(act A (ket ((∅ : Finset (Fin n)), a₀))) (X, a)‖ ^ 2

/-- **Problem 3.1** (Union Size Testing; Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, p.26), YES case: some `T ⊆ [n]` with `|T| ≤ k` has `Pr_{X ∼ 𝒟}[X ⊆ T] = 1`.

**Formalization Note** Stated as: `𝒟` gives mass `0` to every `X ⊄ T` (for the probability
distribution of a sampler this is `Pr[X ⊆ T] = 1`). -/
def UnionYes {n : ℕ} (D : Finset (Fin n) → ℝ) (k : ℕ) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ k ∧ ∀ X : Finset (Fin n), ¬ X ⊆ T → D X = 0

/-- **Problem 3.1** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.26), NO
case: every `T ⊆ [n]` with `|T| ≤ k` has `Pr_{X ∼ 𝒟}[X ⊈ T] ≥ δ`. -/
def UnionNo {n : ℕ} (D : Finset (Fin n) → ℝ) (k : ℕ) (δ : ℝ) : Prop :=
  ∀ T : Finset (Fin n), T.card ≤ k → δ ≤ ∑ X ∈ Finset.univ.filter (fun X => ¬ X ⊆ T), D X

end OptQJunta


