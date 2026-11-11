-- Prove2me | Definitions.Def_DistQuantumQuery_Qdist
-- name    : DistQuantumQuery_Qdist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:41.738608+00:00
-- url     : https://prove2.me/theorems/e0a6c2c1-6dac-4122-9021-20bc5a068395
-- title:
--   Coherent phase oracle, $T$-query algorithms, projective measurements, distributional query complexity $Q^\mu_\varepsilon(f)$ and $Q(\Phi\to\Psi)$
-- statement:
--   **Model.** For inputs $x\in\Sigma\subseteq\{0,1\}^n$ the work register is $W=\mathcal I\otimes\mathcal A$, an index register with basis $|0\rangle,|1\rangle,\dots,|n\rangle$ and an ancilla. The **coherent oracle** acts by $O_x|0\rangle=|0\rangle$ and $O_x|i\rangle=(-1)^{x_i}|i\rangle$ for $i\in[n]$, trivially on the ancilla. A **$T$-query algorithm** is a list of input-independent unitaries $U_0,\dots,U_T$ on $W$; on input $x$ it maps a state $|\phi\rangle$ to
--   $$
--   U^x_Q|\phi\rangle=U_T(O_x\otimes I)U_{T-1}\cdots(O_x\otimes I)U_0|\phi\rangle,
--   $$
--   and its final work state is $|\psi_x\rangle=U^x_Q|0\rangle_W$. A **projective measurement** with finite outcome set $\Omega$ is a family of Hermitian projectors $\Pi_s$ with $\Pi_s\Pi_t=0$ for $s\ne t$ and $\sum_r\Pi_r=I$. The **Gram matrix** of a family $\{|\psi_x\rangle\}$ is $\Psi(x,y)=\langle\psi_x|\psi_y\rangle$.
--
--   **Distributional query complexity.** For a search problem $f\subseteq\Sigma\times\Omega$, a distribution $\mu$ and $\varepsilon\in[0,1)$, $Q^\mu_\varepsilon(f)$ is the least $t$ for which some $t$-query algorithm and some projective measurement satisfy
--   $$
--   \mathbb E_{x\sim\mu}\Big[\sum_{s\in f(x)}\langle\psi_x|\Pi_s|\psi_x\rangle\Big]\ge1-\varepsilon .
--   $$
--
--   **State conversion.** For Gram matrices $\Phi,\Psi$, $Q(\Phi\to\Psi)$ is the least $T$ such that some $T$-query algorithm maps $|\phi_x\rangle$ to $|\psi_x\rangle=U^x_Q|\phi_x\rangle$ for all $x$, where $\{|\phi_x\rangle\},\{|\psi_x\rangle\}$ realize $\Phi,\Psi$ in the work space; $Q(\Psi):=Q(J\to\Psi)$.
--
--   **Formalization Note** The index register is `Option ι` (`none` is the null index $|0\rangle$), the ancilla is $\mathbb C^{d+1}$ with $d$ existential (so it always contains the start vector $|0,0\rangle$). Both complexities are infima in $\mathbb N\cup\{\infty\}$. The page lists idempotence, orthogonality and completeness of $\Pi_s$ and reads outcome probabilities as $\mathrm{Tr}[\Pi_s\rho]$; the projectors are therefore written as Hermitian. For $Q(\Phi\to\Psi)$ the realizations are existential in the algorithm's work space instead of a fixed realization space; by Corollary 2.7 two realizations with the same Gram matrix differ by an input-independent unitary, absorbed into $U_0$. The success probability uses the real part of $\langle\psi_x|\Pi_s|\psi_x\rangle$, which is real.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 2.9 p.18, Definition 2.10 pp.18–19, Definition 2.11 p.19, §2.3.2 p.16, Definition 3.1 p.22

import Mathlib
import Definitions.Def_DistQuantumQuery_muMat

open scoped Matrix

namespace DistQuantumQuery

/-- The **work register** `W = I ⊗ A` of a query algorithm on `n = |ι|` input bits: the index
register `I ≅ ℂ^{n+1}` with basis `|0⟩, |1⟩, …, |n⟩` and an ancilla `A ≅ ℂ^d`
(Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.5.1, p.18).

**Formalization Note** The index basis is `Option ι`: `none` is the paper's null index `|0⟩`,
`some i` is `|i⟩`. -/
abbrev Work (ι : Type*) (d : ℕ) : Type _ := Option ι × Fin d

/-- The **coherent (phase) oracle** `O_x` on the work register, `O_x|0⟩ = |0⟩` and
`O_x|i⟩ = (−1)^{x_i}|i⟩` for `i ∈ [n]`, acting trivially on the ancilla
(arXiv:2610.06835, held version, sha256 6334ffaf…, Definition 2.9, p.18). -/
noncomputable def oracle {ι : Type*} [DecidableEq ι] (d : ℕ) (x : ι → Bool) :
    Matrix (Work ι d) (Work ι d) ℂ :=
  Matrix.diagonal fun w =>
    match w.1 with
    | none => 1
    | some i => if x i then -1 else 1

/-- A **`T`-query quantum algorithm** (arXiv:2610.06835, held version, sha256 6334ffaf…,
Definition 2.10, pp.18–19): `T + 1` input-independent unitaries `U_0, …, U_T` on the work
register `W = Option ι × Fin d`. -/
structure QueryAlg (ι : Type*) [Fintype ι] [DecidableEq ι] (d T : ℕ) where
  /-- the unitaries `U_0, …, U_T` -/
  U : Fin (T + 1) → Matrix.unitaryGroup (Work ι d) ℂ

namespace QueryAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d T : ℕ}

/-- `U_t` as a matrix, for `t ≤ T` (the identity for `t > T`, never used). -/
noncomputable def Umat (A : QueryAlg ι d T) (t : ℕ) : Matrix (Work ι d) (Work ι d) ℂ :=
  if h : t < T + 1 then (A.U ⟨t, h⟩ : Matrix (Work ι d) (Work ι d) ℂ) else 1

/-- The state after `t` queries started from `|φ⟩`:
`|ψ^0⟩ = U_0|φ⟩` and `|ψ^t⟩ = U_t O_x |ψ^{t−1}⟩` (arXiv:2610.06835, held version,
Definition 2.10, p.19 and Lemma 4.6, p.40). -/
noncomputable def stateFrom (A : QueryAlg ι d T) (x : ι → Bool) (φ : Work ι d → ℂ) :
    ℕ → Work ι d → ℂ
  | 0 => A.Umat 0 *ᵥ φ
  | t + 1 => A.Umat (t + 1) *ᵥ (oracle d x *ᵥ stateFrom A x φ t)

/-- The final state `U^x_Q|φ⟩ = U_T O_x U_{T−1} ⋯ O_x U_0 |φ⟩` (arXiv:2610.06835, held version,
Definition 2.10, p.19). -/
noncomputable def runFrom (A : QueryAlg ι d T) (x : ι → Bool) (φ : Work ι d → ℂ) :
    Work ι d → ℂ :=
  A.stateFrom x φ T

end QueryAlg

/-- The start state `|0⟩_W` of the work register: index `|0⟩` (`none`) and ancilla basis vector
`0` (arXiv:2610.06835, held version, Definition 2.10, p.19).

**Formalization Note** The ancilla is `Fin (d + 1)`, so it always has a basis vector `0`. -/
def startVec (ι : Type*) [DecidableEq ι] (d : ℕ) : Work ι (d + 1) → ℂ :=
  Pi.single (none, 0) 1

/-- The **Gram matrix** `Ψ(x, y) := ⟨ψ_x|ψ_y⟩` of a family of vectors (arXiv:2610.06835, held
version, §2.3.3, p.16 and Definition 2.10, p.19), conjugate-linear in the first argument. -/
def gram {X W : Type*} [Fintype W] (ψ : X → W → ℂ) : Matrix X X ℂ :=
  Matrix.of fun x y => star (ψ x) ⬝ᵥ ψ y

/-- A **projective measurement** with finite outcome set `Ω`: Hermitian idempotents
`Π_s² = Π_s`, `Π_sΠ_t = 0` for `s ≠ t`, `Σ_r Π_r = I` (arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.3.2, p.16).

**Formalization Note** The page lists idempotence, orthogonality and completeness and says the
probability of outcome `s` on `ρ` is `Tr[Π_s ρ]`; for these to be probabilities on every state
each `Π_s` must be an orthogonal (Hermitian) projector, which is written out here. -/
def IsProjMeas {W Ω : Type*} [Fintype W] [DecidableEq W] [Fintype Ω]
    (M : Ω → Matrix W W ℂ) : Prop :=
  (∀ s, (M s).IsHermitian) ∧ (∀ s, M s * M s = M s) ∧ (∀ s t, s ≠ t → M s * M t = 0) ∧
    ∑ r, M r = 1

open Classical in
/-- The average success probability `E_{x∼μ}[Σ_{s∈f(x)} ⟨ψ_x|Π_s|ψ_x⟩]` of an algorithm with
final states `ψ_x` and measurement `{Π_s}` on a search problem `R ⊆ Σ × Ω`
(arXiv:2610.06835, held version, Definition 3.1, p.22).

**Formalization Note** `⟨ψ_x|Π_s|ψ_x⟩` is real for a Hermitian `Π_s`; its real part is taken. -/
noncomputable def successProb {X W Ω : Type*} [Fintype X] [Fintype W] [Fintype Ω]
    (μ : X → ℝ) (R : X → Ω → Prop) (ψ : X → W → ℂ) (M : Ω → Matrix W W ℂ) : ℝ :=
  ∑ x, μ x * ∑ s, if R x s then (star (ψ x) ⬝ᵥ (M s *ᵥ ψ x)).re else 0

/-- **Distributional query complexity** `Q^μ_ε(f)` (arXiv:2610.06835, held version,
sha256 6334ffaf…, Definition 3.1, p.22): the minimum `t` such that some `t`-query algorithm, with
final states `|ψ_x⟩ = U^x_Q|0⟩_W`, and some projective measurement `{Π_s : s ∈ Ω}` on the work
register satisfy `E_{x∼μ}[Σ_{s∈f(x)} ⟨ψ_x|Π_s|ψ_x⟩] ≥ 1 − ε`.

**Formalization Note** Inputs form a `Finset` `Σ` of bit strings `ι → Bool` over a finite type of
positions `ι`; the search problem is a relation `R x s` ("`s ∈ f(x)`"); a functional problem
`f` enters as `graphRel f`. The ancilla `Fin (d + 1)` ("arbitrarily large") is existential. The
value is in `ℕ∞` (the infimum over achievable `t`; `⊤` would mean no algorithm, which never
happens for `ε ≥ 0` and a total relation). -/
noncomputable def Qdist {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (S : Finset (ι → Bool)) (μ : S → ℝ) (R : S → Ω → Prop) (ε : ℝ) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : ∃ (d : ℕ) (A : QueryAlg ι (d + 1) T) (M : Ω → Matrix (Work ι (d + 1))
      (Work ι (d + 1)) ℂ), IsProjMeas M ∧
        1 - ε ≤ successProb μ R (fun x => A.runFrom x.1 (startVec ι d)) M), (T : ℕ∞)

/-- The **query complexity of a Gram-matrix transformation** `Q(Φ → Ψ)` (arXiv:2610.06835, held
version, sha256 6334ffaf…, Definition 2.11, p.19): the minimum `T` such that some `T`-query
algorithm maps `|φ_x⟩` to `|ψ_x⟩ = U^x_Q|φ_x⟩` for all `x ∈ Σ`, where `{|φ_x⟩}`, `{|ψ_x⟩}` are
state families with Gram matrices `Φ`, `Ψ` realized in the work space. `Q(Ψ) := Q(J → Ψ)`.

**Formalization Note** The paper fixes a "sufficiently large" realization space `V` inside the
work space; here the realizations are existential in the algorithm's work space
`Option ι × Fin (d + 1)`. By Corollary 2.7 (p.16) two realizations with the same Gram matrix in a
space of the same dimension differ by an input-independent unitary, which can be absorbed into
`U_0`, so this is the paper's quantity. Value in `ℕ∞`. -/
noncomputable def QConv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → Bool)) (Φ Ψ : Matrix S S ℂ) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : ∃ (d : ℕ) (A : QueryAlg ι (d + 1) T) (φ ψ : S → Work ι (d + 1) → ℂ),
      gram φ = Φ ∧ gram ψ = Ψ ∧ ∀ x, A.runFrom x.1 (φ x) = ψ x), (T : ℕ∞)

end DistQuantumQuery


