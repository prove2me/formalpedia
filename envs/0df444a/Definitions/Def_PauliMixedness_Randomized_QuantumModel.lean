-- Prove2me | Definitions.Def_PauliMixedness_Randomized_QuantumModel
-- name    : PauliMixedness_Randomized_QuantumModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:45:55.324463+00:00
-- url     : https://prove2.me/theorems/dee081f1-e8b7-4728-945d-5661067fd135
-- title:
--   Physical product Pauli effects and nonidentity influence
-- statement:
--   An $N$-qubit operator is a complex matrix on all $2^N$ computational basis vectors. States use the published predicate $\rho\succeq0$, $\operatorname{Tr}\rho=1$. The maximally mixed state is $\rho_{\rm mm}=2^{-N}I$. A setting $P\in\{X,Y,Z\}^N$ chooses a basis on each wire. The source convention is $Y=\left[\begin{smallmatrix}0&i\\-i&0\end{smallmatrix}\right]$; identity is allowed in words, but never as a setting. For $S\subseteq[N]$, $P^S$ uses $P_j$ on $S$ and identity elsewhere. Define
--
--   $$M_x^P=\bigotimes_j\frac{I+(-1)^{x_j}P_j}{2},\qquad r_{\rho,P}(x)=\operatorname{Re}\operatorname{Tr}(M_x^P\rho).$$
--
--   Coefficients are $\alpha_Q=\operatorname{Re}\operatorname{Tr}(Q\rho)$ and $\alpha_P(S)=\operatorname{Re}\operatorname{Tr}(P^S\rho)$. The nonidentity energy and influence are
--
--   $$L=\sum_{Q\ne I}\alpha_Q^2,\qquad L_P=\sum_{S\ne\varnothing}3^{|S|}\alpha_P(S)^2.$$
--
--   These are computed from the matrix, with no expansion or detectability axiom. The physical Born mass is defined independently of its Fourier expansion. The unhalved trace norm is reused from the published matrix-distance definition: $\|A\|_1=\operatorname{Re}\operatorname{Tr}\sqrt{A^\dagger A}$. Identity normalization is $\alpha_I=1$ for states, correcting inconsistent intermediate prose on p.9; the identity contribution to $\rho$ is $I/2^N$.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Definition 2.1 p.6, §§3.1–3.4 pp.9–11, Observation 3.2 pp.10–11

import Definitions.Def_PauliMixedness_Randomized_CubeFourier
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

noncomputable section
open scoped BigOperators Matrix

namespace PauliMixedness.Randomized

/-- §§3.1–3.2: arbitrary complex matrices on all N qubits. -/
abbrev Operator (N : ℕ) := Matrix (QAlgorithms.Qubits N) (QAlgorithms.Qubits N) ℂ

/-- X, Y, Z, in this order; identity is not a measurement setting. -/
abbrev Setting (N : ℕ) := Fin N → Fin 3

/-- Identity, X, Y, Z, in this order. -/
abbrev Word (N : ℕ) := Fin N → Fin 4

/-- §3.1 p.9: the paper's Y has upper-right entry +i, opposite the
published gate convention. Other matrix and wire conventions agree. -/
def localPauli (a : Fin 4) : Matrix Bool Bool ℂ :=
  if a = 0 then 1 else if a = 1 then QAlgorithms.pauliX
  else if a = 2 then -QAlgorithms.pauliY else QAlgorithms.pauliZ

/-- The tensor Pauli word, with the source's Y convention. -/
def wordMatrix {N : ℕ} (Q : Word N) : Operator N :=
  QAlgorithms.kronAll (fun j => localPauli (Q j))

/-- P^S, including the full identity for S = ∅. -/
def pauliOn {N : ℕ} (P : Setting N) (S : Finset (Fin N)) : Operator N :=
  wordMatrix (fun j => if j ∈ S then ⟨(P j).val + 1, by omega⟩ else 0)

/-- §3.2 p.9: maximally mixed state I / 2^N; α_Id = 1, not 1/d. -/
def maximallyMixed (N : ℕ) : Operator N := ((2 : ℂ)^N)⁻¹ • 1

/-- §3.2: α_Q = Re Tr(Qρ). No expansion is assumed of the input. -/
def pauliCoeff {N : ℕ} (ρ : Operator N) (Q : Word N) : ℝ :=
  QAlgorithms.effectProb (wordMatrix Q) ρ

/-- The coefficient α_P(S), including α_P(∅) = 1 on density matrices. -/
def basisCoeff {N : ℕ} (ρ : Operator N) (P : Setting N) (S : Finset (Fin N)) : ℝ :=
  QAlgorithms.effectProb (pauliOn P S) ρ

/-- §2.1 / §3.2: L = Σ_{Q ≠ Id} α_Q². -/
def totalPauliEnergy {N : ℕ} (ρ : Operator N) : ℝ :=
  ∑ Q : Word N, if Q = (fun _ => 0) then 0 else pauliCoeff ρ Q ^ 2

/-- Definition 2.1 p.6: L_P omits the empty subset. -/
def pauliInfluence {N : ℕ} (ρ : Operator N) (P : Setting N) : ℝ :=
  ∑ S : Finset (Fin N), if S = ∅ then 0 else (3 : ℝ)^S.card * basisCoeff ρ P S ^ 2

/-- Observation 3.2 pp.10–11: physical N-bit product basis effect.
No Fourier expansion or correctness condition is built into this object. -/
def basisEffect {N : ℕ} (P : Setting N) (x : Cube N) : Operator N :=
  QAlgorithms.kronAll (fun j => (2 : ℂ)⁻¹ •
    (1 + (sign (x j) : ℂ) • localPauli ⟨(P j).val + 1, by omega⟩))

/-- §3.3: actual Born mass Re Tr(M_x^P ρ). Positivity and normalization
for density matrices follow from the physical effects; no oracle is supplied. -/
def outcomeMass {N : ℕ} (ρ : Operator N) (P : Setting N) (x : Cube N) : ℝ :=
  QAlgorithms.effectProb (basisEffect P x) ρ

end PauliMixedness.Randomized


