-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
-- name    : OAI_InformationTheory_QuantumCircuit_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:09:53.681628+00:00
-- url     : https://prove2.me/theorems/8d3d0b12-17c5-402b-a86a-a19a9b105322
-- title:
--   Mismatch counts of product projections and depth-$d$ normal-form circuits
-- statement:
--   Throughout, the $N$ qubits are indexed by $i\in[N]=\{0,1,\dots,N-1\}$, a word is $x\in\{0,1\}^N$, and an operator on $N$ qubits is a complex $2^N\times2^N$ matrix indexed by words, i.e. an operator on $(\mathbb{C}^2)^{\otimes N}$ written in the computational basis $\{|x\rangle\}$. For $2\times2$ matrices $a_0,\dots,a_{N-1}$ the tensor product $\bigotimes_i a_i$ has entries $\prod_i (a_i)_{x_i y_i}$. The file defines:
--
--   1. **Rank-one qubit operator.** For $v\in\mathbb{C}^2$, $|v\rangle\langle v|$ is the $2\times2$ matrix with entries $v_x\overline{v_y}$; for a unit vector it is the orthogonal projection onto $\mathbb{C}v$.
--
--   2. **Counts.** A count $M$ on $N$ qubits consists of a support $S\subseteq[N]$ and one-qubit vectors $v_i\in\mathbb{C}^2$ ($i\in[N]$) such that $\sum_{b\in\{0,1\}}|v_i(b)|^2=1$ for every $i\in S$. Write $P_i=|v_i\rangle\langle v_i|$. A count encodes the observable "number of qubits $i\in S$ that are not in the state $v_i$".
--
--   3. **Zero projection.** $\Pi^M_0=\bigotimes_{i}Q_i$ with $Q_i=P_i$ for $i\in S$ and $Q_i=I$ for $i\notin S$: the product projection onto the states with no mismatch.
--
--   4. **Pattern projections.** For $F\subseteq[N]$, $\Pi^M_F=\bigotimes_i Q^F_i$, where $Q^F_i=I-P_i$ for $i\in S\cap F$, $Q^F_i=P_i$ for $i\in S\setminus F$, and $Q^F_i=I$ for $i\notin S$. For $F\subseteq S$ it projects onto the states whose mismatch set is exactly $F$.
--
--   5. **High projection.** For $r\in\mathbb{R}$,
--   $$
--   \Pi^M_{\ge r}=\sum_{F\subseteq S,\ |F|\ge r}\Pi^M_F ,
--   $$
--   the spectral projection of the count onto "at least $r$ mismatches".
--
--   6. **Mismatch operator.** $\widehat M=\sum_{i\in S}(I-P_i)_{(i)}$, where $(I-P_i)_{(i)}$ acts as $I-P_i$ on qubit $i$ and as the identity on the other qubits.
--
--   7. **Local layers.** A local layer is a family $L=(L_i)_{i\in[N]}$ of one-qubit unitaries $L_i\in U(2)$; its matrix is $\bigotimes_i L_i$.
--
--   8. **Reflection layers.** A reflection layer is a list of counts $A_1,\dots,A_m$ with pairwise disjoint supports; its matrix is the product $\prod_{j=1}^{m}\bigl(I-2\,\Pi^{A_j}_0\bigr)$ in list order.
--
--   9. **Normal-form circuits.** The class $\mathrm{Circ}_d$ is defined recursively: $U\in\mathrm{Circ}_0$ iff $U$ is the matrix of a local layer, and $U\in\mathrm{Circ}_{d+1}$ iff $U=V\,R\,L$ with $V\in\mathrm{Circ}_d$, $R$ the matrix of a reflection layer and $L$ the matrix of a local layer. Unrolling, $U=L_0R_1L_1R_2L_2\cdots R_dL_d$, where identity local layers and empty reflection layers are allowed.
--
--   10. **Localization statement.** The proposition: for every $d\in\mathbb{N}$ and all reals $s,t$ with $0\le s<t$ there is $N_0$ such that for all $N\ge N_0$, all $U\in\mathrm{Circ}_d$ on $N$ qubits and all counts $M,D$ on $N$ qubits,
--   $$
--   \bigl\|\,\Pi^M_{\ge N^t}\,U\,\Pi^D_0\,U^{*}\,\Pi^M_0\,\bigr\|\le e^{-N^{s}} .
--   $$
--
--   The reflections $I-2\Pi_0^{A}$ about product projections are the normal form of unbounded-arity Toffoli gates (a Toffoli gate is $I-2\Pi^A_0$ for the count $A$ that asks for $|1\rangle$ on the controls and $|-\rangle$ on the target), and one-qubit gates can be collected into local layers; this is how circuits of one-qubit and Toffoli gates are placed into $\mathrm{Circ}_d$. The localization statement says that a constant-depth circuit applied to the product projection $\Pi^D_0$ cannot connect the no-mismatch states of a count $M$ to states with at least $N^t$ mismatches, except with amplitude $e^{-N^s}$. It is the analytic core of the measured-output parity lower bound.
--
--   **Formalization Note** The base objects `Bit`, `Word N`, `Operator N`, `QubitOperator` and `tensorMatrix` come from the base definitions of the mission. The Lean names are `rankOne`, `Count` (fields `support`, `vector`, `normalized`), `Count.zero`, `Count.pattern`, `Count.high`, `Count.operator`, `LocalLayer`, `localMatrix`, `ReflectionLayer`, `reflectionMatrix`, `IsCircuit d U` and `LocalizationStatement`. The vectors $v_i$ for $i\notin S$ are arbitrary and never used. In `Count.high` the threshold is compared with the cardinality cast to a real number, and $N^t$ is the real power `(N : ℝ) ^ t`. The norm is the operator norm induced by the Euclidean norm (the spectral norm), from the scoped instance `Matrix.Norms.L2Operator`; in `reflectionMatrix` the scalar $2$ is complex.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff

namespace QAC

/-- The orthogonal projection onto a normalized one-qubit vector. -/
def rankOne (v : Bit → ℂ) : QubitOperator := fun x y => v x * star (v y)

/-- The same data describe a product projection and its mismatch count.
Normalization is exactly the sum of the squared moduli being one. -/
structure Count (N : ℕ) where
  support : Finset (Fin N)
  vector : Fin N → Bit → ℂ
  normalized : ∀ i ∈ support, ∑ b, Complex.normSq (vector i b) = 1

namespace Count

def zero {N : ℕ} (M : Count N) : Operator N :=
  tensorMatrix fun i => if i ∈ M.support then rankOne (M.vector i) else 1

/-- The orthogonal projection specifying precisely the mismatch set F.
It is used only for F contained in the counted support. -/
def pattern {N : ℕ} (M : Count N) (F : Finset (Fin N)) : Operator N :=
  tensorMatrix fun i => if i ∈ M.support then
    (if i ∈ F then 1 - rankOne (M.vector i) else rankOne (M.vector i)) else 1

/-- The spectral projection [M ≥ r], explicitly expanded in its product eigenbasis. -/
def high {N : ℕ} (M : Count N) (r : ℝ) : Operator N :=
  ∑ F ∈ M.support.powerset, if r ≤ (F.card : ℝ) then M.pattern F else 0

/-- The mismatch operator ∑ᵢ (I - |vᵢ⟩⟨vᵢ|)ᵢ. -/
def operator {N : ℕ} (M : Count N) : Operator N :=
  ∑ i ∈ M.support, tensorMatrix fun j => if j = i then 1 - rankOne (M.vector i) else 1

end Count

abbrev LocalLayer (N : ℕ) := Fin N → Matrix.unitaryGroup Bit ℂ

def localMatrix {N : ℕ} (L : LocalLayer N) : Operator N :=
  tensorMatrix fun i => (L i : QubitOperator)

/-- A parallel layer of product-projection reflections, with disjoint supports. -/
structure ReflectionLayer (N : ℕ) where
  gates : List (Count N)
  disjoint : gates.Pairwise (fun A B => Disjoint A.support B.support)

def reflectionMatrix {N : ℕ} (R : ReflectionLayer N) : Operator N :=
  (R.gates.map fun A => (1 : Operator N) - (2 : ℂ) • A.zero).prod

/-- The enlarged normal form of depth at most `d`.
Identity local and reflection layers are allowed. -/
def IsCircuit {N : ℕ} : ℕ → Operator N → Prop
  | 0, U => ∃ L : LocalLayer N, U = localMatrix L
  | d + 1, U => ∃ (V : Operator N) (R : ReflectionLayer N) (L : LocalLayer N),
      IsCircuit d V ∧ U = V * reflectionMatrix R * localMatrix L

/-- Full uniform localization theorem, including s = 0 and arbitrary t > s. -/
def LocalizationStatement : Prop :=
  ∀ (d : ℕ) (s t : ℝ), 0 ≤ s → s < t →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : Operator N, IsCircuit d U →
      ∀ M D : Count N,
        ‖M.high ((N : ℝ) ^ t) * U * D.zero * star U * M.zero‖ ≤
          Real.exp (-((N : ℝ) ^ s))

end QAC

end

end OAI


