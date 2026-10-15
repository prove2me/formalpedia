-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:08:31.154185+00:00
-- url     : https://prove2.me/theorems/78698257-e971-432c-9a75-6e7c09b65ceb
-- title:
--   Product projections, mismatch counts, normal-form circuits and the localization statement
-- statement:
--   This file sets up the operator vocabulary for the localization approach to constant-depth circuits. An $N$-qubit operator is a complex matrix indexed by $\{0,1\}^N\times\{0,1\}^N$; for one-qubit matrices $a_0,\dots,a_{N-1}\in\mathbb C^{2\times2}$ the tensor product $\bigotimes_i a_i$ has entries $\prod_i (a_i)_{x_i,y_i}$. The norm $\|\cdot\|$ is the operator norm induced by the Euclidean norm, and $U^{\ast}$ is the conjugate transpose.
--
--   1. **Rank-one projector.** For $v\in\mathbb C^2$, $|v\rangle\langle v|$ is the $2\times2$ matrix with entries $v_x\overline{v_y}$; for a unit vector it is the orthogonal projection onto $\mathbb C v$.
--   2. **Count data.** A count $M=(S,v)$ on $N$ qubits consists of a finite set $S\subseteq\{0,\dots,N-1\}$ (the support) and vectors $v_i\in\mathbb C^2$ for all qubits $i$, such that $\sum_{b}|v_i(b)|^2=1$ for every $i\in S$. Write $\Pi_i=|v_i\rangle\langle v_i|$; the $v_i$ are reference axes, and a qubit $i\in S$ is "mismatched" if it is orthogonal to $v_i$.
--   3. **Zero-mismatch projection.** $P_M^0=\bigotimes_i A_i$ with $A_i=\Pi_i$ for $i\in S$ and $A_i=I$ for $i\notin S$.
--   4. **Mismatch patterns.** For a finite set $F$ of qubits,
--   $$
--   P_M^F=\bigotimes_i A_i^F,\qquad A_i^F=\begin{cases}I-\Pi_i & i\in S\cap F,\\ \Pi_i & i\in S\setminus F,\\ I & i\notin S.\end{cases}
--   $$
--   For $F\subseteq S$ this is the projection onto the states whose mismatch set is exactly $F$.
--   5. **High projection.** For $r\in\mathbb R$, $[\mathcal N_M\ge r]=\sum_{F\subseteq S,\ |F|\ge r}P_M^F$, the spectral projection of the mismatch count onto the values at least $r$.
--   6. **Mismatch operator.** $\mathcal N_M=\sum_{i\in S}(I-\Pi_i)_{(i)}$, where $(B)_{(i)}$ denotes $B$ acting on qubit $i$ and the identity elsewhere.
--   7. **Local layers.** A local layer is a family $L=(L_0,\dots,L_{N-1})$ of $2\times2$ unitaries, with matrix $\bigotimes_i L_i$.
--   8. **Reflection layers.** A reflection layer is a list $(A_1,\dots,A_m)$ of counts whose supports are pairwise disjoint; its matrix is the ordered product $\prod_{j=1}^m\bigl(I-2P_{A_j}^0\bigr)$.
--   9. **Normal-form circuits.** The predicate "$U$ is a circuit of depth $d$" is defined by recursion: depth $0$ means $U$ is the matrix of a local layer; depth $d+1$ means $U=V\,R\,L$ with $V$ of depth $d$, $R$ the matrix of a reflection layer and $L$ the matrix of a local layer. Thus $U=L_0R_1L_1R_2\cdots R_dL_d$; identity layers are allowed, so this really means depth at most $d$.
--   10. **Localization statement.** The proposition: for every $d\in\mathbb N$ and all real $s,t$ with $0\le s<t$ there is $N_0$ such that for all $N\ge N_0$, every depth-$d$ circuit $U$ on $N$ qubits and all counts $M,D$ on $N$ qubits,
--   $$
--   \bigl\|\,[\mathcal N_M\ge N^t]\;U\,P_D^0\,U^{\ast}\;P_M^0\,\bigr\|\ \le\ e^{-N^s}.
--   $$
--
--   The localization statement says that a constant-depth circuit cannot move a product state with zero mismatches relative to one product basis (after conjugating another product projection) to a state with polynomially many mismatches, except with exponentially small amplitude, uniformly over all product bases. It is the central technical input for the parity lower bound, where the Toffoli gates are rewritten as reflections $I-2P^0_A$.
--
--   **Formalization Note** The count structure is `Count` with fields `support`, `vector`, `normalized`; items 3 to 6 are `Count.zero`, `Count.pattern`, `Count.high`, `Count.operator`; items 9 and 10 are `IsCircuit` and `LocalizationStatement`. Vectors $v_i$ for $i\notin S$ play no role. The norm is `Matrix.Norms.L2Operator`, and $N^t$, $N^s$ are real powers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model

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


