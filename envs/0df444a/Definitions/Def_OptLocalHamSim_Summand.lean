-- Prove2me | Definitions.Def_OptLocalHamSim_Summand
-- name    : OptLocalHamSim_Summand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:43.890695+00:00
-- url     : https://prove2.me/theorems/6c351bd4-e9d4-4138-80f6-61f46205684f
-- title:
--   Pauli strings and the local Pauli summands $F_a=h_aP_a$ of Eq. (18), colorings with disjoint supports
-- statement:
--   Write $I,X,Y,Z$ for the one-qubit Pauli matrices and, for a finite set of qubits, $P_\sigma=\bigotimes_i\sigma_i$ for the **Pauli string** with factors $\sigma_i\in\{I,X,Y,Z\}$. The block Hamiltonian is expanded in Pauli strings:
--
--   $$
--   H=\sum_aF_a=\sum_{j=1}^cH_{j},\qquad F_a:=h_aP_a,\qquad H_{j}:=\sum_{a:\,\mathrm{col}(a)=j}F_a .
--   $$
--
--   Here a summand $a=(Z,\sigma)$ consists of a declared set $Z$ and a Pauli string $\sigma$ acting only on the data qubits of $Z$, with real coefficient $h_a=2^{-n}\mathrm{Tr}(P_\sigma h_Z)\ne0$; its declared support is $Z$. A **coloring** $\mathrm{col}$ into $c$ classes is proper if two distinct summands of the same color have disjoint declared supports.
--
--   The color Hamiltonians $H_j$ are the building blocks of the product formula (20)–(21); within a color the summands commute.
--
--   **Formalization Note** The expansion is the canonical Pauli expansion of each $h_Z$; summands with zero coefficient are dropped. The paper's coloring is greedy; any proper coloring is allowed here.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §3.1, eq. (18), p.14

import Mathlib
import Definitions.Def_OptLocalHamSim_IsLocalHam

namespace OptLocalHamSim

/-- The one-qubit Pauli matrices, indexed `0 ↦ I`, `1 ↦ X`, `2 ↦ Y`, `3 ↦ Z`, on the basis
`false = |0⟩`, `true = |1⟩`. -/
def pauliMat (k : Fin 4) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    if k = 0 then (if a = b then 1 else 0)
    else if k = 1 then (if a = b then 0 else 1)
    else if k = 2 then (if a = b then 0 else if a then Complex.I else -Complex.I)
    else (if a = b then (if a then -1 else 1) else 0)

/-- The Pauli string `⊗_i σ_{k_i}` on a finite set of qubits `ι`: a tensor product of `I, X, Y, Z`
(Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission, held version, sha256 44a9768a…, §3.1, p.14). -/
def pauliString {ι : Type} [Fintype ι] (σ : ι → Fin 4) : Matrix (ι → Bool) (ι → Bool) ℂ :=
  Matrix.of fun x y => ∏ i, pauliMat (σ i) (x i) (y i)

variable {D : ℕ} {L : Fin D → ℕ} {q : ℕ}

/-- The real Pauli coefficient `2^{−n} Tr(P_σ h_Z)` of the Hermitian term `h_Z` along the Pauli string
`P_σ` on the `n` data qubits. -/
noncomputable def pauliCoeff (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ)
    (Z : Finset (Site L)) (σ : Dat L q → Fin 4) : ℝ :=
  (Matrix.trace (pauliString σ * h Z) / (2 : ℂ) ^ Fintype.card (Dat L q)).re

/-- **The local summands of eq. (18)**, §3.1, p.14: the Pauli expansion
`H = ∑_a F_a`, `F_a := h_a P_a`, `h_a ∈ ℝ`, `P_a` a Hermitian Pauli string. A summand is a declared set
`Z` together with a Pauli string `σ` acting only on the data qubits of `Z`, with nonzero coefficient
`h_{Z,σ} = 2^{−n} Tr(P_σ h_Z)`. Its declared support is `Z` (the paper assigns each `F_a` "the declared
support" of its input term).

**Formalization Note** The expansion is the canonical Pauli expansion of every `h_Z`; summing `F_{Z,σ}`
over `σ` gives back `h_Z`. Zero summands are dropped. -/
abbrev Summand (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) : Type :=
  {a : Finset (Site L) × (Dat L q → Fin 4) //
    (∀ d : Dat L q, d.1 ∉ a.1 → a.2 d = 0) ∧ pauliCoeff h a.1 a.2 ≠ 0}

noncomputable instance (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) :
    Fintype (Summand h) := Fintype.ofFinite _

noncomputable instance (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ) :
    DecidableEq (Summand h) := Classical.decEq _

/-- The matrix `F_a = h_a P_a` of a summand. -/
noncomputable def summandMat {h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ}
    (a : Summand h) : Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ :=
  ((pauliCoeff h a.1.1 a.1.2 : ℝ) : ℂ) • pauliString a.1.2

/-- A coloring `col` of the summands into `c` classes with **disjoint (declared) supports within a
class** (§3.1, p.14: "greedy coloring uses a constant number c of classes, with disjoint supports
within a class"). -/
def IsProperColoring {h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ} {c : ℕ}
    (col : Summand h → Fin c) : Prop :=
  ∀ a b, a ≠ b → col a = col b → Disjoint a.1.1 b.1.1

/-- The color Hamiltonian `H_{blk,j} := ∑_{a : col(a) = j} F_a` of eq. (18). -/
noncomputable def colorHam {h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ}
    {c : ℕ} (col : Summand h → Fin c) (j : Fin c) : Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a => col a = j), summandMat a

end OptLocalHamSim


