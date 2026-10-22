-- Prove2me | Definitions.Def_EastinKnill_Transversal_Setting
-- name    : EastinKnill_Transversal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:25:59.580853+00:00
-- url     : https://prove2.me/theorems/1f84c384-6af1-4a32-aece-3f1e9c35067f
-- title:
--   pp. 1–2, Eq. (1) — product operators, codes as projectors, logical and encoded unitaries, local error detection, universality, block codes
-- statement:
--   This file fixes the objects of Eastin and Knill's no-go theorem for transversal gates.
--
--   **The composite system.** A quantum system $\mathcal Q$ consists of finitely many physical subsystems $j \in \iota$; subsystem $j$ has an orthonormal basis indexed by a finite set $\alpha_j$, so its dimension is $d_j = |\alpha_j|$. The composite system has basis indexed by tuples $a = (a_j)_{j}$, and operators on it are complex matrices indexed by such tuples.
--
--   1. **Product operators.** For operators $U_j$ on the subsystems, $\bigotimes_j U_j$ is the operator with matrix entries $\left(\bigotimes_j U_j\right)_{a,b} = \prod_j (U_j)_{a_j b_j}$. For an operator $E$ on subsystem $j$, $I\otimes E\otimes I$ denotes the product operator with $E$ in slot $j$ and the identity in every other slot.
--   2. **The group $\mathcal T$.** $\mathcal T$ is the set of unitary product operators $\bigotimes_j U_j$ with each $U_j \in \mathcal U(d_j)$ unitary.
--   3. **Codes.** A quantum code is given by the projector $P$ onto its code space: $P$ is Hermitian and $P^2 = P$. The dimension of the code (of the encoded system) is the rank of $P$.
--   4. **Logical operators (Eq. (1)).** A unitary $U$ is *logical* for the code if it preserves the code space, that is,
--   $$(I-P)\,U\,P = 0.$$
--   5. **Local error detection.** An error $E$ is detectable when $PEP \propto P$. The code is *local-error-detecting* if every error on any single subsystem is detectable: for every $j$ and every operator $E$ on subsystem $j$ there is $c \in \mathbb C$ with $P\,(I\otimes E\otimes I)\,P = c\,P$.
--   6. **Encoded unitaries.** An encoded unitary is a unitary operator of the code space, written as an operator $W$ on the whole system with $PWP = W$ and $W^\dagger W = W W^\dagger = P$.
--   7. **Universality.** A set $S$ of unitaries is *universal* for the code if every encoded unitary $W$ is approximated to arbitrary accuracy by the action $PUP$ of gates $U\in S$ on the code space, i.e. $W$ lies in the closure of $\{PUP : U \in S\}$.
--   8. **The group $\mathcal G$.** $\mathcal G = \mathcal T \cap \mathcal L$ is the set of logical unitary product operators, where $\mathcal L$ is the set of logical unitaries.
--   9. **Block codes.** For code blocks $b \in \beta$, each made of subsystems at the same positions $j \in \iota$ (subsystem $j$ of block $b$ has basis $\alpha_{b,j}$), and a code $P_b$ on each block, the joint code is $\bigotimes_b P_b$. It is written on the system whose parts are the transversal parts: part $j$ collects subsystem $j$ of every block, with basis $\prod_b \alpha_{b,j}$.
--
--   These are the objects in terms of which the mission's theorems are stated.
--
--   **Formalization Note** A subsystem is an index type rather than $\mathrm{Fin}\,d_j$, so that a transversal part (a product of index types) is again a subsystem and Theorem 1 applies to the parts verbatim. The closure in item 7 is taken in the standard topology on complex matrices; since the space is finite-dimensional this is the topology of every operator norm. The factor $i$ in the exponential map of the physics convention (footnote 1) appears in the theorem statements, not here.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, pp. 1–2, Eq. (1); p. 4 (nontrivial = dimension > 1)

import Mathlib

namespace EastinKnill.Transversal

open scoped Matrix

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → Type*) [∀ j, Fintype (α j)]
  [∀ j, DecidableEq (α j)]

/-- The tensor product `⊗_j U_j` of operators `U_j` on the subsystems, as an operator on the
composite system with basis `∀ j, α j` (Eastin–Knill, p. 2). -/
noncomputable def prodOp (U : ∀ j, Matrix (α j) (α j) ℂ) : Matrix (∀ j, α j) (∀ j, α j) ℂ :=
  Matrix.of fun a b => ∏ j, U j (a j) (b j)

/-- The operator `I ⊗ E ⊗ I`: `E` on subsystem `j`, the identity on every other subsystem. -/
noncomputable def localOp (j : ι) (E : Matrix (α j) (α j) ℂ) : Matrix (∀ j, α j) (∀ j, α j) ℂ :=
  prodOp α (Function.update (fun k => (1 : Matrix (α k) (α k) ℂ)) j E)

/-- `𝒯`, the set of unitary product operators `⊗_j U_j` with `U_j ∈ 𝒰(d_j)` (p. 2). -/
def productUnitaries : Set (Matrix.unitaryGroup (∀ j, α j) ℂ) :=
  {U | ∃ V : ∀ j, Matrix.unitaryGroup (α j) ℂ,
    (U : Matrix (∀ j, α j) (∀ j, α j) ℂ) = prodOp α (fun j => (V j : Matrix (α j) (α j) ℂ))}

variable {α}

/-- A quantum code, given by its projector `P` onto the code space: Hermitian and idempotent. -/
def IsCodeProjector {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- Eq. (1): the operator `U` is logical for the code with projector `P` iff `(I − P) U P = 0`. -/
def IsLogical {n : Type*} [Fintype n] [DecidableEq n] (P U : Matrix n n ℂ) : Prop :=
  (1 - P) * U * P = 0

/-- Local error detection (pp. 1–2): every error `E` on any single subsystem `j` is detectable,
i.e. `P (I ⊗ E ⊗ I) P ∝ P`. -/
def IsLocalErrorDetecting (P : Matrix (∀ j, α j) (∀ j, α j) ℂ) : Prop :=
  ∀ (j : ι) (E : Matrix (α j) (α j) ℂ), ∃ c : ℂ, P * localOp α j E * P = c • P

/-- An encoded operator: a unitary operator on the code space, written as an operator `W` on the
whole system with `P W P = W`, `W† W = P` and `W W† = P`. -/
def IsEncodedUnitary {n : Type*} [Fintype n] [DecidableEq n] (P W : Matrix n n ℂ) : Prop :=
  P * W * P = W ∧ Wᴴ * W = P ∧ W * Wᴴ = P

/-- Universality (p. 1): every encoded unitary is approximated to arbitrary accuracy by the
action `P U P` on the code space of some gate `U ∈ S`. -/
def IsUniversal {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (S : Set (Matrix.unitaryGroup n ℂ)) : Prop :=
  {W | IsEncodedUnitary P W} ⊆
    closure ((fun U : Matrix.unitaryGroup n ℂ => P * (U : Matrix n n ℂ) * P) '' S)

variable (α)

/-- `𝒢`, the logical unitary product operators: `𝒯 ∩ ℒ` (p. 2). -/
def logicalProductUnitaries (P : Matrix (∀ j, α j) (∀ j, α j) ℂ) :
    Set (Matrix.unitaryGroup (∀ j, α j) ℂ) :=
  productUnitaries α ∩ {U | IsLogical P (U : Matrix (∀ j, α j) (∀ j, α j) ℂ)}

end Setting

section Blocks

variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
  (α : β → ι → Type*) [∀ b j, Fintype (α b j)] [∀ b j, DecidableEq (α b j)]

/-- The joint code `⊗_b P_b` of the code blocks `b ∈ β`, on the system indexed by transversal
parts: part `j` has basis `∀ b, α b j` (subsystem `j` of every block). -/
noncomputable def blockCode (P : ∀ b, Matrix (∀ j, α b j) (∀ j, α b j) ℂ) :
    Matrix (∀ j, ∀ b, α b j) (∀ j, ∀ b, α b j) ℂ :=
  Matrix.of fun x y => ∏ b, P b (fun j => x j b) (fun j => y j b)

end Blocks

end EastinKnill.Transversal


