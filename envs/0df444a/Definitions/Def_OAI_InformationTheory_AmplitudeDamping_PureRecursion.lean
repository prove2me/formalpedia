-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
-- name    : OAI_InformationTheory_AmplitudeDamping_PureRecursion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:02:23.697493+00:00
-- url     : https://prove2.me/theorems/17cb03aa-e73c-46e9-9e3e-fffdc130e95e
-- title:
--   Norms, normalization, branches and site populations of multi-qubit vectors
-- statement:
--   Let $\mathcal I$ be a finite index set. An $n$-qubit vector is a vector $\psi\in\mathbb{C}^{\{0,1\}^n}$ indexed by bit strings $i=(i_0,\dots,i_{n-1})$; for $b\in\{0,1\}$ and $i\in\{0,1\}^n$, $(b,i)\in\{0,1\}^{n+1}$ denotes the string with first bit $b$ followed by $i$.
--
--   1. **Mass.** For $\psi\in\mathbb{C}^{\mathcal I}$, $\|\psi\|^2=\sum_i|\psi_i|^2$. The rank-one matrix $\psi\psi^*$ (entries $\psi_i\overline{\psi_j}$) is positive semidefinite with trace $\|\psi\|^2$; hence it is a density matrix when $\|\psi\|^2=1$.
--   2. **Default unit vector.** If $\mathcal I$ has a designated element $i_\star$, then $e_{i_\star}$ is the standard basis vector ($1$ at $i_\star$, $0$ elsewhere), and $\|e_{i_\star}\|^2=1$. For bit strings the designated element is $00\cdots0$.
--   3. **Normalization.** $\widehat\psi=\psi/\|\psi\|$ if $\psi\neq0$, and $\widehat\psi=e_{i_\star}$ if $\psi=0$. Thus $\widehat\psi$ is always a unit vector and $\psi=\|\psi\|\,\widehat\psi$.
--   4. **Branches.** For $\psi\in\mathbb{C}^{\{0,1\}^{n+1}}$ and $b\in\{0,1\}$, the branch $\psi^{(b)}\in\mathbb{C}^{\{0,1\}^n}$ is $\psi^{(b)}_i=\psi_{(b,i)}$, so that $\psi=|0\rangle\otimes\psi^{(0)}+|1\rangle\otimes\psi^{(1)}$.
--   5. **Site population.** For $\psi\in\mathbb{C}^{\{0,1\}^n}$ and a site $j\in\{0,\dots,n-1\}$,
--   $$\pi_j(\psi)=\sum_{i\in\{0,1\}^n:\ i_j=1}|\psi_i|^2,$$
--   the unnormalized weight of $\psi$ on strings whose $j$-th bit is $1$; for a unit vector it is the probability of finding qubit $j$ in $|1\rangle$.
--   6. **First-bit splitting.** The bijection $\{0,1\}^n\sqcup\{0,1\}^n\to\{0,1\}^{n+1}$ sending $i$ in the first copy to $(0,i)$ and $i$ in the second copy to $(1,i)$.
--
--   These are the bookkeeping objects of an induction on the number of qubits. Splitting off the first qubit expresses a unit vector $\psi$ through its normalized branches with weights $\|\psi^{(0)}\|^2$ and $\|\psi^{(1)}\|^2$, and for $\gamma,\nu\in[0,1]$ the output entropy satisfies the recursion
--   $$\sum_{b\in\{0,1\}}\|\psi^{(b)}\|^2\,S\bigl(\mathcal N_n(\widehat{\psi^{(b)}}\,\widehat{\psi^{(b)}}^{\,*})\bigr)+g\bigl(v(\gamma,\nu,\pi_0(\psi))\bigr)\le S\bigl(\mathcal N_{n+1}(\psi\psi^*)\bigr),$$
--   where $\mathcal N_n$ is the memoryless $n$-qubit generalized amplitude-damping channel, $S$ the von Neumann entropy, $v(\gamma,\nu,p)=\gamma\nu(1-\nu)+\gamma(1-\gamma)(p-\nu)^2$ and $g(u)=h\bigl(\tfrac{1+\sqrt{1-4u}}{2}\bigr)$ with $h$ the binary entropy.
--
--   **Formalization Note** The names are `vecMass`, `unitVec` (which needs an `Inhabited` index type; the default element of `Basis n = Fin n → Fin 2` is the all-zero string), `normalize`, `branch`, `population` and `basisSplit`. The accompanying lemmas `pure_posSemidef`, `pure_trace`, `pure_state`, `vecMass_unitVec`, `basisSplit_inl` and `basisSplit_inr` record the facts stated in items 1, 2 and 6.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/PureRecursion.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PureRecursion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι]

def vecMass (ψ : ι → ℂ) : ℝ := ∑ i, Complex.normSq (ψ i)

theorem pure_posSemidef (ψ : ι → ℂ) : (pure ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

theorem pure_trace (ψ : ι → ℂ) : (pure ψ).trace = (vecMass ψ : ℂ) := by
  simp [Matrix.trace, pure, vecMass, Complex.mul_conj]

theorem pure_state [DecidableEq ι] {ψ : ι → ℂ} (hψ : vecMass ψ = 1) : IsState (pure ψ) := by
  exact ⟨pure_posSemidef ψ, by rw [pure_trace,hψ]; rfl⟩

variable [DecidableEq ι]

def unitVec [Inhabited ι] : ι → ℂ := fun i ↦ if i = default then 1 else 0

@[simp] theorem vecMass_unitVec [Inhabited ι] : vecMass (unitVec (ι := ι)) = 1 := by
  simp [vecMass, unitVec]

def normalize [Inhabited ι] (ψ : ι → ℂ) : ι → ℂ :=
  if vecMass ψ = 0 then unitVec else ((Real.sqrt (vecMass ψ) : ℂ)⁻¹) • ψ

end

section
open scoped BigOperators ComplexOrder
open Matrix

def branch {n : ℕ} (ψ : Basis (n+1) → ℂ) (b : Fin 2) : Basis n → ℂ :=
  fun i ↦ ψ (Fin.cons b i)

def population {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) : ℝ :=
  ∑ i, if i j = 1 then Complex.normSq (ψ i) else 0

def basisSplit (n : ℕ) : Basis n ⊕ Basis n ≃ Basis (n+1) where
  toFun := Sum.elim (fun i : Basis n ↦ Fin.cons 0 i) (fun i : Basis n ↦ Fin.cons 1 i)
  invFun i := if i 0 = 0 then Sum.inl (Fin.tail i) else Sum.inr (Fin.tail i)
  left_inv i := by cases i <;> simp
  right_inv i := by
    have h := Fin.cons_self_tail i
    have hi : i 0 = 0 ∨ i 0 = 1 := by have := (i 0).isLt; omega
    rcases hi with hi | hi <;> simp [hi] at * <;> exact h

@[simp] theorem basisSplit_inl {n : ℕ} (i : Basis n) : basisSplit n (Sum.inl i) = Fin.cons 0 i := rfl
@[simp] theorem basisSplit_inr {n : ℕ} (i : Basis n) : basisSplit n (Sum.inr i) = Fin.cons 1 i := rfl

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

end GAD

end

end OAI


