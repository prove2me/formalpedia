-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
-- name    : OAI_InformationTheory_AmplitudeDamping_Channel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:50:10.4045+00:00
-- url     : https://prove2.me/theorems/fe4759be-9e8f-42d8-bef7-cd64105b12e6
-- title:
--   Kraus operators of the generalized amplitude-damping channel and finite Kraus maps
-- statement:
--   This file fixes the four Kraus operators of the single-qubit generalized amplitude-damping channel and introduces three constructions for maps given by finitely many Kraus operators.
--
--   Let $\gamma,\nu\in\mathbb{R}$ be the damping and thermal parameters (the intended range is $[0,1]$). Qubit matrices are indexed by the computational basis $|0\rangle,|1\rangle$, and $A^*$ denotes the conjugate transpose of a complex matrix $A$.
--
--   1. **Single-qubit Kraus operators.** The operators $K_r=K_r(\gamma,\nu)$, $r\in\{0,1,2,3\}$, are
--   $$K_0=\begin{pmatrix}\sqrt{1-\nu}&0\\0&\sqrt{1-\nu}\,\sqrt{1-\gamma}\end{pmatrix},\qquad K_1=\begin{pmatrix}0&\sqrt{\gamma(1-\nu)}\\0&0\end{pmatrix},$$
--   $$K_2=\begin{pmatrix}\sqrt{\nu}\,\sqrt{1-\gamma}&0\\0&\sqrt{\nu}\end{pmatrix},\qquad K_3=\begin{pmatrix}0&0\\\sqrt{\gamma\nu}&0\end{pmatrix}.$$
--   These four explicit forms are recorded as simplification rules, valid for all real $\gamma,\nu$.
--   2. **Rank-one matrix of a vector.** For an index set $\mathcal I$ and a vector $\psi\in\mathbb{C}^{\mathcal I}$, $\operatorname{pure}(\psi)=\psi\psi^*$ is the matrix with entries $\operatorname{pure}(\psi)_{ij}=\psi_i\,\overline{\psi_j}$. When $\sum_i|\psi_i|^2=1$ it is the density matrix of the pure state $\psi$.
--   3. **Kraus map.** For finite index sets $\mathcal J,\mathcal R$, a family $L=(L_r)_{r\in\mathcal R}$ of complex $\mathcal I\times\mathcal J$ matrices and a $\mathcal J\times\mathcal J$ matrix $P$,
--   $$\Phi_L(P)=\sum_{r\in\mathcal R}L_r\,P\,L_r^{*}\qquad(\text{an }\mathcal I\times\mathcal I\text{ matrix}).$$
--   4. **Column matrix.** For $L$ as above and $\psi\in\mathbb{C}^{\mathcal J}$, $C_L(\psi)$ is the $\mathcal I\times\mathcal R$ matrix whose $r$-th column is the vector $L_r\psi$, that is, $C_L(\psi)_{ir}=(L_r\psi)_i$.
--
--   With $L=(K_r)_{r=0}^{3}$ the Kraus map $\Phi_K$ is the single-qubit generalized amplitude-damping channel: for $\gamma,\nu\in[0,1]$ one has $\sum_rK_r^*K_r=\mathbf 1$, and an input state whose $|1\rangle$-population is $p$ is mapped to an output whose $|1\rangle$-population is $(1-\gamma)p+\gamma\nu$. The memoryless $n$-qubit channel is the Kraus map of the $4^n$ tensor products $K_{r_1}\otimes\cdots\otimes K_{r_n}$. The column matrix is a factor of a pure-state output, $C_L(\psi)\,C_L(\psi)^*=\Phi_L(\psi\psi^*)$, which lets output entropies of pure inputs be studied through rectangular factor matrices.
--
--   **Formalization Note** The Kraus operators are `kraus γ ν r` from the base definitions of this project, defined by a case distinction on `r : Fin 4`; the lemmas `kraus_zero`, `kraus_one`, `kraus_two`, `kraus_three` unfold the four cases. `Real.sqrt` returns $0$ on negative arguments. The constructions are `pure`, `applyKraus` and `columns`; `pure` needs no finiteness of the index type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Channel.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/Channel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

@[simp] theorem kraus_zero (γ ν : ℝ) : kraus γ ν 0 = !![(Real.sqrt (1 - ν) : ℂ), 0; 0, (Real.sqrt (1 - ν) * Real.sqrt (1 - γ) : ℂ)] := by
  norm_num [kraus]

@[simp] theorem kraus_one (γ ν : ℝ) : kraus γ ν 1 = !![0, (Real.sqrt (γ * (1 - ν)) : ℂ); 0, 0] := by
  norm_num [kraus]

@[simp] theorem kraus_two (γ ν : ℝ) : kraus γ ν 2 = !![(Real.sqrt ν * Real.sqrt (1 - γ) : ℂ), 0; 0, (Real.sqrt ν : ℂ)] := by
  simp only [kraus, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide, ite_false, ite_true]

@[simp] theorem kraus_three (γ ν : ℝ) : kraus γ ν 3 = !![0, 0; (Real.sqrt (γ * ν) : ℂ), 0] := by
  simp only [kraus, show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide, ite_false]

def pure {ι : Type u_3} (ψ : ι → ℂ) : Matrix ι ι ℂ := fun i j ↦ ψ i * star (ψ j)

def applyKraus {ι : Type u_4} {κ : Type u_5} {ρ : Type u_6} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (P : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  ∑ r, L r * P * (L r).conjTranspose

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

def columns {ι : Type u_15} {κ : Type u_16} {ρ : Type u_17} [Fintype κ] (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    Matrix ι ρ ℂ := fun i r ↦ (L r *ᵥ ψ) i

end GAD

end

end OAI


