-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
-- name    : OAI_Probability_EntangledGames_CorrelatedSampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:59:42.976792+00:00
-- url     : https://prove2.me/theorems/9e352bf5-56c0-4ce5-afac-78add6a8aa53
-- title:
--   Winning effect, flattened states, block rows, and the binned resource state for correlated sampling
-- statement:
--   Let $m,n$ be finite index sets and $\otimes$ the Kronecker product. A matrix $C\in\mathbb{C}^{m\times n}$ encodes the vector $\operatorname{vec}(C)\in\mathbb{C}^m\otimes\mathbb{C}^n$ with $\operatorname{vec}(C)_{(i,j)}=C_{ij}$. A POVM $P=(P_a)_{a\in A}$ on $\mathbb{C}^m$ is a family of positive semidefinite matrices summing to the identity, indexed by a finite outcome set $A$.
--
--   1. **Winning effect.** For POVMs $P$ on $\mathbb{C}^m$ and $Q=(Q_b)_{b\in B}$ on $\mathbb{C}^n$ and a predicate $V:A\times B\to\{\text{true},\text{false}\}$,
--   $$W(P,Q,V)=\sum_{(a,b):\,V(a,b)}P_a\otimes Q_b\in\mathbb{C}^{(m\times n)\times(m\times n)} .$$
--   2. **Flattening.** $\operatorname{flat}(C)$ is $\operatorname{vec}(C)$ written as a single-column matrix of size $(m\times n)\times 1$.
--   3. **Block rows.** For a finite index set $\iota$ and matrices $F_k\in\mathbb{C}^{m\times n}$ ($k\in\iota$), $\operatorname{rows}(F)\in\mathbb{C}^{m\times(n\times\iota)}$ is the horizontal concatenation $[F_k]_{k\in\iota}$: $\operatorname{rows}(F)_{i,(j,k)}=(F_k)_{ij}$.
--   4. **Binned resource state.** For a finite set $L\subset\mathbb{Z}$ of bin labels, a bin width $\varepsilon$ and a shift $s$, $R_L\in\mathbb{C}^{(n\times L)\times(n\times L)}$ is the diagonal matrix with entry $e^{\varepsilon(\ell-s)}$ at position $((j,\ell),(j,\ell))$, i.e. $R_L=\bigoplus_{\ell\in L}e^{\varepsilon(\ell-s)}I_n$.
--   5. **Bob's binned filter.** For $N\in\mathbb{C}^{n\times n}$, $\Psi_L(N)=\operatorname{rows}\bigl(\ell\mapsto P_\ell(|N|)^{\mathsf T}\bigr)\in\mathbb{C}^{n\times(n\times L)}$, where $|N|=(N^*N)^{1/2}$ and $P_\ell(|N|)$ is the orthogonal projection onto the eigenvectors of $|N|$ with positive eigenvalues $a$ satisfying $\lfloor\log a/\varepsilon+s\rfloor=\ell$.
--
--   With these, the payoff $\sum_{a,b}[V(a,b)]\operatorname{Re}\langle\operatorname{vec}(C),(P_a\otimes Q_b)\operatorname{vec}(C)\rangle$ of a state $C$ is the quadratic form $\operatorname{Re}\langle\operatorname{vec}(C),W\operatorname{vec}(C)\rangle=\|W^{1/2}\operatorname{flat}(C)\|_2^2$ (Hilbert–Schmidt norm), and $0\le W\le I$. On the strategy side, write $\operatorname{pol}(M)=M\,|M|^{+}$ for the polar part of $M\in\mathbb{C}^{n\times n}$ ($|M|^{+}$ the pseudo-inverse of $|M|$) and $\Phi_L(M)=\operatorname{rows}\bigl(\ell\mapsto\operatorname{pol}(M)P_\ell(|M|)\bigr)$ for Alice's binned filter. Then
--   $$\Phi_L(M)\,R_L\,\Psi_L(N)^{\mathsf T}=\operatorname{pol}(M)\sum_{\ell\in L}e^{\varepsilon(\ell-s)}\,P_\ell(|M|)\,P_\ell(|N|),$$
--   so a shared diagonal resource state together with local filters reproduces a binned approximation of $M$. This is the correlated-sampling step that converts approximating matrices into actual strategies.
--
--   **Formalization Note** The definitions are `winEffect`, `flat` (built with `Matrix.replicateCol` and column index `Unit`), `rowBlocks`, `binResource` (whose side index type `n` is implicit) and `bobBinFilter`. The identities in the last paragraph are not part of this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/CorrelatedSampling.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CorrelatedSampling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_m u_n u_A u_B u_p u_ι

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Norm
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
end Norm

section WinEffect
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]
def winEffect (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    Matrix (m × n) (m × n) ℂ := ∑ a, ∑ b, if V a b then P.effect a ⊗ₖ Q.effect b else 0
def flat (C : Matrix m n ℂ) : Matrix (m × n) Unit ℂ := Matrix.replicateCol Unit (vec C)
end WinEffect

section Blocks
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype p] [Fintype ι]
def rowBlocks (F : ι → Matrix m n ℂ) : Matrix m (n × ι) ℂ := fun i j => F j.2 i j.1
end Blocks

section Resource
variable {n : Type u_n} [Fintype n] [DecidableEq n]
def binResource (L : Finset ℤ) (ε s : ℝ) : Matrix (n × L) (n × L) ℂ :=
  Matrix.diagonal (fun j => (binScale ε s j.2 : ℂ))
def bobBinFilter (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ) : Matrix n (n × L) ℂ :=
  rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ)
end Resource

end ThresholdParallelRepetition.QuantumSampling

end

end OAI


