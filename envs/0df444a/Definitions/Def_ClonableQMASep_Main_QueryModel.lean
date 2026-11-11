-- Prove2me | Definitions.Def_ClonableQMASep_Main_QueryModel
-- name    : ClonableQMASep_Main_QueryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:32.586178+00:00
-- url     : https://prove2.me/theorems/21e1415e-8b37-48d7-bbab-53dcb8688daf
-- title:
--   Quantum query algorithms and query verifiers with classical witnesses
-- statement:
--   A **$T$-query algorithm** for oracles $f:X\to R$ ($R$ a finite additive group; for $R=(\mathbb Z/2)^r$ the group operation is XOR) acts on $\mathbb C^{X\times R\times W}$, with $W$ a workspace of arbitrary finite size. It is a list of oracle-independent unitaries $U_0,\dots,U_T$, and the oracle acts by
--   $$U_f|x,y,z\rangle=|x,y+f(x),z\rangle .$$
--   Starting from $\psi_0$, the state after $U_0$ and $k$ rounds (query, next unitary) is $U_kU_f\cdots U_fU_0\psi_0$; for $k<T$ this is the state immediately before query $k+1$, and for $k=T$ it is the final state. Computation between queries is unrestricted, and measurements are deferred by purification.
--
--   The **query weight** of a vector $\varphi$ on a set $S\subseteq X$ is $\operatorname{Tr}((\Pi_S\otimes I)|\varphi\rangle\langle\varphi|)=\sum_{x\in S,y,z}|\varphi(x,y,z)|^2$. An acceptance event is an orthogonal projector $P$, with probability $\|P\varphi\|^2$.
--
--   A **query verifier with a $t$-bit classical witness** is a query algorithm whose workspace is $\{0,1\}^t\times\mathrm{Aux}$, started in the basis state $|x_0,0,(w,a_0)\rangle$ (that is, $|w,0\rangle$ up to fixed default values), followed by a projective acceptance measurement. Its acceptance probability on witness $w$ with oracle $f$ is written $\Pr[A^f(w)=1]$.
--
--   This is the model of §2.2 used in all query lower bounds of the paper (Lemmas 1, 7, 8 and Theorem 5, part 2).
-- source:
--   Alper Cakan, Kai-Min Chung, Wei-Hsiang Hung, Tzu-Yi Yang, Separating ClonableQMA and QCMA Relative to a Classical Oracle, STOC 2027 submission #844 (October 2026), §2.2 p. 11 (quantum query model); §6.2 pp. 26–27 (the verifier's execution V_Q M ⋯ M V_0 |w,0⟩ followed by a measurement)

import Definitions.Def_ClonableQMASep_Main_Channels

set_option autoImplicit false

namespace ClonableQMASep.Main

open scoped ComplexConjugate Matrix

/-- A **`T`-query quantum algorithm** in the query model with oracle-independent computation
between queries unrestricted. The state space is `ℂ^{X × R × W}`: a query register `X`, a response
register `R` (a finite additive group, combined by XOR when `R = (ℤ/2)^r`), and a workspace `W` of
arbitrary finite size. The algorithm is a sequence of `T + 1` unitaries `U_0, …, U_T` interleaved
with `T` oracle queries. Measurements are deferred by purification. -/
structure QueryAlgo (X R W : Type) [Fintype X] [Fintype R] [Fintype W]
    [DecidableEq X] [DecidableEq R] [DecidableEq W] where
  /-- the number of queries -/
  T : ℕ
  /-- the oracle-independent unitaries `U_0, …, U_T` -/
  U : Fin (T + 1) → Matrix (X × R × W) (X × R × W) ℂ
  unitary : ∀ t, U t ∈ Matrix.unitaryGroup (X × R × W) ℂ

/-- The query unitary `U_f |x, y, z⟩ = |x, y + f(x), z⟩` acting on a vector. -/
def oracleApply {X R W : Type} [AddCommGroup R] (f : X → R) (ψ : X × R × W → ℂ) :
    X × R × W → ℂ :=
  fun p => ψ (p.1, p.2.1 - f p.1, p.2.2)

/-- `stepState A f ψ₀ k` is the state `U_k U_f ⋯ U_f U_0 ψ₀` after `U_0`, then `k` rounds of
(query, next unitary), for `k ≤ T`; for `k < T` it is the state immediately before query `k+1`,
and `stepState A f ψ₀ T` is the final state. -/
noncomputable def stepState {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [DecidableEq X] [DecidableEq R] [DecidableEq W] [AddCommGroup R]
    (A : QueryAlgo X R W) (f : X → R) (ψ₀ : X × R × W → ℂ) : ℕ → (X × R × W → ℂ)
  | 0 => A.U 0 *ᵥ ψ₀
  | k + 1 =>
    if h : k + 1 ≤ A.T then A.U ⟨k + 1, by omega⟩ *ᵥ oracleApply f (stepState A f ψ₀ k)
    else stepState A f ψ₀ k

/-- The **query weight** `Tr((Π_S ⊗ I) |φ⟩⟨φ|) = ∑_{x ∈ S, y, z} |φ(x,y,z)|²` of a vector on the
query inputs in `S`. -/
noncomputable def queryWeight {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    (S : Set X) (φ : X × R × W → ℂ) : ℝ := by
  classical exact ∑ p : X × R × W, if p.1 ∈ S then Complex.normSq (φ p) else 0

/-- An **orthogonal projector** `P` (`P† = P`, `P² = P`): a two-outcome projective measurement
with acceptance operator `P`. -/
def IsProjector {ι : Type} [Fintype ι] (P : Matrix ι ι ℂ) : Prop := Pᴴ = P ∧ P * P = P

/-- The probability `‖P φ‖²` of the outcome `P` on the vector `φ`. -/
noncomputable def projProb {ι : Type} [Fintype ι] (P : Matrix ι ι ℂ) (φ : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq ((P *ᵥ φ) i)

/-- A **query verifier with a `t`-bit classical witness**: a query algorithm whose workspace is
`{0,1}^t × Aux`, started in the basis state `|x₀, 0, (w, a₀)⟩` (`|w, 0⟩` up to the fixed default
values `x₀`, `a₀`), followed by the projective measurement `accept`. -/
structure QueryVerifier (X R Aux : Type) [Fintype X] [Fintype R] [Fintype Aux]
    [DecidableEq X] [DecidableEq R] [DecidableEq Aux] [Zero R] (t : ℕ) where
  alg : QueryAlgo X R ((Fin t → Bool) × Aux)
  x₀ : X
  a₀ : Aux
  accept : Matrix (X × R × ((Fin t → Bool) × Aux)) (X × R × ((Fin t → Bool) × Aux)) ℂ
  accept_proj : IsProjector accept

/-- The acceptance probability `Pr[A^f(w) = 1]` of a query verifier with oracle `f` on the
classical witness `w`. -/
noncomputable def QueryVerifier.acceptProb {X R Aux : Type} [Fintype X] [Fintype R] [Fintype Aux]
    [DecidableEq X] [DecidableEq R] [DecidableEq Aux] [AddCommGroup R] {t : ℕ}
    (A : QueryVerifier X R Aux t) (f : X → R) (w : Fin t → Bool) : ℝ :=
  projProb A.accept
    (stepState A.alg f (fun p => if p = (A.x₀, 0, (w, A.a₀)) then 1 else 0) A.alg.T)

end ClonableQMASep.Main


