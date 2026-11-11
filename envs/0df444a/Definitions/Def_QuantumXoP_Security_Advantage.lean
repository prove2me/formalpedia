-- Prove2me | Definitions.Def_QuantumXoP_Security_Advantage
-- name    : QuantumXoP_Security_Advantage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:32.745207+00:00
-- url     : https://prove2.me/theorems/a28c73e4-e3ce-4bed-974f-cfd20c6da0d7
-- title:
--   Acceptance probability, distinguishing advantage $\mathrm{Adv}_q^{\mathrm{dist}}$ and the representing polynomial $P_A$
-- statement:
--   A **$q$-query algorithm** is the published `QueryAlg`: an oracle-independent unit start state on (query input $x$, answer $y$, workspace $W$) with any finite workspace $W$, oracle-independent unitaries $U_0,\dots,U_q$, and the standard oracle $O_f:|x,y\rangle\mapsto|x,y+f(x)\rangle$ (identity on $W$) between consecutive unitaries. The final state is measured in the computational basis and an arbitrary output map gives the output bit.
--
--   1. $\Pr[A^{O_f}\to1]$ is the probability that the output bit is $1$; as a functional of $f$ it is the **representing polynomial** $P_A$.
--   2. $\Pr_{f\leftarrow D}[A^{O_f}\to1]=\sum_f\Pr[f\leftarrow D]\Pr[A^{O_f}\to1]$.
--   3. The **advantage** is
--   $$\mathrm{Adv}^{\mathrm{dist}}(D_D,D_E;A)=\Big|\Pr_{f\leftarrow D_D}[A^{O_f}\to1]-\Pr_{f\leftarrow D_E}[A^{O_f}\to1]\Big|.$$
--   4. $\mathrm{Adv}_q^{\mathrm{dist}}(D_D,D_E)\le c$ means that every algorithm making at most $q$ queries, with any finite workspace and any output map, has advantage at most $c$; this is the maximum of §2 bounded by $c$.
--
--   The oracle domain and range are general finite types, so the same definitions serve $F_n$ and the Boolean oracles on $[M]$ of Claim B.1.
--
--   **Formalization Note** The maximum over all algorithms is never formed as a supremum over a type of workspaces; the bound is stated for every algorithm instead.
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), §2 p. 8 (PDF p. 10); §3.2 p. 11 (PDF p. 13), Theorem 3.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QuantumXoP_Security_Fourier

noncomputable section

namespace QuantumXoP.Security

open QAlgorithms

/-!
# Acceptance probabilities and distinguishing advantage (Choi–Hhan–Jang, §2 p. 8, §3.2 p. 11)

A `q`-query algorithm is the published `QAlgorithms.QueryAlg ι κ W q`: an oracle-independent unit
start state on `(ι × κ) × W` with an arbitrary finite workspace `W`, oracle-independent unitaries
`U_0, …, U_q`, and the standard (XOR) oracle `O_f : |x, y⟩ ↦ |x, y + f(x)⟩` (tensored with the
identity on `W`) between consecutive unitaries. Its output bit is `out` applied to the outcome of a
computational-basis measurement of the final state; with an arbitrary `W`, `U_q` and `out` this
covers every binary projective measurement.
-/

/-- p. 11 (Theorem 3.4): `Pr[A^{O_f} → 1]`, the probability that the algorithm `(A, out)` outputs
`1` (`true`) with oracle access to `O_f`. -/
def accFun {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] [AddCommGroup κ] {q : ℕ} (A : QueryAlg ι κ W q)
    (out : (ι × κ) × W → Bool) (f : ι → κ) : ℝ :=
  A.outputProb (xorOracle f) out true

/-- p. 8: `Pr_{f←D}[A^{O_f} → 1] = Σ_f Pr[f ← D] · Pr[A^{O_f} → 1]`. -/
def accProb {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] [AddCommGroup κ] {q : ℕ} (D : PMF (ι → κ)) (A : QueryAlg ι κ W q)
    (out : (ι × κ) × W → Bool) : ℝ :=
  ∑ f : ι → κ, (D f).toReal * accFun A out f

/-- p. 8: the distinguishing advantage
`Adv^dist(D_D, D_E; A) = |Pr_{f←D_D}[A^{O_f} → 1] − Pr_{f←D_E}[A^{O_f} → 1]|`. -/
def adv {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] [AddCommGroup κ] {q : ℕ} (D E : PMF (ι → κ)) (A : QueryAlg ι κ W q)
    (out : (ι × κ) × W → Bool) : ℝ :=
  |accProb D A out - accProb E A out|

/-- p. 8: `Adv_q^dist(D_D, D_E) ≤ c`, where `Adv_q^dist` is the maximum of the advantage over all
quantum oracle algorithms making at most `q` queries: every algorithm with `q' ≤ q` queries, every
finite workspace `W` and every output map has advantage at most `c`. -/
def AdvAtMost (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup κ] (q : ℕ) (D E : PMF (ι → κ)) (c : ℝ) : Prop :=
  ∀ q' : ℕ, q' ≤ q → ∀ (W : Type) [Fintype W] [DecidableEq W] (A : QueryAlg ι κ W q')
    (out : (ι × κ) × W → Bool), adv D E A out ≤ c

/-- p. 11 (Theorem 3.4): the representing polynomial `P_A(f) := Pr[A^{O_f} → 1]` of an algorithm
`(A, out)` on `F_n`, as a functional `F_n → ℂ`. -/
def repPoly {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits n) (Qubits n) W q) (out : (Qubits n × Qubits n) × W → Bool) :
    Fn n → ℂ :=
  fun f => ((accFun A out f : ℝ) : ℂ)

/-! ### Sanity checks -/

/-- The advantage of an algorithm between a distribution and itself is `0`. -/
example {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits n) (Qubits n) W q) (out : (Qubits n × Qubits n) × W → Bool)
    (D : PMF (Fn n)) : adv D D A out = 0 := by
  simp [adv]

end QuantumXoP.Security


