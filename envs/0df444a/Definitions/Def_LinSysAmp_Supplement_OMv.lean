-- Prove2me | Definitions.Def_LinSysAmp_Supplement_OMv
-- name    : LinSysAmp_Supplement_OMv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:48:03.794202+00:00
-- url     : https://prove2.me/theorems/d447ea1b-d496-46d0-a3cd-e0f6d169f108
-- title:
--   Data structures for online matrix-vector multiplication (Definition 5.3)
-- statement:
--   Definition 5.3 of the paper. A **data structure $D$ for OMv** over $\mathbb F_q$ with state space $S$ consists of two randomized algorithms:
--
--   1. $D_{\mathrm{pre}}$: on input $A\in\mathbb F_q^{n\times n}$ it outputs a state $\sigma\in S$;
--   2. $D_{\mathrm{query}}$: on input a state $\sigma$ and a vector $v\in\mathbb F_q^n$ it outputs a vector of $\mathbb F_q^n$, with fresh coins at each query.
--
--   $D(A;v)$ denotes this output when $\sigma\leftarrow D_{\mathrm{pre}}(A)$. $D$ **solves OMv with probability $\alpha$** if $\Pr_{A,v,D}[D(A;v)=Av]\ge\alpha$, and has **expected agreement $\gamma$** if $\mathbb E_{A,v,D}[\mathrm{agr}(D(A;v),Av)]\ge\gamma$, with $A\leftarrow\mathbb F_q^{n\times n}$ and $v\leftarrow\mathbb F_q^n$ independent and uniform.
--
--   A data structure built by a reduction is a pair of programs $(P_{\mathrm{pre}},P_{\mathrm{query}})$ of the oracle machine whose interface gives mode $0$ to $D_{\mathrm{pre}}$ (the returned state is kept as an opaque handle) and mode $1$ to $D_{\mathrm{query}}$ on a stored handle. Preprocessing runs $P_{\mathrm{pre}}$ on $A$; a query $v$ runs $P_{\mathrm{query}}$ from the final preprocessing configuration with $v$ added to memory. $\Pr[E_{\mathrm{wc}}(A;v)=w]$ is the probability, over the coins of both runs, that the query run halts with output $w$. Since the state is computed once and is not modified by queries, guarantees are stated for a single query, as in the paper.
--
--   **Formalization Note** The state type $S$ is arbitrary and opaque to the reduction. The query run starts from the halted preprocessing configuration with program counter and counters reset and $v$ at addresses $-n,\dots,-1$, so preprocessing and query costs (operations, and calls per mode) are counted separately.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Definition 5.3, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_Problems

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

/-!
# Data structures for online matrix-vector multiplication (Definition 5.3)

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), Definition 5.3,
p.27 (PDF p.29): "A data structure D for OMv consists of two randomized algorithms: i. D_pre (the
preprocessing algorithm): on input a matrix A ∈ F_q^{n×n}, the algorithm outputs a state σ.
ii. D_query (the query algorithm): on input a state σ and a vector v ∈ F_qⁿ, the algorithm outputs a
vector in F_qⁿ, with fresh coins at each query. We write D(A; v) for this output when σ ← D_pre(A).
[…] The data structure solves OMv with probability α if Pr_{A,v,D}[D(A; v) = Av] ≥ α, and it has
expected agreement γ if E_{A,v,D}[agr(D(A; v), Av)] ≥ γ. (Here, A ← F_q^{n×n} and v ← F_qⁿ are
independent […].) The state σ is computed once, and it is not modified by the queries. We therefore
state our guarantees for a single query."

**Formalization Note.**
* An oracle data structure is a pair `(pre, query)` over an arbitrary state type `S`; the state is
  opaque to the reduction.
* The constructed data structure `E_wc` is a pair of programs `(P_pre, P_query)` of the machine
  `LinSysAmp.Supplement.OracleMachine` with the interface `omvIface D`: mode `0` calls `D_pre` on the
  `n²` cells read (row-major) and stores the returned state as a handle; mode `1` calls `D_query` on
  the handle given and the `n` cells read, writes the answer, and keeps the handle; any other mode,
  or mode `1` without a handle, returns nothing (and still counts as a call).
* Preprocessing runs `P_pre` from `oinit par (A row-major)`. The state of `E_wc` is the final
  configuration of that run (memory, registers and handles). A query `v` runs `P_query` from
  `queryInit σ v`: the same memory, registers and handles, with `v` written at addresses
  `−n, …, −1`, program counter and all counters reset. Preprocessing and query costs are counted
  separately; `callsAt 0` counts `D_pre` calls and `callsAt 1` counts `D_query` calls.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Definition 5.3: a data structure for OMv with state type `S`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3, p.27 (PDF p.29).) -/
structure OMvDS (n : ℕ) (F : Type*) (S : Type*) where
  pre : Matrix (Fin n) (Fin n) F → PMF S
  query : S → (Fin n → F) → PMF (Fin n → F)

variable {n : ℕ} {S : Type*}

/-- `D(A; v)`: the distribution of the answer to `v` when `σ ← D_pre(A)`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3, p.27 (PDF p.29).) -/
noncomputable def OMvDS.answer (D : OMvDS n F S) (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    PMF (Fin n → F) :=
  (D.pre A).bind fun σ => D.query σ v

/-- Definition 5.3: `Pr_{A, v, D}[D(A; v) = Av]`, `A ← F^{n×n}`, `v ← Fⁿ` independent.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3, p.27 (PDF p.29).) -/
noncomputable def omvSuccess (D : OMvDS n F S) : ℝ :=
  ((Fintype.card F : ℝ) ^ (n * n) * (Fintype.card F : ℝ) ^ n)⁻¹ *
    ∑ A : Matrix (Fin n) (Fin n) F, ∑ v : Fin n → F, (D.answer A v (A *ᵥ v)).toReal

/-- Definition 5.3: the expected agreement `E_{A, v, D}[agr(D(A; v), Av)]`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3, p.27 (PDF p.29).) -/
noncomputable def omvAgreement (D : OMvDS n F S) : ℝ :=
  ((Fintype.card F : ℝ) ^ (n * n) * (Fintype.card F : ℝ) ^ n)⁻¹ *
    ∑ A : Matrix (Fin n) (Fin n) F, ∑ v : Fin n → F, ∑ w : Fin n → F,
      (D.answer A v w).toReal * agrVec w (A *ᵥ v)

/-- The machine interface of an OMv data structure: mode `0` is `D_pre`, mode `1` is `D_query` on a
stored state. (arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3, p.27.) -/
noncomputable def omvIface (D : OMvDS n F S) : Iface F S where
  inLen m := if m = 0 then n * n else if m = 1 then n else 0
  call m x h :=
    if m = 0 then (D.pre (unflatMat n x 0)).map fun σ => ([], some σ)
    else if m = 1 then
      match h with
      | some σ => (D.query σ (unflatVec n x 0)).map fun w => (List.ofFn w, some σ)
      | none => PMF.pure ([], none)
    else PMF.pure ([], none)

/-- The configuration at which a query `v` starts, from the final preprocessing configuration `σ`:
same memory, registers and handles, `v` at addresses `−n, …, −1`, counters and `pc` reset.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3, p.27 (PDF p.29).) -/
def queryInit (σ : OConfig F S) (v : Fin n → F) : OConfig F S :=
  { σ with
    pc := 0
    ops := 0
    calls := 0
    callsAt := fun _ => 0
    status := .running
    mem := writeList σ.mem (-(n : ℤ)) (List.ofFn v) }

/-- `Pr[E_wc(A; v) = Av]` for the data structure `(P_pre, P_query)`: preprocess `A` for `N₁` steps,
then answer the single query `v` for `N₂` steps; the probability that the query run has halted
with output `w`. (arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 5.3, p.27.) -/
noncomputable def ewcAnswerProb (D : OMvDS n F S) (Ppre Pq : OProgram F) (par : List ℤ)
    (N₁ N₂ : ℕ) (A : Matrix (Fin n) (Fin n) F) (v w : Fin n → F) : ℝ :=
  (((orun (omvIface D) Ppre N₁ (oinit par (flatMat A))).bind fun σ =>
      orun (omvIface D) Pq N₂ (queryInit σ v)).map OConfig.status
    (.done (some (.vec (List.ofFn w))))).toReal

end LinSysAmp.Supplement


