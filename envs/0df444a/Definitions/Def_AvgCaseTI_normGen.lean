-- Prove2me | Definitions.Def_AvgCaseTI_normGen
-- name    : AvgCaseTI_normGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:28.723641+00:00
-- url     : https://prove2.me/theorems/a8785246-5f9c-4b50-9f90-9ddf2dca7b1a
-- title:
--   Conditioning event, normalized hull generator and contraction of Proposition 3.6
-- statement:
--   Let $\mathbf A=(A_1,\dots,A_n)\in\mathrm M(n,\mathbb F)^n$ and $\mathcal A=\mathrm{span}\{A_1,\dots,A_n\}$.
--   1. The **event $E$** holds when the $A_i$ are linearly independent, $\dim H(\mathcal A)=1$, and every nonzero element of the hull $H(\mathcal A)$ has exactly one eigenvalue in $\mathbb F$, which is nonzero and of algebraic multiplicity 1.
--   2. The **normalized generator** $A$ is the element of $H(\mathcal A)$ whose only eigenvalue in $\mathbb F$ is $1$, a simple root (on $E$ it exists and is unique: divide any nonzero generator by its eigenvalue).
--   3. For a row vector $v$, the **contraction** is $X=\sum_i v_iA_i$.
--
--   These are the objects of steps 2 and 3 of the algorithm of Theorem 1.1, analysed in Proposition 3.6.
--
--   **Formalization Note** The spectral condition is invariant under nonzero rescaling, so "the hull generator has the property" and "every nonzero element of the hull has it" say the same. `normGen` returns $0$ when no such element exists (only off $E$).
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.6, p.20 (PDF p.22); §3.1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_AvgCaseTI_UniqueSimpleEig

set_option autoImplicit false

namespace AvgCaseTI

variable {K : Type*} [Field K] {n : ℕ}

/-- **The conditioning event of Proposition 3.6.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.6, p.20
(PDF p.22): "Condition on their linear independence, dim H(A) = 1, and the hull generator having
exactly one F_q-eigenvalue, which is nonzero and of algebraic multiplicity 1."

For a tuple `A = (A₁, …, A_n)` of `n × n` matrices with span `𝒜`: the `A_i` are linearly independent,
`dim H(𝒜) = 1`, and every nonzero element of `H(𝒜)` has exactly one eigenvalue in `K`, nonzero and
simple.

**Formalization Note.** The spectral condition is invariant under nonzero rescaling (p.18), so "the
hull generator" and "every nonzero element of the hull" say the same. -/
def Prop36Event (A : Fin n → Mat K n) : Prop :=
  LinearIndependent K A ∧
    Module.finrank K (hull (Submodule.span K (Set.range A))) = 1 ∧
    ∀ H ∈ hull (Submodule.span K (Set.range A)), H ≠ 0 → UniqueSimpleNonzeroEig H

open Classical in
/-- **The hull generator normalized to eigenvalue 1**, §3.1, p.19 (PDF p.21): "Divide the generator
by α … This is the unique matrix on the hull line whose only F_q-eigenvalue is 1."

`normGen A` is an element of `H(span A)` with exactly one eigenvalue in `K`, equal to `1` and simple,
when one exists (on `Prop36Event A` it exists and is unique); otherwise `0`. -/
noncomputable def normGen (A : Fin n → Mat K n) : Mat K n :=
  if h : ∃ H : Mat K n, H ∈ hull (Submodule.span K (Set.range A)) ∧ UniqueSimpleEig H ∧
      H.charpoly.IsRoot 1 then h.choose else 0

/-- **The contraction `X = Σ_i v_i A_i`**, §3.1, p.19 (PDF p.21), Step 3. -/
def contraction (v : Fin n → K) (A : Fin n → Mat K n) : Mat K n := ∑ i, v i • A i

end AvgCaseTI


