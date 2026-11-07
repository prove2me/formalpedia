-- Prove2me | Definitions.Def_AvgCaseTI_epsGen
-- name    : AvgCaseTI_epsGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:26.51839+00:00
-- url     : https://prove2.me/theorems/575d5e42-e8d6-4a75-b0ae-92d797bada38
-- title:
--   Generation failure $\varepsilon_{\mathrm{gen}}(n,q)$ and conjugacy cosets
-- statement:
--   For a finite field $\mathbb F_q$:
--   1. $\varepsilon_{\mathrm{gen}}(n,q)$ is the probability that two independent uniform matrices $A_1,A_2\in\mathrm M(n,q)$ do **not** generate the full matrix algebra $\mathrm M(n,q)$, i.e. that the unital subalgebra $\mathbb F_q\langle A_1,A_2\rangle$ is proper.
--   2. For matrix tuples $\mathbf A=(A_1,\dots,A_m)$, $\mathbf B=(B_1,\dots,B_m)\in\mathrm M(n,q)^m$, the **conjugacy coset** is
--   $$
--   \mathrm{Conj}^{\to}(\mathbf A,\mathbf B)=\{T\in\mathrm{GL}(n,q):TA_i=B_iT\ \text{for all }i\in[m]\}.
--   $$
--
--   **Formalization Note** "Generate" is `Algebra.adjoin K {A₁, A₂} = ⊤` (unital subalgebra); the proof of Corollary 2.4 uses exactly that the centralizer of a generating pair is the scalars.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 2.3, §2.3, p.15 (PDF p.17); Proposition 3.6, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI

/-- **`ε_gen(n, q)`: two uniform matrices fail to generate `M(n, q)`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 2.3, p.15
(PDF p.17) and Proposition 3.6, p.20 (PDF p.22): "Let εgen(n, q) = q^{−Ω(n)} be the failure
probability in Theorem 2.3."

`epsGen K n` is the fraction of pairs `(A₁, A₂) ∈ M(n, K)²` whose generated (unital) subalgebra
`K⟨A₁, A₂⟩` is not all of `M(n, K)`.

**Formalization Note.** "Generate the full matrix algebra" is `Algebra.adjoin K {A₁, A₂} = ⊤`, the
unital subalgebra; the proof of Corollary 2.4 (p.15) uses exactly that its centralizer is the
scalars. -/
noncomputable def epsGen (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : Fin 2 → Mat K n // Algebra.adjoin K {A 0, A 1} ≠ ⊤} : ℝ) /
    Nat.card (Fin 2 → Mat K n)

/-- **The conjugacy coset `Conj→(A, B) = {T ∈ GL(n, q) | ∀ i, T A_i = B_i T}`** of two matrix
tuples, §2.3, p.15 (PDF p.17). -/
def conjCoset {K : Type*} [Field K] {n m : ℕ} (A B : Fin m → Mat K n) : Set (GL (Fin n) K) :=
  {T | ∀ i, (T : Mat K n) * A i = B i * (T : Mat K n)}

end AvgCaseTI


