-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_QSOWF
-- name    : QuantumKtSoI_Supplement_QSOWF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:04.556035+00:00
-- url     : https://prove2.me/theorems/ec62a642-2ca3-441b-834c-c01cf2bb529a
-- title:
--   Quantum-secure classical one-way functions (Definition 8.1)
-- statement:
--   A family $f_N:\{0,1\}^N\to\{0,1\}^*$ is a **quantum-secure classical one-way function** if a single deterministic classical algorithm computes $f_N(r)$ from $\langle 1^N,r\rangle$ in time polynomial in $N$, and every adversary has negligible inversion probability
--   $$\Pr_{r,A}\big[\,|r'|=N \text{ and } f_N(r')=f_N(r)\,\big],$$
--   where $r$ is uniform on $\{0,1\}^N$ and $r'$ is the output of one execution of $A$ on $\langle1^N,f_N(r)\rangle$. An **adversary** is a machine of Definition 3.1 that, for a fixed polynomial $p$, halts within $p(N+|u|)$ steps on every input $\langle1^N,u\rangle$ and every branch.
--
--   This is the cryptographic notion of Theorems 8.3 and A.1.
--
--   **Formalization Note** The family is one function $f$ on strings. Polynomials are taken as $c(n+2)^k$, and the adversary's output is read at its all-branch deadline. Negligible is the published `QAdvFew.PoQOracle.Negligible` (nonnegative and eventually at most $n^{-c}$ for every $c>0$), which is the paper's notion of p.14.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 8.1, p.111; negligible, p.14

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine
import Definitions.Def_QAdvFew_PoQOracle_Negligible

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- An **adversary** of Definition 8.1 (p.111 of Myrisiotis, STOC 2027 submission, held version
sha256 6616571c…): a machine of Definition 3.1 (a valid coded machine) and a polynomial
`p(n) = c(n+2)^k` such that it halts within `p(N + |u|)` steps on every input `⟨1^N, u⟩` and every
branch.

**Formalization Note** Every polynomial is bounded by one of this form, and the output law of a
machine that has halted on every branch does not change at later deadlines (Definition 3.4). -/
structure Adversary where
  A : CodedMachine
  valid : A.Valid
  c : ℕ
  k : ℕ
  halts : ∀ N : ℕ, ∀ u : List Bool,
    A.toMachine.HaltsWithin (pair (ones N) u) (c * (N + u.length + 2) ^ k)

/-- The inversion probability `Pr_{r, A}[|r′| = N ∧ f_N(r′) = f_N(r)]` of an adversary against a
family `f` (Definition 8.1, p.111): `r` uniform on `{0,1}^N`, `r′` the output of one execution of
`A` on `⟨1^N, f_N(r)⟩` at its all-branch deadline; a wrong-length response is rejected. -/
def invProb (f : List Bool → List Bool) (Adv : Adversary) (N : ℕ) : ℝ :=
  ∑ r : Fin N → Bool, (1 / 2 ^ N : ℝ) *
    ∑ r' ∈ (Finset.univ : Finset (Fin N → Bool)).filter (fun r' => f (List.ofFn r') = f (List.ofFn r)),
      Adv.A.toMachine.outputProb (pair (ones N) (f (List.ofFn r)))
        (Adv.c * (N + (f (List.ofFn r)).length + 2) ^ Adv.k) (List.ofFn r')

/-- **Definition 8.1** (Quantum-secure one-way functions, p.111): a family `f_N : {0,1}^N → {0,1}*`
(written as one function `f` on strings, `f_N = f` on `{0,1}^N`) is a **quantum-secure classical
one-way function** if a single deterministic classical algorithm (a valid coded machine without
gate states) computes `f_N(r)` from `⟨1^N, r⟩` in time `c(N+2)^k`, and every adversary has
negligible inversion probability (negligible as on p.14, the published
`QAdvFew.PoQOracle.Negligible`: nonnegative and eventually below `N^{−c}` for every `c > 0`). -/
def QuantumSecureOWF (f : List Bool → List Bool) : Prop :=
  (∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ N : ℕ, ∀ r : List Bool, r.length = N →
      F.toMachine.HaltsWithin (pair (ones N) r) (c * (N + 2) ^ k) ∧
        F.toMachine.outputProb (pair (ones N) r) (c * (N + 2) ^ k) (f r) = 1) ∧
    ∀ Adv : Adversary, QAdvFew.PoQOracle.Negligible (invProb f Adv)

end QuantumKtSoI.Supplement


