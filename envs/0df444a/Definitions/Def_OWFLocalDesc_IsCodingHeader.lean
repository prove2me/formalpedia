-- Prove2me | Definitions.Def_OWFLocalDesc_IsCodingHeader
-- name    : OWFLocalDesc_IsCodingHeader
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:23.072409+00:00
-- url     : https://prove2.me/theorems/acffc226-18f4-4fab-8840-368dd461a370
-- title:
--   A coding header $\sigma_Q$ (Definition 3.2)
-- statement:
--   Fix a PAC-style sampler $D=(\mu,Q)$. The **coding procedure** on a query $z$ and payload $v$ computes $n=|z|$, $q=q(n)$ and $j=|v|$, reads a $q\times j$ binary matrix $M$ and a $q$-bit vector $b$ from the first $q(j+1)$ public bits, computes $r=Mv\oplus b$ over $\mathbb F_2$, and returns $c_r(z)$.
--
--   A self-delimiting header $\sigma$ is a **coding header** for $D$ if, with the empty anchor list and on every tape of at least $q(j+1)$ bits,
--
--   1. whenever the run of $U$ on $\sigma v$ halts, its output is the coding procedure's answer, and
--   2. the run halts within a polynomial in $|\sigma v|$ and $|z|$ steps.
--
--   The length $c_Q=|\sigma|$ enters the coding bound of Lemma 3.3.
--
--   **Formalization Note** The paper fixes one header; statements quantify over every header with properties 1 and 2. Property 2 is the polynomial simulation overhead of §2.1. The tape holds $M$ row by row, then $b$ (helper `codingSeed`); any fixed layout gives the same distribution of $r$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 3.2, p.15

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_Decoder
import Definitions.Def_OWFLocalDesc_PACSampler
set_option autoImplicit false

namespace OWFLocalDesc

/-- The concept seed `r = Mv ⊕ b` read from a public tape `w`: the `q × j` matrix `M`
(`j = |v|`) is the first `qj` tape bits, row by row, and `b` is the next `q` bits. -/
def codingSeed (q : ℕ) (v w : List Bool) : List Bool :=
  List.ofFn fun i : Fin q =>
    (List.ofFn fun k : Fin v.length => w.getD (i * v.length + k) false && v.getD k false).foldl
      xor (w.getD (q * v.length + i) false)

/-- The answer of the coding procedure on payload `v`, tape `w` and query `z`: `c_r(z)` with
`n = |z|` and `r = codingSeed (q n) v w`. -/
def codingAnswer (D : PACSampler) (v w z : List Bool) : Bool :=
  (D.conc (QuantumPRC.tupleCode
    [QuantumPRC.unary z.length, codingSeed (D.q z.length) v w, z])).headD false

/-- **A coding header `σ_Q` (Definition 3.2).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 3.2,
p.15: "Fix once and for all a self-delimiting header σ_Q, depending only on D, of length c_Q, for the
following procedure. On a query z and payload v, it computes n = |z| and q = q(n). It reads the
payload up to its end marker and sets j = |v|. It reads a q × j binary matrix M and a q-bit vector b
from the first q(j+1) public bits. It then computes r = Mv ⊕ b, runs Q(1^n; r), and returns the
concept value c_r(z)."

`IsCodingHeader U D σ` says that, with the empty anchor list and on every tape holding at least
`q(j+1)` bits, the program `σ ++ v` (1) returns `codingAnswer D v w z` whenever it halts and
(2) halts within a polynomial in the lengths of the program and the query.

**Formalization Note.** The paper fixes one header; the formalization quantifies over every header
with these properties. Property (2) is §2.1's polynomial simulation overhead (p.12) for this
polynomial-time procedure; without it a slow but correct header would qualify. The layout of
`M` and `b` on the tape is the one of `codingSeed` (any fixed layout gives the same
distribution of `r`). `c_Q` is `σ.length`. -/
def IsCodingHeader (U : Decoder) (D : PACSampler) (σ : List Bool) : Prop :=
  (∀ (v w z : List Bool) (s : ℕ) (o : Option Bool), D.q z.length * (v.length + 1) ≤ w.length →
      U.run (σ ++ v) [] w z s = some o → o = some (codingAnswer D v w z)) ∧
    ∃ c : ℕ, ∀ v w z : List Bool, D.q z.length * (v.length + 1) ≤ w.length →
      ∃ s ≤ ((σ ++ v).length + z.length) ^ c + c, (U.run (σ ++ v) [] w z s).isSome

end OWFLocalDesc


