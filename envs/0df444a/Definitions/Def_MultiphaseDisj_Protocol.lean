-- Prove2me | Definitions.Def_MultiphaseDisj_Protocol
-- name    : MultiphaseDisj_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:27.123045+00:00
-- url     : https://prove2.me/theorems/983c9ddf-3752-49d1-9081-3938334d0b0d
-- title:
--   2.5-round protocols for the multiphase game and the quantities $\Phi$, $A_{\mathrm{all}}$, $B_Q$, $Z_{\mathrm{alice}}$, $\rho_1$
-- statement:
--   In the **2.5-round multiphase communication game** (Protocol 1) Alice holds $\vec S$, Bob holds $X$ and private randomness $R_{\mathrm{Bob}}$, and Merlin holds both.
--
--   1. Round 0: Merlin sends Bob a message $U=U(\vec S,X)$.
--   2. Round 0.5: Bob sends Alice $\Phi=(X^{(\neq i)},\Psi)$, where $X^{(\neq i)}=X\setminus B_i$ and $\Psi=\Psi(U,R_{\mathrm{Bob}})$; it does not depend on the query.
--   3. Round 1: a query index $Q$ is revealed to Alice only, and she sends $A_Q=A_Q(\vec S,\Phi)$.
--   4. Round 2: Bob outputs "disjoint", "intersecting" or FAIL, as a function of $(\Psi,A_Q,U)$.
--
--   $B_Q$ is the indicator that Bob outputs "disjoint", and $\rho_1=\Pr_{\mathcal D,R_{\mathrm{Bob}},Q}[B_Q=1]$. The analysis variables are $A_{\mathrm{all}}=(A_1,\dots,A_m)$, $Z_{\mathrm{alice}}=(\Phi,A_{\mathrm{all}},Q,S_{<Q})$ and $Z=(Z_{\mathrm{alice}},B_Q)$; a value of $Z$ with $B_Q=1$ is written $(z,1)$.
--
--   A protocol for epoch $i$ **has the properties of Theorem 3.3(a)–(c)** if, on the support of the joint law of $((\vec S,X),Q,R_{\mathrm{Bob}})$:
--
--   1. (zero error) $B_Q=1$ implies $S_Q\cap X=\emptyset$;
--   2. $|U|\le5t_uws_i$ and $|\Psi|\le\varepsilon s_i/4$;
--   3. $|A_q|\le17t_qw$ for every $q\in[m]$,
--
--   where a message of length $\lambda$ takes at most $2^\lambda$ values and $\varepsilon=1/40$.
--
--   **Formalization Note** The argument lists of the four message maps are exactly the structure of Theorem 3.3(e): $\Psi$ is a function of $(U,R_{\mathrm{Bob}})$, each $A_q$ of $(\vec S,\Phi)$, and Bob's output of $(\Psi,A_Q,U)$. Message lengths are counted as numbers of values on the support. Queries range over $[m]$ with $m=n$ (`Fin n`, 0-based).
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Protocol 1, p.9; Theorem 3.3, p.17; §3.3, p.19

import Mathlib
import Definitions.Def_MultiphaseDisj_HardDist

set_option autoImplicit false

noncomputable section

open Classical

namespace MultiphaseDisj

/-- A protocol for the **2.5-round multiphase communication game** of Protocol 1 for the query
sets `S⃗ = (S_q)_{q ∈ [n]}` (Alice) and the set `X` (Bob), with Merlin holding both (Ko,
*Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held version
sha256 ba26649b…, Protocol 1, p.9, and Theorem 3.3(e), p.17), in the form used for an epoch `i`
in §3.2–3.3:

* Round 0: Merlin sends `U(S⃗, X) : UT`;
* Round 0.5: Bob sends `Φ = (X^{(≠i)}, Ψ)` with `Ψ = Psi(U, R_Bob) : PT`, independent of the query;
* Round 1: the query `q` is revealed to Alice, who sends `A_q = A q S⃗ Φ : AT`;
* Round 2: Bob outputs `B(Ψ, A_q, U)`: `some true` ("disjoint"), `some false` ("intersecting")
  or `none` (FAIL).

**Formalization Note** The argument lists of the fields are the structure of Theorem 3.3(e):
`Ψ` is a function of `(U, R_Bob)`, each `A_q` of `(S⃗, Φ)`, and Bob's output of `(Ψ, A_q, U)`.
The component `X^{(≠i)} = X \ Bᵢ` of `Φ` is supplied by `phi`. -/
structure Protocol (n : ℕ) (R UT PT AT : Type*) where
  U : (Fin n → Finset (Fin n)) → Finset (Fin n) → UT
  Psi : UT → R → PT
  A : Fin n → (Fin n → Finset (Fin n)) → Finset (Fin n) × PT → AT
  B : PT → AT → UT → Option Bool

namespace Protocol

variable {n : ℕ} {R UT PT AT : Type*}

/-- The sample space of `((S⃗, X), Q, R_Bob)`; its law is `jointLaw`. -/
abbrev Sample (n : ℕ) (R : Type*) : Type _ :=
  ((Fin n → Finset (Fin n)) × Finset (Fin n)) × Fin n × R

/-- Bob's message `Ψ = Psi(U, R_Bob)`. -/
def psi (G : Protocol n R UT PT AT) (ω : Sample n R) : PT :=
  G.Psi (G.U ω.1.1 ω.1.2) ω.2.2

/-- Bob's 0.5-round message `Φ = (X^{(≠i)}, Ψ)` for the block `Bi = Bᵢ`. -/
def phi (G : Protocol n R UT PT AT) (Bi : Finset (Fin n)) (ω : Sample n R) :
    Finset (Fin n) × PT :=
  (ω.1.2 \ Bi, G.psi ω)

/-- `A_all = (A_1, …, A_m)`, the transcripts Alice would send for every query (p.19). -/
def aall (G : Protocol n R UT PT AT) (Bi : Finset (Fin n)) (ω : Sample n R) : Fin n → AT :=
  fun q => G.A q ω.1.1 (G.phi Bi ω)

/-- Bob's output when the query is `Q`. -/
def out (G : Protocol n R UT PT AT) (Bi : Finset (Fin n)) (ω : Sample n R) : Option Bool :=
  G.B (G.psi ω) (G.A ω.2.1 ω.1.1 (G.phi Bi ω)) (G.U ω.1.1 ω.1.2)

/-- The event `B_Q = 1`: Bob outputs "disjoint" (Theorem 3.3, p.17). -/
def bq (G : Protocol n R UT PT AT) (Bi : Finset (Fin n)) (ω : Sample n R) : Prop :=
  G.out Bi ω = some true

/-- `Z_alice := (Φ, A_all, Q, S_{<Q})` (p.19). -/
def zalice (G : Protocol n R UT PT AT) (Bi : Finset (Fin n)) (ω : Sample n R) :
    (Finset (Fin n) × PT) × (Fin n → AT) × Fin n × (Fin n → Option (Finset (Fin n))) :=
  (G.phi Bi ω, G.aall Bi ω, ω.2.1, prefixBefore ω.1.1 ω.2.1)

/-- The event `Z = (z, 1)`, i.e. `Z_alice = z` and `B_Q = 1` (p.19–20). -/
def zEvent (G : Protocol n R UT PT AT) (Bi : Finset (Fin n))
    (z : (Finset (Fin n) × PT) × (Fin n → AT) × Fin n × (Fin n → Option (Finset (Fin n))))
    (ω : Sample n R) : Prop :=
  G.zalice Bi ω = z ∧ G.bq Bi ω

/-- `S_Q^{(i)} := S_Q ∩ Bᵢ`. -/
def sQi (Bi : Finset (Fin n)) (ω : Sample n R) : Finset (Fin n) := ω.1.1 ω.2.1 ∩ Bi

/-- `X^{(i)} := X ∩ Bᵢ`. -/
def xi (Bi : Finset (Fin n)) (ω : Sample n R) : Finset (Fin n) := ω.1.2 ∩ Bi

/-- `ρ₁ := Pr_{D,R_Bob,Q}[B_Q = 1]` (Theorem 3.3, p.17), for the hard distribution with
`t = tu · w` and the law `rlaw` of `R_Bob`. -/
def rho1 (G : Protocol n R UT PT AT) (t : ℕ) [Fintype R] (rlaw : R → ℝ) (Bi : Finset (Fin n)) :
    ℝ :=
  pr (jointLaw n t rlaw) (G.bq Bi)

/-- The properties (a)–(c) of Theorem 3.3 (p.17) for epoch `i`, word size `w`, update time `tu`
and query time `tq` (with `t = tu · w`, `ε = 1/40`, block `Bᵢ` and `sᵢ`), on the support of the
joint law of `((S⃗, X), Q, R_Bob)`:

* (a) zero error: `B_Q = 1` implies `S_Q ∩ X = ∅`;
* (b) `|U| ≤ 5 tu w sᵢ` and `|Ψ| ≤ ε sᵢ / 4`;
* (c) `|A_q| ≤ 17 tq w` for every `q ∈ [m]`.

A message of length `λ` takes at most `2 ^ λ` values (p.17). Property (e) is built into the
types of `Protocol`. -/
def IsSimProtocol (G : Protocol n R UT PT AT) [Fintype R] (rlaw : R → ℝ) (w tu : ℕ) (tq : ℝ)
    (i : ℕ) : Prop :=
  (∀ ω, jointLaw n (tu * w) rlaw ω ≠ 0 → G.bq (block n (tu * w) i) ω →
      Disjoint (ω.1.1 ω.2.1) ω.1.2) ∧
    (supportRangeCard (jointLaw n (tu * w) rlaw) (fun ω => G.U ω.1.1 ω.1.2) : ℝ) ≤
      2 ^ ((5 * tu * w * setSize (tu * w) i : ℕ) : ℝ) ∧
    (supportRangeCard (jointLaw n (tu * w) rlaw) G.psi : ℝ) ≤
      2 ^ ((1 / 40 : ℝ) * setSize (tu * w) i / 4) ∧
    ∀ q : Fin n, (supportRangeCard (jointLaw n (tu * w) rlaw)
      (fun ω => G.A q ω.1.1 (G.phi (block n (tu * w) i) ω)) : ℝ) ≤ 2 ^ (17 * tq * w)

end Protocol

end MultiphaseDisj


