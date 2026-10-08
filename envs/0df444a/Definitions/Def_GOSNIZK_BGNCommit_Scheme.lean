-- Prove2me | Definitions.Def_GOSNIZK_BGNCommit_Scheme
-- name    : GOSNIZK_BGNCommit_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:18.590186+00:00
-- url     : https://prove2.me/theorems/7969cbb8-4d51-4d1c-94cb-74de75770c4e
-- title:
--   Figure 1: the BGN homomorphic proof commitment — keys, $\mathrm{com}$, $\mathrm{Topen}$, $P_{01}$, $V_{01}$, $\mathrm{Ext}$ (p. 10)
-- statement:
--   Fix a BGN bilinear group $(p, q, \mathbb G, \mathbb G_T, e, g)$ with $n = pq$. Figure 1 of Groth, Ostrovsky and Sahai defines the following homomorphic proof commitment scheme, whose commitment key is $ck = (n, \mathbb G, \mathbb G_T, e, g, h)$ for an element $h \in \mathbb G$.
--
--   1. **Perfectly binding keys.** $h = g^{px}$ for some $x \in \mathbb Z_q^*$ (a unit modulo $q$); the extraction key is $xk = (ck, q)$. Such an $h$ has order $q$.
--   2. **Perfectly hiding keys.** $h = g^{x}$ for some $x \in \mathbb Z_n^*$; the trapdoor key is $tk = (ck, x)$. Such an $h$ generates $\mathbb G$.
--   3. **Commitment.** For a message $m$ and a randomizer $r \in \mathbb Z_n$,
--   $$\mathrm{com}_{ck}(m; r) = g^m h^r .$$
--   4. **Trapdoor opening.** $\mathrm{Topen}_{tk}(m, r, m') = r - (m' - m)/x \bmod n$.
--   5. **Proof that a commitment contains 0 or 1.** $P_{01}(ck, m, r) = (g^{2m-1} h^r)^r$; it uses no randomness.
--   6. **Verification.** $V_{01}(ck, c, \pi)$ accepts if and only if
--   $$e(c, c g^{-1}) = e(h, \pi).$$
--   7. **Extraction.** $\mathrm{Ext}_{xk}(c)$ computes $c^q$ and searches exhaustively for $m \in \mathbb Z_p$ with $c^q = (g^q)^m$: it returns the least $k \in \{0, \dots, p-1\}$ with $c^q = (g^q)^k$, read in $\mathbb Z_p$, and returns $0$ if there is none.
--
--   These are the algorithms whose perfect properties Theorem 2 of the paper asserts.
--
--   **Formalization Note** The keys are described by the support of the two key generators: predicates on $h$ (binding) and on $(h, x)$ (hiding). Messages and randomizers are elements of $\mathbb Z_n$ (`ZMod n`) and $g^a$ means $g$ raised to the representative of $a$ in $\{0, \dots, n-1\}$; since $g^n = 1$ this makes $\mathrm{com}$ a well-defined homomorphism. The paper says the message space is $\mathbb Z_p$, but $g^m$ is not well defined on $\mathbb Z_p$ in a group of order $pq$; the mission therefore reads messages in $\mathbb Z_n$ and compares them modulo $p$ wherever the paper's message space matters (binding, extraction). $(m'-m)/x$ is $(m'-m)\,x^{-1}$ with the inverse in $\mathbb Z_n$, meaningful because $x$ is a unit. The verifier is a proposition (accept = the equation holds). The extractor's fallback value $0$ is never used on commitments under a binding key. The second key generator is headed "$K_{\mathrm{binding}}$" on the page, a typo for $K_{\mathrm{hiding}}$.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 10, Figure 1

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup

namespace GOSNIZK.BGNCommit

namespace BGNSetup

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- The support of the perfectly binding key generator `K_binding` of Figure 1 (Groth, Ostrovsky,
Sahai 2012, p. 10): `h = g^{px}` for some `x ∈ ℤ_q^*`. The commitment key is `ck = (n, 𝔾, 𝔾_T, e, g, h)`
and the extraction key is `xk = (ck, q)`; both are determined by `S` and `h`. -/
def IsBindingKey (S : BGNSetup G GT) (h : G) : Prop :=
  ∃ x : ZMod S.q, IsUnit x ∧ h = S.g ^ (S.p * x.val)

/-- The support of the perfectly hiding key generator of Figure 1 (p. 10; printed "K_binding", a typo
for `K_hiding`): `h = g^x` for the trapdoor `x ∈ ℤ_n^*`; the trapdoor key is `tk = (ck, x)`. -/
def IsHidingKey (S : BGNSetup G GT) (h : G) (x : ZMod S.n) : Prop :=
  IsUnit x ∧ h = S.g ^ x.val

/-- The commitment `com_ck(m; r) = g^m h^r` of Figure 1. Messages and randomizers are elements of
`ℤ_n`; the exponent of `a ∈ ℤ_n` is its representative `a.val ∈ {0, …, n − 1}`. -/
def com (S : BGNSetup G GT) (h : G) (m r : ZMod S.n) : G :=
  S.g ^ m.val * h ^ r.val

/-- The trapdoor opening `Topen_tk(m, r, m′) = r − (m′ − m)/x mod n` of Figure 1. -/
def Topen (S : BGNSetup G GT) (x : ZMod S.n) (m r m' : ZMod S.n) : ZMod S.n :=
  r - (m' - m) * x⁻¹

/-- The prover `P01(ck, m, r) = (g^{2m−1} h^r)^r` of Figure 1 (deterministic: no proof randomness). -/
def P01 (S : BGNSetup G GT) (h : G) (m r : ZMod S.n) : G :=
  (S.g ^ (2 * m - 1).val * h ^ r.val) ^ r.val

/-- The verifier `V01(ck, c, π)` of Figure 1: accept iff `e(c, c g^{-1}) = e(h, π)`. -/
def V01 (S : BGNSetup G GT) (h c π : G) : Prop :=
  S.e c (c * S.g⁻¹) = S.e h π

/-- The extractor `Ext_xk(c)` of Figure 1: compute `c^q` and exhaustively search for `m ∈ ℤ_p` with
`c^q = (g^q)^m`, i.e. return the least `k < p` with `c^q = (g^q)^k`, read in `ℤ_p`; if there is none,
return `0` (failure symbol; this branch never fires on a binding key). -/
noncomputable def Ext (S : BGNSetup G GT) (c : G) : ZMod S.p := by
  classical
  exact if hc : ∃ k : ℕ, k < S.p ∧ c ^ S.q = (S.g ^ S.q) ^ k then ((Nat.find hc : ℕ) : ZMod S.p) else 0

end BGNSetup

end GOSNIZK.BGNCommit


