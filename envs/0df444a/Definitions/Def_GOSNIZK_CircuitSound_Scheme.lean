-- Prove2me | Definitions.Def_GOSNIZK_CircuitSound_Scheme
-- name    : GOSNIZK_CircuitSound_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:26.647801+00:00
-- url     : https://prove2.me/theorems/abc06186-ab65-48bb-b117-44ce5e779bfb
-- title:
--   Homomorphic proof commitment: com, K_binding, K_hiding, Topen, P01, V01, Ext and their perfect properties (§3, pp. 6–8)
-- statement:
--   A **homomorphic proof commitment scheme** consists of a message space $\mathcal M$, a randomizer space $\mathcal R$ and a commitment space $\mathcal C$, together with the algorithms
--   $$(K_{\mathrm{binding}},\ K_{\mathrm{hiding}},\ \mathrm{com},\ \mathrm{Topen},\ P_{01},\ V_{01}),$$
--   and, for perfect extractability, an extraction algorithm $\mathrm{Ext}$. Here $\mathcal M$ is a finite cyclic group $(\mathcal M,+,0)$ with generator $1$, $\mathcal R$ a finite abelian group $(\mathcal R,+,0)$ and $\mathcal C$ a finite abelian group $(\mathcal C,\cdot,1)$. The key generator $K_{\mathrm{binding}}$ outputs a commitment key $ck$ with an extraction key $xk$, and $K_{\mathrm{hiding}}$ outputs $ck$ with a trapdoor key $tk$. The commitment to $m\in\mathcal M$ with randomizer $r\in\mathcal R$ is $c=\mathrm{com}(m;r)$. On proof randomness $\rho\in\mathcal R_{\mathrm{proof}}$, the prover $P_{01}(ck,m,r;\rho)$ outputs a proof that the commitment contains $0$ or $1$, and $V_{01}(ck,c,\pi)\in\{0,1\}$ checks it.
--
--   A bit $b$ is read as the message $0$ or $1$ of $\mathcal M$. The perfect properties used in this mission are:
--
--   1. **Homomorphic property.** For every key $ck$ output by $K_{\mathrm{binding}}$ or by $K_{\mathrm{hiding}}$ and all $(m_1,r_1),(m_2,r_2)\in\mathcal M\times\mathcal R$,
--   $$\mathrm{com}(m_1+m_2;r_1+r_2)=\mathrm{com}(m_1;r_1)\,\mathrm{com}(m_2;r_2).$$
--   2. **Perfect binding.** For every $(ck,xk)$ output by $K_{\mathrm{binding}}$ there are no $(m_1,r_1),(m_2,r_2)$ with $m_1\ne m_2$ and $\mathrm{com}(m_1;r_1)=\mathrm{com}(m_2;r_2)$.
--   3. **Perfect completeness (of the 0/1 proof).** For every key $ck$ of either mode, every $(m,r)\in\{0,1\}\times\mathcal R$ and every $\rho$, $V_{01}(ck,\mathrm{com}(m;r),P_{01}(ck,m,r;\rho))=1$.
--   4. **Perfect soundness (of the 0/1 proof).** For every $(ck,xk)$ output by $K_{\mathrm{binding}}$, whenever $V_{01}(ck,c,\pi)=1$ there is $(m,r)\in\{0,1\}\times\mathcal R$ with $c=\mathrm{com}(m;r)$.
--   5. **Perfect extractability.** For every $(ck,xk)$ output by $K_{\mathrm{binding}}$ and every $(m,r)\in\{0,1\}\times\mathcal R$, $\mathrm{Ext}_{xk}(\mathrm{com}(m;r))=m$.
--
--   These are the hypotheses under which the Circuit SAT proof of Figure 3 is perfectly complete, perfectly sound and a perfect proof of knowledge.
--
--   **Formalization Note** The message space is `ZMod N`: a finite cyclic group with a chosen generator $1$ is isomorphic to $\mathbb Z/N\mathbb Z$ with $1\mapsto 1$; the order bound is a hypothesis of the theorems, not of the structure. Key generators are `PMF`s. The paper writes each property as "for all non-uniform polynomial time adversaries $\mathcal A$, $\Pr[\dots]=1$" (or $=0$); for a perfect property this says the event holds for every key in the support of the generator and every choice an adversary could make, which is how each property is stated here. The prover takes its randomness $\rho$ as an argument. Each property is a separate `Prop`, so that every theorem assumes exactly what it uses. Key indistinguishability and both witness indistinguishability properties are not included: the first is computational, and the others are not used by this mission. The display defining perfect extractability on p. 8 omits its "$=1$"; it is read with it. `Topen` is carried for uniformity with the zero-knowledge mission and is not used here.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, pp. 6–8, Section 3 (Homomorphic property, Perfect binding, Perfect completeness, Perfect soundness, Perfect extractability)

import Mathlib

namespace GOSNIZK.CircuitSound

/-- A bit read as a message: `false ↦ 0`, `true ↦ 1` in the message space `M = ZMod N`
(Groth, Ostrovsky, Sahai, *New Techniques for Noninteractive Zero-Knowledge*, J. ACM 59(3) (2012),
authors' version of March 7, 2011, §3, p. 6: "the message space has a generator 1"). -/
def ofBit {N : ℕ} (b : Bool) : ZMod N := if b then 1 else 0

/-- A homomorphic proof commitment scheme (§3, pp. 6–8), with message space `M = ZMod N` (a finite
cyclic group with generator `1`), randomizer space `R` (an additive abelian group), commitment space
`C` (a multiplicative abelian group), commitment keys `CK`, extraction keys `XK`, trapdoor keys `TK`,
proof randomness `Rp` (the paper's `R_proof`, p. 7) and 0/1-proofs `Prf`.

* `com ck m r` is the commitment `com(m; r)` under key `ck`;
* `Kbind` and `Khide` are the two key generators `K_binding`, `K_hiding`, as distributions;
* `Topen tk m₁ r₁ m₂` is the trapdoor opening `Topen_tk(m₁, r₁, m₂)`;
* `P01 ck m r ρ` is the prover `P01(ck, m, r; ρ)` that `com(m; r)` contains `0` or `1`, run on
  proof randomness `ρ`;
* `V01 ck c π` is the verifier `V01(ck, c, π)`;
* `Ext xk c` is the extraction algorithm `Ext_xk(c)` of perfect extractability (p. 8). -/
structure Scheme (N : ℕ) (R C CK XK TK Rp Prf : Type) [AddCommGroup R] [CommGroup C] where
  com : CK → ZMod N → R → C
  Kbind : PMF (CK × XK)
  Khide : PMF (CK × TK)
  Topen : TK → ZMod N → R → ZMod N → R
  P01 : CK → ZMod N → R → Rp → Prf
  V01 : CK → C → Prf → Bool
  Ext : XK → C → ZMod N

namespace Scheme

variable {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [CommGroup C]
variable (S : Scheme N R C CK XK TK Rp Prf)

/-- `ck` is a commitment key output with positive probability by `K_binding`. -/
def IsBindingKey (ck : CK) : Prop := ∃ xk : XK, (ck, xk) ∈ S.Kbind.support

/-- `ck` is a commitment key output with positive probability by `K_hiding`. -/
def IsHidingKey (ck : CK) : Prop := ∃ tk : TK, (ck, tk) ∈ S.Khide.support

/-- `ck` is a key of either mode: `mode ← {binding, hiding}; (ck, *) ← K_mode` (p. 7). -/
def IsKey (ck : CK) : Prop := S.IsBindingKey ck ∨ S.IsHidingKey ck

/-- **Homomorphic property** (p. 7): on every key of either mode,
`com(m₁ + m₂; r₁ + r₂) = com(m₁; r₁) com(m₂; r₂)` for all messages and randomizers. -/
def Homomorphic : Prop :=
  ∀ ck : CK, S.IsKey ck → ∀ (m₁ m₂ : ZMod N) (r₁ r₂ : R),
    S.com ck (m₁ + m₂) (r₁ + r₂) = S.com ck m₁ r₁ * S.com ck m₂ r₂

/-- **Perfect binding** (p. 7): on every binding key there are no openings `(m₁, r₁)`, `(m₂, r₂)`
with `m₁ ≠ m₂` and `com(m₁; r₁) = com(m₂; r₂)`. -/
def PerfectBinding : Prop :=
  ∀ (ck : CK) (xk : XK), (ck, xk) ∈ S.Kbind.support →
    ∀ (m₁ : ZMod N) (r₁ : R) (m₂ : ZMod N) (r₂ : R), m₁ ≠ m₂ → S.com ck m₁ r₁ ≠ S.com ck m₂ r₂

/-- **Perfect completeness** of the 0/1 proof (p. 7): on every key of either mode, for every
opening `(m, r) ∈ {0, 1} × R` and every proof randomness `ρ`,
`V01(ck, com(m; r), P01(ck, m, r; ρ)) = 1`. -/
def PerfectCompleteness01 : Prop :=
  ∀ ck : CK, S.IsKey ck → ∀ (b : Bool) (r : R) (ρ : Rp),
    S.V01 ck (S.com ck (ofBit b) r) (S.P01 ck (ofBit b) r ρ) = true

/-- **Perfect soundness** of the 0/1 proof (p. 7): on every binding key, whenever
`V01(ck, c, π) = 1` there is an opening `(m, r) ∈ {0, 1} × R` with `c = com(m; r)`. -/
def PerfectSoundness01 : Prop :=
  ∀ (ck : CK) (xk : XK), (ck, xk) ∈ S.Kbind.support → ∀ (c : C) (π : Prf),
    S.V01 ck c π = true → ∃ (b : Bool) (r : R), c = S.com ck (ofBit b) r

/-- **Perfect extractability** (p. 8): on every binding key with extraction key `xk`,
`Ext_xk(com(m; r)) = m` for all `(m, r) ∈ {0, 1} × R`. -/
def PerfectExtractability : Prop :=
  ∀ (ck : CK) (xk : XK), (ck, xk) ∈ S.Kbind.support → ∀ (b : Bool) (r : R),
    S.Ext xk (S.com ck (ofBit b) r) = ofBit b

end Scheme

end GOSNIZK.CircuitSound


