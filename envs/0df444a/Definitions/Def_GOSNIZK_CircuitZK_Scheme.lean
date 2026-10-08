-- Prove2me | Definitions.Def_GOSNIZK_CircuitZK_Scheme
-- name    : GOSNIZK_CircuitZK_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:29.57643+00:00
-- url     : https://prove2.me/theorems/c90c5318-3d5a-42eb-88c8-0e6fe8e9dff7
-- title:
--   Homomorphic proof commitment and its perfect properties: homomorphic, trapdoor opening, trapdoor opening indistinguishability, witness indistinguishability (§3, pp. 6–7)
-- statement:
--   A **homomorphic proof commitment scheme** consists of a message space $M$, a randomizer space $R$ and a commitment space $C$, all finite abelian groups ($M$ and $R$ written additively, $C$ multiplicatively), where $M$ has a generator $1$; a commitment function $\mathrm{com}_{ck}(m; r)$; a *binding* key generator $K_{\mathrm{binding}}$ that outputs a commitment key $ck$ with an extraction key $xk$; a *hiding* key generator $K_{\mathrm{hiding}}$ that outputs $ck$ with a trapdoor key $tk$; a trapdoor opening algorithm $\mathrm{Topen}_{tk}(m_1, r_1, m_2)$; a prover $P_{01}(ck, m, r; \rho)$ with randomness $\rho$ uniform on a finite set $R_{\mathrm{proof}}$, producing a proof that a commitment contains $0$ or $1$; a verifier $V_{01}$; and an extractor $\mathrm{Ext}$.
--
--   The perfect properties used in this mission are:
--
--   1. *Homomorphic property*: for every key $ck$ output by either generator and all $m_1, m_2 \in M$, $r_1, r_2 \in R$,
--   $$\mathrm{com}(m_1 + m_2; r_1 + r_2) = \mathrm{com}(m_1; r_1)\,\mathrm{com}(m_2; r_2).$$
--   2. *Perfect trapdoor opening*: for every hiding key $(ck, tk)$, all $m_1, m_2 \in M$ and every $r_1 \in R$, $\mathrm{com}(m_2; \mathrm{Topen}_{tk}(m_1, r_1, m_2)) = \mathrm{com}(m_1; r_1)$.
--   3. *Perfect trapdoor opening indistinguishability*: for every choice of messages $m_1(ck), m_2(ck)$ depending on the public key, the pair $(ck, \mathrm{Topen}_{tk}(m_1, r_1, m_2))$ with $(ck, tk) \leftarrow K_{\mathrm{hiding}}$ and $r_1$ uniform on $R$ has the same law as the pair $(ck, r_2)$ with $r_2$ uniform on $R$.
--   4. *Perfect witness indistinguishability*: for every hiding key $(ck, tk)$ and all $r_0, r_1 \in R$ with $\mathrm{com}(0; r_0) = \mathrm{com}(1; r_1)$, the proofs $P_{01}(ck, 0, r_0; \rho)$ and $P_{01}(ck, 1, r_1; \rho)$, $\rho$ uniform, have the same law.
--
--   These are the hypotheses under which the Circuit SAT proof on a hiding key is perfectly zero-knowledge.
--
--   **Formalization Note** The message space is `ZMod N` (a finite cyclic group with a chosen generator $1$ is $\mathbb Z/N$); its order bound is a hypothesis of the theorems that need it. The key generators are probability mass functions on key pairs. The paper writes each property as "for all adversaries, probability $=1$" or as an equality of two probabilities: probability-one properties are stated for every key in the support of the generator, and the equalities as equalities of laws. Trapdoor opening indistinguishability is stated jointly with $ck$, because the adversary sees $ck$ but not $tk$; it does not say that $\mathrm{Topen}_{tk}$ is uniform for each fixed $tk$. Key indistinguishability (a computational assumption), perfect binding, completeness, soundness and extractability are not stated here; the structure still carries $K_{\mathrm{binding}}$, $V_{01}$ and $\mathrm{Ext}$ so that the scheme has the paper's full shape. The paper writes $r_2 \leftarrow \mathrm{Topen}_{tk}(m_1, r_1, m_2)$, allowing a randomized trapdoor opening; here $\mathrm{Topen}$ is a function (deterministic), as it is in both of the paper's instantiations (Sections 4 and 5), and $P_{01}$ receives its coins $\rho$ explicitly.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, pp. 6–7, Section 3 (Homomorphic proof commitment: Homomorphic property, Perfect trapdoor opening, Perfect trapdoor opening indistinguishability, Perfect witness indistinguishability)

import Mathlib

namespace GOSNIZK.CircuitZK

/-- A homomorphic proof commitment scheme (Groth, Ostrovsky, Sahai, *New Techniques for Noninteractive
Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011, §3, pp. 6–8).

* The message space is `ZMod N`: a finite cyclic group with a chosen generator `1` is `ZMod N`, `N` its order.
* `R` is the randomizer space (a finite abelian group, written additively), `C` the commitment space (an abelian
  group, written multiplicatively).
* `CK`, `XK`, `TK` are the commitment, extraction and trapdoor keys; `Rp` is the randomness space `R_proof` of the
  0/1 proof and `Pf` the type of 0/1 proofs.
* `com ck m r` is `com(m; r)`, `Kbind` and `Khide` are the binding and hiding key generators (as distributions),
  `Topen tk m₁ r₁ m₂` is `Topen_tk(m₁, r₁, m₂)`, `P01 ck m r ρ` is the 0/1 prover `P01(ck, m, r; ρ)` run on the
  coins `ρ`, `V01 ck c π` the 0/1 verifier and `Ext xk c` the extractor. -/
structure Scheme (N : ℕ) (R C CK XK TK Rp Pf : Type) [AddCommGroup R] [CommGroup C] where
  com : CK → ZMod N → R → C
  Kbind : PMF (CK × XK)
  Khide : PMF (CK × TK)
  Topen : TK → ZMod N → R → ZMod N → R
  P01 : CK → ZMod N → R → Rp → Pf
  V01 : CK → C → Pf → Bool
  Ext : XK → C → ZMod N

variable {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]

/-- *Homomorphic property* (p. 7): for every key output by either generator,
`com(m₁ + m₂; r₁ + r₂) = com(m₁; r₁) com(m₂; r₂)` for all messages and randomizers. -/
def Scheme.Homomorphic (S : Scheme N R C CK XK TK Rp Pf) : Prop :=
  ∀ ck : CK, ((∃ xk, (ck, xk) ∈ S.Kbind.support) ∨ (∃ tk, (ck, tk) ∈ S.Khide.support)) →
    ∀ (m₁ m₂ : ZMod N) (r₁ r₂ : R), S.com ck (m₁ + m₂) (r₁ + r₂) = S.com ck m₁ r₁ * S.com ck m₂ r₂

/-- *Perfect trapdoor opening* (p. 7): on every hiding key `(ck, tk)`, for all messages `m₁, m₂` and every
randomizer `r₁`, `com(m₂; Topen_tk(m₁, r₁, m₂)) = com(m₁; r₁)`. -/
def Scheme.PerfectTrapdoorOpening (S : Scheme N R C CK XK TK Rp Pf) : Prop :=
  ∀ kt ∈ S.Khide.support, ∀ (m₁ : ZMod N) (r₁ : R) (m₂ : ZMod N),
    S.com kt.1 m₂ (S.Topen kt.2 m₁ r₁ m₂) = S.com kt.1 m₁ r₁

/-- *Perfect trapdoor opening indistinguishability* (p. 7). The adversary sees `ck` only and picks `m₁, m₂` as a
function of it; the joint law of `ck` and `Topen_tk(m₁, r₁, m₂)`, with `(ck, tk) ← K_hiding` and `r₁` uniform on `R`,
equals the joint law of `ck` and a fresh uniform `r₂`. -/
def Scheme.PerfectTrapdoorOpeningIndist [Fintype R] [Nonempty R] (S : Scheme N R C CK XK TK Rp Pf) : Prop :=
  ∀ m₁ m₂ : CK → ZMod N,
    (S.Khide.bind fun kt => (PMF.uniformOfFintype R).map fun r₁ =>
        (kt.1, S.Topen kt.2 (m₁ kt.1) r₁ (m₂ kt.1))) =
      (S.Khide.bind fun kt => (PMF.uniformOfFintype R).map fun r₂ => (kt.1, r₂))

/-- *Perfect witness indistinguishability* (p. 7): on every hiding key, whenever `com(0; r₀) = com(1; r₁)`, the
proof `P01(ck, 0, r₀; ρ)` and the proof `P01(ck, 1, r₁; ρ)`, with `ρ` uniform on `R_proof`, have the same law. -/
def Scheme.PerfectWI [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Pf) : Prop :=
  ∀ kt ∈ S.Khide.support, ∀ r₀ r₁ : R, S.com kt.1 0 r₀ = S.com kt.1 1 r₁ →
    (PMF.uniformOfFintype Rp).map (S.P01 kt.1 0 r₀) = (PMF.uniformOfFintype Rp).map (S.P01 kt.1 1 r₁)

end GOSNIZK.CircuitZK


