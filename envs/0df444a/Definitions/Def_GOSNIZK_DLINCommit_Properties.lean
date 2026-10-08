-- Prove2me | Definitions.Def_GOSNIZK_DLINCommit_Properties
-- name    : GOSNIZK_DLINCommit_Properties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:49.306763+00:00
-- url     : https://prove2.me/theorems/8595859a-e66e-42cf-b5c3-d0db7c9a87ef
-- title:
--   The perfect properties of a homomorphic proof commitment (§3, pp. 7–8), for the scheme of Figure 2
-- statement:
--   Section 3 lists the properties a homomorphic proof commitment must satisfy. Instantiated for the scheme of Figure 2 over a DLIN bilinear group, the exact ones read as follows ($\rho, \rho_0, \rho_1$ range over randomizers in $\mathbb Z_p^2$, $t$ over proof randomness in $\mathbb Z_p$).
--
--   1. **Homomorphic.** On every key in the support of either generator, $\mathrm{com}(m_1+m_2; r_1+r_2, s_1+s_2) = \mathrm{com}(m_1; r_1, s_1)\,\mathrm{com}(m_2; r_2, s_2)$.
--   2. **Perfect binding.** On every binding key, $\mathrm{com}(m_1; \rho_1) = \mathrm{com}(m_2; \rho_2)$ implies $m_1 = m_2$.
--   3. **Perfect extractability.** On every binding key $(ck, xk)$, $\mathrm{Ext}_{xk}(\mathrm{com}(m; r, s)) = m$ for $m \in \{0, 1\}$ and all $r, s$.
--   4. **Perfect trapdoor opening.** On every hiding key $(ck, tk)$, $\mathrm{com}(m_1; \rho_1) = \mathrm{com}(m_2; \mathrm{Topen}_{tk}(m_1, \rho_1, m_2))$ for all $m_1, m_2, \rho_1$.
--   5. **Perfect trapdoor opening indistinguishability.** On every hiding key and for all $m_1, m_2$, if $\rho_1$ is uniform on $\mathbb Z_p^2$ then $\mathrm{Topen}_{tk}(m_1, \rho_1, m_2)$ is uniform on $\mathbb Z_p^2$.
--   6. **Perfect completeness.** On every key in the support of either generator, $V_{01}(ck, \mathrm{com}(m; r, s), P_{01}(ck, m, (r, s); t))$ holds for $m \in \{0,1\}$ and all $r, s, t$.
--   7. **Perfect soundness.** On every binding key, if $V_{01}(ck, c, \pi)$ accepts for some $c \in \mathbb G^3$, $\pi \in \mathbb G^6$, then $c = \mathrm{com}(m; r, s)$ for some $m \in \{0, 1\}$ and $r, s \in \mathbb Z_p$.
--   8. **Perfect witness indistinguishability.** On every hiding key, whenever $\mathrm{com}(0; \rho_0) = \mathrm{com}(1; \rho_1)$, the proofs $P_{01}(ck, 0, \rho_0; t)$ and $P_{01}(ck, 1, \rho_1; t)$ have the same distribution for $t$ uniform on $\mathbb Z_p$.
--   9. **Perfect non-erasure witness indistinguishability** with simulator $\mathrm{Sim}$. On every hiding key, for $m \in \{0,1\}$ and whenever $\mathrm{com}(m; \rho_0) = \mathrm{com}(1-m; \rho_1)$,
--   $$\bigl(P_{01}(ck, m, \rho_0; t_0),\ \mathrm{Sim}(m, \rho_0, \rho_1, t_0)\bigr) \ \overset{d}{=}\ \bigl(P_{01}(ck, 1-m, \rho_1; t_1),\ t_1\bigr), \qquad t_0, t_1 \text{ uniform on } \mathbb Z_p.$$
--
--   Theorem 4 of the paper asserts all of them for Figure 2, together with key indistinguishability under the decisional linear assumption.
--
--   **Formalization Note** The paper states each property as "for all non-uniform polynomial-time adversaries, a probability over the key generator equals 1 (or 0)", or "two probabilities are equal". For perfect properties this is equivalent to the support-wise statements above: every key in the support of the generator and every choice an adversary could make, resp. equality of the output distributions (`PMF` equality) for every such key and choice. Key indistinguishability, the one computational clause, is not part of these definitions. In property 9 the simulator is an argument; the paper asks for the existence of a polynomial-time simulator taking $(ck, m, \rho_0, \rho_1, t_0)$. The structural requirement of §3 that the message space have a generator $1$ and order at least $3$ is not included.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, pp. 7–8, Section 3 (Homomorphic property, Perfect binding, Perfect trapdoor opening, Perfect trapdoor opening indistinguishability, Perfect completeness, Perfect soundness, Perfect witness indistinguishability, Perfect extractability, Perfect non-erasure witness indistinguishability)

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Scheme

namespace GOSNIZK.DLINCommit

namespace DLINSetup

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
variable (S : DLINSetup G GT)

/-! The perfect properties of a homomorphic proof commitment (Groth, Ostrovsky, Sahai 2012, §3, pp. 7–8),
instantiated for the scheme of Figure 2. "Probability 1 (resp. 0) over the key generator for every
adversary" is stated for every key in the support of the generator and every choice the adversary could
make; "equal probabilities for every adversary" is stated as equality of the output distributions
(`PMF`s) for every key in the support and every adversarial choice. The computational clause (key
indistinguishability) is not part of these definitions. -/

/-- **Homomorphic property** (p. 7): on every key in the support of either key generator,
`com(m₁ + m₂; r₁ + r₂, s₁ + s₂) = com(m₁; r₁, s₁) com(m₂; r₂, s₂)` for all messages and randomizers. -/
def Homomorphic : Prop :=
  ∀ ck : CommitKey G,
    ((∃ xk, S.IsBindingKey ck xk) ∨ (∃ tk, S.IsHidingKey ck tk)) →
    ∀ m₁ r₁ s₁ m₂ r₂ s₂ : ZMod S.p,
      S.com ck (m₁ + m₂) (r₁ + r₂) (s₁ + s₂) = S.com ck m₁ r₁ s₁ * S.com ck m₂ r₂ s₂

/-- **Perfect binding** (p. 7): on every binding key, no commitment has openings to two different
messages. -/
def PerfectBinding : Prop :=
  ∀ ck xk, S.IsBindingKey ck xk →
    ∀ m₁ r₁ s₁ m₂ r₂ s₂ : ZMod S.p, S.com ck m₁ r₁ s₁ = S.com ck m₂ r₂ s₂ → m₁ = m₂

/-- **Perfect extractability** (p. 8): on every binding key `(ck, xk)`, `Ext_xk(com(m; r, s)) = m` for
every `m ∈ {0, 1}` and every randomizer `(r, s)`. -/
def PerfectExtractability : Prop :=
  ∀ ck xk, S.IsBindingKey ck xk →
    ∀ m : ZMod S.p, (m = 0 ∨ m = 1) → ∀ r s : ZMod S.p, S.Ext xk (S.com ck m r s) = m

/-- **Perfect trapdoor opening** (p. 7): on every hiding key `(ck, tk)`, for all messages `m₁, m₂` and
every randomizer `ρ₁`, `com(m₁; ρ₁) = com(m₂; Topen_tk(m₁, ρ₁, m₂))`. -/
def PerfectTrapdoorOpening : Prop :=
  ∀ ck tk, S.IsHidingKey ck tk →
    ∀ (m₁ m₂ : ZMod S.p) (ρ₁ : ZMod S.p × ZMod S.p),
      S.com ck m₁ ρ₁.1 ρ₁.2 = S.com ck m₂ (S.Topen tk m₁ ρ₁ m₂).1 (S.Topen tk m₁ ρ₁ m₂).2

/-- **Perfect trapdoor opening indistinguishability** (p. 7): on every hiding key `(ck, tk)` and for all
messages `m₁, m₂`, the trapdoor opening `Topen_tk(m₁, ρ₁, m₂)` of a uniformly random randomizer
`ρ₁ ← ℤ_p × ℤ_p` is distributed uniformly on `ℤ_p × ℤ_p`. -/
def PerfectTrapdoorOpeningIndist : Prop :=
  ∀ ck tk, S.IsHidingKey ck tk →
    ∀ m₁ m₂ : ZMod S.p,
      (PMF.uniformOfFintype (ZMod S.p × ZMod S.p)).map (fun ρ₁ => S.Topen tk m₁ ρ₁ m₂) =
        PMF.uniformOfFintype (ZMod S.p × ZMod S.p)

/-- **Perfect completeness** (p. 7): on every key in the support of either key generator, for every
opening `(m, (r, s)) ∈ {0, 1} × ℤ_p²` and every proof randomness `t`,
`V01(ck, com(m; r, s), P01(ck, m, (r, s); t))` holds. -/
def PerfectCompleteness : Prop :=
  ∀ ck : CommitKey G,
    ((∃ xk, S.IsBindingKey ck xk) ∨ (∃ tk, S.IsHidingKey ck tk)) →
    ∀ m : ZMod S.p, (m = 0 ∨ m = 1) →
      ∀ r s t : ZMod S.p, S.V01 ck (S.com ck m r s) (S.P01 ck m (r, s) t)

/-- **Perfect soundness** (p. 7): on every binding key, whenever `V01(ck, c, π)` accepts for some
`c ∈ 𝔾³` and `π ∈ 𝔾⁶`, there is an opening `(m, (r, s)) ∈ {0, 1} × ℤ_p²` with `c = com(m; r, s)`. -/
def PerfectSoundness : Prop :=
  ∀ ck xk, S.IsBindingKey ck xk →
    ∀ (c : G × G × G) (π : Proof01 G), S.V01 ck c π →
      ∃ m r s : ZMod S.p, (m = 0 ∨ m = 1) ∧ c = S.com ck m r s

/-- **Perfect witness indistinguishability** (p. 7): on every hiding key and for all randomizers
`ρ₀, ρ₁` with `com(0; ρ₀) = com(1; ρ₁)`, the proof `P01(ck, 0, ρ₀; t)` and the proof
`P01(ck, 1, ρ₁; t)` have the same distribution when the proof randomness `t` is uniform on `ℤ_p`. -/
def PerfectWI : Prop :=
  ∀ ck tk, S.IsHidingKey ck tk →
    ∀ ρ₀ ρ₁ : ZMod S.p × ZMod S.p, S.com ck 0 ρ₀.1 ρ₀.2 = S.com ck 1 ρ₁.1 ρ₁.2 →
      (PMF.uniformOfFintype (ZMod S.p)).map (S.P01 ck 0 ρ₀) =
        (PMF.uniformOfFintype (ZMod S.p)).map (S.P01 ck 1 ρ₁)

/-- **Perfect non-erasure witness indistinguishability** (p. 8) with the randomness simulator `Sim`: on
every hiding key, for every `m ∈ {0, 1}` and all randomizers `ρ₀, ρ₁` with `com(m; ρ₀) = com(1 − m; ρ₁)`,
the pair `(P01(ck, m, ρ₀; t₀), Sim(m, ρ₀, ρ₁, t₀))` with `t₀` uniform has the same distribution as the
pair `(P01(ck, 1 − m, ρ₁; t₁), t₁)` with `t₁` uniform. The paper's definition asks for *some*
polynomial-time simulator; here the simulator is an explicit argument. -/
def PerfectNonErasureWI
    (Sim : ZMod S.p → ZMod S.p × ZMod S.p → ZMod S.p × ZMod S.p → ZMod S.p → ZMod S.p) : Prop :=
  ∀ ck tk, S.IsHidingKey ck tk →
    ∀ m : ZMod S.p, (m = 0 ∨ m = 1) →
      ∀ ρ₀ ρ₁ : ZMod S.p × ZMod S.p, S.com ck m ρ₀.1 ρ₀.2 = S.com ck (1 - m) ρ₁.1 ρ₁.2 →
        (PMF.uniformOfFintype (ZMod S.p)).map (fun t₀ => (S.P01 ck m ρ₀ t₀, Sim m ρ₀ ρ₁ t₀)) =
          (PMF.uniformOfFintype (ZMod S.p)).map (fun t₁ => (S.P01 ck (1 - m) ρ₁ t₁, t₁))

end DLINSetup

end GOSNIZK.DLINCommit


