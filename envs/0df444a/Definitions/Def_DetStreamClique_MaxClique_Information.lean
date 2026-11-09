-- Prove2me | Definitions.Def_DetStreamClique_MaxClique_Information
-- name    : DetStreamClique_MaxClique_Information
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:58:16.51868+00:00
-- url     : https://prove2.me/theorems/c8e16c90-c86d-4545-a211-bcdabcb675b4
-- title:
--   Base-2 entropy, conditioning and message-wise information
-- statement:
--   Use the published finite probability laws $P$ and their entropy, converting nats to bits by division by $\log 2$. For finite-valued random variables $X,Y,Z$, the event mass and marginal event mass are $P(E)$ and $P(X=x,E)$. On $P(E)>0$, the event entropy is
--   $$H_P(X\mid E)=-\sum_x\frac{P(X=x,E)}{P(E)}\log_2\frac{P(X=x,E)}{P(E)}.$$
--   Define $H(X\mid Y)$ by averaging these conditional entropies, $I(X;Y)=H(X)-H(X\mid Y)$, and $I(X;Y\mid E)=H(X\mid E)+H(Y\mid E)-H(X,Y\mid E)$. Definition 2.1 is
--   $$J(X\mid Y=y,Z=z)=H(X\mid Z=z)-H(X\mid Y=y,Z=z).$$
--   The order of $Y$ and $Z$ is part of the definition. Conditional product structure is the equality of the conditional joint mass with the product of its marginal masses, for every tuple.
--
--   Null conditional events return zero as a total extension; theorem hypotheses exclude them wherever a particular conditional distribution is used. Zero-mass terms follow $0\log 0=0$. All sums are finite, so no integrability or infinite-support conventions are introduced.
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, §2.2 and Definition 2.1, pp. 8–9

import Mathlib
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

abbrev FiniteLaw (Ω : Type) [Fintype Ω] := OAI.ThorpCompatibility.Law Ω

/-- Entropy in bits, converting the published finite-law entropy from nats. -/
noncomputable def entropyBits {Ω X : Type} [Fintype Ω] [Fintype X]
    (P : FiniteLaw Ω) (f : Ω → X) : ℝ :=
  (P.map f).entropy / Real.log 2

noncomputable def eventProb {Ω : Type} [Fintype Ω]
    (P : FiniteLaw Ω) (E : Ω → Prop) : ℝ :=
  ∑ w, if E w then P.mass w else 0

noncomputable def eventMass {Ω X : Type} [Fintype Ω] [Fintype X]
    (P : FiniteLaw Ω) (f : Ω → X) (E : Ω → Prop) (x : X) : ℝ :=
  ∑ w, if E w ∧ f w = x then P.mass w else 0

/-- Entropy of the normalized conditional marginal; used only on positive events.
On a null event every normalized mass is zero, and this total extension returns zero. -/
noncomputable def eventEntropy {Ω X : Type} [Fintype Ω] [Fintype X]
    (P : FiniteLaw Ω) (f : Ω → X) (E : Ω → Prop) : ℝ :=
  -(∑ x, let p := eventMass P f E x / eventProb P E; p * Real.log p) / Real.log 2

noncomputable def conditionalEntropy {Ω X Y : Type}
    [Fintype Ω] [Fintype X] [Fintype Y]
    (P : FiniteLaw Ω) (f : Ω → X) (g : Ω → Y) : ℝ :=
  ∑ y, (P.map g).mass y * eventEntropy P f (fun w => g w = y)

noncomputable def mutualInformation {Ω X Y : Type}
    [Fintype Ω] [Fintype X] [Fintype Y]
    (P : FiniteLaw Ω) (f : Ω → X) (g : Ω → Y) : ℝ :=
  entropyBits P f - conditionalEntropy P f g

/-- Conditional mutual information given an event, in its joint-entropy form. -/
noncomputable def mutualAt {Ω X Y : Type}
    [Fintype Ω] [Fintype X] [Fintype Y]
    (P : FiniteLaw Ω) (f : Ω → X) (g : Ω → Y) (E : Ω → Prop) : ℝ :=
  eventEntropy P f E + eventEntropy P g E -
    eventEntropy P (fun w => (f w, g w)) E

/-- Definition 2.1: the order of message g and background h matters. -/
noncomputable def messageInformation {Ω X Y Z : Type}
    [Fintype Ω] [Fintype X] [Fintype Y] [Fintype Z]
    (P : FiniteLaw Ω) (f : Ω → X) (g : Ω → Y) (y : Y) (h : Ω → Z) (z : Z) : ℝ :=
  eventEntropy P f (fun w => h w = z) -
    eventEntropy P f (fun w => g w = y ∧ h w = z)

/-- Product law conditional on h=z, as an equality of every atom's mass. -/
def ConditionalProduct {Ω I : Type} {X : I → Type} {Z : Type}
    [Fintype Ω] [Fintype I] [∀ i, Fintype (X i)] [Fintype Z]
    (P : FiniteLaw Ω) (f : Ω → ((i : I) → X i)) (h : Ω → Z) (z : Z) : Prop :=
  ∀ x, eventMass P f (fun w => h w = z) x / eventProb P (fun w => h w = z) =
    ∏ i, eventMass P (fun w => f w i) (fun w => h w = z) (x i) /
      eventProb P (fun w => h w = z)

end DetStreamClique.MaxClique


