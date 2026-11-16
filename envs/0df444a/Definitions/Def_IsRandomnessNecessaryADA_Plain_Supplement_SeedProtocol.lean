-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_Supplement_SeedProtocol
-- name    : IsRandomnessNecessaryADA_Plain_Supplement_SeedProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:21:18.995902+00:00
-- url     : https://prove2.me/theorems/cbf53a2d-498b-410f-9c04-a6dafec85cc6
-- title:
--   Persistent private seeds and the seed-averaged interaction
-- statement:
--   Let $b,n$ be nonnegative integers and $X$ a domain. A private tape is a function $\sigma:\{0,\ldots,b-1\}\to\{0,1\}$. A mechanism with this tape is a family $\sigma\mapsto m_\sigma$ of unrestricted deterministic mechanisms in the published ADA protocol: responses may use the ordered sample, full query and real transcript, but do not receive the target distribution. The seed law is uniform on all $2^b$ tapes. For a history-only analyst $A$, a population law $P$, and horizon $k$, the interaction law is
--
--   $$\mathcal L(T)=2^{-b}\sum_{\sigma\in\{0,1\}^b}\mathcal L\bigl(T(m_\sigma,A,S,k)\bigr),\qquad S\sim P^n.$$
--
--   The sample is independent of the seed; the chosen seed persists for the entire run. The same analyst is used for all seeds and does not receive the seed or sample. This adapter also covers fewer than $b$ bits and adaptive bit consumption by ignoring unused tape coordinates. At $b=0$ the tape space is a singleton. It reuses the published query, transcript, replay and sampling types without imposing naturalness, measurability or efficiency restrictions.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, Is Randomness Necessary for Adaptive Data Analysis?, STOC 2027 submission #267 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf, §4.5, p.15 (PDF p.15); Definitions 2.1–2.2, pp.7–8; supporting conventions §§3–4.4, pp.8–14.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Supplement

/-- Section 4.5, p.15: one persistent private tape of b fair bits. -/
abbrev PrivateSeed (b : ℕ) := Fin b → Bool

/-- Fixing the tape leaves an unrestricted full-query deterministic mechanism. -/
abbrev SeedMechanism (X : Type) (n b : ℕ) := PrivateSeed b → Mechanism X n

noncomputable def seedLaw (b : ℕ) : PMF (PrivateSeed b) :=
  PMF.uniformOfFintype (PrivateSeed b)

/-- The seed is drawn once, independently of the iid sample inside interactionLaw.
The same history-only analyst is used for every seed; no seed is exposed to it. -/
noncomputable def seedInteractionLaw {X : Type} {n b : ℕ}
    (m : SeedMechanism X n b) (A : Analyst X) (p : PMF X) (k : ℕ) :
    PMF (Transcript (StatisticalQuery X)) :=
  (seedLaw b).bind (fun σ => interactionLaw (m σ) A p k)

end IsRandomnessNecessaryADA.Plain.Supplement


