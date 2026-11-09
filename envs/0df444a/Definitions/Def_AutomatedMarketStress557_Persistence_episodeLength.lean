-- Prove2me | Definitions.Def_AutomatedMarketStress557_Persistence_episodeLength
-- name    : AutomatedMarketStress557_Persistence_episodeLength
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:03.584329+00:00
-- url     : https://prove2.me/theorems/551e1c1f-92d6-43d2-a096-8313a824bc7c
-- title:
--   Pathwise maximal stress episodes and their expectations
-- statement:
--   Let $r_1,r_2,\ldots$ be a real return trajectory and $c\ge0$ a threshold. Period $t\ge1$ is stressed when $r_t<-c$. Scan from period 1 to the first stressed period, then to the first subsequent nonstressed period. Repeat after that exit. Denote the successive entry and exit times by $T_j,U_j$, with $j=0,1,\ldots$. A run beginning at period 1 is included; the arbitrary initial return is outside the scan. The length is the first nonstressed offset from its entry:
--
--   $$L_j=U_j-T_j\in\{1,2,\ldots\}\cup\{+\infty\}.$$
--
--   An absent entry or a run without an exit is assigned length $+\infty$. All searches take infima in the extended natural numbers, where the infimum of an empty search is $+\infty$. The operational definition never subtracts two infinities. It searches offsets directly.
--
--   For the recursively generated return trajectory on a probability space with measure $P$, define its extended mean by
--
--   $$\overline m_j(\beta,s,c)=\int_\Omega L_j\,dP\in[0,+\infty].$$
--
--   The real mean $m_j$ is its real conversion, used only alongside the theorem's finiteness conclusion. Infinity is preserved inside the integral. These definitions enable a statement about actual successive maximal episodes, rather than abstract geometric variables or lengths assigned their intended distribution in advance.
-- source:
--   Irene Aldridge, STOC 2027 submission #557 (October 2026), Definition 3.1 and Theorem 4.2(2), PDF p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/557.pdf

import Mathlib
import Definitions.Def_AutomatedMarketStress557_Persistence_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace AutomatedMarketStress557.Persistence

/-- Definition 3.1, PDF p. 3, on the observed periods t ≥ 1. -/
def stressed (r : ℕ → ℝ) (c : ℝ) (t : ℕ) : Prop := 1 ≤ t ∧ r t < -c

/-- First time satisfying `S` at or after an extended lower bound.
The infimum is in ℕ∞: an empty set has infimum +∞. In particular a lower
bound of +∞ gives +∞, rather than restarting the scan at zero. -/
def nextTime (S : ℕ → Prop) (b : ℕ∞) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ b ≤ t ∧ S n}

/-- Successive entries into maximal stress runs. Run 0 starts at the first
stressed period ≥ 1, including period 1 itself. Each later entry follows
the first nonstressed exit of the preceding run. No prehistory is scanned. -/
def episodeEntry (r : ℕ → ℝ) (c : ℝ) : ℕ → ℕ∞
  | 0 => nextTime (stressed r c) 1
  | j + 1 => nextTime (stressed r c)
      (nextTime (fun t => ¬ stressed r c t) (episodeEntry r c j) + 1)

/-- The first nonstressed time at or after the j-th entry; +∞ if absent. -/
def episodeExit (r : ℕ → ℝ) (c : ℝ) (j : ℕ) : ℕ∞ :=
  nextTime (fun t => ¬ stressed r c t) (episodeEntry r c j)

/-- Actual pathwise run length, found by scanning offsets from its entry.
An absent entry or a never-ending run has length +∞. No infinity is
subtracted from infinity, and no infinite run is given length zero. -/
def episodeLength (r : ℕ → ℝ) (c : ℝ) (j : ℕ) : ℕ∞ :=
  if episodeEntry r c j = ⊤ then ⊤ else
    nextTime (fun k => ¬ stressed r c ((episodeEntry r c j).toNat + k)) 0

/-- Embedding extended counts into extended nonnegative reals, preserving +∞. -/
def lengthValue (l : ℕ∞) : ℝ≥0∞ := if l = ⊤ then ⊤ else (l.toNat : ℝ≥0∞)

/-- Extended expectation of the actual j-th run. Nonintegrable and infinite
lengths are retained as +∞ rather than Bochner's default zero. -/
def extendedMeanLength {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (β s c : ℝ) (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, lengthValue (episodeLength (fun t => returns β s d₀ ξ t ω) c j) ∂P

/-- The finite real mean when the preceding extended expectation is finite.
Theorem 4.2 certifies finiteness before using this real conversion. -/
def meanLength {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (β s c : ℝ) (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) (j : ℕ) : ℝ :=
  (extendedMeanLength P β s c d₀ ξ j).toReal

end AutomatedMarketStress557.Persistence


