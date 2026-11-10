-- Prove2me | Definitions.Def_BirthdayEntropy_Soundness_Counting
-- name    : BirthdayEntropy_Soundness_Counting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:49:11.51324+00:00
-- url     : https://prove2.me/theorems/1e2c15c0-2e69-4800-aaab-e9023bb59144
-- title:
--   Uniform finite subsets, deterministic cells and mutual information
-- statement:
--   Let $\Omega$ be a nonempty finite subset of a finite ambient type. Its uniform law is the pushforward of the published uniform law on the subtype $\Omega$. For a deterministic cell map $F$, put $\Omega_f=\{\omega\in\Omega:F(\omega)=f\}$. Entropy and expectation use the published finite-law definitions, with natural logarithms and zero-mass atoms allowed. Mutual information is computed from the actual pushforward laws:
--   $$I_Q(X;Y)=H_Q(X)+H_Q(Y)-H_Q(X,Y).$$
--   The fixed-size avoidance probability is the number of $\ell$-subsets containing none of the distinct forbidden unordered pairs, divided by $\binom{|U|}{\ell}$.
--
--   These interfaces support the abstract counting lemmas on arbitrary finite sets as well as the graph-specific experiment. Conditional laws require a nonempty conditioning event; no arbitrary distribution on coordinate views is introduced.
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, §4, Lemma 4.1, PDF p6 / printed p5; Lemmas 4.2,4.4, PDF pp7–8 / printed pp6–7; conditional-law setup PDF p9 / printed p8

import Mathlib
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness
open OAI.ThorpCompatibility

/-- The actual uniform law on a nonempty finite subset, as a law on the ambient type. -/
def uniformOn {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty) : Law α := by
  letI : Nonempty {a // a ∈ Ω} := ⟨⟨hΩ.choose, hΩ.choose_spec⟩⟩
  exact (Law.uniform (α := {a // a ∈ Ω})).map Subtype.val

/-- The occupied fiber of a deterministic cell map. Empty cells have count zero. -/
def cell {α τ : Type*} [Fintype α] (Ω : Finset α) (F : α → τ) (f : τ) : Finset α :=
  Ω.filter (fun a => F a = f)

/-- Mutual information in nats, computed from pushforward entropies.
No unsupported real relative entropy is used. -/
def mutualInfo {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (Q : Law α) (X : α → β) (Y : α → γ) : ℝ :=
  (Q.map X).entropy + (Q.map Y).entropy - (Q.map (fun a => (X a, Y a))).entropy

/-- The fixed-size uniform-subset probability in Lemma 4.1. The denominator
is nonzero under 2≤ell≤card U; pairs are distinct unordered two-sets. -/
def avoidanceProbability {U : Type*} [Fintype U] (P : Finset (Finset U)) (ℓ : ℕ) : ℝ :=
  (((Finset.univ.powersetCard ℓ).filter (fun S => ∀ e ∈ P, ¬ e ⊆ S)).card : ℝ) /
    Nat.choose (Fintype.card U) ℓ

end BirthdayEntropy.Soundness


