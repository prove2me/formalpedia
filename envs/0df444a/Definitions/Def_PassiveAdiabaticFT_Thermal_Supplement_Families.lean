-- Prove2me | Definitions.Def_PassiveAdiabaticFT_Thermal_Supplement_Families
-- name    : PassiveAdiabaticFT_Thermal_Supplement_Families
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:59:33.842198+00:00
-- url     : https://prove2.me/theorems/eb32c48f-d43d-43a2-ac5c-be7fba94c230
-- title:
--   Code families, rare bad syndromes and eventual barrier lower bounds
-- statement:
--   A code family consists of block lengths $n_i$ tending to infinity and a stabilizer code $C_i$ on $n_i$ qubits for each $i\in\mathbb N$. The number of checks $m_i$ and encoded qubits may vary. The condition $m=O(n)$ means that some $M>0$ satisfies $m_i\le Mn_i$ for all sufficiently large $i$.
--
--   At fixed penalty $J$ and inverse temperature $\beta$, rare bad syndromes with exponent $c$ mean that some $A,a>0$, independent of $i$, admit a starting index after which each code has a Pauli decoder $D_i$ with canonical bad set $B_{\mathrm{dec},i}$ satisfying the commutator condition of Definition 1.1 and
--
--   $$\pi_{\beta,i}(B_{\mathrm{dec},i})\le A\exp(-a n_i^c).$$
--
--   The decoder may depend on $i$ and $\beta$. By the published Lemma 2.4, the canonical set is the smallest admissible bad set, so this is equivalent to the formulation with an arbitrary admissible set.
--
--   For a function $f:\mathbb N\to\mathbb R$, the notation $\Delta=\Omega(f(n))$ means that there are $d>0$ and an index after which
--
--   $$n_i\ge2,\qquad d f(n_i)\le\Delta_i=2J\,r_i,$$
--
--   where $r_i$ is the published integer barrier count. Cofinality permits the harmless $n_i\ge2$ convention, so logarithms in asymptotic targets have positive arguments and nonzero values. No barrier or decoder existence theorem is a field of the family datum. These wrappers express the three asymptotic assertions of Corollary 2.11 on arbitrary available block lengths, including sparse sequences.
-- source:
--   Arsalan Motamedi, Peter Love, STOC 2027 submission #1144 (October 2026), Definition 1.1, p. 7; Definitions 1.3–1.4, p. 8; Corollary 2.11, pp. 18–19, (2.36)–(2.39).

import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

set_option autoImplicit false

noncomputable section

namespace PassiveAdiabaticFT.Thermal.Supplement

/-- A family along any sequence of available block lengths tending to infinity.
No independence, degree, locality, CSS or fixed logical-dimension condition is imposed. -/
structure CodeFamily where
  n : ℕ → ℕ
  code : (i : ℕ) → StabCode (n i)
  cofinal : ∀ N : ℕ, ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → N ≤ n i

/-- The standing assumption m = O(n) of Corollary 2.11.
The coefficient and starting index are independent of the family index. -/
def linearChecks (F : CodeFamily) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
    ((F.code i).m : ℝ) ≤ M * (F.n i : ℝ)

/-- Definition 1.1, expressed using the canonical bad set (2.6), as in Corollary 2.11.
Lemma 2.4 identifies this with the formulation using any admissible bad set.
The prefactor, decay rate and starting index are uniform in block length.
Decoders can depend on the index and on the fixed inverse temperature. -/
def rareBad (F : CodeFamily) (J β c : ℝ) : Prop :=
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
    ∃ D : PauliDecoder (F.code i), D.BadSetCondition D.Bdec ∧
      (F.code i).gibbsSet J β D.Bdec ≤ A * Real.exp (-a * (F.n i : ℝ) ^ c)

/-- A positive eventual lower-bound coefficient: Delta_n = Omega(f(n)).
The starting index can be enlarged so that n >= 2, avoiding undefined source logarithms. -/
def barrierOmega (F : CodeFamily) (J : ℝ) (f : ℕ → ℝ) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
    2 ≤ F.n i ∧ d * f (F.n i) ≤ (F.code i).barrier J

end PassiveAdiabaticFT.Thermal.Supplement


