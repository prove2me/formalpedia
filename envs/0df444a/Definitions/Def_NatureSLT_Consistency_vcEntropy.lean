-- Prove2me | Definitions.Def_NatureSLT_Consistency_vcEntropy
-- name    : NatureSLT_Consistency_vcEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:10.797227+00:00
-- url     : https://prove2.me/theorems/921ab41a-ce5e-451e-ac12-553370f815e2
-- title:
--   VC entropy $H^\Lambda(\varepsilon;\ell)$ of a set of bounded real functions
-- statement:
--   Let $A \le Q(z,\alpha) \le B$, $\alpha\in\Lambda$, be a set of bounded real functions on $Z$ and $z_1,\dots,z_\ell$ a sample. The vectors
--
--   $$q(\alpha) = \bigl(Q(z_1,\alpha),\dots,Q(z_\ell,\alpha)\bigr), \qquad \alpha\in\Lambda, \tag{2.9}$$
--
--   lie in the cube $[A,B]^\ell$. A set $q(\alpha_1),\dots,q(\alpha_N)$ is an $\varepsilon$-net of them in the metric $C$ if for every $\alpha^*\in\Lambda$ some $r$ satisfies
--   $\rho_C(q(\alpha^*),q(\alpha_r)) = \max_{1\le i\le \ell}|Q(z_i,\alpha^*)-Q(z_i,\alpha_r)| \le \varepsilon$. Let $N^\Lambda(\varepsilon;z_1,\dots,z_\ell)$ be the number of elements of a minimal such net. Then
--
--   $$H^\Lambda(\varepsilon;z_1,\dots,z_\ell)=\ln N^\Lambda(\varepsilon;z_1,\dots,z_\ell)$$
--
--   is the **random VC entropy** and its expectation over an i.i.d. sample from $F$,
--
--   $$H^\Lambda(\varepsilon;\ell) = E\,H^\Lambda(\varepsilon;z_1,\dots,z_\ell),$$
--
--   is the **VC entropy** of the set of functions on samples of size $\ell$. It measures the expected diversity of the set on samples and is the quantity of the entropy criterion for uniform convergence.
--
--   **Formalization Note** As in the book's footnote, the net is internal (its elements are vectors $q(\alpha_r)$ of the set) and uses the metric $C$, not $L_p$; $N^\Lambda$ is the least cardinality of a finite parameter set $\{\alpha_1,\dots,\alpha_N\}$ with that covering property. For a bounded set and $\varepsilon>0$ such a finite net exists; for an unbounded set none may, and the count is then the junk value $0$, a case no theorem uses. The logarithm is natural. The expectation is the Bochner integral under the product measure $F^\ell$; theorems using it assume the random VC entropy measurable.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 43–44, Section 2.3.3, Definition, Eq. (2.9) and footnote 3

import Mathlib

open MeasureTheory

namespace NatureSLT.Consistency

/-- `N^Λ(ε; z₁, …, z_ℓ)` (Vapnik 2000, Section 2.3.3, p. 43, with footnote 3): the number of
elements of a minimal `ε`-net of the set of vectors `q(α) = (Q(z₁, α), …, Q(z_ℓ, α))`,
`α ∈ Λ` (Eq. (2.9)), in the metric `C`. As in footnote 3 the net is internal — its elements are
vectors `q(α_r)` of the set itself — and `q(α_r)` is `ε`-close to `q(α*)` when
`ρ_C(q(α*), q(α_r)) = max_{1≤i≤ℓ} |Q(zᵢ, α*) − Q(zᵢ, α_r)| ≤ ε`. It is the least cardinality of
a finite set of parameters `{α_1, …, α_N}` such that every `q(α*)` is `ε`-close to some
`q(α_r)`. For a bounded set `A ≤ Q ≤ B` and `ε > 0` such a finite net exists; when none exists
(an unbounded set) Lean's `sInf ∅ = 0` is a junk value, and no theorem uses that case. -/
noncomputable def coveringNumber {Z Λ : Type*} (Q : Λ → Z → ℝ) (ε : ℝ) {ℓ : ℕ}
    (z : Fin ℓ → Z) : ℕ :=
  sInf {n : ℕ | ∃ S : Finset Λ, S.card = n ∧
    ∀ α : Λ, ∃ r ∈ S, ∀ i : Fin ℓ, |Q α (z i) - Q r (z i)| ≤ ε}

/-- The **random VC entropy** `H^Λ(ε; z₁, …, z_ℓ) = ln N^Λ(ε; z₁, …, z_ℓ)` (p. 44), natural
logarithm. -/
noncomputable def randomVCEntropy {Z Λ : Type*} (Q : Λ → Z → ℝ) (ε : ℝ) {ℓ : ℕ}
    (z : Fin ℓ → Z) : ℝ :=
  Real.log (coveringNumber Q ε z : ℝ)

/-- The **VC entropy** `H^Λ(ε; ℓ) = E H^Λ(ε; z₁, …, z_ℓ)` (p. 44): the expectation of the random
VC entropy under the product measure `F^ℓ` of an i.i.d. sample of size `ℓ`. It is the genuine
expectation when the random VC entropy is measurable (it is bounded for a bounded set and
`ε > 0`); theorems using it assume that measurability. -/
noncomputable def vcEntropy {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) (ε : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ z, randomVCEntropy Q ε z ∂(Measure.pi fun _ : Fin ℓ => F)

end NatureSLT.Consistency


