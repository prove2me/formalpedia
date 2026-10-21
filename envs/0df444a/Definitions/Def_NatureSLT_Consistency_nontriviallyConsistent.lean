-- Prove2me | Definitions.Def_NatureSLT_Consistency_nontriviallyConsistent
-- name    : NatureSLT_Consistency_nontriviallyConsistent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:46.608256+00:00
-- url     : https://prove2.me/theorems/c48526c1-f376-4776-9010-3496157f067a
-- title:
--   Nontrivial consistency of the ERM method, Eq. (2.3)
-- statement:
--   Let $F$ be a probability measure on $Z$, let $Q(z,\alpha)$, $\alpha\in\Lambda$, be a set of real functions with risk $R(\alpha)=\int Q(z,\alpha)\,dF(z)$ and empirical risk $R_{\mathrm{emp}}(\alpha)=\frac1\ell\sum_{i=1}^\ell Q(z_i,\alpha)$ on an i.i.d. sample $z_1,\dots,z_\ell$ drawn from $F$. For $c\in\mathbb R$ let
--
--   $$\Lambda(c) = \Bigl\{\alpha \in \Lambda : \int Q(z,\alpha)\,dF(z) > c\Bigr\}.$$
--
--   The ERM method is **nontrivially consistent** for the set $Q(z,\alpha)$, $\alpha\in\Lambda$, and the distribution $F$ if for every $c$ for which $\Lambda(c)$ is nonempty,
--
--   $$\inf_{\alpha\in\Lambda(c)} R_{\mathrm{emp}}(\alpha) \xrightarrow[\ell\to\infty]{P} \inf_{\alpha\in\Lambda(c)} R(\alpha), \tag{2.3}$$
--
--   that is, for every $\varepsilon>0$ the probability, under the product measure $F^\ell$ of the sample, that $\bigl|\inf_{\Lambda(c)} R_{\mathrm{emp}} - \inf_{\Lambda(c)} R\bigr| > \varepsilon$ tends to $0$ as $\ell\to\infty$.
--
--   Removing the functions with the smallest risks excludes the trivial consistency produced by a single minorizing function in the set; the book calls this notion simply "consistency" from Section 2.1 on.
--
--   **Formalization Note** The infimum of the empirical risks over $\Lambda(c)$ is taken in the extended reals, so it is the genuine infimum (possibly $-\infty$) even though only the risks, not the functions, are assumed bounded. The infimum of the risks over a nonempty $\Lambda(c)$ is a real number bounded below by $c$. The event $|\inf R_{\mathrm{emp}} - \inf R|>\varepsilon$ is written as $\inf R_{\mathrm{emp}} < \inf R - \varepsilon$ or $\inf R + \varepsilon < \inf R_{\mathrm{emp}}$, with no extended-real subtraction. Probabilities are values of $F^\ell$ in $[0,\infty]$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 38, Section 2.1, Definition, Eq. (2.3)

import Mathlib
import Definitions.Def_NatureSLT_Consistency_risk

open MeasureTheory Filter Topology

namespace NatureSLT.Consistency

/-- The subset `Λ(c) = {α : ∫ Q(z, α) dF(z) > c, α ∈ Λ}` of the parameter set
(Vapnik 2000, Section 2.1, p. 38): the functions whose risk exceeds `c`. -/
def levelSet {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) (Q : Λ → Z → ℝ) (c : ℝ) :
    Set Λ :=
  {α | c < risk F Q α}

/-- `inf_{α ∈ S} R_emp(α)` on the sample `z`, taken in the extended reals `EReal`, so that it is
the genuine infimum (possibly `−∞`) even when the empirical risks over `S` are unbounded below;
it is `⊤` only for `S = ∅`. -/
noncomputable def infEmpiricalRisk {Z Λ : Type*} (Q : Λ → Z → ℝ) (S : Set Λ) {ℓ : ℕ}
    (z : Fin ℓ → Z) : EReal :=
  ⨅ α ∈ S, ((empiricalRisk Q z α : ℝ) : EReal)

/-- `inf_{α ∈ Λ(c)} R(α)`, a real number. On a nonempty `Λ(c)` it is the genuine infimum: the
risks over `Λ(c)` are bounded below by `c`. (On `Λ(c) = ∅` it is Lean's junk value `0`; it is
only used for nonempty `Λ(c)`.) -/
noncomputable def infRiskLevel {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) (c : ℝ) : ℝ :=
  ⨅ α : levelSet F Q c, risk F Q α

/-- **Nontrivial consistency** of the ERM method (Vapnik 2000, Section 2.1, Definition, p. 38,
Eq. (2.3)): for every `c ∈ ℝ` with `Λ(c)` nonempty, `inf_{α ∈ Λ(c)} R_emp(α)` converges in
probability to `inf_{α ∈ Λ(c)} R(α)` as `ℓ → ∞`, i.e. for every `ε > 0` the probability, under
the product measure `F^ℓ` of an i.i.d. sample of size `ℓ`, that the two infima differ by more
than `ε` tends to `0`. The event `|inf R_emp − inf R| > ε` is written as
`inf R_emp < inf R − ε ∨ inf R + ε < inf R_emp` in `EReal`. -/
def NontriviallyConsistent {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) : Prop :=
  ∀ c : ℝ, (levelSet F Q c).Nonempty → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun ℓ : ℕ => Measure.pi (fun _ : Fin ℓ => F)
      {z : Fin ℓ → Z | infEmpiricalRisk Q (levelSet F Q c) z
            < ((infRiskLevel F Q c - ε : ℝ) : EReal) ∨
          ((infRiskLevel F Q c + ε : ℝ) : EReal) < infEmpiricalRisk Q (levelSet F Q c) z})
      atTop (𝓝 0)

end NatureSLT.Consistency


