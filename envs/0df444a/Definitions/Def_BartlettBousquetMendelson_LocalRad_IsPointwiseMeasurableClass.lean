-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
-- name    : BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:58:35.169934+00:00
-- url     : https://prove2.me/theorems/592dc916-b114-4ca4-8f45-3addd947087d
-- title:
--   Pointwise measurable class of functions
-- statement:
--   A class $\mathcal F$ of real functions on $\mathcal X$ is **pointwise measurable** if there is a countable subclass $\mathcal F_0\subseteq\mathcal F$ such that every $f\in\mathcal F$ is the pointwise limit of a sequence $(u_k)$ of elements of $\mathcal F_0$:
--
--   $$
--   u_k(y)\to f(y)\quad\text{for every } y\in\mathcal X.
--   $$
--
--   The paper assumes throughout (p. 7) that suprema such as $\sup_{f\in\mathcal F}(Pf-P_nf)$ are measurable, under "appropriate (mild) conditions" on $\mathcal F$ and $P$. Pointwise measurability (van der Vaart–Wellner, §2.3.3) is the standard such condition: with measurable members, every supremum over $\mathcal F$ of the sample-dependent quantities becomes a supremum over the countable $\mathcal F_0$.
--
--   **Formalization Note** This is the mission's reading of the paper's open convention (Reading M).
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §2, p. 7 (measurability convention) (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib

open Filter Topology

namespace BartlettBousquetMendelson.LocalRad

/-- **Pointwise measurable class** (the mission's reading of the measurability convention).
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §2, p. 7: "Throughout this paper, we will manipulate suprema of empirical processes, that is,
quantities of the form sup_{f∈F}(Pf − Pnf). We will always assume they are measurable without
explicitly mentioning it. In other words, we assume that the class F and the distribution P satisfy
appropriate (mild) conditions for measurability of this supremum (we refer to [11, 28] for a
detailed account of such issues)."

`IsPointwiseMeasurableClass F` says: some countable subclass `F₀ ⊆ F` has every `f ∈ F` as a
pointwise limit of a sequence of elements of `F₀`.

**Formalization Note.** This is the standard "pointwise measurable class" condition (van der
Vaart–Wellner, *Weak Convergence and Empirical Processes*, §2.3.3). Together with measurability of
each `f ∈ F` it makes suprema over `F` of the sample-dependent quantities of the mission equal to
suprema over the countable `F₀`, hence measurable. The paper leaves the convention open
("appropriate (mild) conditions"); this is the mission's reading of it (Reading M). -/
def IsPointwiseMeasurableClass {X : Type*} (F : Set (X → ℝ)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ u : ℕ → X → ℝ, (∀ k, u k ∈ F₀) ∧
    ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y))

end BartlettBousquetMendelson.LocalRad


