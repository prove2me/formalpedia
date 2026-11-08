-- Prove2me | Definitions.Def_ValiantModel_HasUniformSuccess
-- name    : ValiantModel_HasUniformSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:58.055197+00:00
-- url     : https://prove2.me/theorems/63b5e4df-d808-4bdc-830e-6c1814f45026
-- title:
--   Definition 12, p.19 — uniform success over all potential targets
-- statement:
--   A learner $L$ has **uniform success over all potential targets** with sample/query complexity $m_{\mathrm{unif}}(d,\varepsilon,\delta)$ if the following holds. For all $d$, $\varepsilon,\delta\in(0,1)$, every target $h^\star\in H_d$ and every distribution $D$ compatible with $h^\star$, run $L$ on input $(d,\varepsilon,\delta)$ with the oracles for $D$ and $h^\star$; let $\hat h$ be the output, $S$ the realized set of samples, and $q,r$ the realized transcript. With probability at least $1-\delta$, for every
--
--   $$
--   h\in V(S)\cap V(q,r)\quad\text{with}\quad\mathrm{supp}(h)\neq\emptyset,
--   $$
--
--   the hypothesis $\hat h$ satisfies the conclusions of Definition 1 with target $h$ and distribution $D_h$. Here $D_h$ is $D$ conditioned on $\mathrm{supp}(h)$, and when $D(\mathrm{supp}(h))=0$ it can be any fixed distribution supported on $\mathrm{supp}(h)$.
--
--   The "for every $h$" is inside the probability: one realization serves all hypotheses that remain consistent with it.
--
--   **Formalization Note** "Any fixed distribution" is read as a universal: the guarantee holds for every family $(\nu_h)$ with $\nu_h$ compatible with $h$ whenever $\mathrm{supp}(h)\neq\emptyset$, fixed before the run, and the learner does not depend on the family. This is the stronger of the possible readings. The budget is counted per oracle and $d\ge 1$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.19 (PDF p.21), Definition 12

import Mathlib
import Definitions.Def_ValiantModel_Learnable
import Definitions.Def_ValiantModel_VersionSpaces

namespace ValiantModel

/-- The distribution `D_h` of Definition 12, arXiv:2605.13840 (version held), p.19 (PDF p.21): `D`
conditioned on `supp(h)` when `D(supp(h)) > 0` (that is, when some point of `supp(h)` has positive
mass), and the given fixed distribution `νh` otherwise. -/
noncomputable def conditioned {d : ℕ} (D : PMF (Point d)) (h : Hypothesis d) (νh : PMF (Point d)) :
    PMF (Point d) :=
  open Classical in if hne : ∃ x ∈ supp h, x ∈ D.support then D.filter (supp h) hne else νh

/-- The uniform guarantee of Definition 12, ibid., for one input `(d, ε, δ)`: for every target
`h⋆ ∈ Hd` and `D` compatible with it, with probability at least `1 - δ`, every `h ∈ V(S) ∩ V(q, r)`
with `supp(h) ≠ ∅`, where `S`, `q, r` are the realized sample and transcript, has the output meeting
the conclusions of Definition 1 with target `h` and distribution `D_h`.

**Formalization Note.** "`D_h` can be any fixed distribution supported on `supp(h)`" is read as a
universal: the guarantee holds for every family `ν` with `ν h` compatible with `h` whenever
`supp(h) ≠ ∅`; the family is fixed before the run, and the learner does not depend on it. The "for
every `h`" is inside the probability. -/
def UniformGuarantee {d : ℕ} (Hd : Set (Hypothesis d)) (P : PMF (Protocol d)) (ε δ : ℝ) : Prop :=
  ∀ hstar ∈ Hd, ∀ D : PMF (Point d), Compatible D hstar →
    ∀ ν : Hypothesis d → PMF (Point d), (∀ h, (supp h).Nonempty → Compatible (ν h) h) →
      ENNReal.ofReal (1 - δ) ≤
        (runLaw P hstar D).toOuterMeasure
          {o | ∀ h ∈ positiveVS Hd o.examples.toFinset ∩ transcriptVS Hd o.transcript,
            (supp h).Nonempty → MeetsValiant h (conditioned D h (ν h)) ε o.output}

/-- **Definition 12 (Uniform Success Over All Potential Targets)**, arXiv:2605.13840 (version
held), p.19 (PDF p.21): `L` has uniform success with sample/query complexity `munif`. -/
def HasUniformSuccess (H : ConceptSequence) (L : Learner) (munif : ℕ → ℝ → ℝ → ℕ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    WithinBudget (L d ε δ) (munif d ε δ) ∧ UniformGuarantee (H d) (L d ε δ) ε δ

end ValiantModel


