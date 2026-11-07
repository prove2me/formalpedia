-- Prove2me | Definitions.Def_PFRelease_IsJDP
-- name    : PFRelease_IsJDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:10.644867+00:00
-- url     : https://prove2.me/theorems/5e2faef1-5ef6-44cf-9629-6559912cea05
-- title:
--   Filters and joint differential privacy (JDP)
-- statement:
--   A **filter** is a randomized map that returns its input up to nulling some records: $\mathcal F(s)=s^{I\to\perp}$ for a random $I\subseteq[|s|]$. A filter is **$(\varepsilon,\delta)$-jointly differentially private** (on datasets of $n$ records) if for every $s\in\mathcal X^n$ and every slot $i$
--   $$
--   \mathcal F(s)^{i\to\perp}\approx_{\varepsilon,\delta}\mathcal F(s^{i\to\perp}).
--   $$
--   The two filtered datasets are compared only after slot $i$ is nulled in both, so a JDP filter may reveal whether it retained $s_i$.
--
--   **Formalization Note** A filter on $n$ slots is given by the probability `Fil s I` that its nulled set on input $s$ is $I$. The two sides are the laws of the **datasets** $(s^{I\to\perp})^{i\to\perp}$ and $(s^{i\to\perp})^{I\to\perp}$ (`jdpLeft`, `jdpRight`), compared on every set of datasets; two index sets can give the same dataset when $s$ has null slots, so index-set laws are not compared.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Definition 3.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory

namespace PFRelease

/-- The law of the filtered dataset `F(s)^{i→⊥}`, for a filter whose nulled index set on input `s`
has probability `Fil s I` of being `I`: the image of that law under `I ↦ (s^{I→⊥})^{i→⊥}`, a law
on datasets. -/
noncomputable def jdpLeft {X : Type*} {n : ℕ}
    (Fil : (Fin n → Option X) → Finset (Fin n) → ENNReal) (s : Fin n → Option X) (i : Fin n) :
    Measure (Dataset X n) :=
  ∑ I : Finset (Fin n), Fil s I • Measure.dirac (α := Dataset X n) (nullOut (nullOut s I) {i})

/-- The law of the filtered dataset `F(s^{i→⊥})`: the image of the law of the nulled index set on
input `s^{i→⊥}` under `I ↦ (s^{i→⊥})^{I→⊥}`. -/
noncomputable def jdpRight {X : Type*} {n : ℕ}
    (Fil : (Fin n → Option X) → Finset (Fin n) → ENNReal) (s : Fin n → Option X) (i : Fin n) :
    Measure (Dataset X n) :=
  ∑ I : Finset (Fin n), Fil (nullOut s {i}) I •
    Measure.dirac (α := Dataset X n) (nullOut (nullOut s {i}) I)

/-- Joint differential privacy of a filter (Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held
version sha256 e1d516b3…, Definition 3.3, p.10 = PDF p.12). A filter returns `F(s) = s^{I→⊥}` for
a random `I ⊆ [|s|]`; it is `(ε, δ)`-JDP (on datasets of `n` records) if
`F(s)^{i→⊥} ≈_{ε,δ} F(s^{i→⊥})` for every `s ∈ Xⁿ` and every slot `i`.

**Formalization Note** A filter on `n` slots is given by `Fil s I`, the probability that its
nulled set on input `s` is `I` (a probability mass function on `Finset (Fin n)`; that it sums to
one is a hypothesis of the theorems, or proved for the concrete filter). The two sides are
compared as laws of **datasets** (`jdpLeft`, `jdpRight`) on every set of datasets (σ-algebra
`⊤` on `Dataset X n`), never as laws of index sets: two index sets give the same dataset when
`s` has null slots. -/
def IsJDP {X : Type*} {n : ℕ} (Fil : (Fin n → Option X) → Finset (Fin n) → ENNReal)
    (ε δ : ℝ) : Prop :=
  ∀ (s : Fin n → Option X) (i : Fin n), Indist (jdpLeft Fil s i) (jdpRight Fil s i) ε δ

end PFRelease


