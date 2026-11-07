-- Prove2me | Definitions.Def_ReplParity_prIID
-- name    : ReplParity_prIID
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:48.859198+00:00
-- url     : https://prove2.me/theorems/936515d1-1578-4ccf-aad7-e56b39e0ed7f
-- title:
--   Probabilities over i.i.d. samples and a uniform shared seed
-- statement:
--   All probability spaces in the mission are finite. For a distribution $D$ on a finite set and a sample $S=(S_1,\dots,S_m)$, the probability of $S$ under $D^m$ is $\prod_i D(S_i)$. For an event $E$ of a sample $S\sim D^m$ and a seed $r$ uniform on a finite set $\Omega$, independent of $S$,
--   $$\Pr_{S\sim D^m,\,r}[E(S,r)]=\sum_{S}\sum_{r\in\Omega}\frac{\prod_i D(S_i)}{|\Omega|}\,\mathbf 1[E(S,r)] .$$
--   The two-run version draws independent samples $S,S'\sim D^m$ and one seed $r$ shared by both runs:
--   $$\Pr_{S,S'\sim D^m,\,r}[E(S,S',r)]=\sum_{S,S'}\sum_{r}\frac{\prod_i D(S_i)\prod_i D(S'_i)}{|\Omega|}\,\mathbf 1[E(S,S',r)],$$
--   and $\mathbb E_{S,S'}[f(S,S')]$ is the corresponding weighted sum without a seed. A seedless version $\Pr_{S\sim D^m}[E(S)]$ is also provided.
--
--   These are the probabilities of Definitions 2.1 and 2.2 and of every lemma of §3.
--
--   **Formalization Note** $D$ is an arbitrary probability mass function with real weights; no rationality or full-support assumption is made.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.10 (PDF p.12), Definitions 2.1–2.2

import Mathlib

namespace ReplParity

/-- **Probabilities over i.i.d. samples and a uniform seed, as finite sums.** Shen, Zhong,
*Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027
submission (manuscript sha256 40424491…), §2.1, p.10 (PDF p.12): "A learner A receives a sample
S ∼ D^m of a size m fixed in advance, together with a random seed r independent of S".

`sampleWeight D S = ∏ᵢ D(Sᵢ)` is the probability of the sample `S` under `D^m`.

**Formalization Note.** All sample spaces are finite, so every probability is a finite sum of
real weights; `D` is an arbitrary `PMF` (real weights, any support). -/
noncomputable def sampleWeight {α : Type*} {m : ℕ} (D : PMF α) (S : Fin m → α) : ℝ :=
  ∏ i, (D (S i)).toReal

open Classical in
/-- `probIID D m E = Pr_{S ∼ D^m}[E S]`. -/
noncomputable def probIID {α : Type*} [Fintype α] (D : PMF α) (m : ℕ)
    (E : (Fin m → α) → Prop) : ℝ :=
  ∑ S : Fin m → α, if E S then sampleWeight D S else 0

open Classical in
/-- `prIID D m E = Pr_{S ∼ D^m, r}[E S r]`, where the seed `r` is uniform on the finite type `Ω`
and independent of `S`. -/
noncomputable def prIID {α Ω : Type*} [Fintype α] [Fintype Ω] (D : PMF α) (m : ℕ)
    (E : (Fin m → α) → Ω → Prop) : ℝ :=
  ∑ S : Fin m → α, ∑ r : Ω, if E S r then sampleWeight D S / Fintype.card Ω else 0

open Classical in
/-- `prIID2 D m E = Pr_{S, S′ ∼ D^m, r}[E S S′ r]`: `S` and `S′` are independent samples, and one
uniform seed `r` on `Ω`, independent of both, is shared by the two runs (Definition 2.1, p.10). -/
noncomputable def prIID2 {α Ω : Type*} [Fintype α] [Fintype Ω] (D : PMF α) (m : ℕ)
    (E : (Fin m → α) → (Fin m → α) → Ω → Prop) : ℝ :=
  ∑ S : Fin m → α, ∑ S' : Fin m → α, ∑ r : Ω,
    if E S S' r then sampleWeight D S * sampleWeight D S' / Fintype.card Ω else 0

/-- `expIID2 D m f = E_{S, S′ ∼ D^m}[f S S′]` for independent samples `S`, `S′`. -/
noncomputable def expIID2 {α : Type*} [Fintype α] (D : PMF α) (m : ℕ)
    (f : (Fin m → α) → (Fin m → α) → ℝ) : ℝ :=
  ∑ S : Fin m → α, ∑ S' : Fin m → α, sampleWeight D S * sampleWeight D S' * f S S'

end ReplParity


