-- Prove2me | Definitions.Def_StretchDepth_crit
-- name    : StretchDepth_crit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:35.144752+00:00
-- url     : https://prove2.me/theorems/744adc02-d0ab-4778-80f4-55e9c56e7248
-- title:
--   Critical queries, $Y^\rho_{x,t}$, $\ell$ and $\alpha$
-- statement:
--   Fix a partial assignment $\rho$ and $G\supseteq\rho$. A query made to $G$ on an input in the free set of $\rho$ is **critical**. For a run, $t^G_j(\rho)$ is the number of critical queries in the first $j$ rounds and $t^G(\rho)$ the number in the whole run, counted with multiplicity. For an input $x$,
--   $$
--   Y^\rho_{x,t}=\{H^G(x) : G\supseteq\rho,\ t^G_x(\rho)=t\}.
--   $$
--   The parameters of the proof of Lemma 1 are
--   $$
--   \ell=n-\log_2(qs),\qquad \alpha=\frac{N-\ell}{(N/\ell)^d-1}.
--   $$
--   These quantities organize the proof of Lemma 1, which trades critical queries against the entropy of earlier critical answers.
--
--   **Formalization Note** The count with zero rounds is $0$, and past the last round it stabilizes at the total.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Lemma 1, p.16

import Definitions.Def_StretchDepth_PartialAssign

namespace StretchDepth

variable {n N M : ℕ}

/-- **Critical queries in the first `j` rounds.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Lemma 1, p.16: "let tG x (ρ) be the number of queries made to G on inputs
in free(ρ) during the execution HG(x); we call such queries “critical queries.” For each j ≤ d let
tG x,j(ρ) be the number of critical queries made during the first j adaptivity phases".

**Formalization Note.** Counted with multiplicity. `crit ρ G t 0 = 0`, and past the last round the
count stabilizes at `critTotal`. -/
def crit (ρ : PartialAssign n N) (G : Bits n → Bits N) (t : RoundTree n N M) (j : ℕ) : ℕ :=
  (((queriesOf G t).take j).flatten.filter fun w => ρ w = none).length

/-- `t^G_x(ρ)`, the number of critical queries in the whole execution (p.16). -/
def critTotal (ρ : PartialAssign n N) (G : Bits n → Bits N) (t : RoundTree n N M) : ℕ :=
  ((queriesOf G t).flatten.filter fun w => ρ w = none).length

open Classical in
/-- `Y^ρ_{x,t} = {H^G(x) | G ⊇ ρ, t^G_x(ρ) = t}` (p.16), for the tree `t` of the input `x`. -/
noncomputable def Y (ρ : PartialAssign n N) (t : RoundTree n N M) (k : ℕ) : Finset (Bits M) :=
  Finset.univ.filter fun y =>
    ∃ G : Bits n → Bits N, Extends G ρ ∧ critTotal ρ G t = k ∧ run G t = y

/-- `ℓ = n − log qs` (p.16), with `log = log₂`. -/
noncomputable def ell (n q : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ) - Real.logb 2 ((q : ℝ) * s)

/-- `α = (N − ℓ) / ((N/ℓ)^d − 1)` (p.16). -/
noncomputable def alpha (N : ℕ) (ℓ : ℝ) (d : ℕ) : ℝ :=
  ((N : ℝ) - ℓ) / (((N : ℝ) / ℓ) ^ d - 1)

end StretchDepth


