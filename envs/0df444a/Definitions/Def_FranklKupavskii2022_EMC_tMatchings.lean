-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_tMatchings
-- name    : FranklKupavskii2022_EMC_tMatchings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:15:17.198727+00:00
-- url     : https://prove2.me/theorems/952c4872-6ce4-47f3-b35a-2fa90a11a423
-- title:
--   Uniformly random $t$-matchings of $l$-sets and the count $\eta=|\mathcal G\cap\mathcal B|$
-- statement:
--   Fix integers $m,l,t$ with $m\ge tl$. A **$t$-matching** of $l$-sets in $[m]$ is an ordered $t$-tuple $\mathcal B=(B_1,\dots,B_t)$ of pairwise disjoint $l$-element subsets of $[m]$. The random matching $\mathcal B$ is uniform on the (nonempty) finite set of all $t$-matchings. For a family $\mathcal G\subseteq\binom{[m]}{l}$ put
--
--   $$
--   \alpha=\frac{|\mathcal G|}{\binom ml},\qquad \eta_i=\mathbf 1[B_i\in\mathcal G],\qquad \eta=\eta_1+\dots+\eta_t=|\mathcal G\cap\mathcal B| .
--   $$
--
--   Probabilities, expectations and covariances of functions of $\mathcal B$ are taken under this uniform distribution. These are the objects of the paper's concentration results (Proposition 11, Theorem 12, Proposition 13).
--
--   **Formalization Note** One module bundles `tMatchings` (the sample space), `eta`, `etaI` (the indicators), `avg` (expectation), `prob`, `cov` and `density` ($\alpha$). Expectations and probabilities are uniform averages over the finite sample space; every random variable is bounded, so no integrability conditions arise. The sample space is nonempty exactly when $tl\le m$ (for $l\ge1$), and the theorems assume this.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 3, p. 6 (random t-matching, α, η; η_i in the proof of Lemma 10)

import Mathlib

namespace FranklKupavskii2022.EMC

/-- The sample space of random `t`-matchings (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 3, p. 6):
"B is taken uniformly at random from the set of all t-tuples of pairwise disjoint ℓ-element sets"
of `[m] = {1, …, m}`.

**Formalization Note.** A `t`-matching is an *ordered* tuple `B : Fin t → Finset ℕ` of
`l`-subsets of `Finset.Icc 1 m` that are pairwise disjoint at distinct positions. When
`t * l ≤ m` the set is nonempty. The random matching is the uniform distribution on this finite
set; probabilities and expectations below are uniform averages over it. -/
def tMatchings (m l t : ℕ) : Finset (Fin t → Finset ℕ) :=
  (Fintype.piFinset (fun _ : Fin t => (Finset.Icc 1 m).powersetCard l)).filter
    (fun B => ∀ i j : Fin t, i ≠ j → Disjoint (B i) (B j))

/-- `η = |G ∩ B|` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 3, p. 6): the number of positions
`i` whose set `B_i` belongs to `G`. -/
def eta {t : ℕ} (G : Finset (Finset ℕ)) (B : Fin t → Finset ℕ) : ℕ :=
  (Finset.univ.filter (fun i => B i ∈ G)).card

/-- `η_i` (Frankl–Kupavskii, arXiv:1806.08855v3, proof of Lemma 10, p. 6): "the indicator
function of the event A_i that the i-th set in B belongs to G", as a real number. -/
def etaI {t : ℕ} (G : Finset (Finset ℕ)) (i : Fin t) (B : Fin t → Finset ℕ) : ℝ :=
  if B i ∈ G then 1 else 0

/-- Expectation `E[X]` of a real function of the random `t`-matching: the uniform average over
`tMatchings m l t`. Every such random variable is bounded on a finite space, so there is no
integrability issue. -/
noncomputable def avg (m l t : ℕ) (X : (Fin t → Finset ℕ) → ℝ) : ℝ :=
  (∑ B ∈ tMatchings m l t, X B) / (tMatchings m l t).card

/-- Probability `Pr[E]` of an event of the random `t`-matching: the proportion of `t`-matchings
in `tMatchings m l t` at which `E` holds. -/
noncomputable def prob (m l t : ℕ) (E : (Fin t → Finset ℕ) → Prop) : ℝ := by
  classical
  exact ((tMatchings m l t).filter E).card / (tMatchings m l t).card

/-- Covariance `Cov[X, Y] = E[XY] − E[X] E[Y]` under the uniform random `t`-matching. -/
noncomputable def cov (m l t : ℕ) (X Y : (Fin t → Finset ℕ) → ℝ) : ℝ :=
  avg m l t (fun B => X B * Y B) - avg m l t X * avg m l t Y

/-- The density `α := |G| / \binom{m}{l}` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 3, p. 6),
as a real number. -/
noncomputable def density (m l : ℕ) (G : Finset (Finset ℕ)) : ℝ :=
  (G.card : ℝ) / (m.choose l : ℝ)

end FranklKupavskii2022.EMC


