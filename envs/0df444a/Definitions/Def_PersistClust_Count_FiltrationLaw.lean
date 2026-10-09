-- Prove2me | Definitions.Def_PersistClust_Count_FiltrationLaw
-- name    : PersistClust_Count_FiltrationLaw
-- status  : Definition
-- author  : @fabianroll
-- created : 2026-10-09T11:26:20.970485+00:00
-- url     : https://prove2.me/theorems/c837d25f-6d52-46ff-8d57-cf1e07e69d12
-- title:
--   FiltrationLaw: the structural law of a 0-dimensional persistence filtration
-- statement:
--   `FiltrationLaw stage J` records the structural axioms of the 0-dimensional persistence module of a filtration: the stage family $\{\mathrm{stage}(\beta)\}_\beta$ decreases as the threshold parameter decreases (a lower threshold holds a larger set), the relation $J_t$ is the "same path component of $\mathrm{stage}(t)$" equivalence, living on $\mathrm{stage}(t)$, and the relations are compatible with the inclusions $\mathrm{stage}(t) \subseteq \mathrm{stage}(s)$ whenever $s \le t$ (components merge as the threshold decreases). This is exactly the structure of a genuine persistence module of a filtration, and is the implicit hypothesis of Lemma 4.6 / Theorem 4.5 of RR-6968 that the rank functions under comparison are rank functions of actual filtrations (not arbitrary functions). The superlevel-set filtration $\{F^\beta\}$ and the upper-star Rips filtration $\{\mathcal R^f_\delta(L^\beta)\}$ of Theorem 4.5 both satisfy `FiltrationLaw` definitionally for their `rankFn` instances.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 8–9 (§2.2, Eq. (1)) and pp. 20–21, Lemma 4.6 / Appendix A (persistence modules of filtrations)

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

namespace PersistClust.Count

/-! ### The structure law of a 0-dimensional persistence module (a filtration by path components)

`rankFn stage J s t` (see `Def_PersistClust_Count_Diagram`) is intended to count the components of
`stage t` that meet `stage s`, for the filtration of a persistence module: the time parameter runs
from `+∞` down to `-∞`, `stage` is a decreasing family of sets, and `J t` is the equivalence relation
"same path component of `stage t`", refined as the threshold decreases. Both rank functions of
Theorem 4.5 — `superRank f = rankFn (superlevel f) (fun t => JoinedIn (superlevel f t))` and
`ripsRank Dm g δ = rankFn (fun t => {i | t ≤ g i}) (ripsJoined Dm g δ)` — are of this shape.

`FiltrationLaw stage J` records exactly the axioms of such a family that enter Lemma 4.6
(Appendix A): the monotonicity of `stage`, the fact that `J t` is an equivalence relation living on
`stage t`, and the compatibility of `J` with the inclusions `stage t ⊆ stage s` for `s ≤ t`. It is the
Lean counterpart of the paper's assumption that the two modules under comparison are genuine
(persistence modules of) filtrations. -/

/-- The structural law of a 0-dimensional persistence filtration: `stage` decreases with the time
parameter and `J t` is the "same component of `stage t`" equivalence, compatible with the inclusion
`stage t ⊆ stage s` whenever `s ≤ t`. -/
structure FiltrationLaw {α : Type*} (stage : ℝ → Set α) (J : ℝ → α → α → Prop) : Prop where
  /-- The stages decrease: a lower threshold holds a larger set. -/
  antitone : ∀ ⦃s t : ℝ⦄, s ≤ t → stage t ⊆ stage s
  /-- `J t` only relates points of `stage t`. -/
  mem : ∀ ⦃t : ℝ⦄ ⦃x y : α⦄, J t x y → x ∈ stage t ∧ y ∈ stage t
  /-- Reflexivity on `stage t`. -/
  refl : ∀ ⦃t : ℝ⦄ ⦃x : α⦄, x ∈ stage t → J t x x
  /-- Symmetry. -/
  symm : ∀ ⦃t : ℝ⦄ ⦃x y : α⦄, J t x y → J t y x
  /-- Transitivity. -/
  trans : ∀ ⦃t : ℝ⦄ ⦃x y z : α⦄, J t x y → J t y z → J t x z
  /-- Components merge as the threshold decreases: `s ≤ t` and `J t x y` force `J s x y`. -/
  compat : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ ⦃x y : α⦄, J t x y → J s x y

end PersistClust.Count


