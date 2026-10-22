-- Prove2me | Definitions.Def_ChapterFockCubicUnbounded
-- name    : ChapterFockCubicUnbounded
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T11:23:50.018283+00:00
-- url     : https://prove2.me/theorems/daa2a767-14e3-4109-a577-e3b3eb1cdefd
-- title:
--   ChapterFockCubicUnbounded
-- statement:
--   ChapterFockCubicUnbounded

import Definitions.Def_ChapterFockPairPerturbation
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Mathlib


/-!
# Chapter FockCubicUnbounded — the quadratic degree is the boundary

`ChapterFockFieldPerturbation` proves that a gap survives a *linear* field coupling
`Φ(f) = a†(f) + a(f)`, and `ChapterFockPairPerturbation` that it survives a *quadratic*,
pair-creating coupling `P(f,g) = a†(f)a†(g) + a(g)a(f)`.  Both proceed by dominating the
perturbing form by the free form `Re⟪u, dΓ(h)u⟫`.  Every status update of
`CONSOLIDATED_PLAN.md` then records the same honest boundary: the *cubic and quartic*
Yang–Mills interaction terms are not covered.

This chapter shows that this is not a gap in the write-up but a fact about the route: the
domination that the linear and quadratic couplings admit **fails outright** at degree three.

## Deliverables

* `cubeA k` — the single-mode cubic field term `C_k = (a_k†)³ + (a_k)³`, self-adjoint,
  unbounded, and changing the particle number by three;
* `trial_numberQuad`, `trial_norm_sq`, `trial_cubic_form` — the exact values of the three
  relevant quantities on the two-term trial states `|n⟩ + c|n+3⟩`: the number form
  `n + (n+3)c²`, the squared norm `1 + c²`, and the cubic form `2c√((n+1)(n+2)(n+3))`;
* **`cubic_no_relative_form_bound`** — for *every* pair of constants `a, b` there is a
  vacuum-orthogonal finite-particle state with
  `a·⟪u, N u⟫ + b‖u‖² < Re⟪u, C_k u⟫`.  So the cubic term admits **no** relative form bound
  of the shape `|v| ≤ a q + b‖·‖²` against the number form — the hypothesis of
  `FockInteractionStability.gap_persists_of_relative_form_bound` can never be met by it,
  however small the coupling constant is made;
* **`fock_gap_fails_for_cubic`** — the consequence for the gap: for the free Fock
  Hamiltonian `dΓ(N)` (one-particle gap `1`) and *any* coupling strength `lam > 0`, the
  perturbed form `dΓ(N) + lam·C_k` is **unbounded below** on the vacuum-orthogonal sector:
  for every `M` there is a vacuum-orthogonal state with
  `Re⟪u, dΓ(N)u⟫ + lam·Re⟪u, C_k u⟫ ≤ -M‖u‖²`.

Together with `ChapterFockPairPerturbation`, this locates the boundary exactly: degree two
survives (with a smallness condition), degree three does not survive at all.

A final section makes the complementary point precise.  `quartA k = (a_k†)²(a_k)²` is the
normal-ordered quartic term, diagonal with eigenvalue `m(m − 1)` (`quartA_single_confAt`,
`trial_quartic_form`), and **`trial_cubic_quartic_bounded_below`** shows that on the very
family of states that drives `dΓ(N) + lam·C_k` to `-∞`, the sum
`dΓ(N) + lam·C_k + Q_k` is bounded below by `-(lam⁴/4 + 2lam²)‖u‖²`, uniformly in the
occupation number and in the mixing coefficient.  The divergence above is therefore a
property of a *bare* cubic term.

## Honest boundary

`C_k` is a single-mode cubic term, not the full Yang–Mills cubic vertex; what is proved is
that *this* form-domination route cannot reach degree three, not that no gap exists for the
physical theory — a physical cubic term is accompanied by a quartic term which is bounded
below, and controlling their sum in general is a different problem, of which only the
statement along the above trial family is proved here.  `1.932` remains a certified
truncated number; no mass gap of the physical Hamiltonian is claimed.

Everything is `sorry`-free and introduces no axioms.
-/

noncomputable section

namespace BookProof.FockCubicUnbounded

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

/-! ## 1. Single-mode configurations -/

/-- The occupation-`m` configuration of the mode `k`. -/
def confAt (k m : ℕ) : Conf := Finsupp.single k m


/-! ## 2. The cubic field term -/

/-- **The single-mode cubic field term** `C_k = (a_k†)³ + (a_k)³`: it is unbounded and
changes the particle number by three. -/
def cubeA (k : ℕ) : FockAlg →ₗ[ℂ] FockAlg :=
  (creA k).comp ((creA k).comp (creA k)) + (annA k).comp ((annA k).comp (annA k))


/-! ## 3. The two-term trial states -/

/-- The trial state `|n⟩ + c|n+3⟩` of the mode `k`. -/
def trial (k n : ℕ) (c : ℝ) : FockAlg :=
  Finsupp.single (confAt k n) 1 + Finsupp.single (confAt k (n + 3)) ((c : ℝ) : ℂ)


/-! ## 4. The three quantities on a trial state -/


/-! ## 5. No relative form bound at degree three -/


/-! ## 6. The quartic term restores a lower bound on the same witnesses -/

/-- **The single-mode quartic (normal-ordered) term** `Q_k = (a_k†)²(a_k)²`, which acts
diagonally with eigenvalue `m(m − 1)` on the occupation-`m` state of the mode `k`. -/
def quartA (k : ℕ) : FockAlg →ₗ[ℂ] FockAlg :=
  (creA k).comp ((creA k).comp ((annA k).comp (annA k)))


/-! ## 7. Axiom audit -/

section Audit


end Audit

end BookProof.FockCubicUnbounded

end


