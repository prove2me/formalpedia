-- Prove2me | Definitions.Def_SybilClinch_TargetMech_Admissible
-- name    : SybilClinch_TargetMech_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:54.811082+00:00
-- url     : https://prove2.me/theorems/89cb2ad5-2cec-4812-939b-4694fd6edc1c
-- title:
--   Admissible abstract target-based mechanism
-- statement:
--   A target-based mechanism $(p_\star,T,D,X_\sigma)$ is **admissible** if $p_\star>0$, $X_\sigma>0$, the domain contains $(p_\star,0,0)$ and is upward closed in the price, and:
--
--   1. (feasibility) $0\le X\le T(p,X,Y)\le X_\sigma$ on $D$;
--   2. (fixed-price invariance) if $0\le\delta\le S$ then $(p,X+\delta,Y+p\delta)\in D$ and $T(p,X+\delta,Y+p\delta)=T(p,X,Y)$ (25);
--   3. (target decreases with mark-to-market gain) $pX-Y\le pX'-Y'\Rightarrow T(p,X,Y)\ge T(p,X',Y')$ (26);
--   4. (clock regularity) for fixed $(X,Y)$, $p\mapsto T(p,X,Y)$ is nondecreasing, right-continuous, locally of bounded variation, has only upward jumps, and is locally absolutely continuous away from its jumps;
--   5. (eventual supply release) if $T(p,X,Y)=X<X_\sigma$ then $(p',X,Y)\in D$ and $T(p',X,Y)>X$ for some $p'>p$ (28).
--
--   **Formalization Note** "Only upward jumps" follows from monotonicity. "Locally absolutely continuous away from the jumps" is read as absolute continuity on every compact price interval of the domain on which the clock map is continuous. Partition independence is automatic because $T$ depends only on $(p,X,Y)$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.1, Definitions 4.1–4.2, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_SybilClinch_TargetMech

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.1, Definitions 4.1–4.2 (Admissible abstract target-based mechanism), printed
pp.13–14 (PDF pp.15–16).

`p⋆ > 0`, `X_σ ∈ (0, +∞]`, and: (1) feasibility, `0 ≤ X ≤ T(p,X,Y) ≤ X_σ` on `D`;
(2) fixed-price invariance (25); (3) the target decreases with mark-to-market gain (26);
(4) clock regularity: for fixed `(X, Y)`, `p ↦ T(p,X,Y)` is nondecreasing, right-continuous,
locally of bounded variation, has only upward jumps, and is locally absolutely continuous away
from its jumps; (5) eventual supply release (28). The domain contains `(p⋆, 0, 0)` and is upward
closed in `p`.

**Formalization Note.** "Only upward jumps" follows from monotonicity and is not a separate
field. "Locally absolutely continuous away from the jumps" is read as: absolutely continuous on
every compact price interval of the domain on which the clock map is continuous. Partition
independence (item 1) is automatic because `T` takes only `(p, X, Y)`. -/
structure TargetMech.Admissible (M : TargetMech) : Prop where
  pstar_pos : 0 < M.pstar
  cap_pos : 0 < M.cap
  start_mem : (M.pstar, 0, 0) ∈ M.D
  upward_closed : ∀ p X Y p', (p, X, Y) ∈ M.D → p ≤ p' → (p', X, Y) ∈ M.D
  feasible : ∀ p X Y, (p, X, Y) ∈ M.D →
    0 ≤ M.T p X Y ∧ X ≤ M.T p X Y ∧ ((M.T p X Y : ℝ) : EReal) ≤ M.cap
  fixed_price : ∀ p X Y δ, (p, X, Y) ∈ M.D → 0 ≤ δ → δ ≤ M.T p X Y - X →
    (p, X + δ, Y + p * δ) ∈ M.D ∧ M.T p (X + δ) (Y + p * δ) = M.T p X Y
  gain_anti : ∀ p X Y X' Y', (p, X, Y) ∈ M.D → (p, X', Y') ∈ M.D →
    p * X - Y ≤ p * X' - Y' → M.T p X' Y' ≤ M.T p X Y
  clock_mono : ∀ X Y, MonotoneOn (fun r => M.T r X Y) {r | (r, X, Y) ∈ M.D}
  clock_rightCont : ∀ p X Y, (p, X, Y) ∈ M.D →
    ContinuousWithinAt (fun r => M.T r X Y) (Ici p) p
  clock_bv : ∀ X Y, LocallyBoundedVariationOn (fun r => M.T r X Y) {r | (r, X, Y) ∈ M.D}
  clock_ac : ∀ X Y a b, (a, X, Y) ∈ M.D → a ≤ b →
    ContinuousOn (fun r => M.T r X Y) (Icc a b) →
    AbsolutelyContinuousOnInterval (fun r => M.T r X Y) a b
  release : ∀ p X Y, (p, X, Y) ∈ M.D → M.T p X Y = X → (X : EReal) < M.cap →
    ∃ p', p < p' ∧ (p', X, Y) ∈ M.D ∧ X < M.T p' X Y

end SybilClinch


