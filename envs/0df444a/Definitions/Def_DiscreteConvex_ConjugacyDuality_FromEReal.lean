-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_FromEReal
-- name    : DiscreteConvex_ConjugacyDuality_FromEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:09:29.595917+00:00
-- url     : https://prove2.me/theorems/a2697750-4961-44e9-9f81-289f10ea95f3
-- title:
--   Projection R-cup-plusminus-infinity to R-cup-infinity
-- statement:
--   The projection $\mathbb R \cup \{\pm\infty\} \to \mathbb R \cup \{+\infty\}$ sending $+\infty \mapsto +\infty$, real values to themselves, and $-\infty$ to the junk value $+\infty$ (never produced by a discrete Legendre-Fenchel transform of a function with nonempty effective domain). Used to view a transform's raw supremum as a function of the same type as the M-/L-convex functions it is compared against.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), supporting notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11) (supporting notion)

import Mathlib

/-!
The projection from `R ∪ {±∞}` to `R ∪ {+∞}`, used to view a discrete Legendre-Fenchel
transform (whose raw supremum lands in `EReal`) as a function of the same type as the M-convex
and L-convex functions it is compared against (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.212, Eq. (8.11)), in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The projection `EReal → WithTop ℝ` sending `⊤ ↦ ⊤`, `(r:ℝ) ↦ (r:WithTop ℝ)`, and `⊥` to the
junk value `⊤` (never produced by a discrete Legendre-Fenchel transform of a function with
nonempty effective domain, since the supremum defining it is then never taken over an empty
set). -/
def FromEReal (v : EReal) : WithTop ℝ :=
  WithBot.unbotD ⊤ v

end DiscreteConvex.ConjugacyDuality


