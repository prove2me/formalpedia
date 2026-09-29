-- Prove2me | Definitions.Def_WeierstrassCurve_Semistability
-- name    : WeierstrassCurve_Semistability
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/c560e26f-f53d-50b6-95d1-523bc81253e0
-- title:
--   Valuation-theoretic semistability for Weierstrass models over Q
-- statement:
--   Two predicates on Weierstrass curves over $\mathbb{Q}$ are introduced, together with one integer invariant of a Frey package.
--
--   For a Weierstrass curve $W$ over $\mathbb{Q}$ (given by its coefficients $a_1,\dots,a_6$, hence a chosen model rather than an isomorphism class) and a natural number $q$, [`WeierstrassCurve.IsSemistableAt W q`](../def/WeierstrassCurve_Semistability.html#L13) is the disjunction
--   $$v_q(\Delta_W) = 0 \quad\text{or}\quad v_q(c_4(W)) = 0,$$
--   where $\Delta_W$ and $c_4(W)$ are the discriminant and the $c_4$-invariant of the model and $v_q$ is the $q$-adic valuation on $\mathbb{Q}$, as given by `padicValRat`. Thus the condition says that the model has either $q$-adically unit discriminant or $q$-adically unit $c_4$; in the classical reading, the first disjunct records good reduction at $q$ for this model and the second excludes additive reduction when $v_q(\Delta_W)>0$. The predicate is stated for an arbitrary natural number $q$; primality is imposed only where it is quantified. [`WeierstrassCurve.IsSemistable W`](../def/WeierstrassCurve_Semistability.html#L16) is the assertion that `IsSemistableAt W q` holds for every prime $q$.
--
--   For a Frey package $P$ — nonzero coprime integers $a,b,c$ with $a^p+b^p=c^p$ for a prime $p\ge 5$, normalised by $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$ — [`FreyCurve.c₄Int P`](../def/WeierstrassCurve_Semistability.html#L10) is the integer
--   $$(a^p)^2 + a^p b^p + (b^p)^2,$$
--   which is the value of the $c_4$-invariant of the associated Frey model [`FreyPackage.freyCurve P`](../def/FLTPrelim_FreyPackage.html#L90), whose coefficients are $a_1 = 1$, $a_2 = (b^p-1-a^p)/4$, $a_3 = 0$, $a_4 = -a^pb^p/16$, $a_6 = 0$.
--
--   **Relation to Mathlib.** The discriminant `Δ` and the invariant `c₄` of a Weierstrass curve, and the $q$-adic valuation `padicValRat`, are Mathlib's; the two semistability predicates are declared in Mathlib's `WeierstrassCurve` namespace but are this project's own, phrased as conditions on the valuations of the invariants of a fixed model rather than intrinsically in terms of reduction type.
--
--   **Where it is used.** Semistability of the Frey curve attached to a putative Fermat solution is the hypothesis under which the modularity theorem of Wiles and Taylor–Wiles is applied, and the primes at which semistability fails (equivalently, the shape of the valuations of $\Delta$ and $c_4$) govern the conductor computation feeding Ribet's level-lowering. The integer [`FreyCurve.c₄Int`](../def/WeierstrassCurve_Semistability.html#L10) is the quantity whose $q$-adic valuations are compared with those of the discriminant in establishing semistability of the Frey model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_Semistability.lean

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FreyCurve

open FreyPackage

def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

def _root_.WeierstrassCurve.IsSemistableAt (W : WeierstrassCurve ℚ) (q : ℕ) : Prop :=
  padicValRat q W.Δ = 0 ∨ padicValRat q W.c₄ = 0

def _root_.WeierstrassCurve.IsSemistable (W : WeierstrassCurve ℚ) : Prop :=
  ∀ q : ℕ, q.Prime → W.IsSemistableAt q

end FreyCurve


