-- Prove2me | Definitions.Def_QFS_BeyondThePaper
-- name    : QFS_BeyondThePaper
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-06T00:02:00.995512+00:00
-- url     : https://prove2.me/theorems/1a815346-a857-4d69-923a-3f12d0bd973f
-- title:
--   Chaining balls, planar averaging geometry, and domination radii
-- statement:
--   This module is explicitly labelled inside the file as lying outside the source being certified: it collects the geometric data for a *chaining* argument in which the oscillation of a function across a pair $(s,t)$ is recovered by averaging over a positive-measure set of intermediate points that both endpoints can see. Throughout, $E$ is a real inner product space, $\vartheta$ an aperture, $\alpha$ the fractional order, $d$ the dimension, and $\Gamma$ a configuration assigning to each $x$ a double cone $\Gamma(x)$; $V(v,\theta)$ denotes the double cone with unit axis $v$ and apex angle $\theta$.
--
--   **The averaging centre and its constants.** For a unit axis $v$ and points $s \ne t$,
--
--   $$\mathrm{midCentre}(v,\vartheta,s,t) \;=\; s + \frac{3\,\|s-t\|}{\sin \vartheta}\, v,$$
--
--   the point reached by walking from $s$ along $v$ far enough that the cone $V(v,\vartheta)$ based at $s$ has opened wider than $\|s-t\|$; the chaining averages over a ball about it. Two constants govern the fibre estimate that lets the average be exchanged with the outer integration, one for each endpoint:
--
--   $$C(d,\vartheta,\alpha) = \frac{\big(1 + 3/\sin\vartheta\big)^{2d+\alpha}}{\big(3/\sin\vartheta - 1\big)^{d}}, \qquad C'(d,\vartheta,\alpha) = \frac{\big(2 + 3/\sin\vartheta\big)^{2d+\alpha}}{\big(3/\sin\vartheta - 2\big)^{d}},$$
--
--   the second differing only by the one extra unit the displacement from $s$ to $t$ costs.
--
--   **Planar toolkit ($d = 2$).** Here the intermediate points are found at the intersection of the two axis lines. The module fixes the quarter-turn $w \mapsto (-w_1, w_0)$, the scalar cross product $x \times y = x_0 y_1 - x_1 y_0$, the two coefficients
--
--   $$a = \frac{(t-s)\times v_t}{v_s \times v_t}, \qquad b = \frac{(t-s)\times v_s}{v_s \times v_t},$$
--
--   placing the intersection point on the axis through $s$ and on the axis through $t$ respectively, and the centre $s + a\,v_s$. The **planar averaging ball** attached to axes $v_s, v_t$, aperture $\vartheta$ and a pair $(s,t)$ is the closed ball about that centre of radius $\|t-s\|\sin^2\vartheta / 2$, intersected with the side conditions $s \neq t$, $t - s \notin V(v_s,\vartheta)$ and $t - s \notin V(v_t,\vartheta)$; when a side condition fails the set is empty, so pairs already joined by a cone, and the diagonal, are simply not served. The corresponding constant is $\big(1/|v_s \times v_t| + 1\big)^{4+\alpha}\cdot 4/\sin^2\vartheta$, which blows up as the two axes become parallel.
--
--   **Domination.** For a finite set $S$ of reference axes, a finite set $\Theta$ of apertures, a fraction $c_0 > 0$ and a radius function $\rho$, the configuration is **locally dominated out to $\rho$** when for almost every $s$ and every $t$ with $\|s-t\| \le \rho(s)$ there is a pair $(\theta, v) \in \Theta \times S$ with
--
--   $$c_0 \|s-t\|^{d} \;\le\; \lambda_d\Big(\{x : V(v,\theta) \subseteq \Gamma(x)\} \cap \bar B\big(\mathrm{midCentre}(v,\theta,s,t),\ \|s-t\|\big)\Big),$$
--
--   i.e. the points whose own cone contains the reference cone $V(v,\theta)$ fill a $c_0$-fraction of the ball the chaining averages over. The set of pairs $(s,t)$ satisfying the same inequality for *some* $(\theta,v)$ is recorded separately, as is the machinery for producing a measurable such $\rho$: for a set $U$, a scale $K$, a defect $\eta$ and $n \in \mathbb{N}$, the set of points at which $U$ fills all but an $\eta$-fraction of every ball of radius $K 2^{-m}$ with $m \ge n$; the union of those sets over the finitely many reference types; and an explicit radius built from them as
--
--   $$\rho(s) = \sup_{n} \big(\text{that union at level } n\big)\text{-indicator}(s)\cdot 2^{-n} \;+\; \mathbf{1}_{\{s \notin \bigcup_n(\cdots)\}}(s),$$
--
--   which is positive everywhere and measurable.
--
--   Collectively these objects are the coordinates of a one-intermediate-point chaining scheme: a ball to average over, a constant controlling the exchange of that average with the outer integrals, an explicit planar construction where the two cones need not share a direction, and a hierarchy of hypotheses (common direction, small axis spread, overlapping types, dense visible type, local domination) under which the ball is populated enough for the average to be useful.
--
--   **Formalization Note.** Volumes and the density defect live in $\mathbb{R}_{\ge 0}^{\infty}$; the domination condition is stated with `∀ᵐ` (almost every $s$), and the planar ball folds its side conditions into the set itself, so it is genuinely empty on the pairs it does not serve rather than being given a junk value. The aperture in the domination condition ranges over a finite set $\Theta$ of reals with no positivity constraint imposed at the definition site.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/7a1a680db2124d46ce370c91fd450aa454edf491/QuadraticFormsSobolev/BeyondThePaper.lean#L250-L7080

-- Generated by skeleton subtraction from QuadraticFormsSobolev/BeyondThePaper.lean
-- source: quadratic-forms-sobolev@7a1a680db212
import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Beyond the paper — new mathematics, not a formalisation of Bux–Kassmann–Schulze

**Everything in this file is outside the scope of the paper being certified.**
None of it appears in arXiv:1707.09277, in any form: not the statements, not the
constants, not the proofs. It is an attempt to close the one gap the
formalisation of that paper leaves open, and it should be read as new (and
incomplete) research rather than as a record of what the authors wrote. No
mathematics elsewhere in this repository depends on this file: deleting it, and
its line in the root module, would leave the certification of the paper
intact.

## The problem

Section 3.2's dominated-convergence step needs an a priori hypothesis its own
argument never establishes: that `f ∈ H_k(B*)` already lies in `H^{α/2}(B*)`.
The formalisation of that step (`QFS.limsup_lintegral_stepG_le`) and of the
whole of §3.2 (`QFS.formHs_ball_le_form_of_formHs_ne_top`) carries the
hypothesis explicitly. This file discharges it in dimension two, in several
regimes in every dimension, and reduces it in general to one integrability
condition.

## What this file proves

The route is a local Poincaré inequality: for two points `s`, `t`,

  (★)  `(f(s) − f(t))²` is recovered by chaining through intermediate points
       that *do* see the relevant cones, averaged over a positive-measure set of
       such points,

which converts the cone-restricted energy into the full fractional energy.
`exists_ball_in_two_cones` is its geometric heart: for two distinct points
sharing a cone direction it supplies a **ball** of intermediate points lying in
both cones — a positive-measure strengthening of the paper's Lemma 4.3, which
produces a single point. In the plane the same is true without a shared
direction (`mem_two_cones_of_mem_planarBall`), because two non-parallel lines
meet; that is what closes dimension two, and `no_common_neighbour_of_skew_axes`
proves that *this* construction cannot be pushed to dimension three.

Stripped of hypotheses, what the chaining gives is one inequality
(`lintegral_visibility_le`): for every configuration satisfying the standing
assumptions — the kernel bounds (2) and condition (M) — the `H^{α/2}` energy of
a pair, weighted by how much of its averaging ball can see both endpoints, is at
most `C·|f|²_{H_k}`. Everything else here exhibits sets of pairs on which that
weight is bounded below:

* **dimension two**: `sobolevInclusion_planar`, `formHs_ball_ne_top_of_planar`,
  `formHs_ball_le_form_planar`, `theoremOneOneBallCondMeas_two`,
  `formHs_le_form_planar`, `Hk_ball_eq_Hs_ball_planar`,
  `formHs_univ_le_form_univ_planar`, `Hk_univ_eq_Hs_univ_planar`,
  `Hk_domain_eq_Hs_domain_planar` — Theorems 1.1 and 1.4 in the plane, granted
  the Whitney/Dyda input Lemma A.1 quotes;
* **dimension one**: `formHs_le_form_dim_one`, where every cone is `ℝ ∖ {0}`;
* **small axis spread** — the cone axes at most `γ` apart as lines with
  `γ < 2ϑ`: `sobolevInclusion_of_axisSpread` and the chain behind it
  (`formHs_ball_le_form_spread`, `Hk_univ_eq_Hs_univ_spread`,
  `Hk_domain_eq_Hs_domain_spread`). **Wide cones** (apex above `π/4`) are the
  case `γ = π/2`, and `sobolevInclusion_wide` is now derived from it;
* **pairwise overlapping cone types**: `sobolevInclusion_of_overlapping`, with
  `exists_narrow_overlapping_cones_without_common_direction` showing that this
  is strictly weaker than a common direction;
* **a densely visible type**, and its exact reach:
  `formHs_le_form_of_visibleDense`, `formHs_le_form_of_ae_commonDirection`;
* **local domination**, where the dominating type may vary from pair to pair:
  `LocallyDominatedRad`, `formHs_ball_le_form_locallyDominated`, together with
  two families that satisfy it — every uniformly continuous configuration
  (`formHs_ball_le_form_of_uniformContinuous`) and two arbitrary narrow cone
  types split by a hyperplane (`formHs_ball_le_form_twoSide`);
* **every admissible configuration**, up to one condition on `f`: there is an
  explicit measurable domination radius `ρ > 0`
  (`exists_measurable_dominationRadius`) with Theorem 1.1's enlarged-ball form
  for every `f` such that `∫ f²ρ^{-α} < ∞`
  (`formHs_ball_le_form_of_dominationRadius`).

`planar_hypotheses_nonvacuous` and `wide_hypotheses_nonvacuous` record that none
of this is vacuous.

## What this file does not prove

The general narrow case in dimension three and above: cones of apex at most `π/4`
whose types neither overlap nor are locally dominated. What is missing there is
precisely the size of the domination radius — that `∫ f²ρ^{-α} < ∞` for every
`f ∈ H_k`. Two thin double cones with skew axes need not meet at all, so one
intermediate point cannot suffice and genuinely longer chains would be required;
producing them, with a uniform bound on the length and with positive measure at
every link, is the continuous analogue of the paper's §§5–6. The paper
establishes that machinery only in the discrete setting — which is precisely why
it goes through `ℤ^d` — and reproducing it in the continuum is an open research
problem, not a gap in this formalisation.
-/

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

namespace QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Lemma 2.2 at an arbitrary aperture

The proof of Lemma 2.2 uses `ϑ/3` only through `2·(ϑ/3) ≤ ϑ`; a net of mesh
`ϑ − θ` gives reference cones of any aperture `θ < ϑ`, at the cost of a larger
family. Nothing in the paper needs this; it is infrastructure for what follows. -/

/-! ## The averaging set, explicitly

For the chaining average one needs the ball of common neighbours as an explicit
function of `(s,t)` — a measurable selection is not enough, since the estimate
must be integrated in `s` and `t`. The centre is an explicit continuous
function, which is what the next definition records. -/

/-- The centre of the ball of common cone-neighbours of `s` and `t`: walk from
`s` along the axis `v` far enough that the cone has opened past `‖s − t‖`. -/
noncomputable def midCentre (v : E) (ϑ : ℝ) (s t : E) : E :=
  s + (3 * ‖s - t‖ / Real.sin ϑ) • v

/-! ## The fibre estimate

The chaining average is exchanged with the integration in `t` by Tonelli, and
what has to survive that exchange is the weight. This is the estimate that makes
it work, and it is the reason the argument is scale-invariant: the singular
weight `‖s − t‖^{-2d-α}` integrated over the `t`-fibre above a point `z` comes
back as `‖z − s‖^{-d-α}`, exactly the weight of the `H_k` form on the pair
`(s,z)` — which the lower bound of (2) then converts into `k(s,z)`. -/

/-- The constant in the fibre estimate: `(1 + 3/sin ϑ)^{2d+α} / (3/sin ϑ − 1)^d`. -/
noncomputable def chainConst (d : ℕ) (ϑ α : ℝ) : ℝ :=
  (1 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) / (3 / Real.sin ϑ - 1) ^ d

/-! ## The averaging step

The other ingredient: the oscillation between `s` and `t` is dominated by the
*average* over the ball of common neighbours of the two oscillations along the
chain `s → z → t`. This is where a positive-measure set of intermediate points
is indispensable — with the single point of Lemma 4.3 the left-hand side would
be multiplied by zero. -/

/-! ## The exchange

With the averaging step and the fibre estimate in hand, the chaining argument is
one application of Tonelli: exchange the average over the ball of common
neighbours with the integration in `t`, and the fibre estimate converts the
weight into the one carried by the pair `(s,z)`. -/

/-! ## The mirror image, on the `t` side

The chained integrand `2(f(z) − f(s))² + 2(f(t) − f(z))²` has two terms. The
first is handled by the lemmas above; the second needs the same statements with
the roles of `s` and `t` exchanged. The displacement from `s` to `t` costs one
extra unit in the estimates — `3/sin ϑ ∓ 2` in place of `3/sin ϑ ∓ 1` — but
nothing else changes. -/

/-- The constant in the `t`-side fibre estimate. -/
noncomputable def chainConst_prime (d : ℕ) (ϑ α : ℝ) : ℝ :=
  (2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) / (3 / Real.sin ϑ - 2) ^ d

/-! ## Assembling the local Poincaré inequality

Averaging bounds the oscillation pointwise; the two exchanges dispose of the two
terms of the chained integrand. Tonelli in the outer pair, once in each order,
puts each term in front of the exchange that handles it. -/

/-! ## The open statement, for configurations with a common cone direction

The lower bound of (2) turns the cone-restricted weight into `k`, so the local
Poincaré inequality above becomes exactly the statement §3.2 is missing —
restricted to configurations all of whose cones share a direction. -/

/-! ## Localising to a set

Corollary 2.4 reduces a configuration to finitely many cone types, so `ℝ^d`
splits into finitely many measurable pieces `U_m` on which a common direction is
available. To exploit that, the chaining estimate must hold with the *endpoints*
confined to a set — the intermediate point `z` may still range freely, since the
conversion to `k` only ever uses the cone at an endpoint. Restricting the outer
integrals is all that is required; the exchange lemmas apply unchanged. -/

/-! ## The obstruction to the cross blocks, as a theorem

The cross blocks are not merely harder — one intermediate point provably cannot
handle them. In dimension three, two double cones of aperture `ϑ < π/4` whose
axes are orthogonal and skew are **disjoint**, so no `z` at all lies in both,
let alone a set of positive measure. Chains of length two are therefore
unavoidable, and their middle edge runs between two points whose cones the
configuration assigns arbitrarily — which is exactly the difficulty §§5–6
address, in the discrete setting. -/

/-! ## The diagonal blocks of the canonical decomposition

Corollary 2.4 supplies, for any `ϑ`-bounded configuration, a finite family of
reference cones of aperture `ϑ/3` covering it pointwise. The sets
`U_V = {x | V ⊆ Γ(x)}` are measurable by Debreu's condition (carried, as
elsewhere in this repository, as the explicit hypothesis `QFS.CondMeas`), they
cover `ℝ^d`, and on each of them a common cone direction is available. So every
diagonal block is controlled, with **one constant** for all of them: `chainConst`
depends on the aperture, which is `ϑ/3` throughout, and not on the axis. -/

/-! ## Dimension two: the toolkit

In the plane the cross blocks *are* reachable: two double cones whose axes are
not parallel have intersecting axis-lines, and the "not already a cone pair"
condition supplies exactly the quantitative separation the chaining needs. The
first step is a concrete orthogonal complement. -/

/-- The rotation of `w` by a quarter turn, in coordinates. -/
noncomputable def perp2 (w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-(w 1), w 0]

/-- The two-dimensional cross product. -/
def cross2 (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 1 - x 1 * y 0

/-- The coefficient placing the intersection point on the axis through `s`. -/
noncomputable def planarA (vs vt s t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  cross2 (t - s) vt / cross2 vs vt

/-- The coefficient placing the intersection point on the axis through `t`. -/
noncomputable def planarB (vs vt s t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  cross2 (t - s) vs / cross2 vs vt

/-- The intersection point of the two axis-lines: the centre of the planar
averaging ball. -/
noncomputable def planarCtr (vs vt s t : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) := s + planarA vs vt s t • vs

/-! ## The planar averaging family, named

To feed the planar balls through `lintegral_swap_of_fibre_bound` they must be an
explicit function of the pair, and the fibre estimate needs the comparability of
`‖z − s‖`, `‖z − t‖` and `‖s − t‖` in **both** directions. -/

/-! ## The planar fibre estimate

The averaging family, packaged as a set-valued function with the side conditions
folded in, and the estimate that lets `lintegral_swap_of_fibre_bound` apply to
it. Pairs that are already cone pairs, and the diagonal, get the empty ball —
they need no chaining. -/

/-- The planar averaging ball, with its side conditions folded in. -/
def planarBall (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ : ℝ)
    (s t : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | s ≠ t ∧ t - s ∉ doubleCone vs ϑ ∧ t - s ∉ doubleCone vt ϑ ∧
    z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)}

/-- The constant in the planar fibre estimate. -/
noncomputable def planarConst (vs vt : EuclideanSpace ℝ (Fin 2)) (ϑ α : ℝ) : ℝ :=
  (1 / |cross2 vs vt| + 1) ^ (4 + α) * 4 / Real.sin ϑ ^ 2

/-! ### The `t` side of the planar family -/

/-! ### Assembling the planar cross blocks -/

/-! ### The dichotomy in the plane

Two reference cones of the same aperture either have non-parallel axes — and then
`formHs_le_form_planar_cross` applies — or they are the *same* double cone, and
then the block is diagonal and `formHs_le_form_of_commonDirection_on` applies. In
the plane there is no third possibility, which is exactly why *this* argument
closes here and not in higher dimensions; the higher-dimensional regimes are
reached below by other means. -/

/-! ### One block of the planar decomposition -/

/-! ## The open statement, in dimension two

Corollary 2.4 covers `ℝ²` by finitely many pieces on each of which a reference
cone is available; the squares of that cover exhaust `ℝ² × ℝ²`; every block is
controlled by `planar_block_le`; and a finite sum of finite constants is
finite. -/

/-! ## The ball-localised form, in dimension two

§3.2 consumes the inclusion on a ball, not on the whole plane. A Lipschitz
cutoff bridges the two: `χf` agrees with `f` on the inner ball and is supported
in the outer one, so the whole-space theorem applies to it, and
`form_cutoff_le` says the cost is the `H_k` form on the outer ball plus an `L²`
term. Both are finite for `f ∈ H_k(B*)`, which is exactly the hypothesis §3.2
has. -/

/-! ## Theorem 1.1 on a ball, unconditionally, in the plane

Section 3.2 leaves one hypothesis undischarged: the `H^{α/2}` form of the
larger ball must be known to be finite before the dominated convergence step
can run (`QFS.formHs_ball_le_form_of_formHs_ne_top`).  In the plane
`formHs_ball_ne_top_of_planar` -- proved above, and *not* in the paper --
supplies exactly that for every `f ∈ H_k`, so the two combine into the paper's
statement with no hypothesis beyond `f ∈ L²` of the larger ball.

The mathematics closing the gap is new; the statement obtained is the paper's. -/

/-! ## Theorem 1.4 for `Ω = ℝ²`

The paper deduces the whole-space case from Theorem 1.1 by monotone convergence,
the constant being independent of the radius.  `QFS.theoremOneFourUniv_of_theoremOneOne`
is that deduction from the paper's `Prop`; here it is run on the planar theorem
instead. -/

/-! ## Theorem 1.4 for a domain, in the plane

Lemma A.1 for a domain (`QFS.formHs_le_form_domain`) turns the ball
comparability into the comparability on `Ω`, given the Whitney family of `Ω` and
Dyda's inequality — the two inputs the paper quotes.  With the planar ball
theorem it gives the inclusion `H_k(Ω) ⊆ H^{α/2}(Ω)` for every planar domain
that has such a family. -/

/-! ## Lemma 3.7's own statement, in the plane

Lemma 3.7 says the two spaces coincide on a ball.  That follows from the
same-ball comparability, which in the plane is `formHs_le_form_planar`. -/

/-! ### The planar hypotheses are satisfiable -/

/-! ## Theorem 1.1 itself, in the plane

Everything above assembles into the paper's own Theorem 1.1, in dimension two,
with the two hypotheses this formalisation carries and the one input Lemma A.1
quotes. -/

/-! ## Wide cones: dimension three and above

The obstruction to the cross blocks is that two double cones with skew axes can
be disjoint (`no_common_neighbour_of_skew_axes`). That cannot happen when the
cones are **wide**: the angle between two axes, read as an angle between lines,
is at most `π/2`, so two double cones of apex angle more than `π/4` always
overlap in a cone of aperture `apex − π/4`. Their bisector is its axis.

Everything else is already in place: the chaining machinery
(`formHs_le_form_of_commonDirection_on`) asks only that the two ends admit a
*common* cone, not that the configuration be constant, so with the bisector in
hand every block — diagonal or cross — is controlled, in every dimension. -/

/-! ## Pairwise overlapping cones: narrow cones without a common direction

Chains of length three or more are what the general narrow case would need (see
the note below), and they are out of reach here: their interior legs run between
two intermediate points whose types the configuration assigns adversarially. But
chains of length two reach further than the wide-cone case suggests. All they need is that
the two cones **overlap** — the intermediate point is then seen by both
endpoints' own cones, and no constraint is placed on its type. Overlapping is
strictly weaker than sharing a direction: three cones can pairwise overlap with
no direction common to all three, and that happens for narrow cones in dimension
three and above. -/

/-! ### When do two cones overlap?

The bisector argument of `exists_common_subcone` is not about `π/4`: two double
cones of apex `θ` overlap in a cone of aperture `θ − β`, where `β` is half the
angle between their axes. The `π/4` threshold is what makes *every* pair overlap;
a particular pair needs only its own axes to be close. -/

/-! ## Theorem 1.1 when the axis spread is below twice the apex bound

The same assembly as in the plane, with `formHs_ball_ne_top_of_spread` in place
of `formHs_ball_ne_top_of_planar`. The wide-cone statements below are the case
`γ = π/2`. -/

/-! ## Theorem 1.4 for small axis spread -/

/-! ## The wide-cone regime, as the case `γ = π/2`

Two lines are never more than `π/2` apart, so a configuration with apex bound
`ϑ > π/4` has axis spread below `2ϑ` automatically. Every wide-cone statement
below is therefore an instance of the corresponding small-spread statement. -/

/-! ## Dimension one is trivial

On the line a double cone of positive apex angle is everything but the origin,
so *every* pair of distinct points is a cone pair and the lower bound of (2)
gives the inclusion directly, with the constant `Λ/2`. This is what makes the
open case precisely "narrow cones in dimension at least three". -/

/-! ### The wide-cone hypotheses are satisfiable -/

/-! ## Narrow cones: a densely visible type

The obstruction in dimension three and above is that the cones at `s` and at `t`
can be disjoint, so no single point sees both. But the chaining never needed the
intermediate point to be seen *by the cones of the endpoints*: it needs the three
points to be joined by cone pairs, and a pair `(s,z)` is a cone pair as soon as
`s − z` lies in the cone at `z`. So it is enough that the intermediate points be
of one fixed type — the balls of `exists_ball_in_two_cones` are available for
*every* pair, since that lemma constrains only the direction `v`, not the
configuration.

What has to be paid for is measure: the average is over the part of the ball
that has the right type. The hypothesis below asks exactly that this part be a
fixed fraction. -/

/-! ### The same, for one pair at a time and on a set of pairs

The density of the visible type is used only at the ball the chaining averages
over, once per pair. Isolating that is what lets the type vary from pair to
pair. -/

/-! ## Local domination: the type may vary from point to point

The chaining needs, for each pair `(s,t)`, only that *some* reference cone is
contained in the cones of a fixed fraction of the one ball it averages over — and
that ball is determined by `s`, by `‖s−t‖` and by the reference direction, not by
the direction of `t−s`. The type may therefore vary from pair to pair, and the
Lebesgue density theorem supplies the fraction at almost every point. What it
does not supply is a *uniform* radius below which the fraction is there; that
uniformity, `QFS.LocallyDominated`, is exactly what separates the theorem below
from the open statement. -/

/-- **Local domination out to a radius that may vary from point to point.** For
every pair `(s,t)` with `‖s−t‖ ≤ ρ s` there are a reference direction `v ∈ S` and
an aperture `θ ∈ Θ` — the aperture fixes how far along `v` the chaining ball sits,
namely `3‖s−t‖/sin θ` — such that `Ṽ(v,θ)` lies inside the cones of a
`c₀`-fraction of that ball. Shrinking `θ` moves the ball further out, so a whole
window of scales is available at each pair; letting `ρ` vary is what the Lebesgue
density theorem provides for free (`QFS.ae_exists_dominating_type`). -/
def LocallyDominatedRad {d : ℕ} (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (S : Finset (EuclideanSpace ℝ (Fin d))) (Θ : Finset ℝ) (c₀ : ℝ)
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ᵐ s : EuclideanSpace ℝ (Fin d), ∀ t : EuclideanSpace ℝ (Fin d), ‖s - t‖ ≤ ρ s →
    ∃ q ∈ Θ ×ˢ S, ENNReal.ofReal (c₀ * ‖s - t‖ ^ d) ≤
      volume ({x : EuclideanSpace ℝ (Fin d) | doubleCone q.2 q.1 ⊆ (Γ x).carrier} ∩
        closedBall (midCentre q.2 q.1 s t) ‖s - t‖)

/-- **The pairs the chaining can serve**: those for which some reference cone,
at some aperture in `Θ`, fills a `c₀`-fraction of the ball the chaining averages
over. -/
def dominatedPairs {d : ℕ} (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (S : Finset (EuclideanSpace ℝ (Fin d))) (Θ : Finset ℝ) (c₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  ⋃ q ∈ Θ ×ˢ S, {p | ENNReal.ofReal (c₀ * ‖p.1 - p.2‖ ^ d) ≤
    volume ({x : EuclideanSpace ℝ (Fin d) | doubleCone q.2 q.1 ⊆ (Γ x).carrier} ∩
      closedBall (midCentre q.2 q.1 p.1 p.2) ‖p.1 - p.2‖)}

/-! ### The consequence for §3.2

The same cutoff argument as in the wide and small-spread regimes, with the extra
`L²` term of `QFS.formHs_univ_le_of_locallyDominated` absorbed. -/


/-! ### A configuration no earlier theorem reaches

Two arbitrary cone types, as narrow as one likes and pointing in unrelated
directions, split by a hyperplane. At every point one of the two closed
half-spaces contains at least half of the ball the chaining averages over — a
point reflection in its centre carries the outside part into the inside part — so
the configuration is locally dominated, and Theorem 1.1 holds for it. -/

/-! ### Continuous configurations are locally dominated

If the cone axis varies uniformly continuously, then near any point every cone
still contains one fixed reference cone, so the whole chaining ball is of a single
type and the hypothesis holds with a uniform radius. Theorem 1.1 therefore holds
for every uniformly continuous configuration, in every dimension and at any apex
angle. -/

/-! ### A measurable domination radius, for every configuration

The pointwise radius of `QFS.ae_exists_dominating_type` is not measurable as it
stands. Restricting the density requirement to the dyadic scales makes the sets
`QFS.denseFrom` measurable, and their union over the finitely many types gives an
explicit measurable radius `QFS.domRadius` which is positive everywhere and below
which the chaining always serves the pair. What is left of the open statement is
then the size of that radius: `∫ f²ρ^{-α} < ∞`. -/

/-- The points at which `U` fills all but an `η`-fraction of every ball of radius
`K·2^{-m}` with `m ≥ n`. -/
def denseFrom (U : Set (EuclideanSpace ℝ (Fin d))) (K : ℝ) (η : ℝ≥0∞) (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {s | ∀ m : ℕ, n ≤ m →
    volume (closedBall s (K * (1 / 2 : ℝ) ^ m))
      ≤ volume (U ∩ closedBall s (K * (1 / 2 : ℝ) ^ m))
        + η * volume (closedBall s (K * (1 / 2 : ℝ) ^ m))}

/-- The union over the finitely many types of the sets `denseFrom`. -/
def denseUnion (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (S : Finset (EuclideanSpace ℝ (Fin d))) (θ K : ℝ) (η : ℝ≥0∞) (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ v ∈ S, denseFrom {x : EuclideanSpace ℝ (Fin d) | doubleCone v θ ⊆ (Γ x).carrier} K η n

/-- **A measurable radius below which the chaining is served.** -/
noncomputable def domRadius (Γ : Configuration (EuclideanSpace ℝ (Fin d)))
    (S : Finset (EuclideanSpace ℝ (Fin d))) (θ K : ℝ) (η : ℝ≥0∞)
    (s : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (⨆ n : ℕ, (denseUnion Γ S θ K η n).indicator (fun _ => (1 / 2 : ℝ) ^ n) s)
    + (⋃ n : ℕ, denseUnion Γ S θ K η n)ᶜ.indicator (fun _ => (1 : ℝ)) s

/-! ### How far the one-point chaining reaches

The hypothesis of `formHs_le_form_of_visibleDense` asks for density at *every*
scale, because pairs at every distance need intermediate points. By the Lebesgue
density theorem that forces the visible set to be co-null: a set of uniform
positive density at all scales has null complement. So the theorem above is
exactly the almost-everywhere form of the common-direction theorem, and **no
sparser set of good types can serve a chaining argument with a single
intermediate point** — which is why the narrow-cone case in dimension three and
above needs chains of length at least three, and with them the continuum
analogue of §§5–6. -/

/-! ### The overlap hypothesis is not vacuous, and is strictly weaker

Three unit vectors in `ℝ³` with pairwise inner product `8/9`, and the apex
`θ = arccos √(14/15) ≈ 15°` — far below the `π/4` at which every pair of double
cones is forced to meet. The three cones still overlap pairwise, because half the
angle between two axes is `arccos √(17/18) < θ`; but no direction lies in all
three at once, because for a unit `u`

  `∑ᵢ ⟪vᵢ, u⟫² = (8 (u₀+u₁+u₂)² + 1)/9 ≤ 25/9 < 3 · 14/15`,

so some `|⟪vᵢ, u⟫|` falls below `cos θ = √(14/15)`. Neither
`sobolevInclusion_wide` nor `formHs_le_form_of_commonDirection` applies to such a
configuration; `sobolevInclusion_of_overlapping` does. -/

/-! ## Theorem 1.4 for a domain, under small axis spread

The planar assembly of `QFS.Hk_domain_eq_Hs_domain_planar`, with
`QFS.ballComparability_spread` in place of the planar ball comparability. Taking
`γ = π/2` gives the wide-cone case in every dimension. -/

end QFS


