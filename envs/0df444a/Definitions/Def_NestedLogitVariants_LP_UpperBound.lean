-- Prove2me | Definitions.Def_NestedLogitVariants_LP_UpperBound
-- name    : NestedLogitVariants_LP_UpperBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:21:12.303982+00:00
-- url     : https://prove2.me/theorems/06fe7f96-105f-4bda-9739-5b529ac3b0b7
-- title:
--   §7, pp. 29–30 — F_i(z_i | x), the tighter program (16) and F̂_i(x) of (17)
-- statement:
--   Relax the assortment of nest $i$ to a vector $z_i = (z_{i1}, \dots, z_{in}) \in [0,1]^n$ and let
--
--   $$F_i(z_i \mid x) = \Big(v_{i0} + \sum_{j \in N} v_{ij} z_{ij}\Big)^{\gamma_i} \left[\frac{\sum_{j\in N} r_{ij} v_{ij} z_{ij}}{v_{i0} + \sum_{j\in N} v_{ij} z_{ij}} - x\right],$$
--
--   the objective of the inner maximization in (16) and (18). At the $0/1$ vector of an assortment $S_i$ it equals $V_i(S_i)^{\gamma_i}(R_i(S_i) - x)$. A pair $(x, y)$ is feasible for problem (16) when
--   $$v_0\, x \ge \sum_{i \in M} y_i, \qquad y_i \ge \max_{z_i \in [0,1]^n} F_i(z_i \mid x) \quad \forall i \in M,$$
--   and $\hat F_i(x) = \max_{z_i \in [0,1]^n} F_i(z_i \mid x)$, as in (17).
--
--   Problem (16) tightens (3) by letting the inner maximization range over fractional assortments; $\hat F_i$ is the function whose convexity makes (17) a convex program.
--
--   **Formalization Note** The second constraint of (16) is stated as $y_i \ge F_i(z_i \mid x)$ for every $z_i$ in the box, which is equivalent and takes no supremum. $\hat F_i(x)$ is the real supremum of $\{F_i(z \mid x) : z \in [0,1]^n\}$; under the standing assumptions this set is nonempty and bounded above, so the supremum is the paper's maximum value. As in the model, $x / 0 = 0$ and powers are `Real.rpow`.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 29–30, §7, displays (16)–(18)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace NestedLogitVariants.LP

variable {ι : Type*} {n : ℕ}

/-- The box `[0, 1]^n` of fractional assortment vectors `z_i = (z_{i1}, …, z_{in})` of §7 (p. 29). -/
def box (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)

/-- The objective `F_i(z_i | x)` of the inner maximization in (16) and (18) (pp. 29–30):
`(v_{i0} + ∑_j v_{ij} z_{ij})^{γ_i} [∑_j r_{ij} v_{ij} z_{ij} / (v_{i0} + ∑_j v_{ij} z_{ij}) − x]`.
At the `0/1` vector of an assortment `S` it equals `V_i(S)^{γ_i} (R_i(S) − x)`. -/
noncomputable def F (I : Instance ι n) (i : ι) (z : Fin n → ℝ) (x : ℝ) : ℝ :=
  (I.vnp i + ∑ j, I.v i j * z j) ^ I.γ i *
    ((∑ j, I.r i j * I.v i j * z j) / (I.vnp i + ∑ j, I.v i j * z j) - x)

/-- `(x, y)` is feasible for problem (16) (p. 29): `v_0 x ≥ ∑_i y_i` and
`y_i ≥ max_{z_i ∈ [0,1]^n} F_i(z_i | x)`, written as `y_i ≥ F_i(z_i | x)` for every `z_i` in the
box (no supremum is taken). -/
def LP16Feasible [Fintype ι] (I : Instance ι n) (x : ℝ) (y : ι → ℝ) : Prop :=
  (∑ i, y i) ≤ I.v0 * x ∧ ∀ i, ∀ z ∈ box n, F I i z x ≤ y i

/-- `F̂_i(x) = max_{z_i ∈ [0,1]^n} F_i(z_i | x)` of (17) (p. 29), as the real supremum of the image
of the box. Under the standing assumptions of §1 the image is nonempty (the box is nonempty) and
bounded above (`F_i(· | x)` is bounded on the box), so the supremum is the paper's maximum value;
no statement of this mission evaluates it outside those assumptions. -/
noncomputable def Fhat (I : Instance ι n) (i : ι) (x : ℝ) : ℝ :=
  sSup ((fun z => F I i z x) '' box n)

end NestedLogitVariants.LP


