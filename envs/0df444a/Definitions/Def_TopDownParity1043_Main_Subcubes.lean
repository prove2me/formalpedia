-- Prove2me | Definitions.Def_TopDownParity1043_Main_Subcubes
-- name    : TopDownParity1043_Main_Subcubes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:18:21.777778+00:00
-- url     : https://prove2.me/theorems/de823cb0-c911-44a2-8690-396bd85e1b65
-- title:
--   §1.3 and §2.1 — subcubes, projected laws and min-entropy deficits
-- statement:
--   Let $V$ be finite. For a word $x$ and a coordinate set $S$, the subcube $[x]_S$ consists of words agreeing with $x$ outside $S$. Write $X_{x,S}=X\cap[x]_S$ and $x_R$ for the restriction of $x$ to the coordinate subtype $R$.
--
--   For an arbitrary probability law $X$ on the cube, its deficit and projected law are
--   $$D_\infty(X)=|V|-H_\infty(X),\qquad X_R=(x\mapsto x_R)_*X.$$
--
--   The min-entropy $H_\infty$ is the referenced published definition. For a nonempty finite set $X$ viewed in a cube of dimension $t$, its deficit is $t-\log_2|X|$. A set deficit bound also requires $X\ne\varnothing$; the numeric expression alone is only used on nonempty sets. Uniform-set expectation divides the finite sum by $|X|$.
--
--   For real $k$, the light-pattern count is
--   $$L_X(R,k)=\bigl|\{z\in\{0,1\}^R:\Pr[X_R=z]\le2^{-|R|-2k-2}\}\bigr|.$$
--
--   These definitions support the entropy and light-pattern lemmas. Fibre deficits use $t=|S|$, while ambient deficits use $t=|V|$; the projection is a genuine pushforward PMF on the smaller cube.
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), §1.3; §2.1 p.5; Lemma 4 p.7; Lemma 10 p.15, p. 4

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Cube
import Definitions.Def_SamplingAC0_minEntropy

set_option autoImplicit false

namespace TopDownParity1043.Main

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Restriction to the actual coordinate subtype, not a cylinder in the ambient cube. -/
def project (R : Finset V) (x : V → Bool) : R → Bool := fun i => x i

/-- §2.1, p.5: the subcube frees precisely the coordinates in S. -/
def InSubcube (x : V → Bool) (S : Finset V) (z : V → Bool) : Prop :=
  ∀ i, i ∉ S → z i = x i

/-- The finite fibre X ∩ [x]_S. -/
noncomputable def fibre (X : Finset (V → Bool)) (x : V → Bool)
    (S : Finset V) : Finset (V → Bool) := by
  classical
  exact X.filter (InSubcube x S)

/-- §1.3: min-entropy deficit of an arbitrary law, reusing the published entropy. -/
noncomputable def lawDeficit (X : PMF (V → Bool)) : ℝ :=
  Fintype.card V - SamplingAC0.minEntropy X

/-- Deficit of a finite set inside a cube of dimension t. Use only for nonempty sets. -/
noncomputable def setDeficit (t : ℕ) (X : Finset (V → Bool)) : ℝ :=
  (t : ℝ) - Real.logb 2 X.card

/-- A set deficit bound carries nonemptiness; the empty set is never dense. -/
noncomputable def SetDeficitLE (X : Finset (V → Bool)) (k : ℝ) : Prop :=
  X.Nonempty ∧ setDeficit (Fintype.card V) X ≤ k

/-- Uniform expectation on a finite nonempty set. The entropy lemma explicitly assumes
nonemptiness, so its denominator is positive and every sampled fibre contains its sample. -/
noncomputable def uniformSetMean (X : Finset (V → Bool)) (a : (V → Bool) → ℝ) : ℝ :=
  (∑ x ∈ X, a x) / X.card

/-- The actual pushforward law on the R-dimensional cube. -/
noncomputable def projectionLaw (X : PMF (V → Bool)) (R : Finset V) : PMF (R → Bool) :=
  X.map (project R)

/-- Number of light projected patterns; the probability threshold is inclusive. -/
noncomputable def lightCount (X : PMF (V → Bool)) (R : Finset V) (k : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun z : R → Bool =>
    ((projectionLaw X R z).toReal) ≤ (2 : ℝ) ^ (-(R.card : ℝ) - 2 * k - 2)).card

end TopDownParity1043.Main


