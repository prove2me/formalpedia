-- Prove2me | Definitions.Def_PrefixMixLearn_Proper_Unmixing
-- name    : PrefixMixLearn_Proper_Unmixing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:23.864596+00:00
-- url     : https://prove2.me/theorems/523da9a6-579c-4cf5-a834-13cc35d132a4
-- title:
--   Signed unmixings $N_0,N_1$, the signed weight $w'$, raw profiles and the constructions of Theorem D.2 and Corollary D.3
-- statement:
--   Let the view $A=\{0,1\}^d$ be the first $d$ coordinates and $B$ a finite future view. For a law $P_{AB}$ on $A\times B$, $P_A$ is its marginal; the comparator is $M_{AB}=(1-w)Q_\nu\otimes R_0+wQ_\mu\otimes R_1$. For a test $e:B\to[0,1]$, $a=E_{R_0}e$, $b=E_{R_1}e$, $g=b-a$, put $P_e(x)=\sum_y e(y)P_{AB}(x,y)$,
--   $$N_0=\frac{bP_A-P_e}{g},\qquad N_1=\frac{P_e-aP_A}{g},\qquad w'=N_1(\{0,1\}^d).$$
--   The raw profiles along a path $x$ are $\tilde\nu_i=N_0[x_{<i}1]/N_0[x_{<i}]$, $\tilde\mu_i=N_1[x_{<i}1]/N_1[x_{<i}]$. **Theorem D.2's construction** returns the uniform product if $w'\notin(0,1)$ or a parent prefix mass $N_j[x_{\le t}]$, $0\le t<d$, is nonpositive, and otherwise the restoration of $(\tilde\nu,\tilde\mu)$ at weight $w'$ (clip the weighted mean, project the direction onto $I(\hat m,w')$). **Corollary D.3's component profile** of $N_j$ on $x$ is its raw profile clipped to $[\alpha,1-\alpha]^d$ if all its parent masses are positive, and the uniform mean vector $(1/2,\dots,1/2)$ otherwise.
--
--   **Formalization Note.** The future view is any finite type `Y`; laws on $A\times B$ are real functions on `Cube d × Y`. All quantities are exact real values (analysis objects), as in the paper.
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 30–31 (PDF 32–33), §D.2; p. 34–35 (PDF 36–37), Corollary D.3

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Geometry

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace PrefixMixLearn.Proper

/-!
# Signed unmixings on a weak product view (Appendix D setting)

Saravanan, *Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional
Samples*, STOC 2027 submission (manuscript sha256 9c359910…), §D.2, pp. 30–31 (PDF 32–33);
Corollary D.3, pp. 34–35 (PDF 36–37).

The first `d` coordinates form the view `A = {0,1}^d`; the future view `B` is a finite set `Y`.
A law on `A × B` is a real function on `Cube d × Y`.

* `marginalA P_AB = P_A`.
* `condProdMix w ν μ R₀ R₁ = (1 − w) Q_ν ⊗ R₀ + w Q_μ ⊗ R₁` (the comparator `M_AB`).
* `testMean R e = E_R e`; with `a = E_{R₀} e`, `b = E_{R₁} e`, `g = b − a`.
* `testedMass P_AB e = P_e`, `P_e(x) = Σ_y e(y) P_AB(x, y)`.
* `unmixN0 = (b P_A − P_e)/g`, `unmixN1 = (P_e − a P_A)/g` (signed measures on `{0,1}^d`),
  `wPrime = N_1({0,1}^d)`.
* `parentsPos N x`: every parent prefix mass `N[x_{≤t}]`, `0 ≤ t < d`, is positive.
* `rawProfile N x = (N[x_{<i}1] / N[x_{<i}])_i`.
* `weakViewEstimate α P_AB e a b x` is the construction of Theorem D.2 on the path `x`: the uniform
  product if `w′ ∉ (0,1)` or a parent prefix mass of `N_0` or `N_1` is nonpositive; otherwise
  `restore α w′ ν̃ μ̃` (clip the weighted mean, project the direction onto `I(m̂, w′)`).
* `indivProfile α N x` is Corollary D.3's clipped component profile: the raw profile of `N` clipped
  to `[α, 1 − α]^d` if all its parent masses are positive, the uniform mean vector otherwise.
-/

variable {d : ℕ} {Y : Type*} [Fintype Y]

/-- The marginal `P_A(x) = Σ_y P_AB(x, y)`. -/
def marginalA (PAB : Cube d × Y → ℝ) : Cube d → ℝ := fun x => ∑ y, PAB (x, y)

/-- The conditional-product comparator `M_AB = (1 − w) Q_ν ⊗ R_0 + w Q_μ ⊗ R_1`. -/
def condProdMix (w : ℝ) (ν μ : Fin d → ℝ) (R0 R1 : Y → ℝ) : Cube d × Y → ℝ :=
  fun p => (1 - w) * prodLaw ν p.1 * R0 p.2 + w * prodLaw μ p.1 * R1 p.2

/-- The expectation `E_R e = Σ_y e(y) R(y)`. -/
def testMean (R : Y → ℝ) (e : Y → ℝ) : ℝ := ∑ y, e y * R y

/-- `P_e(x) = Σ_y e(y) P_AB(x, y)`. -/
def testedMass (PAB : Cube d × Y → ℝ) (e : Y → ℝ) : Cube d → ℝ :=
  fun x => ∑ y, e y * PAB (x, y)

/-- The signed unmixing `N_0 = (b P_A − P_e)/(b − a)`. -/
def unmixN0 (PAB : Cube d × Y → ℝ) (e : Y → ℝ) (a b : ℝ) : Cube d → ℝ :=
  fun x => (b * marginalA PAB x - testedMass PAB e x) / (b - a)

/-- The signed unmixing `N_1 = (P_e − a P_A)/(b − a)`. -/
def unmixN1 (PAB : Cube d × Y → ℝ) (e : Y → ℝ) (a b : ℝ) : Cube d → ℝ :=
  fun x => (testedMass PAB e x - a * marginalA PAB x) / (b - a)

/-- The signed total mass `w′ = N_1({0,1}^d)`. -/
def wPrime (PAB : Cube d × Y → ℝ) (e : Y → ℝ) (a b : ℝ) : ℝ := ∑ x, unmixN1 PAB e a b x

/-- Every parent prefix mass `N[x_{≤t}]`, `0 ≤ t < d`, is positive. -/
def parentsPos (N : Cube d → ℝ) (x : Cube d) : Prop := ∀ t : ℕ, t < d → 0 < prefMass N x t

/-- The raw conditional profile `(N[x_{<i}1] / N[x_{<i}])_{i}` of a signed measure along `x`. -/
def rawProfile (N : Cube d → ℝ) (x : Cube d) : Fin d → ℝ := fun i => condOne N x i

/-- The analytic construction of Theorem D.2 on the path `x`. -/
def weakViewEstimate (α : ℝ) (PAB : Cube d × Y → ℝ) (e : Y → ℝ) (a b : ℝ) (x : Cube d) :
    Cube d → ℝ :=
  if 0 < wPrime PAB e a b ∧ wPrime PAB e a b < 1 ∧
      parentsPos (unmixN0 PAB e a b) x ∧ parentsPos (unmixN1 PAB e a b) x then
    restore α (wPrime PAB e a b) (rawProfile (unmixN0 PAB e a b) x)
      (rawProfile (unmixN1 PAB e a b) x)
  else uniformLaw d

/-- Corollary D.3's clipped component profile of `N` on the path `x`, with the uniform mean vector
as fallback. -/
def indivProfile (α : ℝ) (N : Cube d → ℝ) (x : Cube d) : Fin d → ℝ :=
  if parentsPos N x then clipBox α (rawProfile N x) else fun _ => 1 / 2

end PrefixMixLearn.Proper


