-- Prove2me | Definitions.Def_TestingEstimation_Dense_Objective
-- name    : TestingEstimation_Dense_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:34.37905+00:00
-- url     : https://prove2.me/theorems/2f71d67e-564c-4cfe-ac0a-93ef7c2a0097
-- title:
--   Independent rounding, multilinear objectives, clipping, and correlations
-- statement:
--   For a weighted graph $W$, let $\mathcal G(W)$ have independent Bernoulli edges with probabilities $W(e)$. Its mass on a graph $J$ and the resulting expectation are
--
--   $$p_W(J)=\prod_e W(e)^{J(e)}(1-W(e))^{1-J(e)},\qquad \mathbb E_W g=\sum_J p_W(J)g(J).$$
--
--   Given a rational rejection rule $f$ on $s$ vertices, define $\phi(Y)=\mathbb E[f(\mathcal G(Y))]$ and $\operatorname{rej}(W)=\mathbb E_v\phi(W[v])$, with $v$ uniform among ordered injective $s$-tuples. For an ordinary input graph $G$, define
--
--   $$\operatorname{cost}_G(W)=\mathbb E[d(G,\mathcal G(W))],\quad E_G(W)=\operatorname{cost}_G(W)+2\operatorname{rej}(W),\quad M(G)=\inf_W E_G(W).$$
--
--   The ordinary-graph counterpart minimizes $d(G,J)+2\operatorname{rej}(J)$. Minimum attainment remains a theorem obligation, explicitly included in the relevant statements. Multilinearity means affinity in each edge coordinate separately; affinity on the cube means preservation of all convex mixtures.
--
--   For real pair functions $X,Y$, their inner product is the uniform unordered-pair average $\langle X,Y\rangle=\mathbb E_e X(e)Y(e)$. For a finite test family $T$, set $\|R\|_T=\sup_{A\in T}|\langle R,A\rangle|$. The empty-family extension is zero; the boosting theorem requires $T$ nonempty. Clipping is $\operatorname{clip}(u)=\min\{1,\max\{0,u\}\}$. A sequence of signed tests $B_1,\ldots,B_t$ defines $\operatorname{clip}(G+\gamma\sum_j B_j)$.
--
--   These are actual finite sums, products, cube objectives, and clipping formulas. No rounding identity, comparison with distance, or approximation guarantee is assumed by these definitions.
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), §3 and §§4.1–4.2, pp. 7–9, 11, 13–14 (PDF pages equal printed pages)

import Definitions.Def_TestingEstimation_Dense_GraphModel

noncomputable section

namespace TestingEstimation.Dense
attribute [local instance] Classical.propDecidable

/-- Independent Bernoulli product law, written as its finite real mass function. -/
def roundingMass {n : ℕ} (W : WGraph n) (J : Graph n) : ℝ :=
  ∏ e, if J e then (W e : ℝ) else 1 - (W e : ℝ)

def roundingExpectation {n : ℕ} (W : WGraph n) (g : Graph n → ℝ) : ℝ :=
  ∑ J, roundingMass W J * g J

/-- Affine in each edge separately, on the entire real unit cube. -/
def Multiaffine {n : ℕ} (g : WGraph n → ℝ) : Prop :=
  ∀ (W : WGraph n) (e : Edge n) (p : UnitWeight),
    g (Function.update W e p) =
      (1 - (p : ℝ)) * g (Function.update W e ⟨0, by norm_num⟩) +
      (p : ℝ) * g (Function.update W e ⟨1, by norm_num⟩)

def mix {n : ℕ} (p : UnitWeight) (W Z : WGraph n) : WGraph n := fun e =>
  ⟨(1-(p:ℝ))*(W e:ℝ) + (p:ℝ)*(Z e:ℝ), by
    rcases p.property with ⟨hp0,hp1⟩
    rcases (W e).property with ⟨hw0,hw1⟩
    rcases (Z e).property with ⟨hz0,hz1⟩
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp1) hw0) (mul_nonneg hp0 hz0)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hw1),
        mul_nonneg hp0 (sub_nonneg.mpr hz1)]⟩

def AffineOnCube {n : ℕ} (g : WGraph n → ℝ) : Prop :=
  ∀ (p : UnitWeight) (W Z : WGraph n),
    g (mix p W Z) = (1-(p:ℝ))*g W + (p:ℝ)*g Z

def phi {s : ℕ} (f : Rule s) (Y : WGraph s) : ℝ :=
  roundingExpectation Y (ruleValue f)

def rejection {s n : ℕ} (f : Rule s) (W : WGraph n) : ℝ :=
  mean (fun v : Fin s ↪ Fin n => phi f (inducedW W v))

def inner {n : ℕ} (X Y : PairFunction n) : ℝ := mean (fun e => X e * Y e)

def cost {n : ℕ} (G : Graph n) (W : WGraph n) : ℝ :=
  roundingExpectation W (editDistance G)

def energy {s n : ℕ} (f : Rule s) (G : Graph n) (W : WGraph n) : ℝ :=
  cost G W + 2 * rejection f W

/-- The infimum is the minimum once attainment, a theorem obligation, is established. -/
def minimumEnergy {s n : ℕ} (f : Rule s) (G : Graph n) : ℝ :=
  sInf (Set.range (energy f G))

def graphMinimumEnergy {s n : ℕ} (f : Rule s) (G : Graph n) : ℝ :=
  sInf (Set.range (fun J : Graph n => editDistance G J + 2 * graphRej f J))

def clip (u : ℝ) : UnitWeight :=
  ⟨min 1 (max 0 u), le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

def clipGraph {n : ℕ} (X : PairFunction n) : WGraph n := fun e => clip (X e)

def correlation {n : ℕ} (T : Finset (PairFunction n)) (R : PairFunction n) : ℝ :=
  sSup {x | ∃ A ∈ T, x = |inner R A|}

/-- A sign is encoded by a bit; both signs are present. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

def boosted {n t : ℕ} (G : WGraph n) (γ : ℝ) (B : Fin t → PairFunction n) : WGraph n :=
  clipGraph (fun e => (G e : ℝ) + γ * ∑ j, B j e)

end TestingEstimation.Dense


