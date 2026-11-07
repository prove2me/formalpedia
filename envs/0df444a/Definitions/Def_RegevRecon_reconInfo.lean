-- Prove2me | Definitions.Def_RegevRecon_reconInfo
-- name    : RegevRecon_reconInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:46.17629+00:00
-- url     : https://prove2.me/theorems/549999b0-530e-4758-8ffe-8465896b8884
-- title:
--   The tree broadcast (44), the retained information $I_\ell(\beta)$ and the threshold $\beta_{\mathrm{dyn}}$
-- statement:
--   On the tree of the Tanner graph, the root has $D$ child constraints, every other variable has $D-1$ child constraints and one parent constraint, and every constraint has $k-1$ child variables. Each variable draws its own coefficient tuple from $\Lambda$, with coordinate $0$ on its parent constraint, and each constraint draws a uniform offset $\tau_j$. Starting from a uniform root $X_0$, a constraint $j$ with parent variable $i$ generates its children with probability
--
--   $$
--   K_j(x_{i_1},\dots,x_{i_{k-1}}\mid x_i)=\frac{w_\beta\bigl(B_{ji}x_i+\sum_{h=1}^{k-1}B_{ji_h}x_{i_h}-\tau_j\bigr)}{p^{k-2}c_\beta}\qquad(44),
--   $$
--
--   with independent randomness at different constraints. With $T$ the tree's coefficients and offsets and $X_{\partial T_\ell}$ the symbols at generation $\ell$, the **retained information** is the conditional mutual information $I_\ell(\beta)=I(X_0;X_{\partial T_\ell}\mid T)$ (45), and the **reconstruction threshold** is
--
--   $$
--   \beta_{\mathrm{dyn}}=\inf\{\beta>0:\lim_{\ell\to\infty}I_\ell(\beta)>0\},\qquad\inf\emptyset=\infty\qquad(46).
--   $$
--
--   This module also defines the law of the posterior error vector $z\mapsto\Pr[X=x^*+z/c_0\mid\text{data below}]$ of a variable with $D-1$ child constraints and planted value $x^*$.
--
--   **Formalization Note** The information is in nats, and the base does not affect the threshold. This is the mutual-information definition of the paper, not the recursion form (50), which is a milestone.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §7, Definition 3, (43)–(46), p.18; Figure 3 and (48), p.19; Theorem 4 preamble, p.21

import Mathlib
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

open Finset Filter Topology

/-- **Conditional mutual information of a finite joint law**: for `(X, T, Y) ∼ J`,
`I(X; Y | T) = Σ_{x,t,y} J(x,t,y) log( J(x,t,y) J(t) / (J(x,t) J(t,y)) )` in nats, equal to
`Σ_t Pr(t) I(X; Y | T = t)`; the sum runs over the support of `J`, so `0 log 0 = 0`. -/
noncomputable def condMutualInfo {X T Y : Type*} (J : Law (X × T × Y)) : ℝ :=
  J.sum fun xty w =>
    w * Real.log (w * (J.map (fun a => a.2.1)) xty.2.1 /
      ((J.map (fun a => (a.1, a.2.1))) (xty.1, xty.2.1) * (J.map (fun a => a.2)) xty.2))

variable (p k D : ℕ)

/-- A coefficient tuple of one variable: its coefficients in its `D` constraints; coordinate `0` is
its parent constraint for a non-root variable (Theorem 4, p.21; p.23). -/
abbrev Tuple := Fin D → (ZMod p)ˣ

/-- The known data `T` of the part of the tree below a non-root variable with `ℓ` generations under
it: for each of its `D − 1` child constraints, the offset and, for each of the `k − 1` child variables,
its tuple and the data below it. -/
def VarT : ℕ → Type
  | 0 => Unit
  | ℓ + 1 => Fin (D - 1) → ZMod p × (Fin (k - 1) → Tuple p D × VarT ℓ)

/-- The symbols observed at the boundary below a non-root variable with `ℓ` generations under it. -/
def VarY : ℕ → Type
  | 0 => ZMod p
  | ℓ + 1 => Fin (D - 1) → Fin (k - 1) → VarY ℓ

/-- The known data of the whole tree of depth `ℓ`: the root's tuple and, for `ℓ ≥ 1`, the data of its
`D` child constraints (Figure 3, p.19: "The full-root problem includes all D constraints"). -/
def RootT : ℕ → Type
  | 0 => Tuple p D
  | ℓ + 1 => Tuple p D × (Fin D → ZMod p × (Fin (k - 1) → Tuple p D × VarT p k D ℓ))

/-- The boundary symbols of the whole tree of depth `ℓ`; at `ℓ = 0` the boundary is the root. -/
def RootY : ℕ → Type
  | 0 => ZMod p
  | ℓ + 1 => Fin D → Fin (k - 1) → VarY p k D ℓ

variable {p k D} [Fact p.Prime]

/-- **The broadcast kernel** `K_j(x_{i_1}, …, x_{i_{k−1}} | x_i)`, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), (44), p.18, with parent
coefficient `a = B_{ji}`, child coefficients `b_h = B_{ji_h}` and offset `τ = τ_j`. -/
noncomputable def broadcastKernel (k : ℕ) (S : Finset (ZMod p)) (β : ℝ) (a : ZMod p)
    (b : Fin (k - 1) → ZMod p) (τ x : ZMod p) (xs : Fin (k - 1) → ZMod p) : ℝ :=
  wBeta S β (a * x + ∑ h, b h * xs h - τ) / ((p : ℝ) ^ (k - 2) * cBeta S β)

/-- One constraint of the broadcast with parent value `x` and parent coefficient `a`: a uniform offset
`τ`, independent tuples `c_h ∼ Λ` of the children (coordinate `0` is the coefficient on this constraint),
child values from (44), then the independent continuation `below` at each child. -/
noncomputable def constraintLaw {A Y : Type} (k : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Tuple p D))
    (β : ℝ) (below : Tuple p D → ZMod p → Law (A × Y)) (x a : ZMod p) :
    Law ((ZMod p × (Fin (k - 1) → Tuple p D × A)) × (Fin (k - 1) → Y)) :=
  (Law.uniform (ZMod p)).bind fun τ =>
    (Law.iid (k - 1) (coeffLaw Λ)).bind fun cs =>
      (Law.ofWeights
          (broadcastKernel k S β a (fun h => ((coeff0 (cs h) : (ZMod p)ˣ) : ZMod p)) τ x) id).bind
        fun xs =>
          (Law.indep (k - 1) fun h => below (cs h) (xs h)).map fun r =>
            ((τ, fun h => (cs h, (r h).1)), fun h => (r h).2)

/-- **The broadcast below a non-root variable**, (44), p.18: the law of the known data and the boundary
symbols below a variable with tuple `c` and value `x` and with `ℓ` generations under it. Its child
constraints `t` use the coefficients `c_{t+1}`, and they are independent given `x` (p.18: "using
independent randomness at different constraints"). -/
noncomputable def subtreeLaw (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Tuple p D)) (β : ℝ) :
    (ℓ : ℕ) → Tuple p D → ZMod p → Law (VarT p k D ℓ × VarY p k D ℓ)
  | 0, _, x => Law.dirac ((), x)
  | ℓ + 1, c, x =>
      (Law.indep (D - 1) fun t =>
          constraintLaw k S Λ β (subtreeLaw k D S Λ β ℓ) x ((c (childIdx t) : (ZMod p)ˣ) : ZMod p)).map
        fun r => ((fun t => (r t).1), (fun t => (r t).2))

/-- **The joint law of `(X_0, T, X_{∂T_ℓ})`**, p.18: uniform root `X_0`, root tuple `c ∼ Λ` and, at depth
`ℓ + 1`, its `D` child constraints with coefficients `c_t`. At depth `0` the boundary is the root. -/
noncomputable def reconJoint (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Tuple p D)) (β : ℝ) :
    (ℓ : ℕ) → Law (ZMod p × RootT p k D ℓ × RootY p k D ℓ)
  | 0 => (Law.uniform (ZMod p)).bind fun x => (coeffLaw Λ).map fun c => (x, c, x)
  | ℓ + 1 => (Law.uniform (ZMod p)).bind fun x => (coeffLaw Λ).bind fun c =>
      (Law.indep D fun t =>
          constraintLaw k S Λ β (subtreeLaw k D S Λ β ℓ) x ((c t : (ZMod p)ˣ) : ZMod p)).map
        fun r => (x, (c, fun t => (r t).1), fun t => (r t).2)

/-- **The retained information** `I_ℓ(β) := I(X_0; X_{∂T_ℓ} | T)`, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), Definition 3, (45), p.18, in
nats (the base does not affect the threshold). -/
noncomputable def reconInfo (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Tuple p D)) (β : ℝ)
    (ℓ : ℕ) : ℝ :=
  condMutualInfo (reconJoint k D S Λ β ℓ)

/-- **The reconstruction threshold**, Definition 3, (46), p.18:
`β_dyn := inf {β > 0 : lim_{ℓ→∞} I_ℓ(β) > 0}`, with `inf ∅ = ∞`.

**Formalization Note** This is the mutual-information form (46), the paper's definition, not the
recursion form (50), which is a milestone. In `ℝ≥0∞`, as `inf ∅ = ∞`; "`lim > 0`" is the negation of
convergence to `0`, and the limit exists by milestone `reconstruction_link`. -/
noncomputable def betaDyn (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Tuple p D)) : ENNReal :=
  sInf (ENNReal.ofReal '' {β : ℝ | 0 < β ∧ ¬ Tendsto (reconInfo k D S Λ β) atTop (𝓝 0)})

/-- **The law of the posterior error vector**, p.19, of a variable with `D − 1` child constraints: planted
value `x* ` uniform, `c ∼ Λ`, data `(t, y)` from the broadcast below it; the vector is
`z ↦ Pr[X = x* + z/c_0 | c, t, y]` for the uniform prior on `X`, where `z = c_0 (X − x*)` is the error
coordinate "after rescaling by the coefficient on its parent constraint". -/
noncomputable def posteriorLaw (k D : ℕ) (S : Finset (ZMod p)) (Λ : PMF (Tuple p D)) (β : ℝ)
    (ℓ : ℕ) : Law (Vec p) :=
  (Law.uniform (ZMod p)).bind fun xs => (coeffLaw Λ).bind fun c =>
    (subtreeLaw k D S Λ β ℓ c xs).map fun ty z =>
      subtreeLaw k D S Λ β ℓ c (xs + z * (((coeff0 c)⁻¹ : (ZMod p)ˣ) : ZMod p)) ty /
        ∑ x', subtreeLaw k D S Λ β ℓ c x' ty

end RegevRecon


