-- Prove2me | Definitions.Def_SVFAppt_DilationOrder
-- name    : SVFAppt_DilationOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:17.137913+00:00
-- url     : https://prove2.me/theorems/3658d6b7-4383-4b51-82ed-81bcb67f8c45
-- title:
--   Dilation order $A\le_{\mathrm{dil}}B$ (Definition 2.3)
-- statement:
--   A random variable $A$ is **smaller than $B$ in the dilation order**, written $A\le_{\mathrm{dil}}B$, if the centred variables are ordered in the convex order:
--
--   $$A-\mathbb E A\ \le_{\mathrm{cx}}\ B-\mathbb E B,$$
--
--   that is, $\mathbb E\varphi(A-\mathbb EA)\le\mathbb E\varphi(B-\mathbb EB)$ for every convex $\varphi:\mathbb R\to\mathbb R$ for which the expectations exist. It compares variability around the mean regardless of location; it implies $\operatorname{Var}A\le\operatorname{Var}B$ when the variances exist.
--
--   **Formalization Note** Built on the published convex order `StochasticOrders.Convex.ConvexOrder`, which quantifies over convex $\varphi$ with $\varphi\circ A$ and $\varphi\circ B$ integrable; for integrable $A,B$ this is the paper's definition. The two variables may live on different probability spaces.
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, Definition 2.3, p. 11

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

open MeasureTheory

namespace SVFAppt

/-- **The dilation order `A ⩽dil B` (Definition 2.3).**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, Definition 2.3, p. 11: "If A − EA ⩽cx B − EB, then
A is said to be smaller than B in the dilation order, denoted as A ⩽dil B."

`DilationOrder μ ν A B` holds when the centred variable `A − E_μ A` is smaller in the convex order
(the published `StochasticOrders.Convex.ConvexOrder`) than `B − E_ν B`.

**Formalization Note** `ConvexOrder` asks `E φ(·) ⩽ E φ(·)` for every convex `φ : ℝ → ℝ` for which
both expectations exist as integrable functions; for integrable `A`, `B` this is equivalent to the
paper's "for which the expectations exist". Means are Bochner integrals (junk `0` for a
non-integrable variable); every use in this mission assumes integrability. -/
def DilationOrder {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (A : Ω → ℝ) (B : Ω' → ℝ) : Prop :=
  StochasticOrders.Convex.ConvexOrder μ ν (fun s => A s - ∫ t, A t ∂μ) (fun s => B s - ∫ t, B t ∂ν)

end SVFAppt


