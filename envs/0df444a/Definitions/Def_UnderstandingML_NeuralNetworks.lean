-- Prove2me | Definitions.Def_UnderstandingML_NeuralNetworks
-- name    : UnderstandingML_NeuralNetworks
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T04:59:37.031986+00:00
-- url     : https://prove2.me/theorems/8359c1ee-facf-4c7c-bbd5-1b8192797168
-- title:
--   Chapter 20: layered feedforward networks, the forward computation, H_{V,E,σ} (20.1), the sign class, growth functions with finite codomain, the squared loss and the backward pass
-- statement:
--   Chapter 20 of Shalev-Shwartz and Ben-David. A **layered graph** (`LayeredGraph`) has depth $T$, layer sizes $|V_t|$ and, for each $t < T$, the set of edges $(v_{t,j}, v_{t+1,i})$ between $V_t$ and $V_{t+1}$; `size` is $|V|$, `numEdges` is $|E|$, `LayeredGraph.full` is the fully connected graph. Activations: `signAct` ($\operatorname{sign}$, with $\operatorname{sign}(0) = -1$) and `sigmoid` ($1/(1+e^{-a})$). `inputLayer x` is $o_{0,\cdot}$: $x_1, \dots, x_n$ and the constant neuron $1$. `netOutput σ G w o₀ t` are the outputs $o_{t,\cdot}$ computed layer by layer, $o_{t+1,i} = \sigma(a_{t+1,i})$ with $a_{t+1,i} = \sum_{j : (v_{t,j}, v_{t+1,i}) \in E} w_{t,i,j}\, o_{t,j}$ (`netInput σ G w o₀ t i`). `netClass σ n G` is $H_{V,E,\sigma}$ (20.1), the vector-valued predictors over all weight functions; `signNetClass n G` is $H_{V,E,\operatorname{sign}}$ with a single output neuron, as $\{0,1\}$-valued predictors ($1$ iff the input to the output neuron is positive). **Growth functions with finite codomain (p. 275):** `restrictionY H C` is $H_C$ and `growthY H m` $= \max_{|C| \le m}|H_C|$; `productClass F₁ F₂` $= F_1 \times F_2$ and `compositionClass F₂ F₁` $= F_2 \circ F_1$ (Exercises 3-4). **Backpropagation (§20.6):** `netLoss` is $\tfrac12\|o_T - y\|^2$; `backDelta σ G w x y t` is $\delta_t$ from the backward pass $\delta_T = o_T - y$, $\delta_t = \delta_{t+1}\operatorname{diag}(\sigma'(a_{t+1}))W_t$; `updateWeight w t i j s` replaces the weight of the edge $(v_{t,j}, v_{t+1,i})$ by $s$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.1 pp. 269-270 (layered graphs, activation functions, forward computation), §20.2 p. 270 (Equation (20.1)), §20.4 p. 275 (growth functions with finite codomain), §20.6 pp. 277-281 (squared loss, backpropagation), §20.9 p. 282 (Exercises 3-4)

import Definitions.Def_UnderstandingML_VC
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 20: neural networks

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §20.1–§20.6.

**Layered feedforward networks (§20.1, pp. 269–270).** A directed acyclic graph `G = (V, E)`
organized in layers `V = V₀ ∪ … ∪ V_T`, every edge joining some `V_{t−1}` to `V_t`, with a
weight function `w : E → ℝ` and an activation `σ : ℝ → ℝ` (the sign function, the threshold
function `𝟙[a > 0]`, or the sigmoid `1/(1 + e^{−a})`). The input layer `V₀` has `n + 1` neurons,
`o_{0,i}(x) = xᵢ` for `i ∈ [n]` and the constant neuron `o_{0,n+1}(x) = 1`. Layer by layer,
`a_{t+1,j}(x) = ∑_{r : (v_{t,r}, v_{t+1,j}) ∈ E} w((v_{t,r}, v_{t+1,j})) o_{t,r}(x)` and
`o_{t+1,j}(x) = σ(a_{t+1,j}(x))`. `T` is the depth, `|V|` the size, `max_t |V_t|` the width.

**The hypothesis class (20.1).** `H_{V,E,σ} = {h_{V,E,σ,w} : w : E → ℝ}`; for binary
classification the output layer is a single neuron and `σ` is the sign function.

**Growth functions with a finite codomain (p. 275, Exercises 3–4).** For a set `H` of functions
from `X` to a finite `Y`, `H_C` is the restriction of `H` to `C` and `τ_H(m) = max_{|C| ≤ m} |H_C|`.

**Backpropagation (§20.6, pp. 278–281).** With `W_t ∈ ℝ^{k_{t+1} × k_t}` the weight matrix between
`V_t` and `V_{t+1}` (phantom edges carry weight `0`), the forward pass computes
`a_t = W_{t−1} o_{t−1}`, `o_t = σ(a_t)`; with the squared loss `Δ(u, y) = ½‖u − y‖²`, the backward
pass sets `δ_T = o_T − y` and `δ_t = δ_{t+1} diag(σ'(a_{t+1})) W_t`, and the partial derivative of
the loss with respect to the weight of the edge `(v_{t−1,j}, v_{t,i})` is `δ_{t,i} σ'(a_{t,i}) o_{t−1,j}`
(20.3).

**Conventions.** Layers and neurons are indexed by natural numbers: `width t = |V_t|` for
`t ≤ depth`, and `(i, j) ∈ edges t` means `(v_{t,j}, v_{t+1,i}) ∈ E`; weights are given for all
index triples and only those on edges are used, so `H_{V,E,σ}` is the image of all weight
functions. The sign activation outputs `±1` with `sign(0) = −1`; the binary classification
class is `Bool`-valued, `true` iff the output neuron's input is positive. A neuron with no
incoming edges outputs `σ(0)`, as in the book. `±1`-valued inputs are encoded by `Bool`,
`true ↦ 1`, `false ↦ −1`.
-/

open MeasureTheory

namespace UnderstandingML

/-! ### Layered graphs and the forward computation -/

/-- A **layered feedforward graph** (§20.1): `depth = T`, `width t = |V_t|` for `t ≤ T`, and
`(i, j) ∈ edges t` iff the edge `(v_{t,j}, v_{t+1,i})` is in `E` (source `j` in `V_t`, target `i`
in `V_{t+1}`). -/
structure LayeredGraph where
  depth : ℕ
  width : ℕ → ℕ
  edges : ℕ → Finset (ℕ × ℕ)
  edges_valid : ∀ t, ∀ e ∈ edges t, e.1 < width (t + 1) ∧ e.2 < width t

namespace LayeredGraph

/-- The **size** `|V|` of the network. -/
def size (G : LayeredGraph) : ℕ := ∑ t ∈ Finset.range (G.depth + 1), G.width t

/-- The number of edges `|E|`. -/
def numEdges (G : LayeredGraph) : ℕ := ∑ t ∈ Finset.range G.depth, (G.edges t).card

/-- The **fully connected** layered graph with layer sizes `k₀, …, k_T` (all edges between
adjacent layers, p. 279: "we can assume, without loss of generality, that all edges exist"). -/
def full (T : ℕ) (k : ℕ → ℕ) : LayeredGraph where
  depth := T
  width := k
  edges := fun t ↦ Finset.range (k (t + 1)) ×ˢ Finset.range (k t)
  edges_valid := by
    intro t e he
    simpa [Finset.mem_product, Finset.mem_range] using he

end LayeredGraph

/-- The **sign activation** `σ(a) = sign(a)`, with `sign(0) = −1`. -/
noncomputable def signAct (a : ℝ) : ℝ := if 0 < a then 1 else -1

/-- The **sigmoid activation** `σ(a) = 1/(1 + exp(−a))`. -/
noncomputable def sigmoid (a : ℝ) : ℝ := 1 / (1 + Real.exp (-a))

/-- The outputs `o_{0,·}` of the input layer on `x ∈ ℝ^n`: `o_{0,i} = xᵢ` for `i < n` and the
constant neuron `1` (p. 269). -/
def inputLayer {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ := fun j ↦ if h : j < n then x ⟨j, h⟩ else 1

/-- The **outputs** `o_{t,j}` of the neurons of layer `t`, computed layer by layer from the
outputs `o₀` of the input layer: `o_{t+1,i} = σ(∑_{j : (i,j) ∈ E_t} w_{t,i,j} o_{t,j})` (p. 269). -/
noncomputable def netOutput (σ : ℝ → ℝ) (G : LayeredGraph) (w : ℕ → ℕ → ℕ → ℝ) (o₀ : ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0 => o₀
  | t + 1 => fun i ↦ σ (∑ j ∈ Finset.range (G.width t),
      (if (i, j) ∈ G.edges t then w t i j else 0) * netOutput σ G w o₀ t j)

/-- The **input** `a_{t+1,i} = ∑_{j : (i,j) ∈ E_t} w_{t,i,j} o_{t,j}` to neuron `i` of layer
`t + 1` (p. 269). -/
noncomputable def netInput (σ : ℝ → ℝ) (G : LayeredGraph) (w : ℕ → ℕ → ℕ → ℝ) (o₀ : ℕ → ℝ)
    (t i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (G.width t), (if (i, j) ∈ G.edges t then w t i j else 0) * netOutput σ G w o₀ t j

/-- The hypothesis class `H_{V,E,σ}` (20.1) as real-vector-valued predictors `ℝ^n → ℝ^{|V_T|}`
(the outputs of the top layer, indexed by `ℕ`). -/
def netClass (σ : ℝ → ℝ) (n : ℕ) (G : LayeredGraph) : Set ((Fin n → ℝ) → ℕ → ℝ) :=
  {h | ∃ w : ℕ → ℕ → ℕ → ℝ, h = fun x ↦ netOutput σ G w (inputLayer x) G.depth}

/-- The binary classification class `H_{V,E,sign}` for a single output neuron (§20.4): the
predictor is `sign(a_{T,1})`, `true` iff the input to the output neuron is positive. -/
noncomputable def signNetClass (n : ℕ) (G : LayeredGraph) : Set ((Fin n → ℝ) → Bool) :=
  {h | ∃ w : ℕ → ℕ → ℕ → ℝ,
    h = fun x ↦ decide (0 < netInput signAct G w (inputLayer x) (G.depth - 1) 0)}

/-! ### Growth functions with a finite codomain -/

section Growth

variable {X Y Z : Type*}

/-- The restriction `H_C` of a set of functions `X → Y` to the finite set `C` (p. 275). -/
def restrictionY (H : Set (X → Y)) (C : Finset X) : Set (C → Y) :=
  {g | ∃ h ∈ H, ∀ c : C, g c = h c}

/-- The **growth function** `τ_H(m) = max_{C ⊆ X, |C| ≤ m} |H_C|` of a set of functions into a
finite set `Y` (p. 275). -/
noncomputable def growthY (H : Set (X → Y)) (m : ℕ) : ℕ :=
  sSup {k | ∃ C : Finset X, C.card ≤ m ∧ (restrictionY H C).ncard = k}

/-- The **Cartesian product class** `F₁ × F₂ = {x ↦ (f₁(x), f₂(x))}` (Exercise 3). -/
def productClass {Y₁ Y₂ : Type*} (F₁ : Set (X → Y₁)) (F₂ : Set (X → Y₂)) :
    Set (X → Y₁ × Y₂) :=
  {h | ∃ f₁ ∈ F₁, ∃ f₂ ∈ F₂, h = fun x ↦ (f₁ x, f₂ x)}

/-- The **composition class** `F₂ ∘ F₁ = {f₂ ∘ f₁}` (Exercise 4). -/
def compositionClass (F₂ : Set (Z → Y)) (F₁ : Set (X → Z)) : Set (X → Y) :=
  {h | ∃ f₁ ∈ F₁, ∃ f₂ ∈ F₂, h = f₂ ∘ f₁}

end Growth

/-! ### Backpropagation -/

/-- The **squared loss** of the network on the example `(x, y)`:
`Δ(h_w(x), y) = ½ ‖o_T − y‖²` (p. 277), summed over the `|V_T|` output neurons. -/
noncomputable def netLoss (σ : ℝ → ℝ) (G : LayeredGraph) (w : ℕ → ℕ → ℕ → ℝ) (x y : ℕ → ℝ) :
    ℝ :=
  (1 / 2) * ∑ i ∈ Finset.range (G.width G.depth), (netOutput σ G w x G.depth i - y i) ^ 2

/-- The **backward pass**, indexed by the distance `s = T − t` from the top: `δ_T = o_T − y` and
`δ_{t,i} = ∑_{j} W_{t,j,i} δ_{t+1,j} σ'(a_{t+1,j})` (pp. 278, 281). -/
noncomputable def backDeltaAux (σ : ℝ → ℝ) (G : LayeredGraph) (w : ℕ → ℕ → ℕ → ℝ)
    (x y : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun i ↦ netOutput σ G w x G.depth i - y i
  | s + 1 => fun i ↦ ∑ j ∈ Finset.range (G.width (G.depth - s)),
      (if (j, i) ∈ G.edges (G.depth - s - 1) then w (G.depth - s - 1) j i else 0) *
        backDeltaAux σ G w x y s j * deriv σ (netInput σ G w x (G.depth - s - 1) j)

/-- `δ_{t,i}`, the gradient of the loss of the subnetwork above layer `t` with respect to the
output `o_{t,i}` (p. 280), computed by the backward pass. -/
noncomputable def backDelta (σ : ℝ → ℝ) (G : LayeredGraph) (w : ℕ → ℕ → ℕ → ℝ) (x y : ℕ → ℝ)
    (t : ℕ) : ℕ → ℝ :=
  backDeltaAux σ G w x y (G.depth - t)

/-- The weight function `w` with the weight of the edge `(v_{t,j}, v_{t+1,i})` replaced by `s`
(all other weights fixed, p. 279). -/
def updateWeight (w : ℕ → ℕ → ℕ → ℝ) (t i j : ℕ) (s : ℝ) : ℕ → ℕ → ℕ → ℝ :=
  fun t' i' j' ↦ if t' = t ∧ i' = i ∧ j' = j then s else w t' i' j'

end UnderstandingML


