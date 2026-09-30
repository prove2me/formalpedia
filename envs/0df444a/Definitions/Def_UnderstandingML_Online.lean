-- Prove2me | Definitions.Def_UnderstandingML_Online
-- name    : UnderstandingML_Online
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:08:19.77262+00:00
-- url     : https://prove2.me/theorems/c037f8cf-6dbd-44ab-90e8-58d1402c888f
-- title:
--   Chapter 21: online algorithms and mistake bounds (Definition 21.1), version spaces, Halving, shattered trees and Ldim, SOA, regret, Weighted-Majority, Online Gradient Descent, the online Perceptron
-- statement:
--   Chapter 21 of Shalev-Shwartz and Ben-David. An **online algorithm** (`OnlineAlg X Y`) maps the history of past examples and the current instance to a prediction; `history S t` is the list of the first $t$ examples; `mistakes A S` is $M_A(S)$, the number of rounds with $A(\text{history}, x_t) \ne y_t$; `mistakeBound A H` is $M_A(H) = \sup M_A(S)$ over all sequences labeled by some $h^\star \in H$, and `OnlineLearnable H` asks for a finite mistake bound (Definition 21.1). `versionSpace H hist` is $V_t$; `IsConsistentAlg H A` says $A$ predicts with some hypothesis of the version space (Consistent); `halving H` predicts the majority label of $V_t$, ties to $1$. `ShattersTree H d v` is an $H$-shattered tree of depth $d$ (Definition 21.4), nodes indexed by the path $(y_1, \dots, y_{t-1})$ leading to them (the binary encoding of the book's $i_t = 2^{t-1} + \sum_{j<t} y_j 2^{t-1-j}$); `ldim H` is Littlestone's dimension (Definition 21.5); `soa H` predicts the label whose version space has the larger Littlestone dimension, ties to $1$, where an empty version space ranks below every nonempty one (`ldimBot`, the convention $\operatorname{Ldim}(\emptyset) = -1$). The convention is needed: with $\operatorname{Ldim}(\emptyset) = 0$ the class $H = \{h_0\}$, $h_0 \equiv 0$, ties $0 = 0$, SOA predicts $1$ and errs on every round. **Unrealizable case (§21.2):** `OnlineAlgR X` predicts $p_t \in [0,1]$; `cumLoss A S` $= \sum_t |p_t - y_t|$ and `cumLossHyp h S` $= \sum_t |h(x_t) - y_t|$; `wmWeights η v t` is the Weighted-Majority distribution $w^{(t)}_i \propto \exp(-\eta\sum_{s<t} v_{s,i})$ over $d$ experts. **Online convex optimization (§21.3-21.4):** `ogdIterates H η g` is Online Gradient Descent $w^{(t+1)} = \operatorname{proj}_H(w^{(t)} - \eta\, g_t(w^{(t)}))$ from $w^{(0)} = 0$; `onlinePerceptron x y` is the online Perceptron and `perceptronRounds x y T` its set $M$ of update rounds $y_t\langle w^{(t)}, x_t\rangle \le 0$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.1 pp. 288-292 (Definition 21.1, Consistent, Halving, Definitions 21.4-21.5, SOA), §21.2 pp. 294-296 (regret (21.1), Weighted-Majority), §21.3 p. 300 (Online Gradient Descent), §21.4 p. 303 (Perceptron)

import Definitions.Def_UnderstandingML_SGD

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 21: online learning

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.1–§21.4.

**Online classification (§21.1, p. 288).** On round `t` the learner receives `xₜ ∈ X`, predicts
`pₜ`, and then the correct label `yₜ ∈ {0,1}` is revealed. For an online algorithm `A` and a
sequence `S = (x₁, h⋆(x₁)), …, (x_T, h⋆(x_T))` with `h⋆ ∈ H`, `M_A(S)` is the number of mistakes
of `A` on `S`, and `M_A(H)` is the supremum over all such sequences (Definition 21.1); a bound
`M_A(H) ≤ B < ∞` is a mistake bound, and `H` is online learnable if some `A` has one. The
algorithms **Consistent** (predict with any hypothesis consistent with the past, p. 289),
**Halving** (predict the majority of the version space, ties to `1`, p. 289) and **SOA** (predict
the label whose version space has the larger Littlestone dimension, ties to `1`, p. 292).

**Shattered trees and `Ldim` (Definitions 21.4–21.5, p. 291).** A shattered tree of depth `d` is
a complete binary tree of instances such that for every labeling `(y₁, …, y_d)` some `h ∈ H`
follows it along the path it determines: the node at depth `t` on that path is the book's
`v_{iₜ}`, `iₜ = 2^{t−1} + ∑_{j<t} yⱼ 2^{t−1−j}`, whose binary encoding is the path
`(y₁, …, y_{t−1})`. `Ldim(H)` is the maximal depth of a shattered tree.

**The unrealizable case (§21.2).** Predictions `pₜ ∈ [0,1]`, read as the probability of
predicting `1`; the loss on a round is `|pₜ − yₜ|` and the regret relative to `h` on a sequence
is `∑ₜ |pₜ − yₜ| − ∑ₜ |h(xₜ) − yₜ|` (21.1). **Weighted-Majority (p. 296)** over `d` experts with
costs `vₜ ∈ [0,1]^d`: `w̃⁽¹⁾ = (1, …, 1)`, `w⁽ᵗ⁾ = w̃⁽ᵗ⁾/Zₜ`, `w̃⁽ᵗ⁺¹⁾ᵢ = w̃⁽ᵗ⁾ᵢ e^{−η vₜ,ᵢ}`, and the
cost paid is `⟨w⁽ᵗ⁾, vₜ⟩`; unrolled, `w⁽ᵗ⁾ᵢ ∝ exp(−η ∑_{s<t} v_{s,i})`.

**Online convex optimization (§21.3, p. 300)** and **Online Gradient Descent**: `w⁽¹⁾ = 0`,
`w⁽ᵗ⁺½⁾ = w⁽ᵗ⁾ − η vₜ` with `vₜ ∈ ∂fₜ(w⁽ᵗ⁾)`, `w⁽ᵗ⁺¹⁾ = argmin_{w ∈ H} ‖w − w⁽ᵗ⁺½⁾‖`; regret
`∑ₜ fₜ(w⁽ᵗ⁾) − ∑ₜ fₜ(w⋆)` (21.5). **The online Perceptron (§21.4, p. 303)**: `w⁽¹⁾ = 0`,
`w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ + yₜ xₜ` if `yₜ⟨w⁽ᵗ⁾, xₜ⟩ ≤ 0`, else unchanged.

**Conventions.** An online algorithm is a deterministic map from the history of past examples
and the current instance to a prediction; sequences are `Fin T`-indexed and the history at
round `t` is the list of the first `t` examples. Rounds and iterates are indexed from `0`. The
Perceptron's set `M` is the set of update rounds `yₜ⟨w⁽ᵗ⁾, xₜ⟩ ≤ 0`, which contains every
prediction mistake whatever `sign(0)` is. Projections and subgradients are those of Chapter 14
(`projOnto`, `IsSubgradient`).
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-! ### Online algorithms, mistakes and mistake bounds -/

section Classification

variable {X Y : Type*}

/-- An **online learning algorithm**: from the history of past examples and the current
instance, a prediction (§21.1). -/
abbrev OnlineAlg (X Y : Type*) := List (X × Y) → X → Y

/-- The history available at round `t`: the first `t` examples of the sequence `S`. -/
def history {T : ℕ} (S : Fin T → X × Y) (t : ℕ) : List (X × Y) := (List.ofFn S).take t

/-- `M_A(S)`, the number of prediction mistakes of `A` on the sequence `S` (Definition 21.1). -/
noncomputable def mistakes [DecidableEq Y] (A : OnlineAlg X Y) {T : ℕ} (S : Fin T → X × Y) : ℕ :=
  (Finset.univ.filter (fun t : Fin T ↦ A (history S t) (S t).1 ≠ (S t).2)).card

/-- `M_A(H)`, the supremum of `M_A(S)` over all sequences labeled by some `h⋆ ∈ H`
(Definition 21.1). -/
noncomputable def mistakeBound [DecidableEq Y] (A : OnlineAlg X Y) (H : Set (X → Y)) : ℕ∞ :=
  ⨆ (T : ℕ) (x : Fin T → X) (h : X → Y) (_ : h ∈ H),
    (mistakes A (fun t ↦ (x t, h (x t))) : ℕ∞)

/-- `H` is **online learnable** (Definition 21.1): some algorithm has a finite mistake bound. -/
def OnlineLearnable [DecidableEq Y] (H : Set (X → Y)) : Prop :=
  ∃ A : OnlineAlg X Y, mistakeBound A H < ⊤

/-- The **version space** `Vₜ`: the hypotheses of `H` consistent with the history (p. 289). -/
def versionSpace (H : Set (X → Y)) (hist : List (X × Y)) : Set (X → Y) :=
  {h ∈ H | ∀ e ∈ hist, h e.1 = e.2}

/-- `A` is a **Consistent** algorithm for `H` (p. 289): whenever the version space is nonempty,
its prediction is that of some hypothesis in the version space. -/
def IsConsistentAlg (H : Set (X → Y)) (A : OnlineAlg X Y) : Prop :=
  ∀ (hist : List (X × Y)) (x : X), (versionSpace H hist).Nonempty →
    ∃ h ∈ versionSpace H hist, A hist x = h x

/-- The **Halving** algorithm (p. 289): predict the majority label of the version space, `1` in
case of a tie. -/
noncomputable def halving (H : Set (X → Bool)) : OnlineAlg X Bool := fun hist x ↦
  decide ((versionSpace H hist ∩ {h | h x = false}).ncard ≤
    (versionSpace H hist ∩ {h | h x = true}).ncard)

end Classification

/-! ### Shattered trees, the Littlestone dimension and SOA -/

section Littlestone

variable {X : Type*}

/-- `v` is an **`H`-shattered tree of depth `d`** (Definition 21.4): `v` assigns an instance to
every node, a node being the path `(y₁, …, y_{t−1})` leading to it, and for every labeling
`y ∈ {0,1}^d` some `h ∈ H` has `h(v(y₁, …, y_{t−1})) = yₜ` for all `t ≤ d`. -/
def ShattersTree (H : Set (X → Bool)) (d : ℕ) (v : List Bool → X) : Prop :=
  ∀ y : Fin d → Bool, ∃ h ∈ H, ∀ t : Fin d,
    h (v (List.ofFn (fun j : Fin (t : ℕ) ↦ y ⟨j, lt_trans j.2 t.2⟩))) = y t

/-- **Littlestone's dimension** `Ldim(H)` (Definition 21.5): the maximal depth of a tree
shattered by `H`. -/
noncomputable def ldim (H : Set (X → Bool)) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree H d v), (d : ℕ∞)

open Classical in
/-- `Ldim(H)` with the empty class ranked below every nonempty one (`⊥`, the convention
`Ldim(∅) = −1`). The book's SOA and the proof of Lemma 21.7 need it: in `ℕ∞`, `ldim ∅ = 0`
ties with a nonempty class of dimension `0`. -/
noncomputable def ldimBot (H : Set (X → Bool)) : WithBot ℕ∞ :=
  if H.Nonempty then (ldim H : WithBot ℕ∞) else ⊥

/-- The **Standard Optimal Algorithm (SOA)** (p. 292): predict the label `r` whose version space
`V⁽ʳ⁾ₜ = {h ∈ Vₜ : h(xₜ) = r}` has the larger Littlestone dimension, `1` in case of a tie; an
empty `V⁽ʳ⁾ₜ` ranks below every nonempty one (`ldimBot`). -/
noncomputable def soa (H : Set (X → Bool)) : OnlineAlg X Bool := fun hist x ↦
  decide (ldimBot (versionSpace H hist ∩ {h | h x = false}) ≤
    ldimBot (versionSpace H hist ∩ {h | h x = true}))

end Littlestone

/-! ### The unrealizable case: real-valued predictions and Weighted-Majority -/

section Unrealizable

variable {X : Type*}

/-- An online classification algorithm whose predictions `pₜ ∈ [0,1]` are read as probabilities
of predicting `1` (§21.2). -/
abbrev OnlineAlgR (X : Type*) := List (X × Bool) → X → ℝ

/-- The label `yₜ ∈ {0,1}` as a real number. -/
def labelR (y : Bool) : ℝ := if y then 1 else 0

/-- The cumulative loss `∑ₜ |pₜ − yₜ|` of `A` on the sequence `S` (§21.2). -/
noncomputable def cumLoss (A : OnlineAlgR X) {T : ℕ} (S : Fin T → X × Bool) : ℝ :=
  ∑ t : Fin T, |A (history S t) (S t).1 - labelR (S t).2|

/-- The cumulative loss `∑ₜ |h(xₜ) − yₜ|` of a fixed hypothesis on the sequence. -/
noncomputable def cumLossHyp (h : X → Bool) {T : ℕ} (S : Fin T → X × Bool) : ℝ :=
  ∑ t : Fin T, |labelR (h (S t).1) - labelR (S t).2|

/-- The **Weighted-Majority** distribution `w⁽ᵗ⁾` over `d` experts after the cost vectors
`v₀, …, v_{t−1}` (p. 296): `w⁽ᵗ⁾ᵢ = exp(−η ∑_{s<t} v_{s,i}) / ∑ⱼ exp(−η ∑_{s<t} v_{s,j})`. -/
noncomputable def wmWeights {d : ℕ} (η : ℝ) (v : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i ↦ Real.exp (-η * ∑ s ∈ Finset.range t, v s i) /
    ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, v s j)

end Unrealizable

/-! ### Online convex optimization and the online Perceptron -/

section Convex

variable {d : ℕ}

/-- **Online Gradient Descent** (p. 300) driven by a subgradient selector `g` (`g t w ∈ ∂fₜ(w)`):
`w⁽⁰⁾ = 0`, `w⁽ᵗ⁺¹⁾ = proj_H(w⁽ᵗ⁾ − η g t w⁽ᵗ⁾)`. -/
noncomputable def ogdIterates (H : Set (Vec d)) (η : ℝ) (g : ℕ → Vec d → Vec d) : ℕ → Vec d
  | 0 => 0
  | t + 1 => projOnto H (ogdIterates H η g t - η • g t (ogdIterates H η g t))

/-- The **online Perceptron** (p. 303): `w⁽⁰⁾ = 0` and `w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ + yₜ xₜ` if
`yₜ⟨w⁽ᵗ⁾, xₜ⟩ ≤ 0`, else `w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾`. -/
noncomputable def onlinePerceptron (x : ℕ → Vec d) (y : ℕ → ℝ) : ℕ → Vec d
  | 0 => 0
  | t + 1 => if y t * ⟪onlinePerceptron x y t, x t⟫_ℝ ≤ 0 then
      onlinePerceptron x y t + y t • x t else onlinePerceptron x y t

open Classical in
/-- `M`, the rounds `t < T` on which the Perceptron updates, `yₜ⟨w⁽ᵗ⁾, xₜ⟩ ≤ 0` (p. 303); it
contains every round on which `sign(⟨w⁽ᵗ⁾, xₜ⟩) ≠ yₜ`. -/
noncomputable def perceptronRounds (x : ℕ → Vec d) (y : ℕ → ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t ↦ y t * ⟪onlinePerceptron x y t, x t⟫_ℝ ≤ 0)

end Convex

end UnderstandingML


