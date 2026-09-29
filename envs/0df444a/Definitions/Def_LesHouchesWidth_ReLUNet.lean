-- Prove2me | Definitions.Def_LesHouchesWidth_ReLUNet
-- name    : LesHouchesWidth_ReLUNet
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T21:56:42.013797+00:00
-- url     : https://prove2.me/theorems/eb0662f2-a0af-4490-9714-70b77b66cab0
-- title:
--   Random ReLU networks at a single input (Lecture 5)
-- statement:
--   Random ReLU networks at a single input, following Section 5.3 of the lectures.
--
--   Fix a depth $L$ and widths $n_0,\dots,n_{L+1}$ (a sequence $n:\mathbb N\to\mathbb N$ of which only the first $L+2$ values are used), and a probability measure $\mu$ on $\mathbb R$.
--
--   1. **Weights.** The normalized weights $\widehat W^{(\ell)}_{ij}$, $1\le\ell\le L+1$, $i\le n_\ell$, $j\le n_{\ell-1}$, are i.i.d. with law $\mu$ (`weightLaw`). The actual weights are $W^{(\ell)}_{ij}=(2/n_{\ell-1})^{1/2}\,\widehat W^{(\ell)}_{ij}$ (`weight`). All biases are $0$.
--   2. **Network.** $z^{(1)}=W^{(1)}x$ and $z^{(\ell+1)}=W^{(\ell+1)}\,\mathrm{ReLU}(z^{(\ell)})$ for $1\le\ell\le L$, with $\mathrm{ReLU}(t)=\max(t,0)$ (`netZ`, `output`$=z^{(L+1)}$).
--   3. **Jacobian.** $\partial z^{(L+1)}_q/\partial x_p$ is the derivative of $y\mapsto z^{(L+1)}_q(y)$ at $x$ in direction $e_p$ (`jacobianEntry`).
--   4. **Paths.** $\Gamma=[n_0]\times\cdots\times[n_{L+1}]$ (`NetPath`), and $\Gamma_{p,q}$ is the set of paths from input neuron $p$ to output neuron $q$ (`pathsFromTo`). Along a path, the weight product is $\prod_{\ell=1}^{L+1}W^{(\ell)}_{\gamma(\ell)\gamma(\ell-1)}$ (`pathWeight`) and the activation product is $\prod_{\ell=1}^{L}\mathbf 1\{z^{(\ell)}_{\gamma(\ell)}(x)>0\}$ (`pathActivation`).
--   5. **Dropout model.** The masks $\xi^{(\ell)}_i$, $1\le\ell\le L$, are i.i.d. Bernoulli$(1/2)$ (`maskLaw`), $D^{(\ell)}=\mathrm{diag}(\xi^{(\ell)})$, and the deep linear network with dropout has output $W^{(L+1)}D^{(L)}W^{(L)}\cdots D^{(1)}W^{(1)}x$ (`dropoutOutput`).
--
--   These are the objects in terms of which Proposition 5.2, eq. (123), the exercises of Section 5.4 and the moment computations of Section 5.5 are stated.
--
--   **Formalization Note** The derivative is Mathlib's `fderiv`, which is $0$ where the map is not differentiable. Weights at layer indices beyond $L+1$ and masks beyond layer $L$ are set to harmless placeholder values and are never used.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), pp. 38–40, Sections 5.1–5.3 (weights, network recursion, Definition 2 of paths), Proposition 5.2 (dropout model).

import Mathlib

/-!
# Random ReLU networks at a single input (Les Houches lectures, Lecture 5)

Definitions for the random ReLU network model of Section 5.3 of
Bahri–Hanin–Brossollet–Erba–Keup–Pacelli–Simon,
*Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3.

Widths are a sequence `n : ℕ → ℕ`; only `n 0, …, n (L+1)` are used.
Layer `ℓ + 1` (paper indexing) has weight matrix `W^{(ℓ+1)} ∈ ℝ^{n_{ℓ+1} × n_ℓ}` with
`W^{(ℓ+1)}_{ij} = (2 / n_ℓ)^{1/2} \hat W^{(ℓ+1)}_{ij}`, the `\hat W` i.i.d. with law `μ`,
and all biases are `0`.
-/

namespace LesHouchesWidth

open MeasureTheory

/-- Index set of the normalized weights `\hat W^{(ℓ+1)}_{ij}` of a network of depth `L`
with widths `n 0, …, n (L+1)`: triples `(ℓ, i, j)` with `ℓ ≤ L`, `i < n (ℓ+1)`, `j < n ℓ`. -/
abbrev WeightIndex (n : ℕ → ℕ) (L : ℕ) : Type :=
  Σ ℓ : Fin (L + 1), Fin (n (ℓ.val + 1)) × Fin (n ℓ.val)

/-- A configuration of all normalized weights `\hat W`. -/
abbrev Weights (n : ℕ → ℕ) (L : ℕ) : Type := WeightIndex n L → ℝ

/-- The law of the normalized weights: i.i.d. with common law `μ`. -/
noncomputable def weightLaw (n : ℕ → ℕ) (L : ℕ) (μ : Measure ℝ) : Measure (Weights n L) :=
  Measure.pi fun _ => μ

instance (n : ℕ → ℕ) (L : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (weightLaw n L μ) := by
  unfold weightLaw; infer_instance

/-- The actual weight `W^{(ℓ+1)}_{ij} = (2 / n_ℓ)^{1/2} \hat W^{(ℓ+1)}_{ij}` connecting neuron
`j` of layer `ℓ` to neuron `i` of layer `ℓ + 1` (and `0` for `ℓ > L`, never used). -/
noncomputable def weight {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (ℓ : ℕ)
    (i : Fin (n (ℓ + 1))) (j : Fin (n ℓ)) : ℝ :=
  if h : ℓ < L + 1 then Real.sqrt (2 / (n ℓ : ℝ)) * ω ⟨⟨ℓ, h⟩, (i, j)⟩ else 0

/-- The ReLU nonlinearity `σ(t) = t · 1_{t > 0} = max(t, 0)`. -/
noncomputable def relu (t : ℝ) : ℝ := max t 0

/-- Preactivations in the indexing of Lecture 5: `netZ ω x 0 = x` (the input) and
`netZ ω x (ℓ+1) = z^{(ℓ+1)}(x)`, where `z^{(1)} = W^{(1)} x` and
`z^{(ℓ+1)} = W^{(ℓ+1)} σ(z^{(ℓ)})` for `ℓ ≥ 1` (zero biases, `σ = ReLU`). -/
noncomputable def netZ {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) :
    (ℓ : ℕ) → Fin (n ℓ) → ℝ
  | 0 => x
  | ℓ + 1 => fun i => ∑ j, weight ω ℓ i j * (if ℓ = 0 then netZ ω x ℓ j else relu (netZ ω x ℓ j))

/-- The network output `z^{(L+1)}(x) ∈ ℝ^{n_{L+1}}`. -/
noncomputable def output {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ) :
    Fin (n (L + 1)) → ℝ :=
  netZ ω x (L + 1)

/-- Entry `∂ z^{(L+1)}_q / ∂ x_p` of the input–output Jacobian at the input `x`, defined as the
Fréchet derivative of `y ↦ z^{(L+1)}_q(y)` at `x` applied to the `p`-th basis vector
(Mathlib convention: `0` where the map is not differentiable). -/
noncomputable def jacobianEntry {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ)
    (p : Fin (n 0)) (q : Fin (n (L + 1))) : ℝ :=
  fderiv ℝ (fun y : Fin (n 0) → ℝ => output ω y q) x (Pi.single p 1)

/-- Paths `γ = (γ(0), …, γ(L+1)) ∈ Γ = [n_0] × ⋯ × [n_{L+1}]` through the network. -/
abbrev NetPath (n : ℕ → ℕ) (L : ℕ) : Type := (ℓ : Fin (L + 2)) → Fin (n ℓ.val)

open Classical in
/-- `Γ_{p,q}`: the paths starting at input neuron `p` and ending at output neuron `q`. -/
noncomputable def pathsFromTo (n : ℕ → ℕ) (L : ℕ) (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    Finset (NetPath n L) :=
  Finset.univ.filter fun γ => γ 0 = p ∧ γ (Fin.last (L + 1)) = q

/-- The product of weights along a path: `∏_{ℓ=1}^{L+1} W^{(ℓ)}_γ`, where
`W^{(ℓ)}_γ = W^{(ℓ)}_{γ(ℓ) γ(ℓ-1)}`. -/
noncomputable def pathWeight {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (γ : NetPath n L) : ℝ :=
  ∏ ℓ : Fin (L + 1), weight ω ℓ.val (γ ℓ.succ) (γ ℓ.castSucc)

/-- The ReLU activation pattern along a path at input `x`:
`∏_{ℓ=1}^{L} ξ^{(ℓ)}_{γ;x}` with `ξ^{(ℓ)}_{γ;x} = 1{z^{(ℓ)}_{γ(ℓ)}(x) > 0}`. -/
noncomputable def pathActivation {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L) (x : Fin (n 0) → ℝ)
    (γ : NetPath n L) : ℝ :=
  ∏ ℓ : Fin L, if 0 < netZ ω x (ℓ.val + 1) (γ ⟨ℓ.val + 1, by omega⟩) then 1 else 0

/-- Index set of the dropout masks `ξ^{(ℓ+1)}_i`, `ℓ < L`, `i < n (ℓ+1)` (hidden layers
`1, …, L`). -/
abbrev MaskIndex (n : ℕ → ℕ) (L : ℕ) : Type := Σ ℓ : Fin L, Fin (n (ℓ.val + 1))

/-- The law of the dropout masks: i.i.d. Bernoulli(1/2), i.e. uniform on `Bool`. -/
noncomputable def maskLaw (n : ℕ → ℕ) (L : ℕ) : Measure (MaskIndex n L → Bool) :=
  Measure.pi fun _ => (PMF.uniformOfFintype Bool).toMeasure

/-- The `0/1` value of the dropout mask of neuron `i` in hidden layer `ℓ + 1`
(and `1` for `ℓ ≥ L`, never used). -/
def maskValue {n : ℕ → ℕ} {L : ℕ} (ξ : MaskIndex n L → Bool) (ℓ : ℕ) (i : Fin (n (ℓ + 1))) :
    ℝ :=
  if h : ℓ < L then (if ξ ⟨⟨ℓ, h⟩, i⟩ then 1 else 0) else 1

/-- Hidden states of the deep linear network with dropout:
`v^{(0)} = x`, `v^{(ℓ+1)} = D^{(ℓ+1)} W^{(ℓ+1)} v^{(ℓ)}` with `D^{(ℓ+1)} = diag(ξ^{(ℓ+1)})`. -/
noncomputable def dropoutHidden {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L)
    (ξ : MaskIndex n L → Bool) (x : Fin (n 0) → ℝ) : (ℓ : ℕ) → Fin (n ℓ) → ℝ
  | 0 => x
  | ℓ + 1 => fun i => maskValue ξ ℓ i * ∑ j, weight ω ℓ i j * dropoutHidden ω ξ x ℓ j

/-- Output of the deep linear network with dropout:
`W^{(L+1)} D^{(L)} W^{(L)} ⋯ D^{(1)} W^{(1)} x`. -/
noncomputable def dropoutOutput {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L)
    (ξ : MaskIndex n L → Bool) (x : Fin (n 0) → ℝ) : Fin (n (L + 1)) → ℝ :=
  fun q => ∑ j, weight ω L q j * dropoutHidden ω ξ x L j

end LesHouchesWidth


