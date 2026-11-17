-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_IsLinearAMDP
-- name    : IntroDelayAMDP_Supplement_IsLinearAMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:44:59.040939+00:00
-- url     : https://prove2.me/theorems/15fbdc42-843b-4277-b3b7-983b31d617bd
-- title:
--   Linear AMDP (Definition 2.1) on a general measurable state space
-- statement:
--   A **linear AMDP** with feature dimension $d$ and horizon $H$ consists of a layered measurable state space $\mathcal S=\mathcal S_0\cup\dots\cup\mathcal S_{H-1}$ (possibly uncountable, $\mathcal S_0=\{s_0\}$), a finite action set $\mathcal A$, transition kernels $P(\cdot\mid s,a)$, known features $\phi(s,a)\in\mathbb R^d$, $d$ finite signed measures $\psi=(\psi_1,\dots,\psi_d)$ and loss vectors $\zeta_{k,h}\in\mathbb R^d$ such that:
--
--   1. the layer map is measurable and each $P(\cdot\mid\cdot,a)$ is a Markov kernel; for $s\in\mathcal S_h$ with $h<H-1$, $P(\cdot\mid s,a)$ is carried by $\mathcal S_{h+1}$;
--   2. each $\phi(\cdot,a)$ is measurable and $\|\phi(s,a)\|_2\le1$;
--   3. for $s\in\mathcal S_h$, $0\le h<H-1$, and every measurable $B\subseteq\mathcal S_{h+1}$,
--   $$P(B\mid s,a)=\langle\phi(s,a),\psi(B)\rangle=\sum_{i=1}^d\phi_i(s,a)\,\psi_i(B);$$
--   4. $\bigl\|\bigl(|\psi_i|(\mathcal S_{h+1})\bigr)_{i=1}^d\bigr\|_2\le\sqrt d$ for every $h<H-1$, where $|\psi_i|$ is the total variation of $\psi_i$;
--   5. for the episodes $k\le K$: $\|\zeta_{k,h}\|_2\le\sqrt d$, $\ell_k(s,a)=\langle\phi(s,a),\zeta_{k,h}\rangle$ for $s\in\mathcal S_h$, and $\ell_k(s,a)\in[0,1]$.
--
--   This is the model of Theorems 4.1 and 5.2: transitions and losses are linear in known features, and the state space can be infinite.
--
--
--   **Formalization Note** The norm bounds are written squared. One family $\psi$ of signed measures on the whole space serves all layers (its restriction to $\mathcal S_{h+1}$ is the page's $\psi$ of that layer). There is no terminal layer, as in the base mission's `LayeredSpace`. Measurability of the layer map and of the features is the standing convention of the field. Episodes are $0$-based.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Definition 2.1, p.13; Section 2.1, p.12

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace

namespace IntroDelayAMDP.Supplement

open MeasureTheory ProbabilityTheory

/-- **Linear AMDP** (Definition 2.1, printed p.13, PDF p.15; Section 2.1, printed p.12, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).
Printed p.13: "every state-action pair `(s, a)` has a known feature `ϕ(s, a) ∈ ℝ^d` with `‖ϕ(s, a)‖₂ ≤ 1`.
There is an unknown mapping `ψ : S → ℝ^d` for the transitions, and `K × H` vectors `ζ_{k,h} ∈ ℝ^d` for
the losses … such that `P(s′ | s, a) = ⟨ϕ(s, a), ψ(s′)⟩` for `s ∈ S_h, a ∈ A, s′ ∈ S_{h+1}, 0 ≤ h < H − 1`,
`ℓ_k(s, a) = ⟨ϕ(s, a), ζ_{k,h}⟩` for `s ∈ S_h, a ∈ A, k ∈ [K], 0 ≤ h < H`. … `‖∑_{s′∈S_{h+1}} |ψ(s′)|‖₂ ≤ √d`
and `‖ζ_{k,h}‖₂ ≤ √d`. When `S` is uncountable, `P(· | s, a)` is a probability measure … `ψ = (ψ₁, …, ψ_d)`
consists of `d` signed measures over `S_{h+1}` … such that `P(B | s, a) = ⟨ϕ(s, a), ψ(B)⟩` for every
measurable `B ⊆ S_{h+1}` … and `∑_{s′}|ψ(s′)|` becomes the vector of total variations `(|ψ_i|(S_{h+1}))_i`."

`IsLinearAMDP L P φ ψ ζ ℓ K` says, for the layered (possibly uncountable) measurable state space `L`, the
transition kernels `P a : X → Measure X` (`P a s = P(· | s, a)`), the features `φ`, the signed measures
`ψ i`, the loss vectors `ζ k h` and the losses `ℓ k` of the 0-based episodes `k < K`:
1. the layer map is measurable and every `P a` is a Markov kernel;
2. for `s ∈ S_h` with `h + 1 < H`, `P(· | s, a)` is carried by `S_{h+1}`;
3. every `φ(·, a)` is measurable and `‖φ(s, a)‖₂² ≤ 1`;
4. `P(B | s, a) = ∑_i φ_i(s, a) ψ_i(B)` for every measurable `B ⊆ S_{h+1}`, `s ∈ S_h`, `h + 1 < H`;
5. `∑_i (|ψ_i|(S_{h+1}))² ≤ d` for every `h + 1 < H` (`|ψ_i|` the total variation);
6. `‖ζ_{k,h}‖₂² ≤ d`, `ℓ_k(s, a) = ⟨φ(s, a), ζ_{k,layer(s)}⟩` and `ℓ_k(s, a) ∈ [0, 1]` (Section 2.1).

**Formalization Note.** The norms are written squared (`‖x‖₂ ≤ √d ⟺ ∑ xᵢ² ≤ d`). One family of `d` finite
signed measures on `X` serves all layers; restricted to `S_{h+1}` it is the page's `ψ` of layer `h + 1`
(per-layer signed measures on the disjoint measurable layers glue into one). There is no terminal layer
`S_H` (as in `LayeredSpace`): the kernel of a last-layer pair is not constrained and never used.
Measurability of the layer map and of `φ(·, a)` is the field's standing convention (features and losses
enter integrals through `V^π`). Episodes are 0-based. -/
def IsLinearAMDP {X A : Type} [MeasurableSpace X] [Fintype A] {d H : ℕ} (L : LayeredSpace X H)
    (P : A → Kernel X X) (φ : X → A → Fin d → ℝ) (ψ : Fin d → SignedMeasure X)
    (ζ : ℕ → ℕ → Fin d → ℝ) (ℓ : ℕ → X → A → ℝ) (K : ℕ) : Prop :=
  Measurable L.layer ∧ (∀ a, IsMarkovKernel (P a)) ∧
  (∀ s a, L.layer s + 1 < H → P a s {x | L.layer x = L.layer s + 1} = 1) ∧
  (∀ a, Measurable fun s => φ s a) ∧ (∀ s a, φ s a ⬝ᵥ φ s a ≤ 1) ∧
  (∀ s a, L.layer s + 1 < H → ∀ B : Set X, MeasurableSet B → B ⊆ {x | L.layer x = L.layer s + 1} →
      (P a s B).toReal = ∑ i, φ s a i * ψ i B) ∧
  (∀ h, h + 1 < H → ∑ i, (((ψ i).totalVariation {x | L.layer x = h + 1}).toReal) ^ 2 ≤ d) ∧
  (∀ k < K, ∀ h < H, ζ k h ⬝ᵥ ζ k h ≤ d) ∧
  (∀ k < K, ∀ s a, ℓ k s a = φ s a ⬝ᵥ ζ k (L.layer s)) ∧
  (∀ k < K, ∀ s a, 0 ≤ ℓ k s a ∧ ℓ k s a ≤ 1)

end IntroDelayAMDP.Supplement


