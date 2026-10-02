-- Prove2me | Definitions.Def_HunterPDE_Parabolic_HilbertTriple
-- name    : HunterPDE_Parabolic_HilbertTriple
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:16:43.283511+00:00
-- url     : https://prove2.me/theorems/c21772fc-677a-46b7-94de-a09f165a1605
-- title:
--   Definition 6.40 — Hilbert triple 𝒱 ↪ ℋ ↪ 𝒱′
-- statement:
--   A **Hilbert triple** consists of real separable Hilbert spaces $\mathcal{V}$ and $\mathcal{H}$, the dual $\mathcal{V}'$ of $\mathcal{V}$ (with duality pairing $\langle f, v\rangle$, $f \in \mathcal{V}'$, $v \in \mathcal{V}$), and continuous injective linear embeddings
--   $$\mathcal{V} \hookrightarrow \mathcal{H} \hookrightarrow \mathcal{V}'$$
--   such that $\mathcal{V}$ is densely embedded in $\mathcal{H}$, $\mathcal{H}$ is densely embedded in $\mathcal{V}'$, and
--   $$\langle f, v\rangle = (f, v)_{\mathcal{H}} \qquad \text{for every } f \in \mathcal{H},\ v \in \mathcal{V}.$$
--   The model example is $\mathcal{V} = H^1_0(\Omega)$, $\mathcal{H} = L^2(\Omega)$, $\mathcal{V}' = H^{-1}(\Omega)$. A $\mathcal{V}$-valued function is compared with its $\mathcal{V}'$-valued time derivative through the composite embedding $\mathcal{V} \hookrightarrow \mathcal{V}'$.
--
--   **Formalization Note.** The embeddings are the fields `toH : V →L[ℝ] H` and `toDual : H →L[ℝ] StrongDual ℝ V` (not literal inclusions), with injectivity, dense range, separability of `V` and `H`, and the compatibility `toDual f v = ⟪f, toH v⟫`. `toDualV` is the composite `toDual ∘ toH`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 207, Definition 6.40

import Mathlib

namespace HunterPDE.Parabolic

/-- A Hilbert triple `𝒱 ↪ ℋ ↪ 𝒱'` (Hunter, Definition 6.40, p. 207) over the real Hilbert
spaces `𝒱` and `ℋ`, with `𝒱' = StrongDual ℝ 𝒱` the dual of `𝒱` (the duality pairing
`⟨f, v⟩` of `f ∈ 𝒱'` and `v ∈ 𝒱` is the application `f v`). The embeddings are continuous
injective linear maps (not literal inclusions): `toH : 𝒱 → ℋ` and `toDual : ℋ → 𝒱'`, each with
dense range; `𝒱` and `ℋ` are separable; and `⟨f, v⟩ = (f, v)_ℋ` for every `f ∈ ℋ`, `v ∈ 𝒱`,
i.e. `toDual f v = (f, toH v)_ℋ`. (`𝒱'` is separable too, as the dual of a separable Hilbert
space.) -/
structure HilbertTriple (V H : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  /-- The embedding `𝒱 ↪ ℋ`. -/
  toH : V →L[ℝ] H
  /-- The embedding `ℋ ↪ 𝒱'`. -/
  toDual : H →L[ℝ] StrongDual ℝ V
  injective_toH : Function.Injective toH
  injective_toDual : Function.Injective toDual
  /-- `𝒱` is densely embedded in `ℋ`. -/
  denseRange_toH : DenseRange toH
  /-- `ℋ` is densely embedded in `𝒱'`. -/
  denseRange_toDual : DenseRange toDual
  separable_V : TopologicalSpace.SeparableSpace V
  separable_H : TopologicalSpace.SeparableSpace H
  /-- The compatibility `⟨f, v⟩ = (f, v)_ℋ` for `f ∈ ℋ`, `v ∈ 𝒱`. -/
  pairing : ∀ (f : H) (v : V), toDual f v = inner ℝ f (toH v)

/-- The composite embedding `𝒱 ↪ ℋ ↪ 𝒱'` of a Hilbert triple, through which a `𝒱`-valued
function is compared with its `𝒱'`-valued weak time derivative. -/
noncomputable def HilbertTriple.toDualV {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (HT : HilbertTriple V H) : V →L[ℝ] StrongDual ℝ V :=
  HT.toDual.comp HT.toH

end HunterPDE.Parabolic


