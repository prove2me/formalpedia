-- Prove2me | Definitions.Def_LeblSCV_Varieties_holGerms
-- name    : LeblSCV_Varieties_holGerms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:11:33.308453+00:00
-- url     : https://prove2.me/theorems/4a43f98a-f99d-4549-82e5-3589d0e098a9
-- title:
--   Definition 6.1.2 — the ring $\mathcal{O}_p$ of germs of holomorphic functions
-- statement:
--   Let $p \in \mathbb{C}^n$. Two functions defined near $p$ have the same **germ** at $p$ if they agree on some neighborhood of $p$ (Definition 6.1.1); germs of complex-valued functions form a commutative ring under pointwise operations. The ring of germs at $p$ of holomorphic functions is
--   $$\mathcal{O}_p = {}_n\mathcal{O}_p = \{ (f, p) : f \text{ holomorphic on some neighborhood of } p \}.$$
--
--   It is the local ring in which the ideal $I_p(X)$ of a subvariety lives.
--
--   **Formalization Note.** Built as a `Subring` of Mathlib's ring `Filter.Germ (nhds p) ℂ` of all germs of functions $\mathbb{C}^n \to \mathbb{C}$ at $p$: a germ belongs to it if it has a representative that is `DifferentiableOn ℂ` on some open neighborhood of $p$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 168, Definition 6.1.2 (germs of functions: p. 167, Definition 6.1.1)

import Mathlib

namespace LeblSCV.Varieties

open Filter Topology

/-- Lebl, Definition 6.1.2 (with Definition 6.1.1): `𝒪_p`, the ring of germs at `p ∈ ℂⁿ` of
holomorphic functions, as the subring of the ring `Germ (𝓝 p) ℂ` of all germs of functions at `p`
consisting of the germs that have a representative holomorphic (`DifferentiableOn ℂ`) on some
open neighborhood `W` of `p`. -/
def holGerms {n : ℕ} (p : Fin n → ℂ) : Subring (Germ (𝓝 p) ℂ) where
  carrier := {g | ∃ (f : (Fin n → ℂ) → ℂ) (W : Set (Fin n → ℂ)),
    IsOpen W ∧ p ∈ W ∧ DifferentiableOn ℂ f W ∧ g = (f : Germ (𝓝 p) ℂ)}
  mul_mem' := by
    rintro _ _ ⟨f, W, hW, hpW, hf, rfl⟩ ⟨f', W', hW', hpW', hf', rfl⟩
    exact ⟨f * f', W ∩ W', hW.inter hW', ⟨hpW, hpW'⟩,
      (hf.mono Set.inter_subset_left).mul (hf'.mono Set.inter_subset_right), rfl⟩
  one_mem' := ⟨fun _ => 1, Set.univ, isOpen_univ, trivial, differentiableOn_const 1, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, W, hW, hpW, hf, rfl⟩ ⟨f', W', hW', hpW', hf', rfl⟩
    exact ⟨f + f', W ∩ W', hW.inter hW', ⟨hpW, hpW'⟩,
      (hf.mono Set.inter_subset_left).add (hf'.mono Set.inter_subset_right), rfl⟩
  zero_mem' := ⟨fun _ => 0, Set.univ, isOpen_univ, trivial, differentiableOn_const 0, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, W, hW, hpW, hf, rfl⟩
    exact ⟨-f, W, hW, hpW, hf.neg, rfl⟩

end LeblSCV.Varieties


