-- Prove2me | Definitions.Def_LeblSCV_Germs_holomorphicGerms
-- name    : LeblSCV_Germs_holomorphicGerms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:29.237918+00:00
-- url     : https://prove2.me/theorems/2645d229-38f8-48d9-a6e5-c30a9115a947
-- title:
--   Definitions 6.1.1–6.1.2 — the ring $\mathcal{O}_p$ of germs of holomorphic functions
-- statement:
--   Let $p \in \mathbb{C}^n$. Two functions defined on open neighborhoods of $p$ are **equivalent** if they agree on some neighborhood of $p$; an equivalence class is a **germ** at $p$, written $(f, p)$. Germs of complex-valued functions form a commutative ring, with $(f,p)(g,p) = (fg, p)$ and $(f,p) + (g,p) = (f+g, p)$.
--
--   The **ring of germs of holomorphic functions** at $p$ is
--   $$ {}_n\mathcal{O}_p = \mathcal{O}_p = \{ (f, p) : f \text{ is holomorphic on some neighborhood of } p \}, $$
--   a subring of the ring of all germs at $p$. It is the basic local object of complex analytic geometry: its algebraic properties (Noetherian, unique factorization) govern the local structure of zero sets of holomorphic functions.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`. Germs are Mathlib's `(𝓝 p).Germ ℂ`, whose ring operations are the book's. `holomorphicGerms n p` is the subring of germs having a representative $f$ that is complex-differentiable (`DifferentiableAt ℂ`) at every point of some neighborhood of $p$; this is the same as being holomorphic on an open neighborhood of $p$ (Definition 1.1.2 and `DifferentiableOn ℂ` agree on open sets by Proposition 1.1.3 and Theorem 1.2.1). `GermRing n p` is this subring as a type, with the induced commutative ring structure. Germs of arbitrary (non-holomorphic) functions and formal power series are *not* used.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 167–168, Definitions 6.1.1 and 6.1.2

import Mathlib

open Filter Topology

namespace LeblSCV.Germs

/-- Definitions 6.1.1 and 6.1.2 (Lebl, pp. 167–168). A germ at `p` of a function is an
equivalence class of functions defined near `p`, two functions being equivalent when they agree
on some neighborhood of `p`; this is Mathlib's `(𝓝 p).Germ ℂ` (whose ring operations are the
book's: `(f, p)(g, p) = (fg, p)`, `(f, p) + (g, p) = (f + g, p)`). The ring `𝒪_p = ₙ𝒪_p` of germs
at `p ∈ ℂⁿ` of holomorphic functions is the subring of germs having a representative that is
holomorphic on a neighborhood of `p`, i.e. complex-differentiable at every point near `p`
(equivalently, holomorphic on an open neighborhood of `p`). -/
def holomorphicGerms (n : ℕ) (p : Fin n → ℂ) : Subring ((𝓝 p).Germ ℂ) where
  carrier := {g | ∃ f : (Fin n → ℂ) → ℂ,
    (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) ∧ ((f : (𝓝 p).Germ ℂ) = g)}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, (hf.and hg).mono fun z h => h.1.mul h.2, rfl⟩
  one_mem' := ⟨1, Eventually.of_forall fun _ => differentiableAt_const _, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, (hf.and hg).mono fun z h => h.1.add h.2, rfl⟩
  zero_mem' := ⟨0, Eventually.of_forall fun _ => differentiableAt_const _, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.mono fun z h => h.neg, rfl⟩

/-- Definition 6.1.2 (Lebl, p. 168). `GermRing n p` is the ring `ₙ𝒪_p = 𝒪_p` of germs at
`p ∈ ℂⁿ` of holomorphic functions, with the ring structure inherited from `(𝓝 p).Germ ℂ`. -/
abbrev GermRing (n : ℕ) (p : Fin n → ℂ) : Type := holomorphicGerms n p

end LeblSCV.Germs


