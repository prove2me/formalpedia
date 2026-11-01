-- Prove2me | Definitions.Def_WildeQIT_Covering_fakeState
-- name    : WildeQIT_Covering_fakeState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:49.401075+00:00
-- url     : https://prove2.me/theorems/75bcd88e-977a-4fa6-86ad-8ca0ad1bcc9b
-- title:
--   Fake expected density operator $\sigma(\mathcal C)=\frac1{|\mathcal M|}\sum_m\sigma_{c_m}$
-- statement:
--   Let $\{\sigma_x\}_{x\in\mathcal X}$ be the states of an ensemble and let $\mathcal C=\{c_m\}_{m\in\mathcal M}$ be a code, that is, a family of codewords $c_m\in\mathcal X$ indexed by a finite set $\mathcal M$ (codewords may repeat). The **fake ensemble** $\{1/|\mathcal M|,\sigma_{c_m}\}_{m\in\mathcal M}$ picks the state $\sigma_{c_m}$ with the uniform probability $1/|\mathcal M|$, and its **fake expected density operator** is
--
--   $$\sigma(\mathcal C)\equiv\frac1{|\mathcal M|}\sum_{m\in\mathcal M}\sigma_{c_m}.$$
--
--   For a subset $S\subseteq\mathcal X$ (Definition 17.2.2) this is $\sigma(S)=\frac1{|S|}\sum_{s\in S}\sigma_s$, the case $\mathcal M=S$, $c_s=s$.
--
--   **Formalization Note** The code is a map $c:\mathcal M\to\mathcal X$ on a finite type. For an empty $\mathcal M$ Lean's convention $0^{-1}=0$ gives the zero operator; the book does not consider that case.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 17.2.2 (Fake Ensemble), eq. (17.9), p. 506, and eq. (17.65), p. 513

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 17.2.2
(Fake Ensemble), eq. (17.9), p. 506, and the code version, eq. (17.65), p. 513.
-/

open Matrix

namespace WildeQIT.Covering

/-- **Fake expected density operator** (Wilde, arXiv:1106.1445v8, Definition 17.2.2, eq. (17.9),
p. 506, and eq. (17.65), p. 513). A fake ensemble `{1/|M|, σ_{c_m}}_{m ∈ M}` picks the states
`σ_{c_m}` of the true ensemble at the codewords `c_m ∈ 𝒳`, `m ∈ M`, with the uniform distribution
on `M`. Its fake expected density operator is
`σ(C) ≡ (1/|M|) ∑_{m ∈ M} σ_{c_m}`.

**Formalization Note.** The fake ensemble is indexed by a finite type `M` through a codeword map
`c : M → 𝒳`, so that codewords may repeat, as in the random code of (17.65). The set version of
(17.9), `σ(S) = (1/|S|) ∑_{s ∈ S} σ_s` for `S ⊆ 𝒳`, is the instance `M = S`, `c = Subtype.val`.
Lean's `(0 : ℂ)⁻¹ = 0` gives the value `0` when `M` is empty, a case the book does not consider. -/
noncomputable def fakeState {𝒳 n M : Type} [Fintype M] (σ : 𝒳 → Matrix n n ℂ)
    (c : M → 𝒳) : Matrix n n ℂ :=
  ((Fintype.card M : ℂ))⁻¹ • ∑ m, σ (c m)

end WildeQIT.Covering


