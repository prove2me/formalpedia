-- Prove2me | Definitions.Def_GoodQLTC_IsCubicalComplex
-- name    : GoodQLTC_IsCubicalComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:36.156355+00:00
-- url     : https://prove2.me/theorems/8d6f8e17-f48f-4f0d-aa0b-dbfee8f28941
-- title:
--   $t$-dimensional cubical complex (Definition 4.1)
-- statement:
--   A **$t$-dimensional cubical complex** is a finite poset $X$ and a map $\phi:X\to C_t$ whose image contains the all-$\star$ word, such that
--   1. for every $f\in X$, the restriction $\phi|_{X_{\le f}}:X_{\le f}\to(C_t)_{\le\phi(f)}$ is a poset isomorphism;
--   2. for every $f,g\in X$, either $X_{\le f}\cap X_{\le g}=\emptyset$ or $X_{\le f}\cap X_{\le g}=X_{\le h}$ for some $h\in X$.
--
--   These are the complexes whose cochains carry the quantum code.
--
--   **Formalization Note** Condition 1 is split into: $\phi$ maps $X_{\le f}$ into $(C_t)_{\le\phi(f)}$, reflects and preserves the order there, and is onto. The single cube $C_t$ itself satisfies the definition (proved in the sanity file).
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Definition 4.1, p.15 (PDF p.18)

import Mathlib
import Definitions.Def_GoodQLTC_dir

namespace GoodQLTC

/-- A **`t`-dimensional cubical complex**, Gay–Jeronimo, arXiv:2609.20780 (held version),
Definition 4.1, p.15: a finite poset `X` and a map `ϕ : X → C_t` whose image contains the word
with every coordinate `⋆`, such that
1. for every `f`, the restriction `ϕ|X_{≤f} : X_{≤f} → (C_t)_{≤ϕ(f)}` is a poset isomorphism;
2. for every `f, g`, either `X_{≤f} ∩ X_{≤g} = ∅` or `X_{≤f} ∩ X_{≤g} = X_{≤h}` for some `h`.

**Formalization Note.** `X` carries `[PartialOrder X] [Fintype X]`. Condition (1) is split into:
`ϕ` maps `X_{≤f}` into `(C_t)_{≤ϕ(f)}` (`lower_mono`), is an order embedding there
(`lower_iff`, which gives injectivity by antisymmetry), and is onto `(C_t)_{≤ϕ(f)}`
(`lower_surj`). -/
structure IsCubicalComplex (t : ℕ) {X : Type} [PartialOrder X] [Fintype X]
    (φ : X → Fin t → Option Bool) : Prop where
  top : ∃ f, φ f = fun _ => none
  lower_mono : ∀ f g : X, g ≤ f → cubeLe (φ g) (φ f)
  lower_iff : ∀ f g h : X, g ≤ f → h ≤ f → (g ≤ h ↔ cubeLe (φ g) (φ h))
  lower_surj : ∀ (f : X) (c : Fin t → Option Bool), cubeLe c (φ f) → ∃ g, g ≤ f ∧ φ g = c
  inter : ∀ f g : X, (∀ h, ¬ (h ≤ f ∧ h ≤ g)) ∨ ∃ h, ∀ y, (y ≤ f ∧ y ≤ g ↔ y ≤ h)

end GoodQLTC


