-- Prove2me | Definitions.Def_PDSEquiv_Embed
-- name    : PDSEquiv_Embed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:39.108955+00:00
-- url     : https://prove2.me/theorems/b98e44c5-1b9d-4d97-b00a-1b42fb64808e
-- title:
--   The embedding $\mathrm{Embed}_{n,N}$ and the operator $T_{n,N}$
-- statement:
--   For $1\le n\le N$ and a graph $H$ on $[n]$, $X=\mathrm{Embed}_{n,N}(H)$ is the random graph on $[N]$ obtained by choosing a uniformly random injection $\phi:[n]\to[N]$, setting $X_{\phi(i)\phi(j)}=H_{ij}$, and drawing every other pair independently from $\mathrm{Ber}(q)$. The embedding operator is
--   $$(T_{n,N}f)(H)=\mathbb E\bigl[f(\mathrm{Embed}_{n,N}(H))\bigr],$$
--   the expectation being over the injection and the fresh pairs.
--
--   It maps $\mathrm{ER}(n,q)$ to $\mathrm{ER}(N,q)$ and $\mathrm{PDS}(n,k,p,q)$ to $\mathrm{PDS}(N,k,p,q)$, and is the tool of Lemma 5.4.
--
--   **Formalization Note** The expectation is a finite average over the injections `Fin n ↪ Fin N` and the graphs on $[N]$ that agree with $H$ on the image.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), §5.2, p.15

import Mathlib
import Definitions.Def_PDSEquiv_Laws

set_option autoImplicit false

namespace PDSEquiv

noncomputable section

/-!
# The embedding `Embed_{n,N}` and the operator `T_{n,N}`

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), §5.2, p.15.

**Formalization Note.** `X = Embed_{n,N}(H)` has a uniform injection `φ : [n] → [N]`,
`X_{φ(i)φ(j)} = H_{ij}`, and every other pair a fresh `Ber(q)`. The operator is the finite average
of this. `T_{n,N}` of a function on graphs needs no quotient for `0 < q < 1`.
-/

/-- A pair of `[N]` lies inside the image of `φ`. -/
def inImage {n N : ℕ} (φ : Fin n ↪ Fin N) (e : Pair N) : Prop :=
  e.1.1 ∈ Set.range φ ∧ e.1.2 ∈ Set.range φ

open Classical in
/-- The conditional mass of `X` given `φ` and `H`: copied on the image of `φ`, `Ber(q)` elsewhere. -/
def embedMass {n N : ℕ} (q : ℝ) (φ : Fin n ↪ Fin N) (H : Graph n) (X : Graph N) : ℝ :=
  (if comap φ X = H then 1 else 0) *
    ∏ e ∈ Finset.univ.filter (fun e : Pair N => ¬ inImage φ e), ber q (X e)

/-- `(T_{n,N} f)(H) = E[f(Embed_{n,N}(H))]`, over the injection and the fresh indicators, p.15. -/
def embedT {n N : ℕ} (q : ℝ) (f : Graph N → ℝ) (H : Graph n) : ℝ :=
  (Fintype.card (Fin n ↪ Fin N) : ℝ)⁻¹ * ∑ φ : Fin n ↪ Fin N, ∑ X, embedMass q φ H X * f X

end

end PDSEquiv


