-- Prove2me | Definitions.Def_GoodQLTC_FamilyHyp
-- name    : GoodQLTC_FamilyHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:52:04.746312+00:00
-- url     : https://prove2.me/theorems/0c43823f-ade5-490d-bff1-7b10ad972207
-- title:
--   Hypotheses (1)–(3) of Theorem 4.12 on a family $\{(X_\nu,\mathcal F_\nu)\}$
-- statement:
--   A family $\{(X_\nu,\mathcal F_\nu)\}_\nu$ over one field $F$ satisfies:
--   1. each $X_\nu$ is a regular, $\lambda$-expanding $t$-dimensional cubical complex with degrees $\{n_i\}$, and $|X_\nu(0)|\to\infty$;
--   2. each $\mathcal F_\nu$ is an $F$-cosheaf equipped with compatible base codes of dimensions $\{m_{i,b}\}$;
--   3. for every $\nu$, every $f\in X_\nu$ and every nonempty $I\subseteq\mathrm{codir}(f)$, both $\{C_{f,i}\}_{i\in I}$ and $\{C^{\perp}_{f,i}\}_{i\in I}$ are universally $\rho$-product-expanding.
--
--   **Formalization Note** The family is indexed by $\nu\in\mathbb N$; the numerical side conditions of Theorem 4.12 are stated in the theorems that use this predicate, so Theorems 4.12 and 4.13 refer to the same hypotheses.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 4.12 (1)–(3), p.19 (PDF p.22)

import Mathlib
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_Face
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_IsExpanding
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_GoodQLTC_BaseCodeData

namespace GoodQLTC

universe u

/-- The **family hypotheses (1)–(3) of Theorem 4.12**, Gay–Jeronimo, arXiv:2609.20780 (held
version), p.19, for a family `{(X_ν, F_ν)}_ν` over one field `F`, with degrees `{n_i}`, endpoint
dimensions `{m_{i,b}}`, and constants `ρ`, `λ`:
1. each `X_ν` is a regular, `λ`-expanding `t`-dimensional cubical complex with degrees `{n_i}`,
   and `|X_ν(0)| → ∞`;
2. each `F_ν` is an `F`-cosheaf equipped with compatible base codes of dimensions `{m_{i,b}}`
   (the data `D ν`);
3. for every `ν`, every `f ∈ X_ν` and every nonempty `I ⊆ codir(f)`, both `{C_{f,i}}_{i∈I}` and
   `{C^⊥_{f,i}}_{i∈I}` are universally `ρ`-product-expanding.

**Formalization Note.** The family is indexed by `ν ∈ ℕ` (the paper's `ν ≥ 1`). The numerical side
conditions of Theorem 4.12 (`t ≥ 4`, `2 ≤ n_1 ≤ ⋯ ≤ n_t`, `0 < m_{i,b} < n_i`, `n_t/n_1 ≤ τ`,
`0 ≤ λ ≤ λ_0`, `|F| = 2^s`) are stated separately in the theorems. Universal product expansion
quantifies over extensions in the universe `u` (a parameter). -/
def FamilyHyp (t : ℕ) (n : Fin t → ℕ) (m : Fin t → Bool → ℕ) (ρ lam : ℝ) {F : Type} [Field F]
    (X : ℕ → Type) [∀ ν, PartialOrder (X ν)] [∀ ν, Fintype (X ν)]
    (φ : ∀ ν, X ν → Fin t → Option Bool) (Fs : ∀ ν, Cosheaf (X ν) F)
    (D : ∀ ν, BaseCodeData (φ ν) (Fs ν) m) : Prop :=
  (∀ ν, IsCubicalComplex t (φ ν) ∧ IsRegular (φ ν) n ∧ IsExpanding (φ ν) n lam) ∧
  Filter.Tendsto (fun ν => numFaces (φ ν) 0) Filter.atTop Filter.atTop ∧
  (∀ ν, IsCompatible (D ν)) ∧
  (∀ ν (f : X ν) (I : Finset (Fin t)), I.Nonempty → I ⊆ codir (φ ν) f →
    IsUnivProductExpanding.{u} ρ (fun i : I => localCode (D ν) f i.1) ∧
    IsUnivProductExpanding.{u} ρ (fun i : I => dualCode (localCode (D ν) f i.1)))

end GoodQLTC


