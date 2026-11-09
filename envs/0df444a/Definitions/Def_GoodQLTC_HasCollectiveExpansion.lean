-- Prove2me | Definitions.Def_GoodQLTC_HasCollectiveExpansion
-- name    : GoodQLTC_HasCollectiveExpansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:11.983571+00:00
-- url     : https://prove2.me/theorems/fe3fac1e-d740-4935-b98e-5bd8740f1b97
-- title:
--   Collective $\rho$-product expansion over $E$ (Definition 4.6)
-- statement:
--   For an extension $E/F$ and a finite-dimensional $E$-space $R$, put $A^E_i(C_i;R)=R\otimes_EA_i(C_i^E)\subseteq R^{\Omega}$ and $A^E(\{C_i\};R)=\sum_iA^E_i(C_i;R)$. The family has **collective $\rho$-product expansion over $E$** if for every such $R$, every $x\in A^E(\{C_i\};R)$ admits $x_i\in A^E_i(C_i;R)$ with
--   $$
--   x=\sum_ix_i\qquad\text{and}\qquad \rho\sum_in_i\,\ell_i(x_i)\le|x|_b,
--   $$
--   where $|x|_b$ counts the $\omega$ with $x(\omega)\ne0$.
--
--   **Formalization Note** $R\otimes_EA_i$ is realized inside $R^{\Omega}$ as the $E$-span of the arrays $\omega\mapsto a(\omega)r$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.2 and Definition 4.6, pp.16–17 (PDF pp.19–20)

import Mathlib
import Definitions.Def_GoodQLTC_IsProductExpanding

namespace GoodQLTC

universe u v

/-- The space `A_i^E(C_i; R) := R ⊗_E A_i(C_i^E) ⊆ R^Ω` for a finite-dimensional `E`-space `R`,
Gay–Jeronimo, arXiv:2609.20780 (held version), §4.2, p.16. **Formalization Note.** The tensor
product is realized inside `R^Ω` as the `E`-span of the arrays `ω ↦ a(ω) r` with `a ∈ A_i(C_i^E)`
and `r ∈ R`. -/
def coefAxisCode {E : Type u} [Field E] {ι : Type} [DecidableEq ι] {Ω : ι → Type}
    (R : Type v) [AddCommGroup R] [Module E R] (C : ∀ i, Submodule E (Ω i → E)) (i : ι) :
    Submodule E ((∀ i, Ω i) → R) :=
  Submodule.span E {x | ∃ a ∈ axisCode C i, ∃ r : R, x = fun ω => a ω • r}

/-- **Collective `ρ`-product expansion over `E`**, Gay–Jeronimo, arXiv:2609.20780 (held version),
Definition 4.6, p.17: for every finite-dimensional `E`-space `R`, every
`x ∈ A^E({C_i}; R) := ∑_i A_i^E(C_i; R)` admits `x_i ∈ A_i^E(C_i; R)` with `x = ∑_i x_i` and
`ρ ∑_i n_i ℓ_i(x_i) ≤ |x|_b`.

**Formalization Note.** `C_i ⊆ F^{Ω_i}` are codes over `F` and `E` is a field extension of `F`;
`R : Type v` with `v` a universe parameter; `|x|_b` is `supportCard`; `ρ > 0` is part of the
predicate. -/
def HasCollectiveExpansion {F : Type} [Field F] (E : Type u) [Field E] [Algebra F E] {ι : Type}
    [Fintype ι] [DecidableEq ι] {Ω : ι → Type} [∀ i, Fintype (Ω i)] (ρ : ℝ)
    (C : ∀ i, Submodule F (Ω i → F)) : Prop :=
  0 < ρ ∧ ∀ (R : Type v) [AddCommGroup R] [Module E R] [FiniteDimensional E R],
    ∀ x ∈ ⨆ i, coefAxisCode R (fun i => extendCode E (C i)) i,
      ∃ y : ι → ((∀ i, Ω i) → R), (∀ i, y i ∈ coefAxisCode R (fun i => extendCode E (C i)) i) ∧
        x = ∑ i, y i ∧
        ρ * ∑ i, (Fintype.card (Ω i) : ℝ) * (lineCount i (y i) : ℝ) ≤ supportCard x

end GoodQLTC


