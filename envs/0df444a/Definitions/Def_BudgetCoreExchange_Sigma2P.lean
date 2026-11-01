-- Prove2me | Definitions.Def_BudgetCoreExchange_Sigma2P
-- name    : BudgetCoreExchange_Sigma2P
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:32.611828+00:00
-- url     : https://prove2.me/theorems/84b53964-4061-43ff-97af-aee012e8e941
-- title:
--   The class $\Sigma_2^p$, $\Sigma_2^p$-hardness and $\Sigma_2^p$-completeness (Cook's machine model)
-- statement:
--   Let $\mathrm{Sym}$ be a finite alphabet. A language $L\subseteq\mathrm{Sym}^*$ is in **$\Sigma_2^p$** if there are a finite nonempty alphabet $\mathrm{Sym}_1$, a relation $R\subseteq \mathrm{Sym}^*\times\mathrm{Sym}_1^*\times\mathrm{Sym}_1^*$ and $k\in\mathbb N$ such that the checking language $\{w\#y\#z : R(w,y,z)\}$ is decidable in polynomial time, and for every word $w$
--   $$
--   w\in L\iff \exists y\ \big(|y|\le|w|^k\ \wedge\ \forall z\ (|z|\le|w|^k\Rightarrow R(w,y,z))\big).
--   $$
--   A language $L$ is **$\Sigma_2^p$-hard** if every $\Sigma_2^p$ language over every finite nonempty alphabet reduces to $L$ by a polynomial-time many-one reduction, and **$\Sigma_2^p$-complete** if moreover $L\in\Sigma_2^p$.
--
--   This is the second level of the polynomial hierarchy in its $\exists\forall$ form, the class in which Theorem 2 of the paper places the core-pricing problem.
--
--   **Formalization Note** Polynomial time, the class $\mathrm P$ and $\le_p$ are those of the published framework `CookPvsNP` (one-tape Turing machines, time bound $|w|^k+k$); the certificate bound $|w|^k$ mirrors `CookPvsNP.NP`. The checking language is over `Option (Sym ⊕ Sym₁)` with `none` as the separator.
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Theorem 2, p.9 and Appendix A, p.27 (Σᵖ₂); definition as in Arora–Barak, Computational Complexity, Def. 5.1

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace BudgetCoreExchange

/-- The language `{w # y # z | R(w, y, z)}` of a two-certificate checking relation
`R ⊆ Sym* × Sym₁* × Sym₁*`, over the alphabet `Option (Sym ⊕ Sym₁)` with `none` as the separator
`#`. It is the two-separator analogue of `CookPvsNP.checkLang`. -/
def checkLang₂ {Sym Sym₁ : Type} (R : List Sym → List Sym₁ → List Sym₁ → Prop) :
    CookPvsNP.Lang (Option (Sym ⊕ Sym₁)) :=
  { s | ∃ w y z, R w y z ∧
      s = w.map (some ∘ Sum.inl) ++ none :: (y.map (some ∘ Sum.inr) ++ none :: z.map (some ∘ Sum.inr)) }

/-- The class **Σᵖ₂** of languages over `Sym` (the second level of the polynomial hierarchy, in
∃∀ form, Arora–Barak Def. 5.1; used in Bichler–Waldherr, arXiv:1807.08253v1, Theorem 2, p.9, and
Appendix A, p.27): `L ∈ Σᵖ₂` iff there are a finite nonempty alphabet `Sym₁`, a relation `R` whose
checking language `checkLang₂ R` is in `CookPvsNP.P`, and `k ∈ ℕ` such that for every `w`,
`w ∈ L ↔ ∃ y, |y| ≤ |w|^k ∧ ∀ z, |z| ≤ |w|^k → R(w, y, z)`.

**Formalization Note.** The machine model is Cook's (`CookPvsNP`), and the certificate bound
`|w|^k` mirrors the bound of `CookPvsNP.NP`. -/
def Sigma2P (Sym : Type) [Fintype Sym] : Set (CookPvsNP.Lang Sym) :=
  { L | ∃ (Sym₁ : Type) (_ : Fintype Sym₁) (_ : Nonempty Sym₁)
      (R : List Sym → List Sym₁ → List Sym₁ → Prop) (k : ℕ),
      checkLang₂ R ∈ CookPvsNP.P (Option (Sym ⊕ Sym₁)) ∧
      ∀ w : List Sym, w ∈ L ↔
        ∃ y : List Sym₁, y.length ≤ w.length ^ k ∧
          ∀ z : List Sym₁, z.length ≤ w.length ^ k → R w y z }

/-- **Σᵖ₂-hardness**: every Σᵖ₂ language over every finite nonempty alphabet polynomial-time
many-one reduces to `L` (Cook's `≤ₚ`, `CookPvsNP.PolyReducible`). -/
def Sigma2Hard {Sym : Type} (L : CookPvsNP.Lang Sym) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ Sigma2P Sym' → CookPvsNP.PolyReducible L' L

/-- **Σᵖ₂-completeness**: `L ∈ Σᵖ₂` and `L` is Σᵖ₂-hard. -/
def Sigma2Complete {Sym : Type} [Fintype Sym] (L : CookPvsNP.Lang Sym) : Prop :=
  L ∈ Sigma2P Sym ∧ Sigma2Hard L

end BudgetCoreExchange


