-- Prove2me | Definitions.Def_MinrankTW_relTransforms
-- name    : MinrankTW_relTransforms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:04.231271+00:00
-- url     : https://prove2.me/theorems/7ee913d3-ed2b-4197-b2d9-dd7b651b27ac
-- title:
--   Restriction transforms $T$, $C$, $B$ on relation tables
-- statement:
--   For $E\le\mathrm{dom}\,R$ let $R|_E=\{(x,y)\in R : x\in E\}$. On tables indexed by linear relations:
--
--   1. $(Tf)(D,L,\beta)=\sum_{E\supseteq D,\ F\supseteq L}\ \sum_{\gamma:\ \gamma|_{D\times L}=\beta} f(E,F,\gamma)$ (19), where $\gamma$ ranges over bilinear forms on $E\times F$;
--   2. $(Cf)(R)=\sum_{E\le\mathrm{dom}\,R} f(R|_E)$ and $(Bf)(R)=\sum_{S\le R,\ \mathrm{dom}\,S=\mathrm{dom}\,R} f(S)$ (21).
--
--   **Formalization Note** Each transform is recorded as its 0/1 matrix: $C$ has entry $1$ at $(R,Q)$ when $Q=R|_E$ for some $E\le\mathrm{dom}\,R$ (distinct $E$ give distinct $R|_E$), $B$ when $S\le R$ and $\mathrm{dom}\,S=\mathrm{dom}\,R$, and $T$ when the triple of $Q$ restricts to the triple of $R$. The entry $f(D,L,\beta)$ of (19) is the entry of $f$ at the relation that the triple represents.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 4.2, p.13, Eq. (19); Section 4.3, pp.13–14, Eq. (21)

import Mathlib
import Definitions.Def_MinrankTW_LinRel
import Definitions.Def_MinrankTW_RelTriple

namespace MinrankTW

/-!
# The restriction transforms `T`, `C`, `B` on relation tables

Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §4.2, p.13, Eq. (19): `(T f)(D, L, β) = ∑_{E ⊇ D, F ⊇ L} ∑_{γ : γ|_{D×L} = β} f(E, F, γ)`;
§4.3, pp.13–14: `R|_E = {(x, y) ∈ R : x ∈ E}` for `E ≤ dom R`, and Eq. (21):
`(Cf)(R) = ∑_{E ≤ dom R} f(R|_E)`, `(Bf)(R) = ∑_{S ≤ R, dom S = dom R} f(S)`.

**Formalization Note** Each transform is given by its 0/1 matrix (a relation between table
indices), to be used with `tableMap`; the transpose is the flipped matrix. Tables are indexed by
linear relations; the entry `f(D, L, β)` of (19) is `f(R)` for the relation `R` that the triple
represents. `cKer R Q` holds when `Q = R|_E` for some `E ≤ dom R` (distinct `E` give distinct
`R|_E`, so `tableMap cKer` is `C`). `tKer R Q` holds when the triple of `Q` restricts to the
triple of `R`: `E ⊇ D`, `F ⊇ L` and `γ|_{D×L} = β`.
-/

variable {F : Type*} [Field F] {α γ : Type*}

/-- `R|_E = {(x, y) ∈ R : x ∈ E}`. -/
def relRestrict (R : Submodule F ((α → F) × (γ → F))) (E : Submodule F (α → F)) :
    Submodule F ((α → F) × (γ → F)) :=
  R ⊓ E.comap (LinearMap.fst F (α → F) (γ → F))

/-- The matrix of `C` (Eq. (21)): `Q = R|_E` for some `E ≤ dom R`. -/
def cKer (R Q : Submodule F ((α → F) × (γ → F))) : Prop :=
  ∃ E : Submodule F (α → F), E ≤ relDom R ∧ Q = relRestrict R E

/-- The matrix of `B` (Eq. (21)): `S ≤ R` and `dom S = dom R`. -/
def bKer (R S : Submodule F ((α → F) × (γ → F))) : Prop :=
  S ≤ R ∧ relDom S = relDom R

/-- The matrix of `T` (Eq. (19)): with `R = (D, L, β)` and `Q = (E, F, γ)`, `E ⊇ D`,
`F ⊇ L` and `γ|_{D×L} = β`. -/
def tKer [Fintype γ] (R Q : Submodule F ((α → F) × (γ → F))) : Prop :=
  ∃ TR TQ : RelTriple F α γ, Represents R TR ∧ Represents Q TQ ∧ TR.D ≤ TQ.D ∧ TR.L ≤ TQ.L ∧
    ∀ (x : α → F) (l : γ → F) (hxR : x ∈ TR.D) (hxQ : x ∈ TQ.D) (hlR : l ∈ TR.L)
      (hlQ : l ∈ TQ.L), TQ.β ⟨x, hxQ⟩ ⟨l, hlQ⟩ = TR.β ⟨x, hxR⟩ ⟨l, hlR⟩

end MinrankTW


