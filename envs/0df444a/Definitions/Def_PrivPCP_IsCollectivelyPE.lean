-- Prove2me | Definitions.Def_PrivPCP_IsCollectivelyPE
-- name    : PrivPCP_IsCollectivelyPE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:06.960032+00:00
-- url     : https://prove2.me/theorems/d1021828-3f40-43e7-ba0b-8dde922aa40a
-- title:
--   Collective product expansion
-- statement:
--   For a finite family $X=(X^{(a)})_{a\in A}$ of words on $\prod_i S_i$ write $\mathrm{wt}_\cup(X)=\left|\bigcup_{a}\mathrm{supp}\,X^{(a)}\right|$ and, for a family $X_i$ in $L_i(C_i)$, $\ell_{i,\cup}(X_i)$ for the number of $i$-axis lines on which some member of $X_i$ is nonzero.
--
--   A tuple $(C_1,\dots,C_r)$ is **collectively $P$-product-expanding** if every finite family $X$ in $\sum_i L_i(C_i)$ has decompositions $X^{(a)}=\sum_i X_i^{(a)}$, $X_i^{(a)}\in L_i(C_i)$, with
--   $$\mathrm{wt}_\cup(X)\ge P\sum_{i}s_i\,\ell_{i,\cup}\big((X_i^{(a)})_{a\in A}\big).\qquad\text{(CPE)}$$
--   For a singleton family this is ordinary product expansion with constant $P$.
--
--   **Formalization Note** The families range over finite index types $A$ (in the lowest universe).
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 4.7, p.18 (PDF p.20); §4.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_GoodQLTC_IsProductExpanding

namespace PrivPCP

/-- The union weight `wt_∪(X) = |⋃_{a∈A} supp X^{(a)}|` of a finite family of words (Bafna, Vyas, *Private
PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), §4.3, p.17). It is the
support size of the `F^A`-valued word `ω ↦ (X^{(a)}(ω))_a`. -/
noncomputable def wtU {F : Type} [Field F] {A α : Type} [Fintype α] (X : A → α → F) : ℕ :=
  GoodQLTC.supportCard (fun ω (a : A) => X a ω)

/-- `ℓ_{i,∪}(X)`, the number of `i`-axis lines on which some member of the family `X` is nonzero (§4.3, p.17):
the published line count `GoodQLTC.lineCount` of the `F^A`-valued word `ω ↦ (X^{(a)}(ω))_a`. -/
noncomputable def lineCountU {F : Type} [Field F] {A ι : Type} [Fintype ι] {Ω : ι → Type}
    [∀ i, Fintype (Ω i)] (i : ι) (X : A → (∀ i, Ω i) → F) : ℕ :=
  GoodQLTC.lineCount i (fun ω (a : A) => X a ω)

/-- **Collective `P`-product expansion** (Definition 4.7, p.18): every finite family `X = (X^{(a)})_{a∈A}` in
`∑_i L_i(C_i)` has decompositions `X^{(a)} = ∑_i X_i^{(a)}`, `X_i^{(a)} ∈ L_i(C_i)`, with
`wt_∪(X) ⩾ P ∑_i s_i ℓ_{i,∪}((X_i^{(a)})_{a∈A})` (CPE).

**Formalization Note** The index sets `A` range over all finite types in `Type` (universe 0). `L_i(C_i)` is the
published `GoodQLTC.axisCode`, as in `GoodQLTC.IsProductExpanding`; `s_i = |Ω_i|`. -/
def IsCollectivelyPE {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : ι → Type}
    [∀ i, Fintype (Ω i)] (P : ℝ) (C : ∀ i, Submodule F (Ω i → F)) : Prop :=
  ∀ (A : Type) [Fintype A] (X : A → ((∀ i, Ω i) → F)), (∀ a, X a ∈ ⨆ i, GoodQLTC.axisCode C i) →
    ∃ Y : A → ι → ((∀ i, Ω i) → F), (∀ a i, Y a i ∈ GoodQLTC.axisCode C i) ∧ (∀ a, X a = ∑ i, Y a i) ∧
      P * ∑ i, (Fintype.card (Ω i) : ℝ) * (lineCountU i (fun a => Y a i) : ℝ) ≤ wtU X

end PrivPCP


