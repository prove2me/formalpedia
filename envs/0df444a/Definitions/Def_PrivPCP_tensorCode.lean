-- Prove2me | Definitions.Def_PrivPCP_tensorCode
-- name    : PrivPCP_tensorCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:46.349196+00:00
-- url     : https://prove2.me/theorems/2619dc39-bc06-4ca6-9eac-dd9d90ab393e
-- title:
--   Tensor codes, Hamming distance to a code, axis-line rejection fractions
-- statement:
--   On a product $\Omega=\prod_i\Omega_i$ of finite sets:
--
--   1. The **tensor code** $\bigotimes_i C_i\subseteq\mathbb F^\Omega$ of linear codes $C_i\subseteq\mathbb F^{\Omega_i}$ is the space of words all of whose $i$-axis lines lie in $C_i$, for every $i$.
--   2. The **distance** of a word $x$ to a linear space $E$ is $\mathrm{dist}(x,E)=\min_{y\in E}\mathrm{wt}(x-y)$ (unnormalized Hamming distance).
--   3. For a word $w$, $b_i(w)$ is the fraction of $i$-axis lines $\ell$ with $w|_\ell\notin C_i$.
--
--   **Formalization Note** $b_i(w)$ is computed as the fraction of points of $\Omega$ whose $i$-axis line is not in $C_i$; every $i$-axis line has $|\Omega_i|$ points, so the fractions agree.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §4 set-up, p.12 (PDF p.14); §4.3, p.17 (PDF p.19); Lemma 7.2, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_GoodQLTC_IsProductExpanding

namespace PrivPCP

/-- The **tensor code** `⊗_i C_i ⊆ F^Ω`, `Ω = ∏_i Ω_i` (Bafna, Vyas, *Private PCPs from Product Expansion*,
STOC 2027 submission manuscript (sha256 c2cac1e0…), §4 set-up, p.13): the words all of whose `i`-axis lines
lie in `C_i`, for every `i`, that is `⋂_i L_i(C_i)` with `L_i(C_i)` the published `GoodQLTC.axisCode`.

**Formalization Note** Words are functions `(∀ i, Ω i) → F`; under `F^Ω = ⊗_i F^{Ω_i}` the intersection of the
axis codes is the tensor product of the `C_i`. -/
def tensorCode {F : Type} [Field F] {ι : Type} [DecidableEq ι] {Ω : ι → Type}
    (C : ∀ i, Submodule F (Ω i → F)) : Submodule F ((∀ i, Ω i) → F) :=
  ⨅ i, GoodQLTC.axisCode C i

/-- The unnormalized **Hamming distance** `dist(x, E) = min_{y ∈ E} wt(x − y)` from a word to a linear space
(§4.3, p.17; §5.1, p.27). The set of values is nonempty (`0 ∈ E`), so the infimum is a minimum. -/
noncomputable def distTo {F : Type} [Field F] {α : Type} [Fintype α] (x : α → F)
    (E : Submodule F (α → F)) : ℕ :=
  sInf {d | ∃ y ∈ E, GoodQLTC.supportCard (x - y) = d}

/-- The fraction `b_i(w)` of `i`-axis lines `ℓ` with `w|_ℓ ∉ C_i` (Lemma 7.2, p.41).

**Formalization Note** It is computed as the fraction of points `ω ∈ Ω` whose `i`-axis line
`x ↦ w(ω with ω_i := x)` is not in `C_i`. Every `i`-axis line contains exactly `|Ω_i|` points, so the two
fractions are equal (both are `0` when `Ω` is empty). -/
noncomputable def lineRejFrac {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : ι → Type}
    [∀ i, Fintype (Ω i)] (C : ∀ i, Submodule F (Ω i → F)) (i : ι) (w : (∀ i, Ω i) → F) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun ω : (∀ i, Ω i) => (fun x : Ω i => w (Function.update ω i x)) ∉ C i).card : ℝ) /
    Fintype.card (∀ i, Ω i)

end PrivPCP


