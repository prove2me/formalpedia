-- Prove2me | Definitions.Def_HomIndGHW_RCR_Exploded
-- name    : HomIndGHW_RCR_Exploded
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:01:56.699192+00:00
-- url     : https://prove2.me/theorems/1dc991c1-c0b9-42c1-9872-f1fe9a2c834c
-- title:
--   The k-exploded signature σ̂_k, the encodings B(A, k) and B_split(A, k), and 1-WL on binary structures (Definitions 1.13, 1.15, 3.4; §2)
-- statement:
--   The **$k$-exploded binary signature** is $\hat\sigma_k=\{U_\alpha\mid\alpha\in\sigma(\le k)\}\cup\{E_{i,j}\mid i,j\in\{1,\dots,k\cdot\mathrm{ar}(\sigma)\}\}$ with $U_\alpha$ unary and $E_{i,j}$ binary (Definition 1.13). The **canonical $k$-exploded encoding** $\mathcal B(\mathcal A,k)$ (Definition 1.15) has universe $\{\bar a\mid \bar a\in R_1^{\mathcal A}\times\dots\times R_n^{\mathcal A}\text{ for some }(R_1,\dots,R_n)\in\sigma(\le k)\}$ (products of relations concatenate tuples), with $\bar a\in U_\alpha$ iff $\bar a\in R_1^{\mathcal A}\times\dots\times R_n^{\mathcal A}$ for $\alpha=(R_1,\dots,R_n)$, and
--   $$E_{i,j}(\bar a,\bar b)\iff \bar a[i]=\bar b[j].$$
--   The **profile-split encoding** $\mathcal B_{\mathrm{split}}(\mathcal A,k)$ (Definition 3.4) has universe the pairs $(\alpha,\bar a)$ with $\alpha\in\sigma(\le k)$ and $\bar a\in R_1^{\mathcal A}\times\dots\times R_n^{\mathcal A}$, $(\alpha,\bar a)\in U_\beta$ iff $\alpha=\beta$, and $E_{i,j}((\alpha,\bar a),(\beta,\bar b))$ iff $\bar a[i]=\bar b[j]$.
--
--   **1-WL** on a binary structure (§2) colours vertices by $c_0(v)=\mathrm{atp}(v)$ (unary symbols containing $v$ and binary symbols containing $(v,v)$) and $c_i(v)=(c_{i-1}(v),\{\!\{(c_{i-1}(w),\mu(v,w))\mid\{v,w\}\in\mathrm{Gaif}\}\!\})$, where $\mu(v,w)$ is the set of binary symbols containing the directed edge $(v,w)$. Two binary structures are $\equiv_{1\text{-WL}}$ when their stable colours occur equally often; Colour Refinement distinguishes them when they are not.
--
--   The encodings turn $k$-proRCR into 1-WL on binary structures, where the classical tree-homomorphism characterisation applies.
--
--   **Formalization Note.** $\hat\sigma_k$'s symbols are the sum type of $\sigma(\le k)$ and `Fin (k·ar σ) × Fin (k·ar σ)`; the index $i$ stands for the paper's $i+1$ (0-based positions). The universe of $\mathcal B(\mathcal A,k)$ is the finite set of flattenings of pro-tuples; that of $\mathcal B_{\mathrm{split}}(\mathcal A,k)$ is $\mathrm{MCT}_k(\mathcal A)$. $\mathrm{atp}(v)$ is uniformly the set of symbols whose relation contains the constant tuple $(v,\dots,v)$. 1-WL colours are canonical values and $\equiv_{1\text{-WL}}$ is in all-rounds form, as for $k$-RCR.
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 9, Definition 1.13; p. 10, Definition 1.15; p. 20, Definition 3.4; p. 15, §2 (1-WL for binary structures)

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement

set_option autoImplicit false

namespace HomIndGHW.RCR

/-!
# The k-exploded binary signature, the encodings B(A, k) and B_split(A, k), and 1-WL

Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, *Homomorphism Indistinguishability Beyond
Graphs*, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…),
Definition 1.13 (p. 9), Definition 1.15 (p. 10), Definition 3.4 (p. 20), and the 1-dimensional
Weisfeiler–Leman algorithm for binary structures (§2, p. 15).

* `σ̂_k = {U_α | α ∈ σ(≤k)} ∪ {E_{i,j} | i, j ∈ [k·ar(σ)]}` is the sum type of `σ(≤k)` and
  `Fin (k·ar σ) × Fin (k·ar σ)`; `U_α` is unary, `E_{i,j}` binary. The index `i : Fin (k·ar σ)`
  stands for the paper's `i + 1` (0-based positions), a relabelling of symbols.
* The domain of `B(A, k)` is the finite set `{ā | ∃ P ∈ Prod(≤k)(A), ā ∈ P}`, i.e. the flattenings
  of the pro-tuples of `A`; the domain of `B_split(A, k)` is `MCT_k(A)` (pairs `(α, ā)`).
* 1-WL colours are canonical values (`WLCol σ i`), compared across structures; `≡_{1-WL}` is read
  in all-rounds form as `≡_{k-RCR}` (see `Def_HomIndGHW_RCR_Refinement`).
-/

open Structure Classical

variable {σ : Sig} {V : Type*} {W : Type*}

/-- `σ(≤k)` is finite (structural). -/
theorem finite_sigLe (σ : Sig) [LinearOrder σ.Sym] (k : ℕ) : (sigLe σ k).Finite :=
  (List.finite_length_le σ.Sym k).subset fun _ h => h.2.1

/-- The **k-exploded binary signature** `σ̂_k` (Definition 1.13, p. 9): a unary symbol `U_α` for
every `α ∈ σ(≤k)` and a binary symbol `E_{i,j}` for all `i, j ∈ [k · ar(σ)]`. -/
noncomputable def explodedSig (σ : Sig) [LinearOrder σ.Sym] (k : ℕ) : Sig where
  Sym := {α // α ∈ sigLe σ k} ⊕ (Fin (k * σ.maxAr) × Fin (k * σ.maxAr))
  fin := by
    haveI : Finite {α // α ∈ sigLe σ k} := (finite_sigLe σ k).to_subtype
    exact Fintype.ofFinite _
  ar := Sum.elim (fun _ => 1) (fun _ => 2)
  ar_pos := fun R => by cases R <;> simp

/-- `ā ∈ R₁^A × ⋯ × R_n^A` for `α = (R₁, …, R_n)` (relational-algebra product, footnote 6, p. 10):
`ā` is the concatenation of tuples `t̄_i ∈ R_i^A`. -/
def InProd (A : Structure σ V) (α : List σ.Sym) (a : List V) : Prop :=
  ∃ cs : List (CT A), cs.map CT.sym = α ∧ (cs.map CT.toList).flatten = a

/-- `E_{i,j}(ā, b̄)` iff `ā[i] = b̄[j]` (both positions exist), 0-based positions. -/
def EqAt (a b : List V) (i j : ℕ) : Prop := ∃ x, a[i]? = some x ∧ b[j]? = some x

/-- The domain of `B(A, k)`: `{ā | ∃ P ∈ Prod(≤k)(A), ā ∈ P}` (Definition 1.15, p. 10). -/
noncomputable def bdom [Finite V] [LinearOrder σ.Sym] (A : Structure σ V) (k : ℕ) :
    Finset (List V) :=
  (mct A k).image Prod.snd

/-- The **canonical k-exploded encoding** `B(A, k)` (Definition 1.15, p. 10), a
`σ̂_k`-structure: `ā ∈ U_α` iff `ā ∈ R₁^A × ⋯ × R_n^A` for `α = (R₁, …, R_n)`, and
`E_{i,j}(ā, b̄)` iff `ā[i] = b̄[j]`. -/
noncomputable def explode [Finite V] [LinearOrder σ.Sym] (A : Structure σ V) (k : ℕ) :
    Structure (explodedSig σ k) (bdom A k) where
  rel := fun R => match R with
    | .inl α => {t | ∀ j, InProd A α.1 (t j).1}
    | .inr ij => {t | ∃ j0 j1, j0.val = 0 ∧ j1.val = 1 ∧ EqAt (t j0).1 (t j1).1 ij.1.val ij.2.val}

/-- The **profile-split k-exploded encoding** `B_split(A, k)` (Definition 3.4, p. 20): universe
`{(α, ā) | α ∈ σ(≤k), ā ∈ R₁^A × ⋯ × R_n^A}` (that is, `MCT_k(A)`), `(α, ā) ∈ U_β` iff `α = β`,
and `E_{i,j}((α, ā), (β, b̄))` iff `ā[i] = b̄[j]`. -/
noncomputable def splitExplode [Finite V] [LinearOrder σ.Sym] (A : Structure σ V) (k : ℕ) :
    Structure (explodedSig σ k) (mct A k) where
  rel := fun R => match R with
    | .inl β => {t | ∀ j, (t j).1.1 = β.1}
    | .inr ij => {t | ∃ j0 j1, j0.val = 0 ∧ j1.val = 1 ∧
        EqAt (t j0).1.2 (t j1).1.2 ij.1.val ij.2.val}

/-! ### 1-WL on binary structures (§2, p. 15) -/

/-- `atp(v)`: the unary symbols `R` with `v ∈ R^A` and the binary symbols `R` with
`(v, v) ∈ R^A` — uniformly, the symbols whose relation contains the constant tuple `(v, …, v)`. -/
noncomputable def wlAtp (A : Structure σ V) (v : V) : Finset σ.Sym :=
  Finset.univ.filter fun R => (fun _ => v) ∈ A.rel R

/-- `µ(v, w)`: the labels of the directed edge `(v, w)`, i.e. the binary symbols `R` with
`(v, w) ∈ R^A`. -/
noncomputable def wlMu (A : Structure σ V) (v w : V) : Finset σ.Sym :=
  Finset.univ.filter fun R => ∃ _ : σ.ar R = 2,
    (fun j : Fin (σ.ar R) => if j.val = 0 then v else w) ∈ A.rel R

/-- Round-`i` colours of 1-WL: `WLCol σ 0 = 2^σ`, `WLCol σ (i+1) = WLCol σ i ×
Multiset (WLCol σ i × 2^σ)`. -/
def WLCol (σ : Sig) : ℕ → Type
  | 0 => Finset σ.Sym
  | i + 1 => WLCol σ i × Multiset (WLCol σ i × Finset σ.Sym)

/-- The 1-WL colouring (§2, p. 15): `c_0(v) = atp(v)` and
`c_i(v) = (c_{i−1}(v), {{(c_{i−1}(w), µ(v, w)) | {v, w} ∈ Gaif(A)}})`. -/
noncomputable def wlColour [Fintype V] (A : Structure σ V) : (i : ℕ) → V → WLCol σ i
  | 0, v => wlAtp A v
  | i + 1, v => (wlColour A i v,
      ((Finset.univ.filter fun w => (gaifman A).Adj v w).val.map fun w =>
        (wlColour A i w, wlMu A v w)))

/-- `A ≡_{1-WL} B` (all-rounds form): for every round `i` and colour `c`, as many vertices of `A` as
of `B` have colour `c` at round `i`. "Colour Refinement distinguishes `A` and `B`" (Theorem 3.21)
is its negation. -/
def WLEquiv [Fintype V] [Fintype W] (A : Structure σ V) (B : Structure σ W) : Prop :=
  ∀ (i : ℕ) (c : WLCol σ i),
    (Finset.univ.filter fun v => wlColour A i v = c).card =
      (Finset.univ.filter fun w => wlColour B i w = c).card

end HomIndGHW.RCR


