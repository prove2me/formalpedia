-- Prove2me | Definitions.Def_HomIndGHW_RCR_InducedBinary
-- name    : HomIndGHW_RCR_InducedBinary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:03:06.117092+00:00
-- url     : https://prove2.me/theorems/ecd06119-719e-4392-a415-5e1c1290c11c
-- title:
--   Ord_λ, Profile, FullTuple, BagTuple, the binary structure A_D induced by a GHD, and D-extensions (Definitions 1.12, 1.14, 3.8)
-- statement:
--   Let $D=(T,B,\lambda)$ be a GHD of $\mathcal A$ of width at most $k$ and fix the order $\preceq_\sigma$. For a node $u$, $\mathrm{Ord}_\lambda(u)=R_1(\bar a_1),\dots,R_{k'}(\bar a_{k'})$ lists the coloured tuples of $\lambda(u)$ in increasing $\preceq_\sigma$-order of their symbols; $\mathrm{Profile}(u)=(R_1,\dots,R_{k'})$, $\mathrm{FullTuple}(u)=\bar a_1+\dots+\bar a_{k'}$, and $\mathrm{BagTuple}(u)=\bar a^\star_1+\dots+\bar a^\star_{k'}$, where $\bar a^\star$ replaces every entry outside $B(u)$ by a fresh symbol $\varepsilon$ (Definition 1.12). The **binary structure induced by $D$**, $\mathcal A_D$ (Definition 1.14), is the $\hat\sigma_k$-structure with universe $V(T)$ and the minimal interpretation with $u\in U_\alpha$ iff $\alpha=\mathrm{Profile}(u)$, and
--   $$E_{i,j}(u,w)\iff \big(\{u,w\}\in E(T)\text{ or }u=w\big)\ \text{and}\ \mathrm{BagTuple}(u)[i]=\mathrm{BagTuple}(w)[j]\neq\varepsilon .$$
--   For $h:A\to B$, a **$D$-extension** of $h$ w.r.t. $\mathcal B$ (Definition 3.8) chooses for every node $u$ a tuple $h^\varepsilon_u(\mathrm{BagTuple}(u))\in\mathrm{dom}(\mathcal B(\mathcal B,k))$ of the same length that agrees with $h$ on the non-$\varepsilon$ entries (the $\varepsilon$ entries are mapped arbitrarily) and lies in $U^{\mathcal B(\mathcal B,k)}_{\mathrm{Profile}(u)}$; $\mathrm{Ext}^D_{\mathcal B}(h)$ is the set of them.
--
--   These objects translate homomorphism counts from $\mathcal A$ into counts between binary structures.
--
--   **Formalization Note.** Ties in $\mathrm{Ord}_\lambda(u)$ (footnote 5 asks only for order by symbol) are kept in their order in $\lambda(u)$ (a stable merge sort); since $\lambda(u)$ is an arbitrary sequence, every admissible ordering arises from some $\lambda$. $\varepsilon$ is `none : Option V`. A $D$-extension is recorded by the map $u\mapsto h^\varepsilon_u(\mathrm{BagTuple}(u))$, as the proof of Lemma 3.10 identifies them; positions in `BagTuple` are 0-based, matching the 0-based $E_{i,j}$.
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 9, Definitions 1.12 and 1.14; p. 22, Definition 3.8

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_GHD
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Exploded

set_option autoImplicit false

namespace HomIndGHW.RCR

/-!
# Ord_λ, Profile, FullTuple, BagTuple, the binary structure A_D, and D-extensions

Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, *Homomorphism Indistinguishability Beyond
Graphs*, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…),
Definition 1.12 (p. 9), Definition 1.14 (p. 9), Definition 3.8 (p. 22).

* `Ord_λ(u)` lists the coloured tuples of `λ(u)` in increasing `⪯σ`-order of their symbols;
  footnote 5 (p. 9) asks only for that, so ties are kept in their order in `λ(u)` (a stable sort).
  Since `λ(u)` is an arbitrary sequence, every admissible ordering arises from some `λ`.
* The fresh placeholder `ε` is `none : Option V`; `BagTuple(u) : List (Option V)`.
* A `D`-extension `{{h^ε_u : u ∈ V(T)}}` of `h` is recorded by its values
  `f(u) = h^ε_u(BagTuple(u)) ∈ dom(B(B, k))`, as in the proof of Lemma 3.10 (p. 22), where the
  extension and the induced map `ĥ : V(T) → dom(B(B, k))` are identified.
-/

open Structure Classical

variable {σ : Sig} {V : Type*} {W : Type*}

namespace GHD

variable [LinearOrder σ.Sym] {A : Structure σ V} {N : Type*}

/-- `Ord_λ(u)`: the coloured tuples of `λ(u)` in increasing `⪯σ`-order of their symbols
(Definition 1.12, p. 9; footnote 5). -/
def ordLam (D : GHD A N) (u : N) : List (CT A) :=
  (D.lam u).mergeSort fun c d => decide (c.sym ≤ d.sym)

/-- `Profile(u) = (R₁, …, R_{k'})` for `Ord_λ(u) = R₁(ā₁), …, R_{k'}(ā_{k'})` (Definition 1.12(1)). -/
def profile (D : GHD A N) (u : N) : List σ.Sym := (D.ordLam u).map CT.sym

/-- `FullTuple(u) = ā₁ + ⋯ + ā_{k'}` (Definition 1.12(2)). -/
def fullTuple (D : GHD A N) (u : N) : List V := ((D.ordLam u).map CT.toList).flatten

/-- `BagTuple(u) = ā₁★ + ⋯ + ā_{k'}★`, where `ā★` replaces every entry not in `B(u)` by `ε`
(`none`) (Definition 1.12(2)). -/
noncomputable def bagTuple (D : GHD A N) (u : N) : List (Option V) :=
  ((D.ordLam u).map fun c => c.toList.map fun x => if x ∈ D.bag u then some x else none).flatten

/-- The **binary structure `A_D` induced by the GHD `D`** (Definition 1.14, p. 9): the
`σ̂_k`-structure with universe `V(T)` and the minimal interpretation with
(1) `u ∈ U_α` iff `α = Profile(u)`;
(2) `E_{i,j}(u, w)` if `{u, w} ∈ E(T) ∪ {{x, x} | x ∈ V(T)}` and `ā[i] = b̄[j] ≠ ε` for
`ā = BagTuple(u)`, `b̄ = BagTuple(w)` (0-based positions, see `explodedSig`). -/
noncomputable def inducedBinary (D : GHD A N) (k : ℕ) : Structure (explodedSig σ k) N where
  rel := fun R => match R with
    | .inl α => {t | ∀ j, α.1 = D.profile (t j)}
    | .inr ij => {t | ∃ j0 j1, j0.val = 0 ∧ j1.val = 1 ∧
        (D.T.Adj (t j0) (t j1) ∨ t j0 = t j1) ∧
        ∃ x : V, (D.bagTuple (t j0))[ij.1.val]? = some (some x) ∧
          (D.bagTuple (t j1))[ij.2.val]? = some (some x)}

/-- `Ext^D_B(h)`, the **`D`-extensions of `h` w.r.t. `B`** (Definition 3.8, p. 22), each recorded
by the family of tuples `f(u) = h^ε_u(BagTuple(u)) ∈ dom(B(B, k))`: `f(u)` has the length of
`BagTuple(u)`, agrees with `h` on every non-`ε` entry of `BagTuple(u)` (the `ε` entries are mapped
to arbitrary elements), and `f(u) ∈ U^{B(B, k)}_{Profile(u)}`, i.e.
`f(u) ∈ R₁^B × ⋯ × R_ℓ^B` for `Profile(u) = (R₁, …, R_ℓ)`. -/
def dExt [Finite W] (D : GHD A N) (k : ℕ) (B : Structure σ W) (h : V → W) :
    Set (N → bdom B k) :=
  {f | ∀ u : N, ((f u).1.length = (D.bagTuple u).length) ∧
      (∀ (i : ℕ) (x : V), (D.bagTuple u)[i]? = some (some x) → (f u).1[i]? = some (h x)) ∧
      InProd B (D.profile u) (f u).1}

end GHD

end HomIndGHW.RCR


