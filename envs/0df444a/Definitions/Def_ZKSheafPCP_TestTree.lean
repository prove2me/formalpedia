-- Prove2me | Definitions.Def_ZKSheafPCP_TestTree
-- name    : ZKSheafPCP_TestTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:11:11.410216+00:00
-- url     : https://prove2.me/theorems/7d4826dc-1b19-478e-96cc-8cce36c7a641
-- title:
--   Testable covers and the recursive tester
-- statement:
--   $S$ is a **$c$-testable cover** for $F_\rho$ with distribution $D(S)$ if $S$ covers $P_\rho$ and for all $f:P_*\to\mathbb F$ and all $\delta\in(0,1]$,
--   $$\mathbb E_{\sigma\leftarrow D(S)}[\Delta(f|_\sigma,F_\sigma)]\le\delta\implies\Delta(f|_\rho,F_\rho)\le c\,\delta.$$
--   It is a **$(c,d)$-testable cover** if, for $d>1$, each $F_\tau$, $\tau\in S$, has a $(c,d-1)$-testable cover. This recursive data is a tree: a leaf at a local code, or a node with a cover, a distribution and a subtree per element. The tester of Construction 5.6 walks down the tree by sampling from these distributions and checks $f|_\rho\in F_\rho$ at the leaf reached.
--
--   **Formalization Note** The depth of the tree is $d$, and all leaves lie at that depth over the elements of the covers. The number of points read is the size of the largest leaf.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 5.1–5.3, p.22; Construction 5.6, p.23

import Mathlib
import Definitions.Def_ZKSheafPCP_LocalCodes

namespace ZKSheafPCP

open Classical

/-- The recursive data of a testable cover (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission, manuscript
sha256 ac5e528f…, Definition 5.2 and Construction 5.6, pp.22–23): a leaf at a local code, or a node at a local code with
a cover `S`, a distribution `D(S)` and a subtree for each element. -/
inductive TestTree (D : Type) : Type
  | leaf (ρ : Finset D) : TestTree D
  | node (ρ : Finset D) (S : Finset (Finset D)) (μ : PMF (Finset D)) (child : Finset D → TestTree D) : TestTree D

namespace TestTree

variable {D : Type}

/-- The local code at the root. -/
def root : TestTree D → Finset D
  | leaf ρ => ρ
  | node ρ _ _ _ => ρ

/-- All leaves are at depth exactly `d` over the elements of the covers. A tree of depth `d` is a `(c, d)`-testable
cover when `d ≥ 1` (Definition 5.2, p.22). -/
def HasDepth : TestTree D → ℕ → Prop
  | leaf _, d => d = 0
  | node _ S _ child, d => ∃ d', d = d' + 1 ∧ ∀ τ ∈ S, HasDepth (child τ) d'

/-- The law of the leaf reached by Construction 5.6 (p.23): at a node, sample `τ ← D(S)` and recurse. -/
noncomputable def leafLaw : TestTree D → PMF (Finset D)
  | leaf ρ => PMF.pure ρ
  | node _ _ μ child => μ.bind fun τ => leafLaw (child τ)

/-- The largest leaf: `max_{α∈S₁} |α|`, the number of points the test reads (Theorem 5.7, p.23). -/
def queries : TestTree D → ℕ
  | leaf ρ => ρ.card
  | node _ S _ child => S.sup fun τ => queries (child τ)

end TestTree

variable {F D : Type} [Field F]

/-- `S` is a `c`-testable cover for `F_ρ` with distribution `μ = D(S)` (Definition 5.1, p.22): `S` is a cover for
`P_ρ`, and for all `f : P∗ → F` and all `δ ∈ (0, 1]`, if `E_{σ←D(S)}[Δ(f|_σ, F_σ)] ≤ δ` then `Δ(f|_ρ, F_ρ) ≤ c · δ`. -/
def IsTestableCover (𝓕 : LocalCodes F D) (PP : CodedSpace D) (c : ℕ) (ρ : Finset D) (S : Finset (Finset D))
    (μ : PMF (Finset D)) : Prop :=
  S ⊆ PP.P ∧ (∀ x ∈ ρ, ∃ τ ∈ S, x ∈ τ) ∧ (∀ τ ∈ μ.support, τ ∈ S) ∧
  ∀ (f : D → F) (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∑ τ ∈ S, (μ τ).toReal * LocalCodes.distTo τ f (𝓕.code τ) ≤ δ →
    LocalCodes.distTo ρ f (𝓕.code ρ) ≤ c * δ

/-- Every node of the tree is a `c`-testable cover of its local code, with subtrees rooted at the elements of the cover,
and every local code in it lies in the coded space (Definition 5.2, p.22). -/
def IsTree (𝓕 : LocalCodes F D) (PP : CodedSpace D) (c : ℕ) : TestTree D → Prop
  | .leaf ρ => ρ ∈ PP.P
  | .node ρ S μ child =>
    ρ ∈ PP.P ∧ IsTestableCover 𝓕 PP c ρ S μ ∧
      ∀ τ ∈ S, (child τ).root = τ ∧ IsTree 𝓕 PP c (child τ)

/-- `F` is a `(c, d)`-testable sheaf code for `F_σ` (Definition 5.3, p.22): it contains a `(c, d)`-testable cover
for `F_σ`. -/
def IsTestableSheaf (𝓕 : LocalCodes F D) (PP : CodedSpace D) (c d : ℕ) (σ : Finset D) : Prop :=
  ∃ t : TestTree D, t.root = σ ∧ IsTree 𝓕 PP c t ∧ t.HasDepth d

/-- The rejection probability of Construction 5.6 (p.23) on `f`: the leaf `ρ` reached is checked, `f|_ρ ∈ F_ρ`. -/
noncomputable def rejectProb (𝓕 : LocalCodes F D) (t : TestTree D) (f : D → F) : ℝ :=
  (t.leafLaw.toOuterMeasure {ρ | restr ρ f ∉ 𝓕.code ρ}).toReal

end ZKSheafPCP


