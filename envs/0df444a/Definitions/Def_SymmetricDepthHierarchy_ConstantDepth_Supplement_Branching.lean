-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching
-- name    : SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:55:29.259228+00:00
-- url     : https://prove2.me/theorems/c345984e-0153-4ce5-991a-df3f1cf55739
-- title:
--   Unlayered algebraic branching programs and their full symmetry orbits
-- statement:
--   An algebraic branching program is a finite directed acyclic graph with a unique source $s$ and unique sink $t$. Each existing edge carries an arbitrary affine linear form over $K$, using the published affine-form object. Its polynomial is
--   $$\sum_{\pi:s\leadsto t}\prod_{e\in\pi}\ell(e).$$
--   The finite dynamic recursion includes the empty path if $s=t$ and counts every directed path exactly once on a DAG. Edges labelled zero remain graph edges. An extending automorphism fixes $s,t$, preserves the edge relation, and transports each affine label by the variable permutation. Symmetry requires an extension for every group element; the orbit maximum uses all extending automorphisms. No chosen lift, layering, homogeneity, degree or total-size constraint is imposed. The class $\mathrm{symVBP}$ consists of invariant matrix families with eventual polynomial vertex-orbit bounds. This separates the general branching-program object from the matrix-specific action and family class.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 14–16 (PDF p. 17–19), Definitions 6.1–6.2; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes
import Definitions.Def_BorderDiffEq_AffineForm

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement


/-- An unlayered algebraic branching program, §6. A zero-labelled edge is still an edge. -/
structure ABP (K X V : Type) where
  edge : V → V → Prop
  label : V → V → BorderDiffEq.AffineForm K X
  source : V
  sink : V

namespace ABP
variable {K X V : Type} [Field K] [Fintype X] [Fintype V]
def wellFormed (G : ABP K X V) : Prop :=
  (∀ v, ¬ Relation.TransGen G.edge v v) ∧
  (∀ v, (¬ ∃ u, G.edge u v) ↔ v = G.source) ∧
  (∀ v, (¬ ∃ u, G.edge v u) ↔ v = G.sink)

/-- Dynamic path sum: the source contributes the empty path; |V| rounds suffice on a DAG. -/
def pathAux (G : ABP K X V) : ℕ → V → MvPolynomial X K
  | 0 => fun v => if v = G.source then 1 else 0
  | k+1 => fun v => (if v = G.source then 1 else 0) +
      ∑ u, if G.edge u v then G.pathAux k u * (G.label u v).toPoly else 0

def polynomial (G : ABP K X V) : MvPolynomial X K := G.pathAux (Fintype.card V) G.sink

def extension (G : ABP K X V) (γ : Equiv.Perm X) (σ : Equiv.Perm V) : Prop :=
  σ G.source = G.source ∧ σ G.sink = G.sink ∧
  (∀ u v, G.edge (σ u) (σ v) ↔ G.edge u v) ∧
  ∀ u v, G.edge u v →
    (G.label (σ u) (σ v)).toPoly = MvPolynomial.rename γ (G.label u v).toPoly

def symmetric (G : ABP K X V) {H : Type} [Group H] (ρ : H →* Equiv.Perm X) : Prop :=
  ∀ γ, ∃ σ, G.extension (ρ γ) σ

def maxOrb (G : ABP K X V) {H : Type} [Group H] (ρ : H →* Equiv.Perm X) : ℕ :=
  Finset.univ.sup fun v => (Finset.univ.filter fun w =>
    ∃ γ σ, G.extension (ρ γ) σ ∧ σ v = w).card
end ABP

def matrixAction (n : ℕ) : Circuit.Gamma n →* Equiv.Perm (Fin n × Fin n) where
  toFun γ := Equiv.prodCongr γ.1 γ.2
  map_one' := rfl
  map_mul' _ _ := rfl

def symVBP (K : Type) [Field K] : Set (Family K) :=
  {p | invariantFamily p ∧ ∃ c N : ℕ, ∀ n, 1 ≤ n → N ≤ n →
    ∃ m, ∃ G : ABP K (Fin n × Fin n) (Fin m),
      G.wellFormed ∧ G.symmetric (matrixAction n) ∧ G.polynomial = p n ∧
      G.maxOrb (matrixAction n) ≤ n ^ c}

end SymmetricDepthHierarchy.ConstantDepth.Supplement


