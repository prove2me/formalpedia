-- Prove2me | Definitions.Def_Hatcher_SingularHomology
-- name    : Hatcher_SingularHomology
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-21T08:25:41.673371+00:00
-- url     : https://prove2.me/theorems/feb64288-a0fb-4091-8140-f075dc7bd898
-- title:
--   Singular homology $H_n(X;R)$ and relative singular homology $H_n(X,A;R)$ with coefficients in a ring
-- statement:
--   Let $R$ be a ring, viewed as a module over itself, and let $X$ be a topological space.
--
--   This file introduces singular homology with coefficients in $R$, in the form used throughout Chapter 2 of Hatcher's book:
--
--   1. **Singular chains.** $C_\bullet(X;R)$, the chain complex of $R$-modules whose degree-$n$ term is the free $R$-module on the singular $n$-simplices $\sigma:\Delta^n\to X$, with the usual boundary $\partial\sigma=\sum_i(-1)^i\,\sigma|[v_0,\dots,\hat v_i,\dots,v_n]$.
--   2. **Singular homology.** $H_n(X;R)=H_n(C_\bullet(X;R))$.
--   3. **Induced maps.** A continuous map $f:X\to Y$ induces a chain map $f_\#:C_\bullet(X;R)\to C_\bullet(Y;R)$ and homomorphisms $f_*:H_n(X;R)\to H_n(Y;R)$.
--   4. **Relative homology.** For a subset $A\subseteq X$ with the subspace topology and inclusion $\iota:A\hookrightarrow X$, the relative chain complex is the quotient
--   $$C_\bullet(X,A;R)=C_\bullet(X;R)\,/\,\iota_\#\,C_\bullet(A;R),$$
--   and $H_n(X,A;R)$ is its homology.
--   5. **Maps of pairs.** A continuous $f:X\to Y$ with $f(A)\subseteq B$ induces $f_*:H_n(X,A;R)\to H_n(Y,B;R)$.
--
--   These are the basic objects of the singular homology theory of Hatcher's Chapter 2 (excision, Mayer–Vietoris, homology of spheres and of projective spaces). Taking $R=\mathbb Z$ gives ordinary singular homology, and $R=\mathbb Q$ gives rational homology and Betti numbers.
--
--   **Formalization Note** The chain complex and homology are Mathlib's `singularChainComplexFunctor` and `singularHomologyFunctor` (with coefficient object the $R$-module $R$), applied to `TopCat.of X`. The relative complex is the cokernel, in the category of chain complexes of $R$-modules, of the chain map induced by the inclusion $A\hookrightarrow X$. Hatcher allows an arbitrary abelian coefficient group $G$; a ring $R$ is used here so that $R=\mathbb Q$ yields $\mathbb Q$-vector spaces.
-- source:
--   A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (online edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1 (“Singular Homology”, p. 108; “Relative Homology Groups”, p. 115) and §2.2 (“Homology with Coefficients”, p. 153). Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Definitions/Def_Hatcher_SingularHomology.lean`.

import Mathlib

/-!
Hatcher, *Algebraic Topology*, Chapter 2, §2.1 (singular homology, pp. 108–110, and relative
groups, p. 115) and §2.2 (homology with coefficients, p. 153), in the book-wide namespace
`Hatcher` (sub-namespace `Hatcher.Singular`).

Singular homology with coefficients in an arbitrary ring `R`, relative singular homology of a
pair `(X, A)` with `A ⊆ X`, and the maps induced by continuous maps and maps of pairs.
Hatcher takes coefficients in an abelian group `G`; a ring `R` (viewed as a module over itself)
is used here so that `R = ℚ` gives `ℚ`-vector spaces and Betti numbers.

* `Chains R X` is Mathlib's singular chain complex `C_•(X; R)`
  (`AlgebraicTopology.singularChainComplexFunctor` with coefficient object the `R`-module `R`).
* `H R n X = H_n(X; R)` is Mathlib's singular homology functor, applied to `X`.
* `RelChains R X A = C_•(X; R) / C_•(A; R)` is the cokernel of the chain map induced by the
  inclusion `A ↪ X`, and `Hrel R n X A = H_n(X, A; R)` is its homology (Hatcher, §2.1, p. 115).
* `map R n f : H_n(X) ⟶ H_n(Y)` and `relMap R n f A B h : H_n(X, A) ⟶ H_n(Y, B)` are the maps
  induced by `f : C(X, Y)` (with `f(A) ⊆ B` for the second).
-/

namespace Hatcher.Singular

open CategoryTheory AlgebraicTopology Limits

variable (R : Type) [Ring R]

/-- The singular chain complex `C_•(X; R)`. -/
noncomputable abbrev Chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj (TopCat.of X)

/-- Singular homology `H_n(X; R)`. -/
noncomputable abbrev H (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat.{0} R :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).obj (TopCat.of X)

variable {R}

/-- The chain map `f_# : C_•(X; R) ⟶ C_•(Y; R)` induced by a continuous map. -/
noncomputable abbrev chainsMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Chains R X ⟶ Chains R Y :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map (TopCat.ofHom f)

variable (R)

/-- The map `f_* : H_n(X; R) ⟶ H_n(Y; R)` induced by a continuous map. -/
noncomputable abbrev map (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : H R n X ⟶ H R n Y :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).map (TopCat.ofHom f)

/-- The inclusion `A ↪ X` of a subset, as a continuous map. -/
abbrev incl {X : Type} [TopologicalSpace X] (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Relative singular chains `C_•(X, A; R) = C_•(X; R) / C_•(A; R)`. -/
noncomputable abbrev RelChains (X : Type) [TopologicalSpace X] (A : Set X) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel (chainsMap (R := R) (incl A))

/-- Relative singular homology `H_n(X, A; R)`. -/
noncomputable abbrev Hrel (n : ℕ) (X : Type) [TopologicalSpace X] (A : Set X) : ModuleCat.{0} R :=
  (RelChains R X A).homology n

/-- The restriction `A → B` of `f : C(X, Y)` with `f(A) ⊆ B`. -/
def restrictPair {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (B : Set Y) (h : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun a ↦ ⟨f a, h a.2⟩, by fun_prop⟩

theorem incl_comp_restrictPair {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (h : Set.MapsTo f A B) :
    (chainsMap (R := R) (incl A)) ≫ chainsMap f =
      chainsMap (restrictPair f A B h) ≫ chainsMap (incl B) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The map `f_* : H_n(X, A; R) ⟶ H_n(Y, B; R)` induced by a map of pairs. -/
noncomputable def relMap (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (h : Set.MapsTo f A B) :
    Hrel R n X A ⟶ Hrel R n Y B :=
  HomologicalComplex.homologyMap
    (cokernel.map _ _ (chainsMap (restrictPair f A B h)) (chainsMap f)
      (incl_comp_restrictPair R f A B h)) n

end Hatcher.Singular


