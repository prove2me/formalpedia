-- Prove2me | Definitions.Def_FLTPrelim_CofixedLine
-- name    : FLTPrelim_CofixedLine
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/4c534de4-c415-529a-8bd8-f35be2710c43
-- title:
--   Galois-stable cofixed lines in n-torsion of a Weierstrass curve
-- statement:
--   This module introduces a single predicate, `HasGaloisStableCofixedLine`. Fix a commutative ring $R$, a commutative ring $S$ and a field $K$ with decidable equality, arranged in a tower $R \to S \to K$ (so $K$ is an $R$- and an $S$-algebra and the scalar actions are compatible), and let $W'$ be an affine Weierstrass curve over $R$ and $n$ a natural number. Write $(W'\!\!\mathbin{/}K)$ for the base change of $W'$ to $K$ and $M =$ `Submodule.torsionBy ℤ (W'⁄K).Point n` for the group of $K$-points killed by $n$; this is a module over $\mathbb Z/n$ by the instance supplied in the project's Galois-representation module, and the group $K \simeq_{\mathrm{alg}[S]} K$ of $S$-algebra automorphisms of $K$ acts on it through `Point.map` coordinatewise. The predicate then asserts the existence of a $\mathbb Z/n$-submodule $N \subseteq M$ such that: $N$ is Galois-stable in the project's sense `IsGaloisStable` ($\sigma \cdot x \in N$ for every automorphism $\sigma$ and every $x \in N$); $N \neq \bot$ and $N \neq \top$, i.e. $N$ is a proper nonzero submodule; and $\sigma \cdot x - x \in N$ for every automorphism $\sigma$ and every $x \in M$, i.e. the action induced on the quotient $M/N$ is trivial.
--
--   Two points of shape deserve notice. First, no rank condition is imposed: "line" is only a name, and what is required is properness and nontriviality of $N$, which for $n$ prime and $M$ of dimension $2$ over $\mathbb Z/n$ amounts to $N$ being a line. Second, the stability clause is implied by the cofixing clause (for $x \in N$, $\sigma \cdot x = x + (\sigma \cdot x - x)$), so it is recorded redundantly. The group acting is the full automorphism group of $K$ over $S$, with no separate Galois hypothesis on $K/S$; in the intended application $S = \mathbb Q$ and $K$ is an algebraic closure of $\mathbb Q$, so it is the absolute Galois group.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Galois-stable or cofixed submodule of the torsion of an elliptic curve; this is the project's own predicate, built on the action of $S$-algebra automorphisms of $K$ on `(W'⁄K).Point` via `Point.map` and the $\mathbb Z/n$-module structure on `Submodule.torsionBy ℤ (W'⁄K).Point n`, both set up in the project's Galois-representation definitions.
--
--   **Where it is used.** This predicate organises the irreducibility step for the mod-$p$ representation attached to a Frey package: if the $p$-torsion of the Frey curve admits a proper nonzero Galois-stable submodule, then after excluding the case $a \equiv 3 \pmod 8$ one obtains a stable submodule on which the quotient action is trivial, i.e. a cofixed line. Statements about `HasGaloisStableCofixedLine` are then contradicted separately for small, medium and large $p$, yielding the project's `GaloisRepIsIrreducible` for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FLTPrelim_CofixedLine.lean

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

variable (S K) in

def HasGaloisStableCofixedLine (W' : Affine R) (n : ℕ) : Prop :=
  ∃ N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n),
    IsGaloisStable S N ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧
      ∀ σ : K ≃ₐ[S] K, ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x - x ∈ N

end WeierstrassCurve.Affine.Point


