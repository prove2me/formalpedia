-- Prove2me | Definitions.Def_NoetherianScheme_defs
-- name    : NoetherianScheme_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-10T22:30:48.50898+00:00
-- url     : https://prove2.me/theorems/4a3f4597-68ea-46b3-b7f9-bb817f34b9e0
-- title:
--   Locally Noetherian and Noetherian schemes
-- statement:
--   Let $X$ be a scheme. For an open subset $U \subseteq X$ write $\Gamma(X,U)=\mathcal O_X(U)$ for its ring of sections; when $U$ is an **open affine** subset, $U \cong \operatorname{Spec}\Gamma(X,U)$.
--
--   1. $X$ is **locally Noetherian** if every point $x \in X$ lies in some open affine $U$ with $\Gamma(X,U)$ a Noetherian ring, i.e. $X$ is covered by open affines $U \cong \operatorname{Spec} A$ with $A$ Noetherian.
--   2. $X$ is **Noetherian** if there are finitely many open affines $U_1,\dots,U_n$ with
--   $$X = U_1 \cup \dots \cup U_n, \qquad \Gamma(X,U_i)\ \text{Noetherian for every } i.$$
--
--   These are the two notions every statement of this mission is phrased in. They are stated directly from the source's definition, not through Mathlib's `AlgebraicGeometry.IsLocallyNoetherian` / `AlgebraicGeometry.IsNoetherian` (which use "every affine open has Noetherian sections" as the definition); the equivalence of the two is part of the mission.
--
--   **Formalization Note** An open affine $U \cong \operatorname{Spec} A$ has $A \cong \Gamma(X,U)$, so "covered by spectra of Noetherian rings" is encoded as "covered by affine opens whose rings of sections are Noetherian". The empty scheme is Noetherian (empty cover).
-- source:
--   Wikipedia, "Noetherian scheme", revision 1372079294 (https://en.wikipedia.org/w/index.php?title=Noetherian_scheme&oldid=1372079294), lead section, paragraph 1 (definition of Noetherian and locally Noetherian schemes).

import Mathlib

universe u

namespace NoetherianScheme

open AlgebraicGeometry

/-- A scheme `X` is locally Noetherian if every point of `X` lies in some open affine subset
`U ≅ Spec Γ(X, U)` whose ring of sections `Γ(X, U)` is a Noetherian ring. -/
def IsLocallyNoetherianScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U ∈ X.affineOpens, x ∈ U ∧ IsNoetherianRing Γ(X, U)

/-- A scheme `X` is Noetherian if it admits a finite covering by open affine subsets
`U_1, …, U_n` (each `U_i ≅ Spec Γ(X, U_i)`) whose rings of sections `Γ(X, U_i)` are
Noetherian rings. -/
def IsNoetherianScheme (X : Scheme.{u}) : Prop :=
  ∃ s : Finset X.Opens, (∀ U ∈ s, U ∈ X.affineOpens ∧ IsNoetherianRing Γ(X, U)) ∧
    ∀ x : X, ∃ U ∈ s, x ∈ U

end NoetherianScheme


