-- Prove2me | Definitions.Def_ObservableActions_Reductive_Defs
-- name    : ObservableActions_Reductive_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:54.847765+00:00
-- url     : https://prove2.me/theorems/3b6d25fa-bdf7-4ab6-b900-0fa37fb9435f
-- title:
--   §4, p. 13, Def. 4.1 — unipotent points, reductive groups, the socle of an action, restricted actions on closed G-stable subsets
-- statement:
--   Throughout, $k$ is an algebraically closed field, $G$ is an affine algebraic group over $k$ with coordinate ring $k[G]$ and group of $k$-points $G(k)$, and $X$ is an affine variety with coordinate ring $k[X]$ on which $G$ acts, $g\cdot x$ denoting the induced action on $k$-points. This module introduces four notions on top of the coordinate model of the public definitions module for this paper.
--
--   1. **Unipotent points.** A point $g\in G(k)$ is *unipotent* when right translation by $g$ on $k[G]$, the linear map $T$ with $(Tf)(h)=f(hg)$ for all $h\in G(k)$, is locally unipotent: for every $f\in k[G]$ there is $n\ge 0$ with $(T-\mathrm{id})^n f=0$. This is the Jordan-decomposition characterisation of unipotent elements.
--
--   2. **Reductive groups.** $G$ is *reductive* when every subgroup $N\le G(k)$ that is normal, Zariski closed and irreducible (equivalently, connected), and all of whose elements are unipotent, is trivial. In other words, the unipotent radical of $G$ is trivial. For a disconnected $G$ this says that the identity component $G^0$ is reductive, which is the usual convention.
--
--   3. **The socle (Definition 4.1).** The *socle* of the action is the Zariski closure of the union of the closed orbits,
--   $$X_{\mathrm{soc}}=\overline{\bigcup_{\overline{\mathcal O(x)}=\mathcal O(x)}\mathcal O(x)} .$$
--
--   4. **Restricted actions.** For a subset $Z\subseteq X$ with ideal $\mathcal I(Z)\subseteq k[X]$ and coordinate ring $k[Z]=k[X]/\mathcal I(Z)$, an action $\rho_Z$ of $G(k)$ on $k[Z]$ by $k$-algebra automorphisms is the *restriction* of the action $\rho$ on $k[X]$ when the quotient map $q:k[X]\to k[Z]$ intertwines them: $\rho_Z(g)(q(f))=q(\rho(g)f)$ for all $g$ and $f$. Such a $\rho_Z$ exists exactly when $\mathcal I(Z)$ is $G$-stable, and it is then unique.
--
--   These notions are the vocabulary of §4 of the paper: Theorem 4.7 characterises the socle as the largest closed $G$-stable subset on which the restricted action is observable.
--
--   **Formalization Note.** The group $G$ is given by its coordinate ring `H` together with a group structure on its $k$-points `Point k H` $=$ `H →ₐ[k] k`, and $X$ by its coordinate ring `A`, exactly as in the referenced definitions module. Closedness of $N$ is `classicalClosure N = N` and irreducibility is primality of the ideal of functions vanishing on $N$. The linear map in the definition of a unipotent point is required to exist; it is unique because a reduced finitely generated algebra over an algebraically closed field is separated by its $k$-points, so the existential is not a loophole. A point lies in the union of the closed orbits exactly when its own orbit is closed, so the socle is `classicalClosure {x | IsClosedOrbit rho x}`.
-- source:
--   Renner–Rittatore, Observable actions of algebraic groups, arXiv:0902.0137v2, p. 13, Definition 4.1 (socle); p. 2 and §4 p. 12 (reductive group, standard notion, not defined in the paper)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10

namespace ObservableActions.Reductive

open QAlgorithms.Papers.Independent.Support21.P10

universe u v w

/-- A k-point `g` of the affine algebraic group `G = Spec H` is unipotent when right
translation by `g` on the coordinate ring `k[G] = H` is locally unipotent: the k-linear
map `T` with `T a (h) = a (h * g)` for every point `h` satisfies, for every `a`,
`(T - 1)^n a = 0` for some `n`. (Jordan decomposition criterion; `T` is unique because
a reduced finitely generated algebra over an algebraically closed field is separated
by its k-points.) -/
def IsUnipotentPoint {k : Type u} {H : Type v} [Field k] [CommRing H] [Algebra k H]
    [Group (Point k H)] (g : Point k H) : Prop :=
  ∃ T : H →ₗ[k] H, (∀ h : Point k H, ∀ a : H, h (T a) = (h * g) a) ∧
    ∀ a : H, ∃ n : ℕ, (((T - LinearMap.id : Module.End k H)) ^ n) a = 0

/-- `G = Spec H` is reductive: every Zariski-closed, irreducible (equivalently connected),
normal subgroup of `G(k)` all of whose elements are unipotent is trivial, i.e. the
unipotent radical of `G` is trivial. Closedness is `classicalClosure N = N`, irreducibility
is primality of the ideal of functions vanishing on `N`. -/
def IsReductiveGroup (k : Type u) (H : Type v) [Field k] [CommRing H] [Algebra k H]
    [Group (Point k H)] : Prop :=
  ∀ N : Subgroup (Point k H), N.Normal →
    classicalClosure (k := k) (N : Set (Point k H)) = N →
    (coordinateVanishingIdeal (k := k) (N : Set (Point k H))).IsPrime →
    (∀ g ∈ N, IsUnipotentPoint g) → N = ⊥

/-- Definition 4.1 (p. 13): the socle `X_soc` of the action, the Zariski closure of the
union of the closed orbits. A point lies in that union exactly when its own orbit is
closed. -/
def socle {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Set (Point k A) :=
  classicalClosure {x : Point k A | IsClosedOrbit rho x}

/-- `rhoZ` is the action of `G` on `k[Z] = A ⧸ I(Z)` induced by `rho`, for a subset `Z` of
the k-points of `X`: the quotient map `k[X] → k[Z]` intertwines `rho g` and `rhoZ g` for
every `g`. Such an action exists exactly when `I(Z)` is `G`-stable, and it is then unique. -/
def IsRestrictionOf {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) (Z : Set (Point k A))
    (rhoZ : Point k H →* ((A ⧸ coordinateVanishingIdeal (k := k) Z) ≃ₐ[k]
      (A ⧸ coordinateVanishingIdeal (k := k) Z))) : Prop :=
  ∀ (g : Point k H) (a : A),
    rhoZ g (Ideal.Quotient.mkₐ k (coordinateVanishingIdeal (k := k) Z) a) =
      Ideal.Quotient.mkₐ k (coordinateVanishingIdeal (k := k) Z) (rho g a)

end ObservableActions.Reductive


