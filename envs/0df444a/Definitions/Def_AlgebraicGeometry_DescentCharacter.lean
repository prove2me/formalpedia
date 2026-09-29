-- Prove2me | Definitions.Def_AlgebraicGeometry_DescentCharacter
-- name    : AlgebraicGeometry_DescentCharacter
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/fef76385-7c1f-5b7f-a4d5-6a2a45ea7fe3
-- title:
--   Descent discrepancy and base-constant values of pullback isomorphisms
-- statement:
--   Fix schemes $X,Y$, an endomorphism $T\colon X\to X$ and a morphism $q\colon X\to Y$ with $T$ followed by $q$ equal to $q$. For a sheaf of modules $M$ on $Y$, `transportIso` is the isomorphism $T^{*}(q^{*}M)\cong q^{*}M$ obtained from the pseudofunctoriality isomorphism $T^{*}q^{*}\cong (T\gg q)^{*}$ together with the congruence of inverse-image functors along the equality $T\gg q=q$; `transportNatIso` is the same datum as a natural isomorphism $q^{*}\cdot T^{*}\cong q^{*}$ of functors, and `transportNatIso_app` records that its components are the former. Given $N,M$ on $Y$ and an isomorphism $\beta\colon q^{*}N\cong q^{*}M$, `translateIso` is the $T$-translate of $\beta$, namely $T^{*}\beta$ conjugated by the transport isomorphisms at $N$ and at $M$, again an isomorphism $q^{*}N\cong q^{*}M$; `discrepancy` is the automorphism of $q^{*}M$ given by $\beta^{-1}$ followed by this translate.
--
--   For $f\colon X\to\operatorname{Spec}R$ with $R$ a commutative ring, $c\in R$ and an open $U\subseteq X$, `baseSection` is the section $c|_{U}\in\Gamma(X,U)$ obtained by transporting $c$ through the global sections of $f$ and restricting from $X$ to $U$; `baseSectionRingHom` packages $c\mapsto c|_{U}$ as a ring homomorphism $R\to\Gamma(X,U)$, and the accompanying lemmas give $1|_{U}=1$, $(cc')|_{U}=c|_{U}c'|_{U}$ and compatibility with the restriction maps of $\mathcal O_{X}$. An endomorphism $\sigma$ of a sheaf of modules $M$ on $X$ satisfies `IsBaseScalar` for $c$ when $\sigma_{U}(s)=c|_{U}\cdot s$ for every open $U$ and every $s\in\Gamma(M,U)$ — a section-wise condition, not a statement about $\Gamma(X,\mathcal O_{X})$. Then `HasValue` asserts that the discrepancy of a given $\beta$ is multiplication by $c$ in this sense, and `IsCharValue` is the existential form: some isomorphism $q^{*}N\cong q^{*}M$ has discrepancy multiplication by $c$. Both are predicates; no uniqueness of $c$ is asserted here, and `HasValue` depends on the chosen $\beta$.
--
--   **Relation to Mathlib.** The inverse-image functors on sheaves of modules over schemes and their pseudofunctoriality and congruence isomorphisms are Mathlib's (`Scheme.Modules.pullback`, `Scheme.Modules.pullbackComp`, `Scheme.Modules.pullbackCongr`); the transport, translate, discrepancy and the value predicates assembled from them are the project's own.
--
--   **Where it is used.** The guiding case is $q=[n]$ on an abelian scheme over $R$ with $T$ translation by an $n$-torsion section, where the value of the discrepancy of a trivialisation $[n]^{*}N\cong\mathcal O_A$ is the value at that section of the character attached to $N$ by descent along the $A[n]$-torsor $[n]$, i.e. Mumford's pairing; with $N=T_y^{*}\mathcal L$ and $M=\mathcal L$ one obtains the Riemann form $e_n^{\mathcal L}$. These definitions are the common vocabulary for the modules developing such pairings on torsion of elliptic curves, which underlie the Galois-theoretic properties of the mod $n$ representations used in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_DescentCharacter.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.DescentCharacter

variable {X Y : Scheme.{u}}

def transportIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (M : Y.Modules) :
    (Scheme.Modules.pullback T).obj ((Scheme.Modules.pullback q).obj M) ≅ (Scheme.Modules.pullback q).obj M :=
  (Scheme.Modules.pullbackComp T q).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

def transportNatIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) :
    Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback T ≅ Scheme.Modules.pullback q :=
  Scheme.Modules.pullbackComp T q ≪≫ Scheme.Modules.pullbackCongr h

theorem transportNatIso_app {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (M : Y.Modules) :
    (transportNatIso h).app M = transportIso h M := rfl

def translateIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M :=
  (transportIso h N).symm ≪≫ (Scheme.Modules.pullback T).mapIso β ≪≫ transportIso h M

def discrepancy {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj M :=
  β.symm ≪≫ translateIso h β

variable {R : Type u} [CommRing R]

def baseSection (f : X ⟶ Spec (CommRingCat.of R)) (c : R) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top (a := U))).op (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))

def baseSectionRingHom (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top (a := U))).op).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

@[simp] theorem baseSectionRingHom_apply (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (c : R) :
    baseSectionRingHom f U c = baseSection f c U := rfl

@[simp] theorem baseSection_one (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : baseSection f 1 U = 1 := by
  rw [← baseSectionRingHom_apply, map_one]

@[simp] theorem baseSection_mul (f : X ⟶ Spec (CommRingCat.of R)) (c c' : R) (U : X.Opens) :
    baseSection f (c * c') U = baseSection f c U * baseSection f c' U := by
  simp only [← baseSectionRingHom_apply, map_mul]

theorem map_baseSection (f : X ⟶ Spec (CommRingCat.of R)) (c : R) {U V : X.Opens} (i : V ⟶ U) :
    X.presheaf.map i.op (baseSection f c U) = baseSection f c V := by
  unfold baseSection
  rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
  rfl

def IsBaseScalar (f : X ⟶ Spec (CommRingCat.of R)) {M : X.Modules} (σ : M ⟶ M) (c : R) : Prop :=
  ∀ (U : X.Opens) (s : Γ(M, U)), σ.app U s = baseSection f c U • s

def HasValue (f : X ⟶ Spec (CommRingCat.of R)) {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) (c : R) : Prop :=
  IsBaseScalar f (discrepancy h β).hom c

def IsCharValue (f : X ⟶ Spec (CommRingCat.of R)) {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (N M : Y.Modules)
    (c : R) : Prop :=
  ∃ β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M, HasValue f h β c

end AlgebraicGeometry.DescentCharacter

end


