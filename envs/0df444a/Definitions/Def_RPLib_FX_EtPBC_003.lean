-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_003
-- name    : RPLib_FX_EtPBC_003
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:46:53.051124+00:00
-- url     : https://prove2.me/theorems/2bdc5acb-2f65-5406-afb4-4c09b2fe050b
-- title:
--   Proper base change for the projective line, library file 003
-- statement:
--   File 003 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_EAlg`: S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs
--   * `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
--   * `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
--   * `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
--   * `S4.Def_RP_EtPBC_A_O2Ap1`: S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below
--   * `S4.Def_RP_EtPBC_A_O2Bd1`: S4-EtPBC-A, O2 REL (O2Bd1): `H = 1 + t_i e` at a bad point (generic algebra)
--   * `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
--   * `S4.Def_RP_EtPBC_A_O2U`: S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`
--   * `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
--   * `S4.Def_RP_EtPBC_A_O2M2`: S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes
--   * `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2D1`: S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open
--   * `S4.Def_RP_EtPBC_A_O2D2`: S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open
--   * `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
--   * `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
--   * `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
--   * `S4.Def_RP_EtPBC_A_O2Km2`: S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition
--   * `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
--   * `S4.Def_RP_EtPBC_A_O2E2`: S4-EtPBC-A, O2 C-plan S4b (ring level): a good basic open of an etale `k[X]`-algebra at a point over `X = a`
--   * `S4.Def_RP_EtPBC_A_O2Km3`: S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2N1b`: S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map
--   * `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
--   * `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
--   * `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
--   * `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
--   * `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
--   * `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2E5b`: S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2Gl1b`: S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2
--   * `S4.Def_RP_EtPBC_A_O2GlA`: S4-EtPBC-A, O2 GLOB (O2GlA): algebra over a domain for the global approximation step
--   * `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
--   * `S4.Def_RP_EtPBC_A_O2Km5`: S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`
--   * `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_45

/-!
# Proper base change for the projective line, library file 003

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_EAlg`: S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs
* `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
* `S4.Def_RP_EtPBC_A_EmbQ`: S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate
* `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
* `S4.Def_RP_EtPBC_A_O2Ap1`: S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below
* `S4.Def_RP_EtPBC_A_O2Bd1`: S4-EtPBC-A, O2 REL (O2Bd1): `H = 1 + t_i e` at a bad point (generic algebra)
* `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
* `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
* `S4.Def_RP_EtPBC_A_O2U`: S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`
* `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
* `S4.Def_RP_EtPBC_A_O2M2`: S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes
* `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2D1`: S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open
* `S4.Def_RP_EtPBC_A_O2D2`: S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open
* `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
* `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
* `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
* `S4.Def_RP_EtPBC_A_O2Km2`: S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition
* `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
* `S4.Def_RP_EtPBC_A_O2E2`: S4-EtPBC-A, O2 C-plan S4b (ring level): a good basic open of an etale `k[X]`-algebra at a point over `X = a`
* `S4.Def_RP_EtPBC_A_O2Km3`: S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains
* `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2N1b`: S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map
* `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
* `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
* `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
* `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
* `S4.Def_RP_EtPBC_A_O2P3a`: S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps
* `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2E5b`: S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
* `S4.Def_RP_EtPBC_A_O2Gl1b`: S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2
* `S4.Def_RP_EtPBC_A_O2GlA`: S4-EtPBC-A, O2 GLOB (O2GlA): algebra over a domain for the global approximation step
* `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
* `S4.Def_RP_EtPBC_A_O2Km5`: S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`
* `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_EAlg =====
section

/-!
# S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs

Fix `e : ∐ Λ[W j] ↠ F` (`J` finite). The generators `gen W e j ∈ F(W j)` are the images of the tautological
sections `taut Λ (W j) ∈ Λ[W j](W j)`. For sections `f j ∈ H(W j)` and `x : P`, `rel W H f x` is the linear map
`(Σ j, fibre of W j at x̄) →₀ Λ → H_x̄`, `l ↦ Σ l(j, a) · germ_a (f j)`.

* `free_stalk_span`, `coprod_span`, **`free_range`**: the stalk of `∐ Λ[W j]` at `x̄` is spanned by the germs of the
  tautological sections (the range of `rel` for `tg W` is everything);
* **`exists_desc`**: if at every `x` the relations of the generators `gen W e` are relations of `f`, there is
  `φ : F ⟶ H` with `φ (gen W e j) = f j`;
* **`mono_stalk`**: if at `x` the relations of `φ (gen W e j)` are relations of `gen W e`, then `φ` is injective on
  the stalk at `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenAlg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- The germ of `s ∈ G(T)` at the point `a` of the fibre of `T` over `x̄`. -/
def germ (G : EtSh Λ P) (x : P) {T : P.Etale} (a : (geomPtAt x).point.fiber.obj T) (s : G.obj.obj (op T)) :
    stalk Λ G x :=
  ((geomPtAt x).point.toPresheafFiber T a G.obj).hom s

theorem germ_natural {G H : EtSh Λ P} (φ : G ⟶ H) (x : P) {T : P.Etale} (a : (geomPtAt x).point.fiber.obj T)
    (s : G.obj.obj (op T)) :
    (((geomPtAt x).stalkF Λ).map φ).hom (germ G x a s) = germ H x a ((φ.hom.app (op T)).hom s) :=
  congrArg (fun ψ => ψ.hom s) (GrothendieckTopology.Point.toPresheafFiber_naturality
    (Φ := (geomPtAt x).point) φ.hom T a)

theorem germ_map (G : EtSh Λ P) (x : P) {V T : P.Etale} (g : V ⟶ T) (b : (geomPtAt x).point.fiber.obj V)
    (s : G.obj.obj (op T)) :
    germ G x b ((G.obj.map g.op).hom s) = germ G x ((geomPtAt x).point.fiber.map g b) s :=
  congrArg (fun ψ => ψ.hom s) (GrothendieckTopology.Point.toPresheafFiber_w (Φ := (geomPtAt x).point) g b G.obj)

variable {J : Type u} [Finite J] (W : J → P.Etale)

/-- The linear map `l ↦ Σ l(j, a) · germ_a (f j)`. -/
def rel (G : EtSh Λ P) (f : ∀ j, G.obj.obj (op (W j))) (x : P) :
    ((Σ j, (geomPtAt x).point.fiber.obj (W j)) →₀ Λ) →ₗ[Λ] stalk Λ G x :=
  Finsupp.linearCombination Λ fun p => germ G x p.2 (f p.1)

omit [Finite J] in
theorem rel_map {G H : EtSh Λ P} (φ : G ⟶ H) (f : ∀ j, G.obj.obj (op (W j))) (x : P)
    (l : (Σ j, (geomPtAt x).point.fiber.obj (W j)) →₀ Λ) :
    (((geomPtAt x).stalkF Λ).map φ).hom (rel W G f x l) = rel W H (fun j => (φ.hom.app (op (W j))).hom (f j)) x l := by
  rw [rel, rel, Finsupp.apply_linearCombination]
  exact congrArg (fun v => Finsupp.linearCombination Λ v l) (funext fun p => germ_natural φ x p.2 (f p.1))

end RamanujanPetersson.EtPBC.GenAlg

end

end

-- ===== S4.Def_RP_EtPBC_A_EN =====
section

/-!
# S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point

* `exists_generic_open`: a closed nonempty `Z` in a noetherian scheme has a point `η` and an open `V₀ ∋ η` with
  `V₀ ∩ Z ⊆ closure {η}`;
* `gsum f τ c := Σ c_p · τ_p^* (f p.1) ∈ G(T)`; `germ_gsum` (its germ at `t` is `rel W G f x c`); `gsum_comp`;
* **`exists_good`**: an etale `T` with a point `t` over `x̄`, maps `τ_p` sending `t` to `p`, such that every relation
  `c` of the `f j` at `x̄` has `gsum f τ c = 0` on all of `T`, and `fpt t` is the only point of `T` over `x`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech GenAlg

universe u

/-- **A generic point of a closed set, with an open neighbourhood meeting the set only in its closure.** -/
theorem exists_generic_open {P : Scheme.{u}} [NoetherianSpace P] (Z : Set P) (hZ : IsClosed Z)
    (hne : Z.Nonempty) : ∃ η ∈ Z, ∃ V₀ : P.Opens, η ∈ V₀ ∧ (V₀ : Set P) ∩ Z ⊆ closure {η} := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have hSne : S.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    rw [hSU] at hz
    obtain ⟨t, ht, -⟩ := hz
    exact ⟨t, ht⟩
  obtain ⟨Z₁, hZ₁, hmax⟩ := hSf.exists_maximal hSne
  let η := (hSi Z₁ hZ₁).genericPoint
  have hη : closure {η} = Z₁ := (hSi Z₁ hZ₁).genericPoint_closure_eq.trans (hSc Z₁ hZ₁).closure_eq
  let S' := {t ∈ S | ¬ Z₁ ⊆ t}
  have hS'c : IsClosed (⋃ t ∈ S', t) :=
    (hSf.subset fun t ht => ht.1).isClosed_biUnion fun t ht => hSc t ht.1
  refine ⟨η, ?_, ⟨(⋃ t ∈ S', t)ᶜ, hS'c.isOpen_compl⟩, ?_, ?_⟩
  · rw [hSU]
    refine ⟨Z₁, hZ₁, ?_⟩
    rw [← hη]
    exact subset_closure rfl
  · intro hmem
    obtain ⟨t, ht, hηt⟩ := Set.mem_iUnion₂.1 hmem
    exact ht.2 (hη ▸ closure_minimal (Set.singleton_subset_iff.2 hηt) (hSc t ht.1))
  · rintro v ⟨hv, hvZ⟩
    rw [hSU] at hvZ
    obtain ⟨t, ht, hvt⟩ := hvZ
    by_cases h : Z₁ ⊆ t
    · rw [hη]
      exact hmax ht h hvt
    · exact (hv (Set.mem_iUnion₂.2 ⟨t, ⟨ht, h⟩, hvt⟩)).elim

section Gsum

end Gsum

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_EmbQ =====
section

/-!
# S4-EtPBC-A, R3 (degree `q` of M4): closure properties of `BCSurj q`, noetherian induction for a predicate

* `Delta.surjAt_of_isZero`, **`Delta.surjAt_biprod`** (abstract): surjectivity on germs in degree `q` holds for zero
  objects and passes to binary biproducts;
* **`bcSurj_succ_of_mono`**: `BCSurj (q+1)` passes from `H` to a subobject `F ↪ H` given `BCInj (q+1)` and
  `BCSurj q` for the cokernel (the epi four-lemma `Delta.surjAt_succ_of_ses`);
* `GenStepP Λ C`, `EmbP C`: the generic step and embeddability for an arbitrary predicate `C` on sheaves;
  **`embP_of_fgt`**: if `C` holds for zero sheaves and is closed under `⊞`, the generic step for `C` embeds every
  `FGT` sheaf into a sheaf satisfying `C` (`GenStep Λ g s = GenStepP Λ (BCSurj Λ g s 0)`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}}

/-- `F` embeds into a sheaf satisfying `C`. -/
def EmbP (C : EtSh Λ P → Prop) (F : EtSh Λ P) : Prop :=
  ∃ (H : EtSh Λ P) (m : F ⟶ H), Mono m ∧ C H

theorem embP_of_mono (C : EtSh Λ P → Prop) (h2 : ∀ H₁ H₂ : EtSh Λ P, C H₁ → C H₂ → C (H₁ ⊞ H₂))
    {F H₁ H₂ : EtSh Λ P} (m : F ⟶ H₁ ⊞ H₂) [Mono m] (h₁ : EmbP C H₁) (h₂ : EmbP C H₂) : EmbP C F := by
  obtain ⟨H₁', m₁, hm₁, hH₁⟩ := h₁
  obtain ⟨H₂', m₂, hm₂, hH₂⟩ := h₂
  have : Mono (biprod.map m₁ m₂) := inferInstance
  exact ⟨H₁' ⊞ H₂', m ≫ biprod.map m₁ m₂, mono_comp _ _, h2 _ _ hH₁ hH₂⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_CovNbB =====
section

/-!
# S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`

* `g_main`: the abstract pullback bookkeeping (no heavy terms): an iso `κ : P' ×_P Y ≅ Y_V'`, a finite surjective
  `ρ' : U' ⟶ Y_V'`, a retract `e, e'` of `Y_s` and a lift `ψ'` over `Y_x` give the `LiftT` tail;
* `surj_χ'`, `isClosedImmersion_xL`: the lift `Spec K ⟶ Spec R'` of `x` is a closed immersion;
* **`liftT_core`**, **`liftT_of_coverLiftAt`**: `CoverLiftAt` at `xV` gives `T2.LiftT (qV K gK) s π`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Gen

variable {P P' Y Ps YV Yx U' Tl : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (κ : pullback f π ⟶ YV) [IsIso κ]
  (ρ' : U' ⟶ YV)

theorem g_hh : (ρ' ≫ inv κ ≫ pullback.snd f π) ≫ π = (ρ' ≫ inv κ ≫ pullback.fst f π) ≫ f := by
  simp only [Category.assoc, pullback.condition]

theorem g_lift : pullback.lift (ρ' ≫ inv κ ≫ pullback.fst f π) (ρ' ≫ inv κ ≫ pullback.snd f π)
    (g_hh π f κ ρ').symm = ρ' ≫ inv κ := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
  · rw [pullback.lift_snd, Category.assoc]

theorem g_surj (hρs : Function.Surjective ρ') : Function.Surjective
    ⇑(pullback.lift (ρ' ≫ inv κ ≫ pullback.fst f π) (ρ' ≫ inv κ ≫ pullback.snd f π) (g_hh π f κ ρ').symm) := by
  rw [g_lift]
  intro z
  obtain ⟨y, rfl⟩ := (inv κ).surjective z
  obtain ⟨w, rfl⟩ := hρs y
  exact ⟨w, Scheme.Hom.comp_apply _ _ _⟩

end Gen

section Aux

end Aux

section Chi

end Chi

section Main

end Main

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Ap1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below

Pure algebra for Km DESIGN v3 (Rel): `O → O'` with `O' = O + t O'` (trivial residue extension along `t`, e.g.
`k[X] → B_w` for an etale neighbourhood), an `O`-algebra `S` (functions on `R`), an `O'`-algebra `Q` (functions on
the generic fibre of `W = D_o ×_P R`) and `f : S →ₐ[O] Q`; `hatS f = O'[f S] ⊆ Q`.
* `exists_pow_dense`: `x = c + t^n y` in `O'`;
* `hatS_dense`: every `q ∈ hatS f` is `f s + t^n x` with `x ∈ hatS f`;
* **`exists_approx`**: if `s ∈ hatS f` has an inverse `v` with `t^c v ∈ hatS f`, then `f u = s (1 - t z)` for some
  `u ∈ S`, `z ∈ hatS f`;
* `isIntegral_of_mem_hatS`: elements of `hatS f` are integral over `O'` when `S` is integral over `O`;
* `exists_crt`, **`exists_approx_crt`**: the same with `u` prescribed modulo finitely many pairwise coprime ideals
  of `S` that are coprime to every `(t^n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Approx

variable {O O' S Q : Type*} [CommRing O] [CommRing O'] [CommRing S] [CommRing Q]
  [Algebra O O'] [Algebra O S] [Algebra O' Q] [Algebra O Q] [IsScalarTower O O' Q]
  (f : S →ₐ[O] Q) (t : O)

/-- `O'[f S] ⊆ Q`. -/
def hatS : Subalgebra O' Q := Algebra.adjoin O' (Set.range f)

theorem exists_pow_dense (h1 : ∀ x : O', ∃ c : O, ∃ y : O', x = algebraMap O O' c + algebraMap O O' t * y)
    (n : ℕ) (x : O') : ∃ c : O, ∃ y : O', x = algebraMap O O' c + algebraMap O O' t ^ n * y := by
  induction n generalizing x with
  | zero => exact ⟨0, x, by simp⟩
  | succ n ih =>
    obtain ⟨c, y, hy⟩ := ih x
    obtain ⟨c', y', hy'⟩ := h1 y
    refine ⟨c + t ^ n * c', y', ?_⟩
    rw [hy, hy', map_add, map_mul, map_pow]
    ring

theorem exists_crt {R : Type*} [CommRing R] {ι : Type*} [Finite ι] (I : ι → Ideal R)
    (hI : Pairwise fun i j => IsCoprime (I i) (I j)) (r : ι → R) : ∃ u : R, ∀ i, u - r i ∈ I i := by
  obtain ⟨y, hy⟩ := Ideal.quotientInfToPiQuotient_surj hI (fun i => Ideal.Quotient.mk (I i) (r i))
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨u, fun i => ?_⟩
  have h := congrFun hy i
  rw [Ideal.quotientInfToPiQuotient_mk'] at h
  exact Ideal.Quotient.eq.1 h

end Approx

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd1 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd1): `H = 1 + t_i e` at a bad point (generic algebra)

REL PLAN v2 (s126), file R2, algebra part. `κ : G₀ → G'` (pull of `Γ(Y₀)` to the pieces' ring `Γ(W')` of a small chart
`D'` at a bad point), `bW' : B' → G'` with `κ ∘ alg = bW' ∘ φ'`. If `H * t^N = κ(t^N + r s)` with `s` integral over `O`
and `φ' t` a unit, then on every piece `q`: `H = 1 + r e_q`, `e_q := (κ s) (φ' t)^{-N}`, all `e_q` roots of ONE monic
`g ∈ B'[X]` of positive degree (`scaleRoots` of the integral equation of `s`, times `X`).
* **`exists_bad_genB`**.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section BadGen

variable {O G₀ G' B' : Type} [CommRing O] [CommRing G₀] [CommRing G'] [CommRing B'] [Algebra O G₀]

/-- **`H = 1 + r e_q` on every piece, `e_q` roots of one monic `g`.** -/
theorem exists_bad_genB (φ' : O →+* B') (bW' : B' →+* G') (κ : G₀ →+* G')
    (hκ : ∀ o, κ (algebraMap O G₀ o) = bW' (φ' o))
    (β : ∀ q : minimalPrimes G', B' →+* FractionRing (G' ⧸ q.1))
    (hβ : ∀ q b, β q b = algebraMap (G' ⧸ q.1) _ (Ideal.Quotient.mk q.1 (bW' b)))
    {t r : O} {N : ℕ} (v : B'ˣ) (hv : φ' t = v) {s : G₀} (hs : IsIntegral O s) {Hc : G'}
    (hH : Hc * bW' (φ' t) ^ N = κ (algebraMap O G₀ t ^ N + algebraMap O G₀ r * s)) [Nontrivial B'] :
    ∃ e : ∀ q : minimalPrimes G', FractionRing (G' ⧸ q.1), ∃ g : B'[X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ q, g.eval₂ (β q) (e q) = 0) ∧
      ∀ q : minimalPrimes G', algebraMap (G' ⧸ q.1) (FractionRing (G' ⧸ q.1)) (Ideal.Quotient.mk q.1 Hc) =
        1 + β q (φ' r) * e q := by
  obtain ⟨p, hpm, hp⟩ := hs
  let c : B' := ((v⁻¹ ^ N : B'ˣ) : B')
  have hvc : (v : B') ^ N * c = 1 := by
    show (v : B') ^ N * ((v⁻¹ ^ N : B'ˣ) : B') = 1
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
  have hu : bW' (φ' t) ^ N * bW' c = 1 := by
    rw [hv, ← map_pow, ← map_mul, hvc, map_one]
  have hH' : Hc * bW' (φ' t) ^ N = bW' (φ' t) ^ N + bW' (φ' r) * κ s := by
    rw [hH, map_add, map_mul, map_pow, hκ, hκ]
  have hHc : Hc = 1 + bW' (φ' r) * (κ s * bW' c) := by
    linear_combination (bW' c) * hH' + (1 - Hc) * hu
  refine ⟨fun q => algebraMap (G' ⧸ q.1) _ (Ideal.Quotient.mk q.1 (κ s * bW' c)),
    (p.map φ').scaleRoots c * X, ((monic_scaleRoots_iff c).2 (hpm.map φ')).mul monic_X, ?_, fun q => ?_, fun q => ?_⟩
  · rw [natDegree_mul_X ((monic_scaleRoots_iff c).2 (hpm.map φ')).ne_zero]
    exact Nat.succ_pos _
  · let φq : G' →+* FractionRing (G' ⧸ q.1) := (algebraMap (G' ⧸ q.1) _).comp (Ideal.Quotient.mk q.1)
    have hβq : ∀ b, β q b = φq (bW' b) := hβ q
    have hcomp : (β q).comp φ' = (φq.comp κ).comp (algebraMap O G₀) := by
      ext o
      simp only [RingHom.comp_apply, hβq, hκ]
    have h0 : (p.map φ').eval₂ (β q) (φq (κ s)) = 0 := by
      rw [eval₂_map, hcomp]
      have e1 := Polynomial.hom_eval₂ p (algebraMap O G₀) (φq.comp κ) s
      rw [hp, map_zero] at e1
      exact e1.symm
    have h1 := scaleRoots_eval₂_eq_zero (β q) (s := c) h0
    rw [eval₂_mul, eval₂_X]
    have he : algebraMap (G' ⧸ q.1) (FractionRing (G' ⧸ q.1)) (Ideal.Quotient.mk q.1 (κ s * bW' c)) =
        β q c * φq (κ s) := by
      rw [hβq]
      show φq (κ s * bW' c) = _
      rw [map_mul, mul_comm]
    beta_reduce
    rw [he, h1, zero_mul]
  · beta_reduce
    rw [hHc, map_add, map_one, map_add, map_one, map_mul, map_mul, hβ q (φ' r)]

end BadGen
end RamanujanPetersson.EtPBC.EtKum
end

end

-- ===== S4.Def_RP_EtPBC_A_O2MV =====
section

/-!
# S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves

For a commutative square `p₁ ≫ w = p₂ ≫ v` of `P.Etale` (`W' ⟶ W, U ⟶ Z`):
* `freeMap_comp`; `stalk_freeMap_injective`/`_surjective` (fibre map injective/surjective ⇒ stalk map so);
* `mvC`: the short complex `Λ[W'] ⟶ Λ[W] ⊞ Λ[U] ⟶ Λ[Z]` (maps `(Λ[p₁], -Λ[p₂])`, `Λ[w] + Λ[v]`);
* **`mvC_shortExact`**: short exact when every fibre of `Z` is subsingleton and at every point either the fibre of
  `W` is a singleton and `p₂` is bijective on fibres, or the fibre of `U` is a singleton and `p₁` is so;
* **`mv_exists`**: a class `β ∈ Ext^{n+1}(Λ[Z], F)` killed by `Λ[w]` and `Λ[v]` is `ε.comp κ`, `κ ∈ Ext^n(Λ[W'], F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

theorem stalk_comp_apply {A B C : EtSh Λ P} (f : A ⟶ B) (g : B ⟶ C) (x : P) (z : stalk Λ A x) :
    (((geomPtAt x).stalkF Λ).map g).hom ((((geomPtAt x).stalkF Λ).map f).hom z) =
      (((geomPtAt x).stalkF Λ).map (f ≫ g)).hom z := by
  rw [Functor.map_comp]
  rfl

variable (Λ) in
/-- The augmentation `Λ[E] ⟶ Λ`. -/
abbrev aug (E : Type u) : (E →₀ Λ) →ₗ[Λ] Λ := Finsupp.linearCombination Λ (fun _ => (1 : Λ))

theorem aug_mapDomain {E E' : Type u} (f : E → E') (l : E →₀ Λ) :
    aug Λ E' (Finsupp.mapDomain f l) = aug Λ E l := by
  rw [Finsupp.linearCombination_mapDomain]
  rfl

theorem eq_of_aug_eq {E : Type u} [Subsingleton E] {p q : E →₀ Λ} (h : aug Λ E p = aug Λ E q) : p = q := by
  ext a
  have hp : p = Finsupp.single a (p a) :=
    Finsupp.ext fun a' => by rw [Subsingleton.elim a' a, Finsupp.single_eq_same]
  have hq : q = Finsupp.single a (q a) :=
    Finsupp.ext fun a' => by rw [Subsingleton.elim a' a, Finsupp.single_eq_same]
  rw [hp, hq, Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h
  exact h

section Stalks

end Stalks

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2MVo =====
section

/-!
# S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`

* `toTop W : W ⟶ etId P`, `toTop_ext`; the fibre of `etId P` is a singleton (`topPt`, `fpt_topPt`);
* `opEt U := opn (etId P) U`: its fibre over `x̄` is subsingleton, nonempty iff `x ∈ U` (`opPt`, `mem_of_fib_opEt`);
* `prd_fib_ext`; `prW_bijective` (`x ∈ U`), `prT_bijective` (`x ∉ U`) for `prd W (opEt U)`;
* **`mvOpen_shortExact`**: `0 → Λ[W ×_P U] → Λ[W] ⊞ Λ[U] → Λ[P] → 0` is short exact when every `x ∉ U` has exactly
  one fibre point of `W` over `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo

universe u

variable {P : Scheme.{u}}

/-- The map to the terminal etale object. -/
def toTop (W : P.Etale) : W ⟶ etId P := MorphismProperty.Over.homMk W.hom (Category.comp_id _)

theorem toTop_ext {W : P.Etale} (f g : W ⟶ etId P) : f = g :=
  MorphismProperty.Over.Hom.ext (((Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f)).trans
    ((Category.comp_id g.left).symm.trans (MorphismProperty.Over.w g)).symm)

/-- The point of the fibre of `etId P`. -/
def topPt (x : P) : (geomPtAt x).point.fiber.obj (etId P) :=
  (Over.homMk (geomPtAt x).pt (Category.comp_id _) :
    CategoryTheory.Over.mk (geomPtAt x).pt ⟶ (Scheme.Etale.forget P).obj (etId P))

instance subsingleton_fib_top (x : P) : Subsingleton ((geomPtAt x).point.fiber.obj (etId P)) := by
  have h : ∀ c : (geomPtAt x).point.fiber.obj (etId P), ((geomPtAt x).liftOf c).left = (geomPtAt x).pt :=
    fun c => (Category.comp_id _).symm.trans (Over.w ((geomPtAt x).liftOf c))
  exact ⟨fun a b => fiber_ext _ ((h a).trans (h b).symm)⟩

/-- The open `U ⊆ P` as an etale object. -/
abbrev opEt (U : P.Opens) : P.Etale := opn (etId P) U

theorem fib_opn_injective (W : P.Etale) (U : W.left.Opens) (x : P) :
    Function.Injective ((geomPtAt x).point.fiber.map (opnι W U)) := fun b b' h => by
  have h1 : ((geomPtAt x).liftOf b).left ≫ U.ι = ((geomPtAt x).liftOf b').left ≫ U.ι :=
    congrArg (fun c => ((geomPtAt x).liftOf c).left) h
  exact fiber_ext _ ((cancel_mono U.ι).1 h1)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2U =====
section

/-!
# S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`

* `oneSec`: the section `1` of `Λ_P` over `P`; `freeToUnit : Λ[etId P] ⟶ Λ_P` (`taut ↦ 1`, `freeToUnit_taut`);
* `stalk_freeToUnit`: on stalks the germ of `taut` goes to `oneStalk`; **`isIso_freeToUnit`**, `unitIso`;
* `extUnit F n : H^n(P, F) ≃+ Ext^n(Λ[etId P], F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] (P : Scheme.{u})

/-- The section `1` of `Λ_P` over `P`. -/
def oneSec : (unitSh Λ P).obj.obj (op (etId P)) := (constUnit (ModuleCat.of Λ Λ) (etId P)).hom 1

variable {Λ P}

theorem oneStalk_hom (x : P) : (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom (oneStalk Λ x) = 1 :=
  congrArg (fun φ => φ.hom (1 : Λ)) (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv_hom_id

theorem eq_smul_oneStalk (x : P) (y : stalk Λ (unitSh Λ P) x) :
    y = ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom y : Λ) • oneStalk Λ x :=
  (congrArg (fun φ => ModuleCat.Hom.hom φ y) (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom_inv_id).symm.trans
    ((congrArg (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv.hom
      (mul_one ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom y)).symm).trans
      ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv.hom.map_smul
        ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom y) 1))

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes

* `mvMapHom`, **`mv_naturality`**: a morphism of MV data gives a morphism of MV complexes, so
  `ε₁ ∘ Λ[a'] = Λ[c] ∘ ε₂` in `Ext¹`.
* `mvPullHom`: `mvC(f⁻¹ data) ⟶ f^* mvC(data)` (an isomorphism), `mvPull_shortExact`;
  **`mapExact_mv`**: `f^*` of `ε.comp κ` is `ε(f⁻¹ data).comp (f^* κ)`.
* `freeToUnit_bcUnit`, **`bc_mv`**: the base change of `ε.comp κ` at a neighbourhood `j` of `s` is
  `σ_j^*(ε(ι⁻¹ data).comp (ι^* κ))`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section Nat

end Nat

section Pull

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

instance pull_preservesBinaryBiproducts : PreservesBinaryBiproducts (pull f Λ) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts (pull f Λ)

variable {W' W U Z : Y.Etale} (p₁ : W' ⟶ W) (p₂ : W' ⟶ U) (w : W ⟶ Z) (v : U ⟶ Z) (hsq : p₁ ≫ w = p₂ ≫ v)

include hsq in
theorem pull_sq : (etPull f).map p₁ ≫ (etPull f).map w = (etPull f).map p₂ ≫ (etPull f).map v := by
  rw [← Functor.map_comp, ← Functor.map_comp, hsq]

end Pull

section BC

end BC

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2M2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M2: local vanishing of cohomology classes

* `exists_local_lift`: a section of the target of an epimorphism lifts on an etale neighbourhood of any point of
  the geometric fibre;
* `vanish_one`, `vanish_succ`, **`local_vanish`**: every `β ∈ Ext^{q+1}(Λ[Z], F)` dies on an etale neighbourhood
  `a : N ⟶ Z` of any point `z` of the geometric fibre of `Z` over `x` (dimension shifting along the injective
  presentation `0 → F → I → I/F → 0`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

instance etsh_enoughInjectives : EnoughInjectives (EtSh Λ P) :=
  haveI : IsGrothendieckAbelian.{u} (EtSh Λ P) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology P (ModuleCat.{u} Λ)
  IsGrothendieckAbelian.enoughInjectives (C := EtSh Λ P)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero

For an etale `e : U ⟶ X` and `V : U.Etale`:
* `res e` is additive and exact (left and right adjoint);
* **`lshFreeIso`**: `Λ[e ∘ V] ≅ e_! Λ[V]`.
For `W : P.Etale`:
* **`freeLshIso`**: `Λ[W] ≅ e_! Λ_W` (`e = W.hom`);
* **`extFree`**: `Ext_P(Λ[W], F) ≃ H(W, F|_W)`, with `extFree_comp_mk₀` (natural in `F`) and `ext_free_eq_zero`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ]

section Free

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e]

instance res_additive' : (res e Λ).Additive where
  map_add {_ _ _ _} := Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl))

instance res_isLeftAdjoint' : (res e Λ).IsLeftAdjoint := (resAdj e Λ).isLeftAdjoint

instance res_preservesFiniteLimits' : PreservesFiniteLimits (res e Λ) := inferInstance

end Free

section GenFl

universe w₁ v₁ u₁ v₂ u₂

/-- Generic `extFree`: `Ext(A, B) ≃+ Ext(U, R B)` for `e : A ≅ L U` and `L ⊣ R` (the `HasExt` instances are implicit
binders, unified from the use site, so the concrete instantiation stays syntactic). -/
def extAdjIsoGen {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w₁} C}
    {D : Type u₂} [Category.{v₂} D] [Abelian D] {hD : HasExt.{w₁} D} [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [L.PreservesMonomorphisms] {A : D} {U : C} (e : A ≅ L.obj U) (B : D) (n : ℕ) :
    Ext.{w₁} A B n ≃+ Ext.{w₁} U (R.obj B) n :=
  (extIsoLeft e.symm B n).trans (extAdjEquiv adj U B n)

end GenFl

section Obj

variable {P : Scheme.{u}}

instance etale_hom (W : P.Etale) : Etale W.hom := W.prop

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe w v v' u₁ u₂ u

section Adj

variable {C : Type u₁} [Category.{v} C] [Abelian C] {D : Type u₂} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The adjunction map on `Ext` is natural in the source. -/
theorem extAdjMap_mk₀_comp {A₀ A : C} (c : A₀ ⟶ A) (B : D) {n : ℕ} (x : Ext.{w} (L.obj A) B n) :
    extAdjMap adj A₀ B n ((Ext.mk₀ (L.map c)).comp x (zero_add n)) =
      (Ext.mk₀ c).comp (extAdjMap adj A B n x) (zero_add n) := by
  rw [extAdjMap_apply, extAdjMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc,
    show adj.unit.app A₀ ≫ R.map (L.map c) = c ≫ adj.unit.app A from (adj.unit.naturality c).symm]

end Adj

section Nat

end Nat

section Obj

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2D1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open

`Y = Spec A` (`A` a noetherian integrally closed domain of dimension `≤ 1`), `g = gen A` its generic point.
* `bOpen f = D(f)`, `rD Λ f : Λ[D(f)] ⟶ Λ_Y` (restriction to `D(f)`);
* `exists_bOpen_zero`: a global section of a sheaf with zero stalks at non-closed points and at the generic point
  vanishes on some `D(f)`, `f ≠ 0` (finite support, `f` = product of elements of the supporting primes);
* **`push_two_dies`**: under `H²(η, -) = 0` and `R²g_* = 0`, every `β ∈ H²(Y, g_* N)` dies on some `D(f)`, `f ≠ 0`
  (`β` comes from a global section of `R¹g_* N` along `presB`, `presA`; that section vanishes on some `D(f)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

/-- The basic open `D(f)` of `Spec A`. -/
def bOpen (f : A) : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen f

theorem mem_bOpen (f : A) (x : Spec (CommRingCat.of A)) : x ∈ bOpen f ↔ f ∉ x.asIdeal :=
  PrimeSpectrum.mem_basicOpen f x

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2D2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 steps (2) and (4): every class of `H²(Spec A, F)` dies on a basic open

* `ext_eq_zero_of_comp`: dévissage along `φ : F ⟶ G` (`Ext^(n+2)(A, ker φ) = Ext^(n+1)(A, coker φ) = 0`): a class
  `e ∈ Ext^(n+2)(A, F)` with `e ∘ φ = 0` is zero;
* `isAffineOpen_bOpen`; **`acyc_bOpen`** (step (2)): `Ext^(n+1)(Λ[D(f)], Q) = 0` when `Q` has zero generic stalk,
  closed points of `Spec A` have algebraically closed residue fields and `D(f)` has a non-generic point;
* **`two_dies`** (step (4)): every `β ∈ H²(Spec A, F)` dies on some `D(f)`, `f ≠ 0` (unit `F ⟶ g_* g^* F`, its kernel
  and cokernel are acyclic on `D(f)`, and `push_two_dies`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.CurveHn

section Devissage

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {F G : C} (φ : F ⟶ G)

/-- **Dévissage, injective form.** -/
theorem ext_eq_zero_of_comp (A : C) (n : ℕ) (hK : ∀ e : Ext.{w} A (kernel φ) (n + 2), e = 0)
    (hC : ∀ e : Ext.{w} A (cokernel φ) (n + 1), e = 0) (e : Ext.{w} A F (n + 2))
    (he : e.comp (Ext.mk₀ φ) (add_zero _) = 0) : e = 0 := by
  have e1 : (s1 φ).g ≫ (s2 φ).f = φ := Abelian.image.fac φ
  have h0 : (e.comp (Ext.mk₀ (s1 φ).g) (add_zero _)).comp (Ext.mk₀ (s2 φ).f) (add_zero _) = 0 := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e1]
    exact he
  have hy : e.comp (Ext.mk₀ (s1 φ).g) (add_zero _) = 0 := by
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ _ (s2_shortExact φ)
      (e.comp (Ext.mk₀ (s1 φ).g) (add_zero _)) h0 (show n + 1 + 1 = n + 2 from rfl)
    rw [← hz, hC z, Ext.zero_comp]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ _ (s1_shortExact φ) e hy
  rw [← hx, hK x, Ext.zero_comp]

end Devissage

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

theorem isAffineOpen_bOpen (f : A) : IsAffineOpen (bOpen f) := by
  have h := (isAffineOpen_top (Spec (CommRingCat.of A))).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)
  rw [basicOpen_eq_of_affine] at h
  exact h

instance isOpenImmersion_opEt_hom (f : A) : IsOpenImmersion (opEt (bOpen f)).hom :=
  show IsOpenImmersion ((bOpen f).ι ≫ 𝟙 _) from inferInstance

theorem opEt_hom_apply (f : A) (v : (opEt (bOpen f)).left) : (opEt (bOpen f)).hom v = (bOpen f).ι v := rfl

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- A closed point of `D(f)` maps to a non-generic point when `D(f)` has a non-generic point. -/
theorem ne_genPt_of_closed (f : A) (hm : ∃ m : Spec (CommRingCat.of A), m ∈ bOpen f ∧ m ≠ GenBr.genPt A)
    (y : (opEt (bOpen f)).left) (hy : IsClosed ({y} : Set (opEt (bOpen f)).left)) :
    (opEt (bOpen f)).hom y ≠ GenBr.genPt A := by
  intro hgy
  obtain ⟨m, hmU, hmne⟩ := hm
  let m' : (opEt (bOpen f)).left := (⟨m, hmU⟩ : bOpen f)
  have hm' : (opEt (bOpen f)).hom m' = m := (opEt_hom_apply f m').trans (Scheme.Opens.ι_apply (bOpen f) ⟨m, hmU⟩)
  have hsp : (opEt (bOpen f)).hom y ⤳ (opEt (bOpen f)).hom m' := by
    rw [hgy, hm']
    exact (PrimeSpectrum.le_iff_specializes (GenBr.genPt A) m).1 bot_le
  have hsp' : y ⤳ m' := ((opEt (bOpen f)).hom.isOpenEmbedding.toIsInducing.specializes_iff).1 hsp
  have hmy : m' = y := hsp'.mem_closed hy rfl
  apply hmne
  rw [← hm', hmy, hgy]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2D3 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`

* `A1.exists_closed_mem`: a nonzero `f ∈ k[X]` is a unit at some closed point (`k` infinite);
* `two_dies_A1`: the `k[X]` instance of `two_dies` (`k = k̄`, `ℓ ≠ char k`, `ℓ^m Λ = 0`);
* `chartEt k`: the chart `A¹ ⟶ P¹` as an étale object; `chart_dies`: `β ∈ Ext²(Λ_{P¹}, F)` dies on
  `chart ∘ D(f)` (restrict to the chart with `extFree`, apply `two_dies_A1`, come back with `restrict_eq_zero`);
* `U' k f := chart ''ᵁ D(f)`, `toU'`: `opEt (U' k f) ⟶ chart ∘ D(f)` (open immersion lift);
* **`claimD`**: every `β ∈ Ext²(Λ[P¹], F)` dies on the open `U' k f` of `P¹` for some `f ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.CurveHn

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

/-- A nonzero polynomial is a unit at some non-generic point of `A¹`. -/
theorem A1.exists_closed_mem (f : k[X]) (hf : f ≠ 0) :
    ∃ m : Spec (CommRingCat.of k[X]), m ∈ bOpen f ∧ m ≠ GenBr.genPt k[X] := by
  have hex : ∃ a : k, f.eval a ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hf (Polynomial.funext (fun r => by rw [h r, eval_zero]))
  obtain ⟨a, ha⟩ := hex
  let p : Spec (CommRingCat.of k[X]) := ⟨RingHom.ker (Polynomial.evalRingHom a), RingHom.ker_isPrime _⟩
  refine ⟨p, (mem_bOpen f p).2 ?_, ?_⟩
  · change f ∉ RingHom.ker (Polynomial.evalRingHom a)
    rw [RingHom.mem_ker, coe_evalRingHom]
    exact ha
  · intro h
    have h1 : (X - C a : k[X]) ∈ RingHom.ker (Polynomial.evalRingHom a) := by
      rw [RingHom.mem_ker, coe_evalRingHom, eval_sub, eval_X, eval_C, sub_self]
    have h3 := congrArg PrimeSpectrum.asIdeal h
    change RingHom.ker (Polynomial.evalRingHom a) = (⊥ : Ideal k[X]) at h3
    rw [h3] at h1
    exact X_sub_C_ne_zero a ((Submodule.mem_bot _).1 h1)

/-- The chart `A¹ ⟶ P¹` as an étale object over `P¹`. -/
abbrev chartEt : (P1 k).Etale := Scheme.Etale.mk (chartA1 k)

/-- The open `chart(D(f))` of `P¹`. -/
def U' (f : k[X]) : (P1 k).Opens := (chartA1 k) ''ᵁ (bOpen f)

section GenDies

universe w₁ v₁ u₁

/-- Generic: if `w ∘ (s ∘ β) = 0` and `t = w ≫ s`, then `t ∘ β = 0` (`HasExt` an implicit binder). -/
theorem dies_gen {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w₁} C} {a b c F : C}
    (β : Ext.{w₁} c F 2) {t : a ⟶ c} (w : a ⟶ b) (s : b ⟶ c) (hts : t = w ≫ s)
    (h : (Ext.mk₀ w).comp ((Ext.mk₀ s).comp β (zero_add 2)) (zero_add 2) = 0) :
    (Ext.mk₀ t).comp β (zero_add 2) = 0 := by
  rw [hts, ← Ext.mk₀_comp_mk₀_assoc]
  exact h

end GenDies

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2S1 =====
section

/-!
# S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes

* `opEt_ext` (maps into `opEt U` are unique), `toOpEt`, `opEtMap`, `freeMap_id`;
* `mvC_shortExact'`: the MV criterion with "surjective onto the fibre of `Z`" instead of "nonempty";
* `locC`, **`locC_shortExact`**: the one-point MV complex `Λ[D ×_P Uo] ⟶ Λ[D] ⊞ Λ[P ∖ z] ⟶ Λ[P]` for an etale `D`
  with one geometric point over `z` and all other points over `Uo` (`Uo ⊆ P ∖ z`);
* `IsLoc Λ F z β` (one-point MV class `ε_loc ∘ κ`), `locSpan Λ F` (the subgroup they generate);
* `exists_good_one`, **`split_step`** (a class dying on `U` differs from a one-point class at `z ∉ U` by a class
  dying on `U ∪ {z}`), **`mem_locSpan_of_dies`** (induction on `#(P ∖ U)`), **`mem_locSpan_P1`**:
  `H²(P¹, F) = locSpan` (with `claimD`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

theorem opEt_left_comp {X : P.Etale} {U : P.Opens} (f : X ⟶ opEt U) : f.left ≫ U.ι = X.hom :=
  (Category.comp_id (f.left ≫ U.ι)).symm.trans ((Category.assoc _ _ _).trans (MorphismProperty.Over.w f))

/-- Maps into `opEt U` are unique. -/
theorem opEt_ext {X : P.Etale} {U : P.Opens} (f g : X ⟶ opEt U) : f = g :=
  MorphismProperty.Over.Hom.ext ((cancel_mono U.ι).1 ((opEt_left_comp f).trans (opEt_left_comp g).symm))

instance isOpenImmersion_opEt (U : P.Opens) : IsOpenImmersion (opEt U).hom :=
  show IsOpenImmersion (U.ι ≫ 𝟙 P) from inferInstance

/-- The map `X ⟶ opEt U` for an etale `X` over `U`. -/
def toOpEt (X : P.Etale) (U : P.Opens) (h : ∀ v : X.left, X.hom v ∈ U) : X ⟶ opEt U :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift (opEt U).hom X.hom (by
      rintro _ ⟨v, rfl⟩
      exact ⟨(⟨X.hom v, h v⟩ : U), rfl⟩))
    (IsOpenImmersion.lift_fac _ _ _)

/-- `opEt U ⟶ opEt V` for `U ≤ V`. -/
def opEtMap {U V : P.Opens} (h : U ≤ V) : opEt U ⟶ opEt V :=
  toOpEt (opEt U) V (fun v => by
    show (U.ι ≫ 𝟙 P) v ∈ V
    rw [Category.comp_id]
    exact h (opnι_mem (etId P) U v))

theorem bij_of_isEmpty {A B : Type*} (f : A → B) [IsEmpty B] : Function.Bijective f :=
  ⟨fun a _ _ => (IsEmpty.false (f a)).elim, fun b => (IsEmpty.false b).elim⟩

end Gen

section P1

end P1

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex

For finitely many points `z k` (`z` injective), one-point neighbourhoods `S k` of `z k` (one geometric point over
`z k`, every other point over `U₀ = P ∖ {z k}`):
* `copPrd S U₀ = ∐ (S k ×_P U₀)`, `copP₁ : copPrd ⟶ cop S`, `copP₂ : copPrd ⟶ U₀`;
* `mvCop Λ S U₀`: the MV complex `Λ[copPrd] ⟶ Λ[cop S] ⊞ Λ[U₀] ⟶ Λ[P]`;
* **`mvCop_shortExact`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} (S : ι → P.Etale) (U₀ : P.Opens)

variable (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)

include hU in
theorem exists_eq_z_of_not_mem (x : P) (hx : x ∉ U₀) : ∃ k₀, x = z k₀ := by
  by_contra hne
  push_neg at hne
  exact hx ((hU x).2 fun k => hne k)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2S2 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die

* `prdMap d X : prd D₁ X ⟶ prd D X` for `d : D₁ ⟶ D`, `prdMap_prW`, `prdMap_prT`;
* **`locC_shrink`**: `ε_loc(D₁) ∘ Λ[prdMap d] = ε_loc(D)`; **`locCls_shrink`**: the class of `κ` through `D` is the
  class of its pullback through `D₁`; `opn_sub`, `opn_nonempty`, `opn_range`, **`isLoc_opn`** (an open of `D`
  containing the points over `z` gives the same class);
* **`mv_res_W`**, **`mv_res_U`**: `ε ∘ Λ[p₁]^* γ = 0`, `ε ∘ Λ[p₂]^* γ = 0` for any MV square; `loc_res_D`,
  `loc_res_U` (the one-point case).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

section Prd

end Prd

section Shrink

end Shrink

section Opn

variable (D : P.Etale) (V : D.left.Opens) (z : P)

theorem opn_nonempty (hV : ∀ v : D.left, D.hom v = z → v ∈ V) (hDn : Nonempty ((geomPtAt z).point.fiber.obj D)) :
    Nonempty ((geomPtAt z).point.fiber.obj (opn D V)) := by
  obtain ⟨n⟩ := hDn
  have hy : fpt z n ∈ V := hV _ (fib_over z n)
  obtain ⟨b, -, -⟩ := exists_lift_fib (opnι D V) z n (⟨fpt z n, hy⟩ : V) (Scheme.Opens.ι_apply V ⟨fpt z n, hy⟩)
  exact ⟨b⟩

theorem opn_range (Uo : P.Opens) (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z) (v : (opn D V).left) :
    (opn D V).hom v ∈ Uo ∨ (opn D V).hom v = z :=
  hDr ((opnι D V).left v)

end Opn

section Res

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R4 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes

* `ext_comp_sum`, `ext_sum_comp`, `ext_mk₀_sum` (finite sums and `Ext`);
* `locLe`, `locRng`; `extClass_loc_eq`: the one-point class at `z k` is the multi-point MV class followed by
  `copPr k` (naturality along `mvLocHom`);
* **`relation_sum`**: `Σ_k ε_loc(S k) ∘ (Λ[S k ×_P U₀ ⟶ U₀]^* κ) = 0` for every `κ ∈ Ext¹(Λ[U₀], F)`;
* `isLoc_relation_term`: each summand is a one-point class (`IsLoc`) at `z k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe w u

section ExtSum

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

theorem ext_comp_sum {X Y Z : C} {a b c : ℕ} (α : Ext.{w} X Y a) {κ : Type*} (s : Finset κ)
    (β : κ → Ext.{w} Y Z b) (h : a + b = c) :
    α.comp (∑ i ∈ s, β i) h = ∑ i ∈ s, α.comp (β i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Ext.comp_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Ext.comp_add, ih]

theorem ext_sum_comp {X Y Z : C} {a b c : ℕ} {κ : Type*} (s : Finset κ) (α : κ → Ext.{w} X Y a)
    (β : Ext.{w} Y Z b) (h : a + b = c) :
    (∑ i ∈ s, α i).comp β h = ∑ i ∈ s, (α i).comp β h := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Ext.zero_comp]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Ext.add_comp, ih]

theorem ext_mk₀_sum {X Y : C} {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ Y)) :
    (Ext.mk₀ (∑ i ∈ s, f i) : Ext.{w} X Y 0) = ∑ i ∈ s, (Ext.mk₀ (f i) : Ext.{w} X Y 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Ext.mk₀_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Ext.mk₀_add, ih]

end ExtSum

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale) (U₀ : P.Opens)
  (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)
  (Uz : ι → P.Opens) (hz : ∀ k (x : P), x ∈ Uz k ↔ x ≠ z k)

include hU hz in
theorem locLe (k : ι) : U₀ ≤ Uz k := fun x hx => (hz k x).2 ((hU x).1 hx k)

include hzi hU hDr hz in
theorem locRng (k : ι) : ∀ j, j ≠ k → ∀ v : (S j).left, (S j).hom v ∈ Uz k := by
  intro j hj v
  rcases hDr j v with h | h
  · exact locLe U₀ z hU Uz hz k h
  · rw [hz, h]
    exact fun e => hj (hzi e)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition

`S : ι → X.Etale` a finite family with `∐ S k ⟶ X` an isomorphism.
* `copIso : cop S ≅ etId X` (when `(cop S).hom` is an isomorphism);
* `toId`, `copι_copIso`; `splitPr k : Λ_X ⟶ Λ[S k]`, `splitIn k : Λ[S k] ⟶ Λ_X`, `sum_split : Σ_k pr_k ≫ in_k = 𝟙`;
* **`h1_split`**: every `c ∈ H¹(X, Λ)` is `Σ_k pr_k^* ((in_k)^* c)` with `(in_k)^* c ∈ Ext¹(Λ[S k], Λ_X)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV

universe u

section Split

variable {X : Scheme.{u}} {ι : Type u} (S : ι → X.Etale) [IsIso (cop S).hom]

/-- `cop S ≅ etId X`. -/
def copIso : cop S ≅ etId X :=
  let e : (cop S).left ≅ X := @asIso _ _ _ _ ((cop S).hom : (cop S).left ⟶ X) ‹IsIso (cop S).hom›
  { hom := MorphismProperty.Over.homMk e.hom (Category.comp_id _)
    inv := MorphismProperty.Over.homMk e.inv e.inv_hom_id
    hom_inv_id := MorphismProperty.Over.Hom.ext e.hom_inv_id
    inv_hom_id := MorphismProperty.Over.Hom.ext e.inv_hom_id }

/-- The structure map of an etale `X`-scheme as a map to `etId X`. -/
def toId (V : X.Etale) : V ⟶ etId X := MorphismProperty.Over.homMk V.hom (Category.comp_id _)

theorem copι_copIso (k : ι) : copι S k ≫ (copIso S).hom = toId (S k) := by
  apply MorphismProperty.Over.Hom.ext
  exact Sigma.ι_desc (fun k => (S k).hom) k

end Split

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E1 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain

`A` Dedekind, `B` of finite type and formally unramified over `A` (e.g. etale).
* **`maximalIdeal_eq_map`**: at a prime `q` over a maximal `p`, `𝔪(B_q) = p B_q` (Mathlib's proof for finite `B`,
  with the Artinian fibre from `FormallyUnramified.finite_of_free`);
* **`isDedekindDomain_of_unramified`**: a domain `B` (with `A ↪ B`) is a Dedekind domain (incomparability from
  `Algebra.QuasiFinite.eq_of_le_of_under_eq` instead of integrality);
* **`isDomain_atPrime`**: if `B` is flat and `q` lies over `(π) ≠ 0`, then `B_q` is a domain (`𝔪 = (π)`, `π` regular,
  Krull intersection);
* **`exists_away_isDomain`**: if `B` is noetherian and `B_q` is a domain, some `B_g` (`g ∉ q`) is a domain;
* **`span_eq_of_unique`**: if `q` is the only maximal ideal containing `π`, then `π B = q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.EtPBC.EtDed

open IsLocalRing

section Max

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B]
  [Algebra.FormallyUnramified A B]

/-- **`𝔪(B_q) = p B_q`** for a prime `q` over a maximal ideal `p`. -/
theorem maximalIdeal_eq_map (q : Ideal B) [q.IsPrime] (hp : (q.under A).IsMaximal) :
    maximalIdeal (Localization.AtPrime q) =
      ((q.under A).map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) := by
  let p := q.under A
  have : p.IsMaximal := hp
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  have : Module.Free (A ⧸ p) (B ⧸ p.map (algebraMap A B)) := Module.Free.of_divisionRing _ _
  have : Module.Finite (A ⧸ p) (B ⧸ p.map (algebraMap A B)) := Algebra.FormallyUnramified.finite_of_free _ _
  have := IsArtinianRing.of_finite (A ⧸ p) (B ⧸ p.map (algebraMap A B))
  rw [← (Algebra.FormallyUnramified.isRadical_map_isMaximal A B p).radical,
    IsLocalization.map_radical q.primeCompl,
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q,
    Localization.AtPrime.map_eq_maximalIdeal]
  rw [Ideal.minimalPrimes_eq_comap]
  exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap A B))),
    IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk Ideal.map_comap_le⟩

end Max

section Ded

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain A] [IsDomain B]
  [Algebra.FiniteType A B] [Algebra.FormallyUnramified A B]

/-- Nonzero primes of `B` lie over nonzero primes of `A` (incomparability of quasi-finite algebras). -/
theorem under_ne_bot (hinj : Function.Injective (algebraMap A B)) (q : Ideal B) [q.IsPrime] (hq : q ≠ ⊥) :
    q.under A ≠ ⊥ := by
  intro h
  apply hq
  have h0 : (⊥ : Ideal B).under A = q.under A := by
    rw [h]
    ext a
    simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun ha => hinj (ha.trans (map_zero _).symm), fun ha => by rw [ha, map_zero]⟩
  exact (Algebra.QuasiFinite.eq_of_le_of_under_eq ⊥ q bot_le h0).symm

end Ded

section Dom

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- In a noetherian local ring with `𝔪 = (t)`, every nonzero element is `t^n * unit`. -/
theorem exists_pow_mul_unit (t : R) (ht : maximalIdeal R = Ideal.span {t}) (x : R) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : R), IsUnit u ∧ x = t ^ n * u := by
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  have hex : ∃ n : ℕ, x ∉ maximalIdeal R ^ n := by
    by_contra hall
    push Not at hall
    apply hx
    have : x ∈ ⨅ n : ℕ, maximalIdeal R ^ n := (Submodule.mem_iInf (fun n : ℕ => maximalIdeal R ^ n)).2 hall
    rw [hK] at this
    exact this
  classical
  let N := Nat.find hex
  have hN : x ∉ maximalIdeal R ^ N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    apply hN
    rw [h0, pow_zero, Ideal.one_eq_top]
    trivial
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxn : x ∈ maximalIdeal R ^ n := by
    by_contra h
    exact Nat.find_min hex (show n < N by omega) h
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨u, hu⟩ := hxn
  refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
  by_contra hu'
  apply hN
  have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
  rw [ht, Ideal.mem_span_singleton'] at hum
  obtain ⟨c, hc⟩ := hum
  rw [hn, ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨c, by rw [← hu, ← hc, pow_succ]; ring⟩

end Dom

section Loc

end Loc

section Away

end Away

section Span

end Span

end RamanujanPetersson.EtPBC.EtDed


end

-- ===== S4.Def_RP_EtPBC_A_O2E2 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4b (ring level): a good basic open of an etale `k[X]`-algebra at a point over `X = a`

`B` etale over `k[X]`, `q` a prime of `B` over `(X - a)`. **`exists_good_away`**: some `g ∉ q` makes `R = B_g` a
Dedekind domain in which `q R` is the only prime over `(X - a)` and `q R = (X - a) R` (so `(X - a)` is prime in `R`):
the setting of the purity theorem `EtCompact.Pur.purity_xi`.
* `exists_away_isDomain'` (`B_{g h}` is a domain for every `h ∉ q`), `algebraMap_injective_of_flat`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.EtPBC.EtDed

open Polynomial

section Away'

variable {B : Type*} [CommRing B] [IsNoetherianRing B]

/-- If `B_q` is a domain, then `B_{g h}` is a domain for some `g ∉ q` and every `h ∉ q`. -/
theorem exists_away_isDomain' (q : Ideal B) [q.IsPrime] [IsDomain (Localization.AtPrime q)] :
    ∃ g ∉ q, ∀ h ∉ q, IsDomain (Localization.Away (g * h)) := by
  classical
  let f := algebraMap B (Localization.AtPrime q)
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker f) : (RingHom.ker f).FG)
  have hc : ∀ x ∈ s, ∃ c : q.primeCompl, (c : B) * x = 0 := fun x hx =>
    (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).1
      (RingHom.mem_ker.1 (hs ▸ Ideal.subset_span hx))
  choose c hc using hc
  let g : B := ∏ x ∈ s.attach, (c x.1 x.2 : B)
  have hg : g ∈ q.primeCompl := Submonoid.prod_mem _ (fun x _ => (c x.1 x.2).2)
  have hgk : ∀ y ∈ RingHom.ker f, g * y = 0 := by
    intro y hy
    rw [← hs] at hy
    refine Submodule.span_induction (fun x hx => ?_) (mul_zero g) (fun a b _ _ ha hb => ?_)
      (fun a b _ hb => ?_) hy
    · have hxs : x ∈ s := hx
      have : (c x hxs : B) ∣ g := Finset.dvd_prod_of_mem _ (Finset.mem_attach s ⟨x, hxs⟩)
      obtain ⟨d, hd⟩ := this
      rw [hd, mul_comm (c x hxs : B) d, mul_assoc, hc x hxs, mul_zero]
    · rw [mul_add, ha, hb, add_zero]
    · rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
  refine ⟨g, hg, fun h hh => ?_⟩
  have hgh : g * h ∈ q.primeCompl := q.primeCompl.mul_mem hg hh
  have hunit : IsUnit (f (g * h)) := IsLocalization.map_units (Localization.AtPrime q) ⟨g * h, hgh⟩
  let φ : Localization.Away (g * h) →+* Localization.AtPrime q := Localization.awayLift f (g * h) hunit
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (g * h)) z
    have h1 : f y = f m * 0 := (IsLocalization.lift_mk'_spec _ _ _ _).1 hz
    rw [mul_zero] at h1
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨g * h, Submonoid.mem_powers (g * h)⟩, ?_⟩
    show g * h * y = 0
    rw [mul_comm g h, mul_assoc, hgk y (RingHom.mem_ker.2 h1), mul_zero]
  exact hφ.isDomain φ

end Away'

/-- A flat algebra over a domain is torsion free, so the algebra map is injective. -/
theorem algebraMap_injective_of_flat {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Nontrivial B]
    [Algebra A B] [Module.Flat A B] : Function.Injective (algebraMap A B) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h0
  have hreg : IsSMulRegular B r := Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h0)
  have h1 : (1 : B) = 0 := hreg (show r • (1 : B) = r • (0 : B) by rw [smul_zero, Algebra.smul_def, hr, zero_mul])
  exact one_ne_zero h1

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtDed


end

-- ===== S4.Def_RP_EtPBC_A_O2Km3 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains

`C` a commutative ring whose localizations at maximal ideals are domains.
* `isReduced_of_loc`, `eq_of_le_max`: two minimal primes inside one maximal ideal agree;
* `isCoprime_minimalPrimes`, `iInf_minimalPrimes`;
* **`piEquiv h : C ≃+* Π p : minimalPrimes C, C ⧸ p`** (`piEquiv_apply` is `rfl`);
* **`isDomain_loc_of_etale`**: for `C` etale over a Jacobson PID `A` (not a field) every `C_m` is a domain;
* **`isDedekindDomain_quot`**: for a minimal prime `p` of such `C`, `C ⧸ p` is a Dedekind domain.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC.EtDed

section Dec

variable {C : Type*} [CommRing C] (h : ∀ (m : Ideal C) [m.IsMaximal], IsDomain (Localization.AtPrime m))

include h in
theorem isReduced_of_loc : IsReduced C :=
  isReduced_ofLocalizationMaximal C fun m hm => by
    have := hm
    have := h m
    show IsReduced (Localization.AtPrime m)
    infer_instance

include h in
/-- Two minimal primes inside one maximal ideal agree. -/
theorem eq_of_le_max {p p' : Ideal C} (hp : p ∈ minimalPrimes C) (hp' : p' ∈ minimalPrimes C) (m : Ideal C)
    (hm : m.IsMaximal) (h1 : p ≤ m) (h2 : p' ≤ m) : p = p' := by
  have := hm
  have := h m
  let f := algebraMap C (Localization.AtPrime m)
  have hker : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have key : ∀ q ∈ minimalPrimes C, q ≤ m → q = RingHom.ker f := by
    intro q hq hqm
    have hle : RingHom.ker f ≤ q := by
      intro x hx
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 (RingHom.mem_ker.1 hx)
      have hsq : (s : C) ∉ q := fun hsq => s.2 (hqm hsq)
      have hmem : (s : C) * x ∈ q := by
        rw [hs]
        exact q.zero_mem
      exact ((hq.1.1).mem_or_mem hmem).resolve_left hsq
    exact le_antisymm (hq.2 ⟨hker, bot_le⟩ hle) hle
  rw [key p hp h1, key p' hp' h2]

instance [IsNoetherianRing C] : Finite (minimalPrimes C) :=
  (minimalPrimes.finite_of_isNoetherianRing C).to_subtype

end Dec

section Et

end Et

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P1 =====
section

/-!
# S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)

`B` Dedekind with fraction field `K`, `Bt = B[1/t]`, `(t)` prime.

* `locPt p hp`: the height-one prime `p Bt` of a localization; `valuation_locPt` (same valuation on `K`);
* `dvd_log_of_mem_maxUnram`: a root `α ∈ maxUnram Bt K` of `u ∈ K` gives `d ∣ log v_p(u)` for `t ∉ p`;
* `valuation_algebraMap_bot`, `root_mem_maxUnram_self`: `d ∣ log v(u)` at every height-one prime of `B` puts every
  `d`-th root of `u` in `maxUnram B K` (`root_mem_maxUnram_of_dvd` with `M = ⊥`, model `B`);
* `exists_root_unit`: `d`-th roots of units of `B` lie in `maxUnram B K`;
* **`root_mem_maxUnram_twist`**: for `α ∈ maxUnram Bt K` with `α ^ d = u`, there is `m : ℤ` such that every `d`-th root
  of `u t^m` lies in `maxUnram B K`.
-/

set_option autoImplicit false

open IsDedekindDomain

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer

section VC

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  (S : Submonoid B) [IsLocalization S Bt] (hS : S ≤ nonZeroDivisors B)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]

include hS in
/-- The height-one prime `p Bt` of the localization, for `p` disjoint from `S`. -/
def locPt (p : HeightOneSpectrum B) (hp : Disjoint (S : Set B) p.asIdeal) : HeightOneSpectrum Bt where
  asIdeal := p.asIdeal.map (algebraMap B Bt)
  isPrime := IsLocalization.isPrime_of_isPrime_disjoint S Bt _ p.isPrime hp
  ne_bot := by
    intro h
    have h1 := IsLocalization.under_map_of_isPrime_disjoint S Bt p.isPrime hp
    rw [h] at h1
    apply p.ne_bot
    rw [← h1, Ideal.under, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsLocalization.injective Bt hS)]

end VC

section Root

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Valuations do not see the field: `v (f x) = v x` for `f : K → M` over `R`. -/
theorem valuation_algebraMap_bot {M : Type} [Field M] [Algebra R M] [IsFractionRing R M] [Algebra K M]
    [IsScalarTower R K M] (v : HeightOneSpectrum R) (x : K) :
    v.valuation M (algebraMap K M x) = v.valuation K x := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

end Root

section Twist

end Twist

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1a =====
section

/-!
# S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`

For an etale `g : U ⟶ X` and `y : U` (generalizing `GalTr`, which treats open immersions):
* `eE g y`: the geometric points `ȳ ≫ g` and `(g y)‾` are isomorphic (`κ(y)/κ(g y)` is finite separable, so
  `κ(y)^sep` is a separable closure of `κ(g y)`); `sepE g y : κ(g y)^sep ≃ κ(y)^sep`;
* `galTrE g y : Gal y →* Gal (g y)` (conjugation by `sepE`, `galTrE_left`);
* `resTrIsoE g y Λ F : (g^* F)_ȳ ≅ F_(g y)‾`, natural (`resTrIsoE_natural`) and **Galois equivariant**
  (`galRep_resTrE`: `galRep (g^* F) y σ` corresponds to `galRep F (g y) (galTrE σ)`);
* `unitRes g Λ : Λ_U ⟶ g^* Λ_X` (the section `1` goes to the restriction of `1`), `resTrIsoE_unitRes`
  (`1 ↦ 1` on stalks), **`isIso_unitRes`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.GenAlg

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) (y : U)

theorem pt_mapE : ((geomPtAt y).map g).pt =
    Spec.map (g.residueFieldMap y ≫ CommRingCat.ofHom (algebraMap (U.residueField y)
      (SeparableClosure (U.residueField y)))) ≫ X.fromSpecResidueField (g y) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField y) (SeparableClosure (U.residueField y)))) ≫
    U.fromSpecResidueField y) ≫ g = _
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc]
  exact congrArg (· ≫ X.fromSpecResidueField (g y)) (Spec.map_comp _ _).symm

variable [Etale g]

theorem sep_mapE : @Algebra.IsSeparable (X.residueField (g y)) (SeparableClosure (U.residueField y)) _ _
    (g.residueFieldMap y ≫ CommRingCat.ofHom (algebraMap (U.residueField y)
      (SeparableClosure (U.residueField y)))).hom.toAlgebra := by
  let : Algebra (X.residueField (g y)) (U.residueField y) := (g.residueFieldMap y).hom.toAlgebra
  let : Algebra (X.residueField (g y)) (SeparableClosure (U.residueField y)) :=
    (g.residueFieldMap y ≫ CommRingCat.ofHom (algebraMap (U.residueField y)
      (SeparableClosure (U.residueField y)))).hom.toAlgebra
  have : IsScalarTower (X.residueField (g y)) (U.residueField y) (SeparableClosure (U.residueField y)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.IsSeparable (X.residueField (g y)) (U.residueField y) := inferInstance
  exact Algebra.IsSeparable.trans (X.residueField (g y)) (U.residueField y) _

/-- The isomorphism of geometric points `ȳ ≫ g ≅ (g y)‾`. -/
abbrev eE : CategoryTheory.Over.mk ((geomPtAt y).map g).pt ≅ CategoryTheory.Over.mk (geomPtAt (g y)).pt :=
  GPtIso.overIsoGeomPtAt (g y) ((geomPtAt y).map g) _ (pt_mapE g y) (sep_mapE g y)

variable (Λ : Type u) [CommRing Λ]

/-- **`(g^* F)_ȳ ≅ F_(g y)‾`** from germs (`resFibIso`) and `eE`. -/
def resTrIsoE (F : EtSh Λ X) : stalk Λ ((res g Λ).obj F) y ≅ stalk Λ F (g y) :=
  resFibIso g (geomPtAt y) Λ F ≪≫ ((ptIsoSheafFiber Λ (GPtIso.ptIso (eE g y))).app F).symm

theorem resTrIsoE_hom (F : EtSh Λ X) : (resTrIsoE g y Λ F).hom =
    resFib g (geomPtAt y) Λ F ≫ (ptIsoSheafFiber Λ (GPtIso.ptIso (eE g y))).inv.app F := rfl

/-! ### `Λ_U ⟶ g^* Λ_X` -/

/-- The restriction of the global section `1` of `Λ_X` to `U`, a global section of `g^* Λ_X`. -/
def oneRes : ((res g Λ).obj (unitSh Λ X)).obj.obj (op (etId U)) :=
  ((unitSh Λ X).obj.map (toTop ((etComp g).obj (etId U))).op).hom (oneSec Λ X)

theorem oneStalk_germ {P : Scheme.{u}} (x : P) : germ (unitSh Λ P) x (topPt x) (oneSec Λ P) = oneStalk Λ x :=
  congrArg (fun φ => φ.hom (1 : Λ)) (constUnit_germ (geomPtAt x) (ModuleCat.of Λ Λ) (etId P) (topPt x))

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1b =====
section

/-!
# S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map

* `hasExtEt`: a named (high priority) `HasExt` instance for etale sheaves;
* generic (any exact `Φ : C ⥤ D` of abelian categories): `mapExtU Φ u B n : Ext^n(A, B) →+ Ext^n(A', Φ B)`
  (`e ↦ mk₀ u ∘ Φ(e)`), `mapExtU_apply`, `mapSE` (image of a short exact sequence, end changed by `e : A' ≅ Φ A`),
  **`mapExtU_extClass`**;
* for an etale `g : U ⟶ X`: `resHE g F n := mapExtU (res g Λ) (unitRes g Λ) F n : H^n(X, F) →+ H^n(U, g^* F)`,
  `resHE_apply`, `resSE`, **`resHE_extClass`**.
The point transport and NAT (`trIso`, `galTrX`, `resHE_kappa`) are in O2N1c.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

universe u

/-- A named `HasExt` instance for etale sheaves: downstream terms then carry this constant instead of a fresh
`IsGrothendieckAbelian.hasExt` proof term, which the kernel would re-check in every declaration. -/
instance (priority := high) hasExtEt (Λ : Type u) [CommRing Λ] (X : Scheme.{u}) : HasExt.{u} (EtSh Λ X) :=
  inferInstance

section Gen

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasExt.{w} D] (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- `Ext^n(A, B) → Ext^n(A', Φ B)`, `e ↦ mk₀ u ∘ Φ(e)`, for `u : A' ⟶ Φ A` (generic, so the kernel stays cheap). -/
def mapExtU {A : C} {A' : D} (u : A' ⟶ Φ.obj A) (B : C) (n : ℕ) : Ext.{w} A B n →+ Ext.{w} A' (Φ.obj B) n where
  toFun e := (Ext.mk₀ u).comp (e.mapExactFunctor Φ) (zero_add n)
  map_zero' := by simp [Ext.mapExactFunctor_zero]
  map_add' x y := by simp [Ext.mapExactFunctor_add]

theorem mapExtU_apply {A : C} {A' : D} (u : A' ⟶ Φ.obj A) (B : C) (n : ℕ) (e : Ext.{w} A B n) :
    mapExtU Φ u B n e = (Ext.mk₀ u).comp (e.mapExactFunctor Φ) (zero_add n) := rfl

omit [HasExt.{w} C] [HasExt.{w} D] in
/-- The image of a short exact sequence under an exact functor, its end changed by an isomorphism. -/
theorem mapSE {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {p : X₂ ⟶ X₃} {w : f ≫ p = 0}
    (hS : (ShortComplex.mk f p w).ShortExact) {B : D} (e : B ≅ Φ.obj X₃) :
    (ShortComplex.mk (Φ.map f) (Φ.map p ≫ e.inv)
      (by rw [← Category.assoc, ← Φ.map_comp, w, Φ.map_zero, zero_comp])).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (hS.map_of_exact Φ)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e.symm
    (by exact (Category.id_comp _).trans (Category.comp_id _).symm) (by exact Category.id_comp _)

/-- Its class: `mapExtU Φ e.hom (class) = class of the image`. -/
theorem mapExtU_extClass {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {p : X₂ ⟶ X₃} {w : f ≫ p = 0}
    (hS : (ShortComplex.mk f p w).ShortExact) {B : D} (e : B ≅ Φ.obj X₃) :
    mapExtU Φ e.hom X₁ 1 hS.extClass = (mapSE Φ hS e).extClass := by
  rw [mapExtU_apply, Ext.mapExactFunctor_extClass]
  have hn := ShortComplex.ShortExact.extClass_naturality (mapSE Φ hS e) (hS.map_of_exact Φ)
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := e.hom
      comm₁₂ := by
        change 𝟙 _ ≫ Φ.map f = Φ.map f ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        change 𝟙 _ ≫ Φ.map p = (Φ.map p ≫ e.inv) ≫ e.hom
        rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id] }
  exact hn.symm.trans (Ext.comp_mk₀_id _)

end Gen

section Res

end Res

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1c =====
section

/-!
# S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)

* `trIso g h Λ F : (g^* F)_ȳ ≅ F_x̄` and `galTrX g h : Gal y → Gal x` for `h : g y = x` (`resTrIsoE`, `galTrE`
  transported along `h`), `galRep_trIso`, `trIso_natural`, `trIso_hom_injective`, `trIso_inv_natural`,
  `trIso_unitRes`, `isoHomInv`, `isoInvHom`;
* **`resHE_kappa`** (NAT): for `g : Spec A' ⟶ Spec A` etale between noetherian integrally closed domains with
  `g η' = η`, `resHE g (κ_A c) = κ_{A'} c'` whenever `trIso (c' (σ|)) = c ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

universe u

section Pt

theorem isoHomInv {Λ : Type u} [CommRing Λ] {M N : ModuleCat.{u} Λ} (e : M ≅ N) (w : M) :
    e.inv.hom (e.hom.hom w) = w :=
  congrArg (fun φ => φ.hom w) e.hom_inv_id

theorem isoInvHom {Λ : Type u} [CommRing Λ] {M N : ModuleCat.{u} Λ} (e : M ≅ N) (v : N) :
    e.hom.hom (e.inv.hom v) = v :=
  congrArg (fun φ => φ.hom v) e.inv_hom_id

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {y : U} {x : X} (h : g y = x) (Λ : Type u) [CommRing Λ]

/-- `(g^* F)_ȳ ≅ F_x̄` for `g y = x`. -/
def trIso (F : EtSh Λ X) : stalk Λ ((res g Λ).obj F) y ≅ stalk Λ F x := by
  subst h
  exact resTrIsoE g y Λ F

theorem trIso_hom_injective (F : EtSh Λ X) : Function.Injective (trIso g h Λ F).hom.hom := fun a b hab =>
  (isoHomInv (trIso g h Λ F) a).symm.trans
    ((congrArg (trIso g h Λ F).inv.hom hab).trans (isoHomInv (trIso g h Λ F) b))

end Pt

section Kappa

end Kappa

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N2 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)

* `unitCoc χ : τ ↦ χ τ • 1` (a cocycle for the trivial action on `(Λ_X)_η̄` when `χ` is additive),
  `fibRep_unitSh'`, `unitCoc_isCocycle`, `unitCoc_isLocallyConstant`;
* `kappaL A K Λ hχ hl : H¹(Spec A, Λ)`, the class of an additive locally constant `χ : π₁(A) → Λ`;
* `resLE g n : H^n(X, Λ) → H^n(U, Λ)` for an etale `g : U ⟶ X` (`resHE` and `unitResIso`);
* **`resLE_kappaL`** (NAT for constant coefficients): for `g : Spec A' ⟶ Spec A` etale with `g η' = η`,
  `resLE g 1 (κ χ) = κ χ'` whenever `χ' (σ|) = χ ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

section Unit

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] (Λ : Type) [CommRing Λ]

/-- The cocycle `τ ↦ χ(τ) • 1` with values in the stalk `(Λ_X)_η̄`. -/
def unitCoc (χ : Pi1 A K → Λ) : Pi1 A K → stalk Λ (unitSh Λ (Spec (CommRingCat.of A))) (genPt A) :=
  fun τ => χ τ • oneStalk Λ (genPt A)

theorem fibRep_unitSh' (τ : Pi1 A K) :
    EssSurj.fibRep A K (unitSh Λ (Spec (CommRingCat.of A))) isLisse_unitSh τ = LinearMap.id := by
  obtain ⟨σ, rfl⟩ := genToPi1_surjective A K τ
  rw [EssSurj.fibRep_genToPi1, galRep_unitSh]

theorem unitCoc_isCocycle {χ : Pi1 A K → Λ} (hχ : ∀ a b, χ (a * b) = χ a + χ b) :
    IsCocycle (EssSurj.fibRep A K (unitSh Λ (Spec (CommRingCat.of A))) isLisse_unitSh) (unitCoc A K Λ χ) := by
  intro a b
  rw [fibRep_unitSh', LinearMap.id_apply]
  simp only [unitCoc, hχ, add_smul]

omit [IsFractionRing A K] [IsIntegrallyClosed A] in
theorem unitCoc_isLocallyConstant {χ : Pi1 A K → Λ} (hl : IsLocallyConstant χ) :
    IsLocallyConstant (unitCoc A K Λ χ) :=
  hl.comp (fun a : Λ => a • oneStalk Λ (genPt A))

variable [IsNoetherianRing A]

/-- **The class `κ(χ) ∈ H¹(Spec A, Λ)` of an additive locally constant `χ : π₁(A) → Λ`.** -/
def kappaL {χ : Pi1 A K → Λ} (hχ : ∀ a b, χ (a * b) = χ a + χ b) (hl : IsLocallyConstant χ) :
    H Λ (unitSh Λ (Spec (CommRingCat.of A))) 1 :=
  kappa A K isLisse_unitSh (unitCoc A K Λ χ) (unitCoc_isCocycle A K Λ hχ) (unitCoc_isLocallyConstant A K Λ hl)

end Unit

section ResL

universe u

end ResL

section NatL

end NatL

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N3 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map

* `kchar_transport` (field theory): two Kummer characters agree when the two groups act compatibly through
  embeddings `e : L → Ω`, `e' : L' → Ω` and one `σ ∈ Aut Ω`, `e ζ = e' ζ'` is fixed by `σ` and `e (γ^N) = e' (γ'^N)`;
* `val_add_smul`, `kumChi hζ γ c : τ ↦ (kchar γ τ).val • c` (an additive locally constant character when
  `N • c = 0`): `kumChi_mul`, `kumChi_isLocallyConstant`;
* `sepX g h`, `resMapX g h` for `h : g y = x` (`sepE`, `residueFieldMap` transported), `galTrX_apply`,
  `sepX_algebraMap`;
* **`resLE_kappaL_kum`** (NAT for Kummer classes): `resLE g 1 (κ (kumChi ζ γ c)) = κ (kumChi ζ' γ' c)` when
  `sepX (ζ) = ζ'` and `sepX (γ^N) = γ'^N` in `κ(η')^sep`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer

section KumTr

variable {K L K' L' Ω : Type} [Field K] [Field L] [Algebra K L] [Field K'] [Field L'] [Algebra K' L'] [Field Ω]
  {N : ℕ} [NeZero N] {ζ : L} {ζ' : L'} (hζ : IsPrimitiveRoot ζ N) (hζ' : IsPrimitiveRoot ζ' N)
  {Γ : Subgroup (L ≃ₐ[K] L)} {Γ' : Subgroup (L' ≃ₐ[K'] L')}

/-- **Transport of Kummer characters** through embeddings into a common field `Ω`. -/
theorem kchar_transport (e : L →+* Ω) (e' : L' →+* Ω) (σ : Ω ≃+* Ω) (τ : Γ) (τ' : Γ')
    (hτ : ∀ x, e ((τ : L ≃ₐ[K] L) x) = σ (e x)) (hτ' : ∀ x, e' ((τ' : L' ≃ₐ[K'] L') x) = σ (e' x))
    (hζe : e ζ = e' ζ') (hσζ : σ (e' ζ') = e' ζ')
    {γ : Lˣ} {γ' : L'ˣ} (hγ : γ ∈ rad Γ N) (hγ' : γ' ∈ rad Γ' N) (hpow : e ((γ : L) ^ N) = e' ((γ' : L') ^ N)) :
    kchar hζ γ τ = kchar hζ' γ' τ' := by
  have hz : IsPrimitiveRoot (e' ζ') N := hζ'.map_of_injective e'.injective
  have ha : e (γ : L) ≠ 0 := (map_ne_zero e).mpr γ.ne_zero
  have hb : e' (γ' : L') ≠ 0 := (map_ne_zero e').mpr γ'.ne_zero
  have hab : (e (γ : L) / e' (γ' : L')) ^ N = 1 := by
    rw [div_pow, ← map_pow, ← map_pow, hpow]
    exact div_self ((map_ne_zero e').mpr (pow_ne_zero _ γ'.ne_zero))
  obtain ⟨j, -, hj⟩ := hz.eq_pow_of_pow_eq_one hab
  have hac : e (γ : L) = e' ζ' ^ j * e' (γ' : L') := by rw [hj, div_mul_cancel₀ _ hb]
  have hσa : σ (e (γ : L)) = e' ζ' ^ (kchar hζ γ τ).val * e (γ : L) := by
    rw [← hτ, kchar_spec hζ hγ τ, epow, map_mul, map_pow, hζe]
  have hσb : σ (e' (γ' : L')) = e' ζ' ^ (kchar hζ' γ' τ').val * e' (γ' : L') := by
    rw [← hτ', kchar_spec hζ' hγ' τ', epow, map_mul, map_pow]
  have h1 : e' ζ' ^ (kchar hζ γ τ).val * e (γ : L) = e' ζ' ^ (kchar hζ' γ' τ').val * e (γ : L) := by
    rw [← hσa, hac, map_mul, map_pow, hσζ, hσb]
    ring
  exact ZMod.val_injective N (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (mul_right_cancel₀ ha h1))

end KumTr

section KumChi

theorem val_add_smul {M : Type*} [AddCommGroup M] {N : ℕ} [NeZero N] {c : M} (hc : N • c = 0) (a b : ZMod N) :
    (a + b).val • c = a.val • c + b.val • c := by
  rw [ZMod.val_add, ← add_smul]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, add_smul, mul_comm N, mul_smul, hc, smul_zero, add_zero]

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
  {Λ : Type} [AddCommGroup Λ]

/-- The Kummer character `τ ↦ (kchar γ τ).val • c` on the whole Galois group. -/
def kumChi (γ : Eˣ) (c : Λ) (τ : E ≃ₐ[K] E) : Λ :=
  (kchar hζ γ (⟨τ, Subgroup.mem_top τ⟩ : (⊤ : Subgroup (E ≃ₐ[K] E)))).val • c

end KumChi

section Sep

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {y : U} {x : X} (h : g y = x)

/-- `κ(x) → κ(y)` for `g y = x` (`residueFieldMap` transported along `h`). -/
def resMapX : X.residueField x →+* U.residueField y := by
  subst h
  exact (g.residueFieldMap y).hom

end Sep

section KumNat

end KumNat

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P2 =====
section

/-!
# S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)

* `exists_cdec`: a locally constant additive `χ : G → Λ` with finite image (`N • Λ = 0`) is
  `σ ↦ ∑ i, (c i σ).val • g i` with `c i : G → ZMod (d i)` additive locally constant, `d i ∣ N`, `d i • g i = 0`;
* `zvHom hg : ZMod d →+ Λ`, `a ↦ a.val • g` (`d • g = 0`), `zvHom_intCast`, `zvHom_apply`;
* `kchar_npow`, `kchar_inv`, `kchar_zpow`: `kchar (γ ^ m) = m * kchar γ`; `mem_rad_of_pow_eq`;
* `kumChi_twist`: `kumChi_d α g = kumChi_d (α τ^{(N/d) m}) g + kumChi_N τ ((-m) • g)`;
* `exists_tau`: an `N`-th root `τ` of `t` in `maxUnram Bt K`;
* **`cyc_twist`**: every locally constant additive `c : π₁(Bt) → ZMod d` gives `(c σ).val • g` as a Kummer character
  `kumChi_d α g` with `α ^ d = u ∈ K` having a `d`-th root in `maxUnram B K`, plus `kumChi_N τ ((-m) • g)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Cdec

variable {G Λ : Type*} [Group G] [TopologicalSpace G] [AddCommGroup Λ]

/-- **Cyclic decomposition** of a finite-image additive character. -/
theorem exists_cdec {N : ℕ} [NeZero N] (hΛ : ∀ x : Λ, N • x = 0) (χ : G → Λ)
    (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) (hχc : IsLocallyConstant χ) (hfin : (Set.range χ).Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (_ : ∀ i, NeZero (d i)) (g : ι → Λ)
      (c : ∀ i, G → ZMod (d i)), (∀ i, d i ∣ N) ∧ (∀ i, d i • g i = 0) ∧ (∀ i, IsLocallyConstant (c i)) ∧
      (∀ i σ τ, c i (σ * τ) = c i σ + c i τ) ∧ ∀ σ, χ σ = ∑ i, (c i σ).val • g i := by
  classical
  have h1 : χ 1 = 0 := by
    have h := hχ 1 1
    rw [mul_one] at h
    exact (add_eq_left.mp h.symm)
  let F : AddSubgroup Λ :=
    { carrier := Set.range χ
      add_mem' := by
        rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
        exact ⟨σ * τ, hχ σ τ⟩
      zero_mem' := ⟨1, h1⟩
      neg_mem' := by
        rintro _ ⟨σ, rfl⟩
        refine ⟨σ⁻¹, ?_⟩
        have h := hχ σ⁻¹ σ
        rw [inv_mul_cancel, h1] at h
        exact eq_neg_of_add_eq_zero_left h.symm }
  have : Finite F := hfin.to_subtype
  have mem : ∀ σ, χ σ ∈ F := fun σ => Set.mem_range_self σ
  obtain ⟨ι, hι, p, hp, ex, ⟨φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite F
  have hdne : ∀ i, NeZero (p i ^ ex i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let ofi : ∀ i, ZMod (p i ^ ex i) →+ DirectSum ι (fun i => ZMod (p i ^ ex i)) :=
    fun i => DirectSum.of (fun i => ZMod (p i ^ ex i)) i
  let g : ι → Λ := fun i => F.subtype (φ.symm (ofi i 1))
  have hof : ∀ i (n : ℕ), n • ofi i 1 = ofi i (n : ZMod (p i ^ ex i)) := fun i n => by
    rw [← map_nsmul, nsmul_eq_mul, mul_one]
  have hdN : ∀ i, p i ^ ex i ∣ N := by
    intro i
    have e1 : φ.symm (N • ofi i 1) = 0 := by
      apply Subtype.ext
      rw [map_nsmul]
      exact hΛ _
    rw [map_eq_zero_iff φ.symm φ.symm.injective, hof] at e1
    have e2 : ((N : ℕ) : ZMod (p i ^ ex i)) = 0 :=
      DirectSum.of_injective (β := fun i => ZMod (p i ^ ex i)) i (e1.trans (map_zero _).symm)
    exact (ZMod.natCast_eq_zero_iff N _).mp e2
  let c : ∀ i, G → ZMod (p i ^ ex i) := fun i σ =>
    (fun l : Λ => if h : l ∈ F then φ ⟨l, h⟩ i else 0) (χ σ)
  have hcv : ∀ i σ, c i σ = φ ⟨χ σ, mem σ⟩ i := fun i σ => dif_pos (mem σ)
  refine ⟨ι, hι, fun i => p i ^ ex i, hdne, g, c, hdN, fun i => ?_,
    fun i => hχc.comp (fun l : Λ => if h : l ∈ F then φ ⟨l, h⟩ i else 0), fun i σ τ => ?_, fun σ => ?_⟩
  · have e : (p i ^ ex i) • ofi i 1 = 0 := by rw [hof, ZMod.natCast_self, map_zero]
    show (p i ^ ex i) • F.subtype (φ.symm (ofi i 1)) = 0
    rw [← map_nsmul, ← map_nsmul, e, map_zero, map_zero]
  · rw [hcv, hcv, hcv]
    have e : (⟨χ (σ * τ), mem _⟩ : F) = ⟨χ σ, mem σ⟩ + ⟨χ τ, mem τ⟩ := Subtype.ext (hχ σ τ)
    rw [e, map_add, DirectSum.add_apply]
  · have e0 : χ σ = F.subtype (φ.symm (φ ⟨χ σ, mem σ⟩)) := by
      rw [AddEquiv.symm_apply_apply]
      rfl
    rw [e0, ← DirectSum.sum_univ_of (φ ⟨χ σ, mem σ⟩), map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := hdne i
    rw [← hcv i σ]
    show F.subtype (φ.symm (ofi i (c i σ))) = _
    conv_lhs => rw [← ZMod.natCast_zmod_val (c i σ)]
    rw [← hof, map_nsmul, map_nsmul]

end Cdec

section Zv

variable {Λ : Type*} [AddCommGroup Λ] {d : ℕ} {g : Λ}

/-- `a ↦ a.val • g` as an additive map `ZMod d →+ Λ` when `d • g = 0`. -/
def zvHom (hg : d • g = 0) : ZMod d →+ Λ :=
  ZMod.lift d ⟨zmultiplesHom Λ g, by rw [zmultiplesHom_apply, natCast_zsmul, hg]⟩

theorem zvHom_intCast (hg : d • g = 0) (m : ℤ) : zvHom hg (m : ZMod d) = m • g := by
  rw [zvHom, ZMod.lift_coe, zmultiplesHom_apply]

theorem zvHom_apply [NeZero d] (hg : d • g = 0) (a : ZMod d) : zvHom hg a = a.val • g := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [← Int.cast_natCast (R := ZMod d), zvHom_intCast, natCast_zsmul]

end Zv

section KZ

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)} {N : ℕ} [NeZero N]
  {ζ : E} (hζ : IsPrimitiveRoot ζ N)

omit [NeZero N] in
theorem mem_rad_of_pow_eq {α : Eˣ} {u : K} (h : (α : E) ^ N = algebraMap K E u) : α ∈ rad Γ N := by
  intro σ _
  rw [h, AlgEquiv.commutes]

end KZ

section Twist2

end Twist2

section Cyc

end Cyc

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P3a =====
section

/-!
# S4-EtPBC-A, O2 M5 P3a: the character group and additive class maps

* `ChL A K Λ`: the additive group of additive locally constant characters `π₁(A) → Λ`; `mem_ChL`, `chl_cyc`;
* `zetaE_prim`, `zetaE_fix`: a primitive root `ζ₀ ∈ K` in `maxUnram A K`;
* `kumTau hζ hζΓ hτ hΛ : Λ →+ ChL`, `c ↦ kumChi ζ τ c`;
* **`kappaLH A K Λ : ChL A K Λ →+ H¹(Spec A, Λ)`** (`kappaL`, additive by `kappa_add`), **`kappaLH_surj`**;
* `resLEHom g n : H^n(X, Λ) →+ H^n(U, Λ)` (`resLE` is additive).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section ChL

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (Λ : Type) [AddCommGroup Λ]

/-- Additive locally constant characters `π₁(A) → Λ`. -/
def ChL : AddSubgroup (Pi1 A K → Λ) where
  carrier := {χ | (∀ a b, χ (a * b) = χ a + χ b) ∧ IsLocallyConstant χ}
  add_mem' := by
    rintro χ₁ χ₂ ⟨h₁, l₁⟩ ⟨h₂, l₂⟩
    refine ⟨fun a b => ?_, l₁.add l₂⟩
    simp only [Pi.add_apply, h₁, h₂]
    abel
  zero_mem' := ⟨fun _ _ => (add_zero 0).symm, IsLocallyConstant.const 0⟩
  neg_mem' := by
    rintro χ ⟨h, l⟩
    exact ⟨fun a b => by simp only [Pi.neg_apply, h, neg_add], l.neg⟩

variable {A K Λ}

theorem mem_ChL {χ : Pi1 A K → Λ} :
    χ ∈ ChL A K Λ ↔ (∀ a b, χ (a * b) = χ a + χ b) ∧ IsLocallyConstant χ := Iff.rfl

theorem chl_cyc {d : ℕ} (hd : NeZero d) {c : Pi1 A K → ZMod d} (hc : IsLocallyConstant c)
    (hhom : ∀ a b, c (a * b) = c a + c b) {g : Λ} (hg : d • g = 0) :
    (fun σ => (c σ).val • g) ∈ ChL A K Λ :=
  mem_ChL.2 ⟨fun a b => by have := hd; rw [hhom, val_add_smul hg], hc.comp (fun k : ZMod d => k.val • g)⟩

variable (A) in
theorem zetaE_prim {ζ0 : K} {N : ℕ} (hζ0 : IsPrimitiveRoot ζ0 N) :
    IsPrimitiveRoot (algebraMap K (maxUnram A K) ζ0) N :=
  hζ0.map_of_injective (algebraMap K (maxUnram A K)).injective

variable (A) in
theorem zetaE_fix (ζ0 : K) :
    ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ (algebraMap K (maxUnram A K) ζ0) = algebraMap K (maxUnram A K) ζ0 :=
  fun σ _ => σ.commutes ζ0

end ChL

section KappaLH

end KappaLH

section ResH

universe u

end ResH

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E5 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)

* generic: **`mapExact_comp_iso`**: for exact `Φ`, `Ψ`, `Φ'` and `τ : Φ ⋙ Ψ ≅ Φ'`, `Ψ(Φ ξ) ∘ τ_B = τ_A ∘ Φ' ξ`
  on `Ext¹` (enough injectives);
* for `m : W' ⟶ W` in `P.Etale`: `Etale m.left`, `etCompCompIso m`, `resCompIso Λ m : res W ⋙ res m ≅ res W'`;
* `diagSec Λ W : Λ_W ⟶ Λ[W]|_W` with `extFree_eq` (`extFree β = diagSec ∘ β|_W`) and `diagSec_sec`;
* **`diagSec_natural`**: `diagSec W' ≫ Λ[m]|_W' = unitRes m.left ≫ (diagSec W)|_W' ≫ (resCompIso m)_{Λ[W]}`.
`extFree_natural` is in O2E5b.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w} E]
  (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (Ψ : D ⥤ E) [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
  {Φ' : C ⥤ E} [Φ'.Additive] [PreservesFiniteLimits Φ'] [PreservesFiniteColimits Φ']

theorem mapExact_mapExact_extClass {S : ShortComplex C} (hS : S.ShortExact) :
    (hS.extClass.mapExactFunctor Φ).mapExactFunctor Ψ = ((hS.map_of_exact Φ).map_of_exact Ψ).extClass :=
  (congrArg (Ext.mapExactFunctor Ψ) (Ext.mapExactFunctor_extClass Φ hS)).trans
    (Ext.mapExactFunctor_extClass Ψ (hS.map_of_exact Φ))

theorem mapExact_mapExact_comp_extClass {S : ShortComplex C} (hS : S.ShortExact) {A : C} (c : A ⟶ S.X₃) :
    (((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor Φ).mapExactFunctor Ψ =
      (Ext.mk₀ (Ψ.map (Φ.map c))).comp ((hS.map_of_exact Φ).map_of_exact Ψ).extClass (zero_add 1) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
    mapExact_mapExact_extClass]
  rfl

theorem extClass_comp_iso (τ : Φ ⋙ Ψ ≅ Φ') {S : ShortComplex C} (hS : S.ShortExact) :
    ((hS.map_of_exact Φ).map_of_exact Ψ).extClass.comp (Ext.mk₀ (τ.hom.app S.X₁)) (add_zero 1) =
      (Ext.mk₀ (τ.hom.app S.X₃)).comp (hS.map_of_exact Φ').extClass (zero_add 1) := by
  let f : (S.map Φ).map Ψ ⟶ S.map Φ' :=
    { τ₁ := τ.hom.app S.X₁, τ₂ := τ.hom.app S.X₂, τ₃ := τ.hom.app S.X₃
      comm₁₂ := (τ.hom.naturality S.f).symm
      comm₂₃ := (τ.hom.naturality S.g).symm }
  exact ShortComplex.ShortExact.extClass_naturality ((hS.map_of_exact Φ).map_of_exact Ψ) (hS.map_of_exact Φ') f

theorem mapExact_comp_extClass {S : ShortComplex C} (hS : S.ShortExact) {A : C} (c : A ⟶ S.X₃) :
    ((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor Φ' =
      (Ext.mk₀ (Φ'.map c)).comp (hS.map_of_exact Φ').extClass (zero_add 1) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_extClass]
  rfl

theorem mapExact_comp_iso_aux (τ : Φ ⋙ Ψ ≅ Φ') {S : ShortComplex C} (hS : S.ShortExact) {A : C} (c : A ⟶ S.X₃) :
    ((((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor Φ).mapExactFunctor Ψ).comp
      (Ext.mk₀ (τ.hom.app S.X₁)) (add_zero 1) =
      (Ext.mk₀ (τ.hom.app A)).comp (((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor Φ') (zero_add 1) := by
  have hc : Ψ.map (Φ.map c) ≫ τ.hom.app _ = τ.hom.app A ≫ Φ'.map c := τ.hom.naturality c
  refine (congrArg (fun x => Ext.comp x (Ext.mk₀ (τ.hom.app S.X₁)) (add_zero 1)) (mapExact_mapExact_comp_extClass Φ Ψ hS c)).trans ?_
  refine (Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by norm_num)).trans ?_
  refine (congrArg (fun x => Ext.comp (Ext.mk₀ (Ψ.map (Φ.map c))) x (zero_add 1)) (extClass_comp_iso Φ Ψ τ hS)).trans ?_
  refine (Ext.mk₀_comp_mk₀_assoc _ _ _).trans ?_
  refine (congrArg (fun g => Ext.comp (Ext.mk₀ g) (hS.map_of_exact Φ').extClass (zero_add 1)) hc).trans ?_
  refine (Ext.mk₀_comp_mk₀_assoc _ _ _).symm.trans ?_
  exact congrArg (fun x => Ext.comp (Ext.mk₀ (τ.hom.app A)) x (zero_add 1)) (mapExact_comp_extClass hS c).symm

/-- **`Ψ ∘ Φ` and `Φ'` act alike on `Ext¹`, along `τ : Φ ⋙ Ψ ≅ Φ'`.** -/
theorem mapExact_comp_iso [EnoughInjectives C] (τ : Φ ⋙ Ψ ≅ Φ') {A B : C} (ξ : Ext.{w} A B 1) :
    ((ξ.mapExactFunctor Φ).mapExactFunctor Ψ).comp (Ext.mk₀ (τ.hom.app B)) (add_zero 1) =
      (Ext.mk₀ (τ.hom.app A)).comp (ξ.mapExactFunctor Φ') (zero_add 1) := by
  obtain ⟨γ, rfl⟩ := Ext.covariant_sequence_exact₁ (X := A) (hS := injPres_shortExact B) ξ
    (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨c, rfl⟩ := (Ext.mk₀_bijective _ _).2 γ
  exact mapExact_comp_iso_aux Φ Ψ τ (injPres_shortExact B) c

end Gen

section Nat

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {W W' : P.Etale} (m : W' ⟶ W)

theorem etComp_cont {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] :
    (etComp g).IsContinuous U.smallEtaleTopology X.smallEtaleTopology :=
  inferInstance

instance etale_ovLeft : Etale m.left := by
  have : Etale (m.left ≫ W.hom) := by rw [MorphismProperty.Over.w m]; exact W'.prop
  exact Etale.of_comp _ W.hom

end Nat

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E5b =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0b: `extFree` is natural in the etale object (degree 1)

**`extFree_natural`**: for `m : W' ⟶ W` in `P.Etale` and `ξ : Ext¹_P(Λ[W], F)`,
`extFree W' (ξ ∘ Λ[m]) = (resHE m.left (extFree W ξ)) ∘ (resCompIso m)_F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {Cp : Type u₁} [Category.{v₁} Cp] [Abelian Cp] {hCp : HasExt.{w} Cp} [EnoughInjectives Cp]
  {Cw : Type u₂} [Category.{v₂} Cw] [Abelian Cw] {hCw : HasExt.{w} Cw}
  {Cw' : Type u₃} [Category.{v₃} Cw'] [Abelian Cw'] {hCw' : HasExt.{w} Cw'}

/-- Generic `extFree_eq`: the adjunction form of `Ext¹(Λ[W], B)`. -/
theorem extAdj_eq_gen {L : Cw ⥤ Cp} {R : Cp ⥤ Cw} (adj : L ⊣ R) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [L.PreservesMonomorphisms] {A : Cp} {U : Cw} (e : A ≅ L.obj U) (B : Cp) (n : ℕ)
    (β : Ext.{w} A B n) :
    ((extIsoLeft e.symm B n).trans (extAdjEquiv adj U B n)) β =
      (Ext.mk₀ (adj.homEquiv U A e.inv)).comp (β.mapExactFunctor R) (zero_add n) := by
  rw [AddEquiv.trans_apply, extIsoLeft_apply, extAdjEquiv_apply, extAdjMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, Adjunction.homEquiv_unit]
  rfl

end Gen

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km4 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains

* `piHom e k : Spec (R k) ⟶ X`, `piS e k : X.Etale` for a ring isomorphism `e : Γ(X, ⊤) ≃+* Π k, R k`;
  `cop_piS_hom`, `IsIso (cop (piS e)).hom` (via `sigmaSpec`);
* `kapS h Λ p χ = pr_p^* (extFreeU⁻¹ (κ(χ)))`: the Kummer class of a character `χ` of `π₁(Γ ⧸ p)` as a class
  in `H¹(X, Λ)` (`Γ = Γ(X, ⊤)` noetherian, localizations at maximal ideals domains, `p` a minimal prime);
  `kapS_apply`. The decomposition theorem `h1_exists_kappa` is in O2Km4b (split for the kernel budget).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur

universe u

instance isPrime_minimalPrimes {C : Type*} [CommRing C] (p : minimalPrimes C) : (p : Ideal C).IsPrime :=
  p.2.1.1

section PiS

variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} {R : ι → Type u} [∀ k, CommRing (R k)]
  (e : Γ(X, ⊤) ≃+* Π k, R k)

instance isIso_ofHom_equiv : IsIso (CommRingCat.ofHom e.toRingHom) :=
  (RingEquiv.toCommRingCatIso e).isIso_hom

/-- The `k`-th piece `Spec (R k) ⟶ X` of a product decomposition of `Γ(X, ⊤)`. -/
def piHom (k : ι) : Spec (CommRingCat.of (R k)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) k)) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    X.isoSpec.inv

end PiS

section GenKap
universe w v₁ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w} C}

def precompSymmGen {A B Z : C} (u : A ⟶ B) {M : Type u₂} {N : Type u₃} [AddCommGroup M] [AddCommGroup N]
    (e : Ext.{w} B Z 1 ≃+ N) (κ : M →+ N) : M →+ Ext.{w} A Z 1 :=
  ((Ext.mk₀ u).precomp Z (zero_add 1)).comp (e.symm.toAddMonoidHom.comp κ)

end GenKap

section Kappa

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1b =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1b): the algebra of stages S1-S2

GLOB/REL PLAN v1, stages S1-S2 (pure algebra). `Q = Π_p Frac(G ⧸ p)` over the minimal primes of `G` (`G = Γ(W₁)`).
* `exists_pow_mul_mem_hatS` (Gen): if `L^N • y ∈ S` for every `y` and `L = t^e L'` with `L'` a unit in `O'`, then every
  `q ∈ O'[F Y]` has `t^N q ∈ hatS (F|_S)`;
* `mem_adjoin_map`: `O'`-algebra maps carry `O'[F₀ Y]` into `O'[ψ F₀ Y]`;
* `pow_mul_div_mem_range`: `x ∣ τ^e w₁`, `y ∣ τ^e' w₂` (`wᵢ` units) ⇒ `τ^(e+e') (x/y)^{±1}` are integral elements;
* `toPiQ`, `exists_toPiQ_update`: CRT over the pieces (`piEquiv`, O2Km3);
* **`exists_glob_approx`** (S1 + S2): `f u_S = t^N ũ (1 - t z)`, `ũ = (u₁ on p₀, 1 elsewhere)`, `z ∈ hatS`,
  `u_S ≡ r_i mod J_i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Gen

variable {O O' Y Q : Type*} [CommRing O] [CommRing O'] [CommRing Y] [CommRing Q]
  [Algebra O O'] [Algebra O Y] [Algebra O' Q] [Algebra O Q] [IsScalarTower O O' Q]

theorem mem_adjoin_map {G : Type*} [CommRing G] [Algebra O' G] (F₀ : Set G) (ψ : G →ₐ[O'] Q) {x : G}
    (hx : x ∈ Algebra.adjoin O' F₀) : ψ x ∈ Algebra.adjoin O' (ψ '' F₀) := by
  rw [← AlgHom.map_adjoin]
  exact ⟨x, hx, rfl⟩

end Gen

section Frac

theorem pow_mul_div_mem_range {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {x y τ w : A} {e : ℕ} (hy : y ∣ τ ^ e * w) (hw : IsUnit w) (hy0 : y ≠ 0) :
    ∃ a : A, algebraMap A K a = algebraMap A K τ ^ e * (algebraMap A K x / algebraMap A K y) := by
  obtain ⟨b, hb⟩ := hy
  obtain ⟨v, rfl⟩ := hw
  have hY : algebraMap A K y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hy0
  have hv : algebraMap A K ↑v * algebraMap A K ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hb' : algebraMap A K τ ^ e * algebraMap A K ↑v = algebraMap A K y * algebraMap A K b := by
    rw [← map_pow, ← map_mul, ← map_mul, hb]
  have h1 : algebraMap A K τ ^ e = algebraMap A K y * (algebraMap A K b * algebraMap A K ↑v⁻¹) := by
    linear_combination algebraMap A K ↑v⁻¹ * hb' - algebraMap A K τ ^ e * hv
  refine ⟨x * b * ↑v⁻¹, ?_⟩
  rw [h1, map_mul, map_mul]
  field_simp

end Frac

section PiQ

variable {G : Type*} [CommRing G]

/-- `x ↦ (x mod p)_p` into the product of the fraction fields of the pieces. -/
def toPiQ : G →+* ∀ p : minimalPrimes G, FractionRing (G ⧸ (p : Ideal G)) :=
  RingHom.pi fun p => (algebraMap (G ⧸ (p : Ideal G)) _).comp (Ideal.Quotient.mk _)

end PiQ

section Glob

/-- `Π_p Frac(G ⧸ p)` over the minimal primes. -/
abbrev PiQ (G : Type*) [CommRing G] : Type _ := ∀ p : minimalPrimes G, FractionRing (G ⧸ (p : Ideal G))

end Glob

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2GlA =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2GlA): algebra over a domain for the global approximation step

Pure algebra for GLOB/REL PLAN v1 (3): `A` an `R`-algebra over a domain `R` (in use `R = k[X]`, `A = Γ(Y₀)` or a
piece `Γ(W)/p`).
* `isAlgebraic_of_quasiFinite`, `algebra_isAlgebraic_of_etale`: quasi-finite (e.g. etale) algebras over a domain
  are algebraic (the generic fibre `K ⊗ A` is finite over `K = Frac R`, and `A → K ⊗ A` kills only torsion);
* `dvd_algebraMap_trailingCoeff`, **`exists_dvd_algebraMap`** (3a): a nonzerodivisor `x` that is algebraic over
  `R` divides the image of some nonzero `c ∈ R` (the trailing coefficient of a relation);
* **`exists_pow_smul_isIntegral`** (3b): for `A` of finite type and algebraic over a domain `R` there is ONE
  nonzero `L ∈ R` with `∀ y, ∃ N, L ^ N • y` integral over `R`;
* `exists_eq_pow_mul_eval_ne_zero` (3c): `F = (X - a)^e F'` with `F'(a) ≠ 0`;
* `isIntegral_of_isIdempotentElem`: idempotents are integral.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open Polynomial
open scoped TensorProduct

section GlA

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- (3a) A nonzerodivisor root of `p` divides the image of the trailing coefficient of `p`. -/
theorem dvd_algebraMap_trailingCoeff {x : A} (hx : x ∈ nonZeroDivisors A) {p : R[X]}
    (hp : aeval x p = 0) : x ∣ algebraMap R A p.trailingCoeff := by
  set n := p.natTrailingDegree with hn
  obtain ⟨q, hq⟩ : X ^ n ∣ p := X_pow_dvd_iff.2 fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 = p.trailingCoeff := by
    have h := congrArg (fun r : R[X] => r.coeff n) hq
    simp only [coeff_X_pow_mul', le_refl, if_true, Nat.sub_self] at h
    rw [← h]; rfl
  have hxq : aeval x q = 0 := by
    have h1 : x ^ n * aeval x q = 0 := by
      rw [← hp, hq, map_mul, map_pow, aeval_X]
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hx n)).1 h1
  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := q)
  have h2 : aeval x q = algebraMap R A (q.coeff 0) + x * aeval x r := by
    have h3 : q = C (q.coeff 0) + X * r := by rw [← hr]; ring
    conv_lhs => rw [h3]
    rw [map_add, aeval_C, map_mul, aeval_X]
  refine ⟨-aeval x r, ?_⟩
  rw [← hq0]
  have h4 := h2.symm.trans hxq
  linear_combination h4

/-- (3a) A nonzerodivisor that is algebraic over `R` divides the image of a nonzero element of `R`. -/
theorem exists_dvd_algebraMap {x : A} (hx : x ∈ nonZeroDivisors A) (halg : IsAlgebraic R x) :
    ∃ c : R, c ≠ 0 ∧ x ∣ algebraMap R A c := by
  obtain ⟨p, hp0, hp⟩ := halg
  exact ⟨p.trailingCoeff, fun h => hp0 (trailingCoeff_eq_zero.1 h), dvd_algebraMap_trailingCoeff hx hp⟩

/-- Quasi-finite algebras over a domain are algebraic. -/
theorem isAlgebraic_of_quasiFinite [IsDomain R] [Algebra.QuasiFinite R A] (y : A) : IsAlgebraic R y := by
  let K := FractionRing R
  have : Module.Finite K (K ⊗[R] A) := Module.Finite.of_quasiFinite
  have h1 : IsIntegral K ((1 : K) ⊗ₜ[R] y) := Algebra.IsIntegral.isIntegral _
  obtain ⟨p, hp0, hp⟩ := (IsFractionRing.isAlgebraic_iff R K (K ⊗[R] A)).2 h1.isAlgebraic
  have h2 : TensorProduct.mk R K A 1 (aeval y p) = 0 := by
    have h3 : (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) (aeval y p) = 0 := by
      rw [← aeval_algHom_apply]; exact hp
    exact h3
  have : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K A 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K (TensorProduct.mk R K A 1)).2
      (TensorProduct.isBaseChange R A K)
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (S := nonZeroDivisors R)
    (f := TensorProduct.mk R K A 1)).1 h2
  refine ⟨C (s : R) * p, mul_ne_zero (C_ne_zero.2 (nonZeroDivisors.coe_ne_zero s)) hp0, ?_⟩
  rw [map_mul, aeval_C, ← Algebra.smul_def]
  simpa [Submonoid.smul_def] using hs

theorem algebra_isAlgebraic_of_quasiFinite [IsDomain R] [Algebra.QuasiFinite R A] :
    Algebra.IsAlgebraic R A := ⟨isAlgebraic_of_quasiFinite⟩

/-- Etale algebras over a domain are algebraic. -/
theorem algebra_isAlgebraic_of_etale [IsDomain R] [Algebra.Etale R A] : Algebra.IsAlgebraic R A :=
  algebra_isAlgebraic_of_quasiFinite

/-- (3b) Density: one nonzero `L` makes every element integral after multiplying by a power of `L`. -/
theorem exists_pow_smul_isIntegral [IsDomain R] [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ L : R, L ≠ 0 ∧ ∀ y : A, ∃ N : ℕ, IsIntegral R (L ^ N • y) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  choose ℓ hℓ0 hℓ using fun y : A => (Algebra.IsAlgebraic.isAlgebraic (R := R) y).exists_integral_multiple
  have hsm : ∀ (r : R) {w : A}, IsIntegral R w → IsIntegral R (r • w) := fun r w hw => by
    rw [Algebra.smul_def]; exact isIntegral_algebraMap.mul hw
  refine ⟨∏ g ∈ s, ℓ g, Finset.prod_ne_zero_iff.2 fun g _ => hℓ0 g, fun y => ?_⟩
  have hy : y ∈ Algebra.adjoin R (s : Set A) := hs ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem g hg =>
    refine ⟨1, ?_⟩
    rw [pow_one, ← Finset.mul_prod_erase s ℓ hg, mul_comm, mul_smul]
    exact hsm _ (hℓ g)
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_smul]; exact isIntegral_algebraMap⟩
  | add y z _ _ hy hz =>
    obtain ⟨N, hN⟩ := hy
    obtain ⟨M, hM⟩ := hz
    refine ⟨N + M, ?_⟩
    have e : (∏ g ∈ s, ℓ g) ^ (N + M) • (y + z) =
        (∏ g ∈ s, ℓ g) ^ M • ((∏ g ∈ s, ℓ g) ^ N • y) + (∏ g ∈ s, ℓ g) ^ N • ((∏ g ∈ s, ℓ g) ^ M • z) := by
      simp only [Algebra.smul_def, map_pow, map_mul, pow_add]; ring
    rw [e]; exact (hsm _ hN).add (hsm _ hM)
  | mul y z _ _ hy hz =>
    obtain ⟨N, hN⟩ := hy
    obtain ⟨M, hM⟩ := hz
    refine ⟨N + M, ?_⟩
    have e : (∏ g ∈ s, ℓ g) ^ (N + M) • (y * z) =
        ((∏ g ∈ s, ℓ g) ^ N • y) * ((∏ g ∈ s, ℓ g) ^ M • z) := by
      simp only [Algebra.smul_def, map_pow, map_mul, pow_add]; ring
    rw [e]; exact hN.mul hM

/-- Idempotents are integral. -/
theorem isIntegral_of_isIdempotentElem {e : A} (he : IsIdempotentElem e) : IsIntegral R e :=
  ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), by
    simp only [eval₂_mul, eval₂_X, eval₂_sub, map_one, mul_sub, mul_one, he.eq, sub_self]⟩

end GlA

/-- (3c) Split off the multiplicity at `a`: `F = (X - a)^e F'` with `F'(a) ≠ 0`. -/
theorem exists_eq_pow_mul_eval_ne_zero {k : Type*} [Field k] {F : k[X]} (hF : F ≠ 0) (a : k) :
    ∃ (e : ℕ) (F' : k[X]), F = (X - C a) ^ e * F' ∧ F'.eval a ≠ 0 := by
  obtain ⟨q, hq, hq'⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd F hF a
  exact ⟨_, q, hq, fun h => hq' (dvd_iff_isRoot.2 h)⟩

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3

GLOB/REL PLAN v1, stage S3 (pure algebra).
* `isUnit_of_mul_eq_one_of_isIntegral`: `t z = 1` with `z` integral over `R ↪ K` makes `t` a unit (so `1 - t z ≠ 0`
  for `z ∈ hatS` when `t` is not a unit);
* `liveIdem`, `liveMod`: on a reduced Noetherian `Y` (`Y ≅ Π Y ⧸ Q`), `x' := v + (x - v) e_live` with `e_live` the
  idempotent of the pieces where `x` is not identically zero; `liveMod_notMem` / `mem_nonZeroDivisors_of_notMem`
  (`x'` is a non-zero-divisor when `v` is), `map_liveMod` (`κ x' = κ x` for every `κ` into a domain with `κ x ≠ 0`),
  `liveMod_mem_integralClosure`;
* `exists_glob_approx'`: `exists_glob_approx` with `N` chosen before the CRT targets `r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Inv

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- **`t z = 1` with `z` integral over `R ↪ K` forces `t` to be a unit.** -/
theorem isUnit_of_mul_eq_one_of_isIntegral (hinj : Function.Injective (algebraMap R K)) {t : R} {z : K}
    (hz : IsIntegral R z) (htz : algebraMap R K t * z = 1) : IsUnit t := by
  obtain ⟨p, hp, hpz⟩ := hz
  have hz0 : z ≠ 0 := by rintro rfl; rw [mul_zero] at htz; exact zero_ne_one htz
  let _ : Invertible z := invertibleOfNonzero hz0
  have h1 : ⅟z = algebraMap R K t := by
    rw [invOf_eq_inv]; exact (eq_inv_of_mul_eq_one_left htz).symm
  have h2 : eval₂ (algebraMap R K) (algebraMap R K t) (reverse p) = 0 := by
    rw [← h1, eval₂_reverse_eq_zero_iff]; exact hpz
  rw [eval₂_at_apply] at h2
  have h3 : (reverse p).eval t = 0 := hinj (by rw [h2, map_zero])
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := reverse p)
  rw [coeff_zero_reverse, hp.leadingCoeff] at hq
  have h4 : (reverse p).eval t = 1 + t * q.eval t := by
    have e := congrArg (eval t) hq
    simp only [eval_sub, eval_C, eval_mul, eval_X] at e
    linear_combination e
  have h5 : t * -q.eval t = 1 := by linear_combination h4 - h3
  exact ⟨⟨t, -q.eval t, h5, by rw [mul_comm]; exact h5⟩, rfl⟩

end Inv

section Live

end Live

section Glob'

end Glob'

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km5 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`

`X` affine, `g : X ⟶ Spec A` etale.
* `gamAlg g : Algebra A Γ(X, ⊤)` (through `ΓSpecIso` and `g.appTop`), **`etale_gamAlg`**;
* `isNoetherianRing_gam`; for a Jacobson PID `A` (not a field): **`isDomain_loc_gam`** (localizations at maximal
  ideals are domains) and **`isDedekindDomain_gam`** (`Γ ⧸ p` is Dedekind for minimal primes `p`) — the hypotheses
  of `h1_exists_kappa` (O2Km4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

universe u

section Gam

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [Etale g]

/-- The `A`-algebra structure on `Γ(X, ⊤)` given by `g : X ⟶ Spec A`. -/
@[instance_reducible]
def gamAlg : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop).hom.toAlgebra

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Tr1 =====
section

/-!
# S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open

* `agr τ₁ τ₂`: for `τ₁ τ₂ : T ⟶ W` over `P` (`W` separated etale), the range of the pull-back of the diagonal of `W`
  along `(τ₁, τ₂)`: closed (`isClosed_agr`), and a fibre point `v` of `T` has `τ₁ v = τ₂ v` iff `fpt v ∈ agr τ₁ τ₂`
  (`mem_agr_iff`).
* **`exists_split_inj`**: for `x ∈ U₀` and `W` quasi-compact separated etale, an etale `T` over `U₀` with a point `t`
  over `x̄` and maps `τ p : T ⟶ W` (`p` in the fibre of `W` over `x̄`) with `τ p (t) = p`, pairwise distinct at every
  geometric point of `T`.
* `locSec τ = Σ_p τ_p^* taut`; `stalkFree_locSec_apply` (all coefficients of its germ are `1` where the `τ_p` biject
  onto the fibre); `stalkFree_injective`.
* **`exists_tr`**: if every geometric fibre of `W` over `U₀` has `n` points, there is a section `s ∈ Λ[W](U₀)` whose
  germ at every geometric point of `U₀` is the sum of all points of the fibre (the trace `Λ[U₀] ⟶ Λ[W]`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtTr

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV

universe u

variable {P : Scheme.{u}}

section Agr

variable {T W : P.Etale} (τ₁ τ₂ : T ⟶ W)

theorem agr_w : τ₁.left ≫ W.hom = τ₂.left ≫ W.hom :=
  (MorphismProperty.Over.w τ₁).trans (MorphismProperty.Over.w τ₂).symm

end Agr

section Loc

end Loc

end RamanujanPetersson.EtPBC.EtTr

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree

* `shObj s`, `shι s`: a map `s : N ⟶ W` of etale `P`-schemes gives a sheet `N ⟶ N ×_P W` over `W`.
* `sheet_cover`: sheets that biject onto every geometric fibre cover `N ×_P W`; `sheet_sep`: distinct sheets
  do not meet; `shι_cancel`.
* **`push_epi`**: if `W` is quasi-compact separated etale over `P` with `n` points in every geometric fibre, then
  `push W.hom` preserves epimorphisms (stalk lifts on a splitting neighbourhood, glued over the sheets), and
  **`push_preservesFiniteColimits_of_deg`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

/-- Cones over finite wide cospans in a cofiltered category. -/
theorem exists_cone {C : Type*} [Category C] [IsCofiltered C] {ι : Type*} [Finite ι] (B : C) (N : ι → C)
    (g : ∀ i, N i ⟶ B) : ∃ (L : C) (c : L ⟶ B) (h : ∀ i, L ⟶ N i), ∀ i, h i ≫ g i = c := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨K⟩ := IsCofiltered.cone_nonempty (WidePullbackShape.wideCospan B N g)
  exact ⟨K.pt, K.π.app none, fun i => K.π.app (some i), fun i => K.w (WidePullbackShape.Hom.term i)⟩

theorem exists_common (x : P) {Z T : P.Etale} (z : (geomPtAt x).point.fiber.obj Z)
    (t : (geomPtAt x).point.fiber.obj T) :
    ∃ (M : P.Etale) (m : (geomPtAt x).point.fiber.obj M) (d : M ⟶ Z) (e : M ⟶ T),
      (geomPtAt x).point.fiber.map d m = z ∧ (geomPtAt x).point.fiber.map e m = t :=
  ⟨_, _, (IsCofiltered.minToLeft (C := (geomPtAt x).point.fiber.Elements) ⟨Z, z⟩ ⟨T, t⟩).1,
    (IsCofiltered.minToRight (C := (geomPtAt x).point.fiber.Elements) ⟨Z, z⟩ ⟨T, t⟩).1,
    (IsCofiltered.minToLeft (C := (geomPtAt x).point.fiber.Elements) ⟨Z, z⟩ ⟨T, t⟩).2,
    (IsCofiltered.minToRight (C := (geomPtAt x).point.fiber.Elements) ⟨Z, z⟩ ⟨T, t⟩).2⟩

section Sheet

variable {W N : P.Etale}

theorem sh_w (s : N ⟶ W) : s.left ≫ W.hom = N.hom := MorphismProperty.Over.w s

theorem sh_lift_w (s : N ⟶ W) : 𝟙 N.left ≫ N.hom = s.left ≫ W.hom := by
  rw [Category.id_comp, sh_w]

/-- The sheet given by `s : N ⟶ W`: `N`, etale over `W.left` through `s`. -/
def shObj (s : N ⟶ W) : W.left.Etale :=
  MorphismProperty.Over.mk ⊤ s.left
    (MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) s.left W.hom W.prop
      (by rw [sh_w]; exact N.prop))

end Sheet

section Lift

variable {W N : P.Etale}

variable (Λ : Type u) [CommRing Λ]

theorem mapc {Y : Scheme.{u}} (F : EtSh Λ Y) {U V V' : Y.Etale} (g : V ⟶ U) (h : V' ⟶ V)
    (s : F.obj.obj (op U)) :
    (F.obj.map (h ≫ g).op).hom s = (F.obj.map h.op).hom ((F.obj.map g.op).hom s) := by
  rw [op_comp, Functor.map_comp]; rfl

end Lift

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree

* `dg W`: the diagonal of `W ×_P W` (clopen: `isClopen_dg`); `dsec Λ W`: its indicator section of `Λ_W`;
* `shapφ Λ W : Λ[W] ⟶ π_* Λ_W` is the map given by `dsec` (`shapφ_taut`);
* `cval_S`: values of `Σ_a l_a · τ_a^* dsec` along a sheet;
* **`isIso_shapφ`**, **`shapIso`**: `shapφ` is an isomorphism (stalkwise: `stalk_inj`, `stalk_surj`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

variable (W : P.Etale)

/-- The diagonal locus of `W ×_P W`. -/
def dg : Set ↥(pullback W.hom W.hom) := Set.range (pullback.diagonal W.hom)

end Dg

section Iso

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end


