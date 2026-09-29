-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronObjectAtP
-- name    : ModularCurve_JZeroNeronObjectAtP
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/a476e6c3-b626-5eb7-b3fb-08b8b148fac9
-- title:
--   Level-N0​p Néron objects at p over level-N0​ data
-- statement:
--   Throughout, the base ring is $R_p=\mathbf{Z}_{(p)}$, realised as [`GaloisRep.ratLocalizedAt p`](../def/GaloisRep_Flat.html#L8) (the rationals whose denominator is coprime to $p$), with `base p` $=\operatorname{Spec}R_p$, `genPt p` the $\overline{\mathbf{Q}}$-point of the base, and, for a valuation subring $A\subseteq\overline{\mathbf{Q}}$, `barPt A` and `resPt A` the inclusions $\operatorname{Spec}\overline{\mathbf{Q}}\to\operatorname{Spec}A\leftarrow\operatorname{Spec}\kappa_A$. A block of helpers transports points along base change (`toFibrePt`, `ofFibrePt`, `fibreMap`, `castOver`, `genOfBaseChangePt`) and presents split tori and their torsion concretely: `torusCoord S t` is the group algebra $S[\mathbf{Z}^t]$ and `muCoord S t m` is $S[(\mathbf{Z}/m)^t]$, so `torusScheme`/`muScheme` are $\mathbf{G}_{m,S}^{t}$ and $\mu_{m,S}^{t}$, with `muToTorus`, `muIncl` (for $m\mid m'$) and `muBaseChange` induced by the evident maps of grading groups; `muPt`, `torusPt` package characters (algebra maps out of these group algebras) as points. `ExtendsToPlace A σA x` says the generic point $x$ is the restriction along `barPt A` of a point over $\sigma_A$.
--
--   `LevelData N₀ p A` is pure data: a morphism $\sigma_A:\operatorname{Spec}A\to\operatorname{Spec}R_p$ with `barPt A ≫ σA = genPt p`, a scheme $f:X\to\operatorname{Spec}R_p$ with a `RelativeGroupLaw`, and bijections $\mathrm{pts}:\mathrm{JZero}\,N_0\simeq X(\overline{\mathbf{Q}})$ and $\mathrm{ptsSp}:\mathrm{JZeroC}\,\kappa_A\,N_0\simeq X(\kappa_A)$ (points over `resPt A ≫ σA`). The predicate `LevelData.IsJacobian` asserts, as a conjunction, that $f$ satisfies `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists), that the group law is commutative on all test points, that both dictionaries are additive, that $\mathrm{pts}$ is Galois-equivariant (the action of $\sigma$ corresponds to precomposition with $\operatorname{Spec}\sigma$), that under the predicate `ReductionInputsModL` the two dictionaries are compatible via `ReductionOfPointsAgreesModL` (each generic point extends to an $A$-point whose reduction is the specialisation given by `reductionModL`), and that every element of `HeckeAlg` is realised by an endomorphism of $f$ over the base which is additive on points and matches the Hecke action under $\mathrm{pts}$.
--
--   The main structure `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ` (with $p\nmid N_0$ and $A$ lying over $p$) carries: a smooth, separated, locally of finite type, quasi-compact, surjective $g:G\to\operatorname{Spec}R_p$ with preconnected fibres and a commutative relative group law, multiplication by each $n\ge 1$ flat and surjective, proper generic fibre, a Galois-equivariant additive bijection $\mathrm{pts}:\mathrm{JZero}(N_0p)\simeq G(\overline{\mathbf{Q}})$, and Hecke endomorphisms as above. The special fibre is described by a closed immersion `torusFibre` of $\mathbf{G}_{m,\kappa_A}^{t}$ ($t=$ `toricRank`) into $G_{\kappa_A}$, multiplicative on characters, together with two additive maps `abqFibre i` $:G_{\kappa_A}\to X_{\kappa_A}$ whose pair is flat and surjective and whose common kernel, on arbitrary test points, consists exactly of the points factoring through the torus; `abqFibre_twist` records commutation with automorphisms of the geometric base point. Two `degeneracyHom` $G\to X$ over $R_p$ are additive and induce `degeneracyPushforwardPair N₀ p i` on $\overline{\mathbf{Q}}$-points; an additive `frobSp` on $\mathrm{JZeroC}\,\kappa_A\,N_0$ is compatible with `reductionModL` for any Frobenius at $A$, and `degeneracyHom_special` gives the Eichler-type formulas $(\nu_0+\mathrm{Frob}\,\nu_1,\ \mathrm{Frob}\,\nu_0+\nu_1)$ on $\kappa_A$-points, while the scheme-theoretic common kernel of the two degeneracy maps on the special fibre is required to be reduced. For each $m>0$ a closed immersion `toricLift` of $\mu_{m,A}^{t}$ into $G_A$ is given, multiplicative on characters, compatible with $m\mid m'$, reducing to `torusFibre` modulo the maximal ideal, with inertia acting on the resulting points of $\mathrm{JZero}(N_0p)$ through the cyclotomic character and the decomposition group permuting them. Finally a finset `ssFinset` of places of `modularFunctionFieldC κ_A N₀` is required to be exactly the supersingular places `ssPlaces p N₀ κ_A`, `frob` is a semilinear automorphism with base map $a\mapsto a^p$ fixing the two geometric generators, $t+1=\#\,$`ssFinset`, positive widths are attached to the node pairs $(w,\mathrm{frob}\cdot w)$, and a surjective homomorphism `comp` from the inertia invariants of $\mathrm{JZero}(N_0p)$ to `componentGroup width` satisfies $T_\ell\mapsto(\ell+1)$ for $\ell\nmid N_0p$ and has kernel precisely the points whose associated section extends to $A$. The closing definitions `nodes`, `toricPoint`, `toricPts` (the subgroup generated by the toric points at level $m$, trivial for $m=0$) and `finPts` (generated by the $m$-torsion points extending to $A$) read off subgroups of $\mathrm{JZero}(N_0p)$ from such an object.
--
--   **Relation to Mathlib.** Mathlib has no Néron models or group schemes in this form; the project's `RelativeGroupLaw`, `SchemeHomOver` and their base-change apparatus are used instead, and tori and their torsion subschemes are presented concretely as spectra of Mathlib's `AddMonoidAlgebra` on $\mathbf{Z}^t$ and $(\mathbf{Z}/m)^t$. The morphism properties invoked (`Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `Surjective`, `Flat`, `IsProper`, `IsClosedImmersion`, `IsReduced`) are Mathlib's.
--
--   **Where it is used.** Nothing is asserted here: this is the data type for the geometric object at $p$ — morally the identity component of the Néron model of $J_0(N_0p)$ over $\mathbf{Z}_{(p)}$, read at a place $A$ above $p$, sitting over a level-$N_0$ good-reduction datum — whose existence is proved elsewhere. Its fields (toric part and its $\mu_m$-lifts, the two degeneracy maps and the Eichler formula on the special fibre, the component-group homomorphism with its Eisenstein relation) are the inputs from which the at-$p$ Néron datum of $J_0(N_0p)$ is assembled for the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronObjectAtP.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_JZeroNeronData
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

namespace JZeroNeronObjectAtP

abbrev baseRing (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)

abbrev base (p : ℕ) : Scheme.{0} := Spec (CommRingCat.of (baseRing p))

abbrev genPt (p : ℕ) : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ base p :=
  Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (AlgebraicClosure ℚ)))

abbrev barPt (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥A) :=
  Spec.map (CommRingCat.ofHom A.subtype)

abbrev resPt (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of ↥A) :=
  Spec.map (CommRingCat.ofHom (residue ↥A))

def overId {B T X : Scheme.{0}} {ι : T ⟶ B} {f : X ⟶ B} (x : SchemeHomOver ι f) :
    SchemeHomOver (𝟙 T ≫ ι) f :=
  ⟨x.1, by rw [Category.id_comp]; exact x.2⟩

def toFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver ι f) : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f) :=
  RelativeGroupLaw.baseChangePointOfBase ι (overId x)

def ofFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) : SchemeHomOver ι f :=
  ⟨(RelativeGroupLaw.baseChangePointToBase ι y).1, by
    simpa only [Category.id_comp] using (RelativeGroupLaw.baseChangePointToBase ι y).2⟩

def fibreMap {R R' : Type} [CommRing R] [CommRing R'] {X Y : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {g : Y ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι f))
    (x : SchemeHomOver ι g) : SchemeHomOver ι f :=
  ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt x) φ)

abbrev muCoord (S : Type) [CommRing S] (t m : ℕ) : Type := AddMonoidAlgebra S (Fin t → ZMod m)

abbrev muScheme (S : Type) [CommRing S] (t m : ℕ) : Scheme.{0} := Spec (CommRingCat.of (muCoord S t m))

abbrev muStr (S : Type) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (muCoord S t m)))

abbrev torusCoord (S : Type) [CommRing S] (t : ℕ) : Type := AddMonoidAlgebra S (Fin t → ℤ)

abbrev torusScheme (S : Type) [CommRing S] (t : ℕ) : Scheme.{0} := Spec (CommRingCat.of (torusCoord S t))

abbrev torusStr (S : Type) [CommRing S] (t : ℕ) : torusScheme S t ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t)))

abbrev muToTorus (S : Type) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))))

abbrev muIncl (S : Type) [CommRing S] (t : ℕ) {m m' : ℕ} (h : m ∣ m') : muScheme S t m ⟶ muScheme S t m' :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => ((ZMod.castHom h (ZMod m)).toAddMonoidHom).comp
      (Pi.evalAddMonoidHom (fun _ : Fin t => ZMod m') i))))

abbrev muBaseChange {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (t m : ℕ) :
    muScheme S' t m ⟶ muScheme S t m :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) φ))

def muPt (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ)
    (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) : SchemeHomOver (barPt A) (muStr ↥A t m) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact χ.comp_algebraMap⟩

def torusPt (S : Type) [CommRing S] (t : ℕ) (χ : torusCoord S t →ₐ[S] S) : SchemeHomOver (𝟙 _) (torusStr S t) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S (torusCoord S t)) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

def castOver {B T X : Scheme.{0}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') (x : SchemeHomOver ι f) :
    SchemeHomOver ι' f :=
  ⟨x.1, x.2.trans h⟩

def genOfBaseChangePt {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {σA : Spec (CommRingCat.of ↥A) ⟶ base p} (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p}
    (y : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr σA f)) : SchemeHomOver (genPt p) f :=
  castOver hσA (RelativeGroupLaw.baseChangePointToBase σA y)

def ExtendsToPlace {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ))
    (σA : Spec (CommRingCat.of ↥A) ⟶ base p) {X : Scheme.{0}} {f : X ⟶ base p}
    (x : SchemeHomOver (genPt p) f) : Prop :=
  ∃ s : SchemeHomOver σA f, x.1 = barPt A ≫ s.1

def castOverEquiv {B T X : Scheme.{0}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') :
    SchemeHomOver ι f ≃ SchemeHomOver ι' f where
  toFun := castOver h
  invFun := castOver h.symm
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

structure LevelData (N₀ p : ℕ) [NeZero N₀] (A : ValuationSubring (AlgebraicClosure ℚ)) where

  σA : Spec (CommRingCat.of ↥A) ⟶ base p

  hσA : barPt A ≫ σA = genPt p

  X : Scheme.{0}

  f : X ⟶ base p

  L : RelativeGroupLaw (baseRing p) f

  pts : JZero N₀ ≃ SchemeHomOver (genPt p) f

  ptsSp : JZeroC (ResidueField ↥A) N₀ ≃ SchemeHomOver (resPt A ≫ σA) f

namespace LevelData

variable {N₀ p : ℕ} [NeZero N₀] {A : ValuationSubring (AlgebraicClosure ℚ)}

def ptsA (Λ : LevelData N₀ p A) : JZero N₀ ≃ SchemeHomOver (barPt A ≫ Λ.σA) Λ.f :=
  Λ.pts.trans (castOverEquiv Λ.hσA.symm)

def IsJacobian (Λ : LevelData N₀ p A) : Prop :=
  letI := heckeModuleBar N₀
  AbelianSchemePropertyBundle (baseRing p) Λ.f ∧
  (∀ {T : Scheme.{0}} (t : T ⟶ base p) (x y : SchemeHomOver t Λ.f), Λ.L.mul t x y = Λ.L.mul t y x) ∧
  (∀ x y : JZero N₀, Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y)) ∧
  (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero N₀),
    (Λ.pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (Λ.pts x).1) ∧
  (∀ u v : JZeroC (ResidueField ↥A) N₀, Λ.ptsSp (u + v) = Λ.L.mul _ (Λ.ptsSp u) (Λ.ptsSp v)) ∧
  (ReductionInputsModL A N₀ → ReductionOfPointsAgreesModL N₀ A Λ.f Λ.σA Λ.ptsA Λ.ptsSp) ∧
  (∀ t : HeckeAlg, ∃ φ : SchemeHomOver Λ.f Λ.f,
    (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      NeronModelInfra.schemeHomOverComp (Λ.L.mul s x y) φ =
        Λ.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
    ∀ x : JZero N₀, (Λ.pts (t • x)).1 = (Λ.pts x).1 ≫ φ.1)

end LevelData

end JZeroNeronObjectAtP

open JZeroNeronObjectAtP

attribute [local instance] instDecidableEqResidueFieldSemistable
  instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

structure JZeroNeronObjectAtP (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) where

  G : Scheme.{0}

  g : G ⟶ base p

  L : RelativeGroupLaw (baseRing p) g

  pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) g

  comm : L.IsCommutative

  smooth : Smooth g
  separated : IsSeparated g
  locallyOfFiniteType : LocallyOfFiniteType g
  quasiCompact : QuasiCompact g
  surjective : Surjective g
  fibre_preconnected : ∀ s : base p, _root_.IsPreconnected (g.base ⁻¹' {s})

  pts_add : ∀ x y : JZero (N₀ * p), pts (x + y) = L.mul _ (pts x) (pts y)

  pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
    (pts (σ • x)).1 =
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1

  hecke : letI := heckeModuleBar (N₀ * p)
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver g g,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero (N₀ * p), (pts (t • x)).1 = (pts x).1 ≫ φ.1

  nsmul_flat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n)
  nsmul_surjective : ∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n)

  proper_generic : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))))

  toricRank : ℕ

  torusFibre : SchemeHomOver (torusStr (ResidueField ↥A) toricRank)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)

  torusFibre_isClosedImmersion : IsClosedImmersion torusFibre.1

  torusFibre_mul :
    ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) torusFibre =
        (L.baseChange (resPt A ≫ Λ.σA)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) torusFibre)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) torusFibre)

  abqFibre : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)

  abqFibre_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      NeronModelInfra.schemeHomOverComp ((L.baseChange (resPt A ≫ Λ.σA)).mul s x y) (abqFibre i) =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).mul s (NeronModelInfra.schemeHomOverComp x (abqFibre i))
          (NeronModelInfra.schemeHomOverComp y (abqFibre i))

  abqFibre_flat : Flat (pullback.lift (abqFibre 0).1 (abqFibre 1).1 ((abqFibre 0).2.trans (abqFibre 1).2.symm))

  abqFibre_surjective :
    Surjective (pullback.lift (abqFibre 0).1 (abqFibre 1).1 ((abqFibre 0).2.trans (abqFibre 1).2.symm))

  abqFibre_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abqFibre i) = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) toricRank),
          NeronModelInfra.schemeHomOverComp y torusFibre = x

  abqFibre_twist : ∀ (τ : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) (i : Fin 2)
      (x : SchemeHomOver (resPt A ≫ Λ.σA) g),
      fibreMap (abqFibre i) (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 x) =
        GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (fibreMap (abqFibre i) x)

  degeneracyHom : Fin 2 → SchemeHomOver g Λ.f

  degeneracyHom_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) (degeneracyHom i) =
        Λ.L.mul s (NeronModelInfra.schemeHomOverComp x (degeneracyHom i))
          (NeronModelInfra.schemeHomOverComp y (degeneracyHom i))

  degeneracyHom_pts : ∀ (i : Fin 2) (x : JZero (N₀ * p)),
      (Λ.pts (degeneracyPushforwardPair N₀ p i x)).1 = (pts x).1 ≫ (degeneracyHom i).1

  frobSp : JZeroC (ResidueField ↥A) N₀ →+ JZeroC (ResidueField ↥A) N₀

  frobSp_reductionModL : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ p →
      ∀ y : JZero N₀, reductionModL A N₀ (φ • y) = frobSp (reductionModL A N₀ y)

  degeneracyHom_special : ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) g,
      Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp x (degeneracyHom 0)) =
          Λ.ptsSp.symm (fibreMap (abqFibre 0) x) + frobSp (Λ.ptsSp.symm (fibreMap (abqFibre 1) x)) ∧
      Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp x (degeneracyHom 1)) =
          frobSp (Λ.ptsSp.symm (fibreMap (abqFibre 0) x)) + Λ.ptsSp.symm (fibreMap (abqFibre 1) x)

  ker_degeneracyHom_special_isReduced :
    let dκ := fun i : Fin 2 =>
      (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f g (degeneracyHom i)).1
    let eκ := ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1
    IsReduced (pullback (pullback.fst (dκ 0) eκ) (pullback.fst (dκ 1) eκ))

  toricLift : ∀ m : ℕ, 0 < m → SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g)

  toricLift_isClosedImmersion : ∀ (m : ℕ) (hm : 0 < m), IsClosedImmersion (toricLift m hm).1

  toricLift_mul : ∀ (m : ℕ) (hm : 0 < m) (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ)),
      NeronModelInfra.schemeHomOverComp (muPt A toricRank m (χ * χ').ofConv) (toricLift m hm) =
        (L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ.ofConv) (toricLift m hm))
          (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ'.ofConv) (toricLift m hm))

  toricLift_compat : ∀ (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m'),
      muIncl ↥A toricRank h ≫ (toricLift m' hm').1 = (toricLift m hm).1

  toricLift_special : ∀ (m : ℕ) (hm : 0 < m),
      muBaseChange (residue ↥A) toricRank m ≫ (toricLift m hm).1 ≫ pullback.fst g Λ.σA =
        muToTorus (ResidueField ↥A) toricRank m ≫ torusFibre.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)

  toricLift_inertia : ∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) →
      ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        σ • pts.symm (genOfBaseChangePt Λ.hσA
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
          c • pts.symm (genOfBaseChangePt Λ.hσA
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm)))

  toricLift_dec : ∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.decompositionSubgroup ℚ,
      ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        ∃ χ' : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          σ • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
            pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ') (toricLift m hm)))

  ssFinset : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀))

  mem_ssFinset_iff : ∀ w, w ∈ ssFinset ↔ w ∈ ssPlaces p N₀ (ResidueField ↥A)

  frob : SemilinearAut (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)

  baseAut_frob : ∀ a : ResidueField ↥A, SemilinearAut.baseAut frob a = a ^ p

  frob_jGeomGen : frob • (jGeomGen (ResidueField ↥A) N₀ : modularFunctionFieldC (ResidueField ↥A) N₀) =
    jGeomGen (ResidueField ↥A) N₀
  frob_jNGeomGen : frob • (jNGeomGen (ResidueField ↥A) N₀ : modularFunctionFieldC (ResidueField ↥A) N₀) =
    jNGeomGen (ResidueField ↥A) N₀

  toricRank_succ_eq_card : toricRank + 1 = ssFinset.card

  width : ↥(nodePairsOfPlaces frob ssFinset) → ℕ

  width_pos : ∀ s, 0 < width s

  comp : ↥(inertiaInvariants A (N₀ * p)) →+ componentGroup width

  comp_heckeGen : letI := heckeModuleBar (N₀ * p)
    ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N₀ * p →
    ∀ (x : ↥(inertiaInvariants A (N₀ * p)))
      (hx : heckeGen ℓ • (x : JZero (N₀ * p)) ∈ inertiaInvariants A (N₀ * p)),
      comp ⟨heckeGen ℓ • (x : JZero (N₀ * p)), hx⟩ = (((ℓ : ℕ) : ℤ) + 1) • comp x

  comp_surjective : Function.Surjective comp

  comp_eq_zero_iff : ∀ x : ↥(inertiaInvariants A (N₀ * p)),
      comp x = 0 ↔ ExtendsToPlace A Λ.σA (pts (x : JZero (N₀ * p)))

attribute [nolint docBlame] JZeroNeronObjectAtP.separated JZeroNeronObjectAtP.locallyOfFiniteType
  JZeroNeronObjectAtP.quasiCompact JZeroNeronObjectAtP.surjective JZeroNeronObjectAtP.fibre_preconnected
  JZeroNeronObjectAtP.nsmul_surjective JZeroNeronObjectAtP.frob_jNGeomGen

namespace JZeroNeronObjectAtP

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

abbrev nodes (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) ×
      Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)) :=
  nodePairsOfPlaces O.frob O.ssFinset

def toricPoint (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) : JZero (N₀ * p) :=
  O.pts.symm (genOfBaseChangePt Λ.hσA
    (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (O.toricLift m hm)))

def toricPts (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) : AddSubgroup (JZero (N₀ * p)) :=
  if hm : 0 < m then AddSubgroup.closure (Set.range (O.toricPoint m hm)) else ⊥

def finPts (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) : AddSubgroup (JZero (N₀ * p)) :=
  AddSubgroup.closure {x | x ∈ jZeroTorsion (N₀ * p) m ∧ ExtendsToPlace A Λ.σA (O.pts x)}

end JZeroNeronObjectAtP

end ModularCurve

end


