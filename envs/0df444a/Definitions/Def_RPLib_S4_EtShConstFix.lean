-- Prove2me | Definitions.Def_RPLib_S4_EtShConstFix
-- name    : RPLib_S4_EtShConstFix
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:34:50.422424+00:00
-- url     : https://prove2.me/theorems/28997e0f-5293-4154-b5b2-a103cdf08e08
-- title:
--   Galois elements fixing a trivialising lift act trivially on the stalk
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. Let $g : Y \to X$ be etale with $g^*F \cong M_Y$ constant and $\bar t$ a geometric point of $Y$. Every element of $F_{g \circ \bar t}$ is the germ at $\bar t$ of a section of $F$ over $Y \to X$. Hence an automorphism $\tau$ of $\mathrm{Spec}\,\Omega$ with $\bar t \circ \tau = \bar t$ acts trivially on $F_{g \circ \bar t}$, and every $\sigma \in \mathrm{Gal}(\kappa(x)^{\mathrm{sep}}/\kappa(x))$ fixing a lift $l : \mathrm{Spec}\,\Omega \to Y$ of $\bar x$ acts trivially on $F_{\bar x}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShGalCont
import Definitions.Def_RPLib_S4_EtShStalkRes
import Definitions.Def_RPLib_S4_EtShFaith

/-!
# S4-EtSheaves, O10c part 3: Galois elements fixing a trivialising lift act trivially

Let `g : Y ⟶ X` be etale with `g^* F ≅ M_Y` constant, and `t` a geometric point of `Y`. Every element of
`F_(t ≫ g)` is the germ of a section of `F` over `Y → X` at the lift `t` (`exists_germ_of_triv`). Hence an
automorphism `τ` of `Spec Ω` with `τ ≫ t = t` acts trivially on `F_(t ≫ g)` (`stalkAut_triv_eq_id`), and
`σ ∈ Gal(κ(x)^sep/κ(x))` with `Spec σ ≫ l = l` for a lift `l : Spec Ω ⟶ Y` of `x̄` acts trivially on `F_x̄`
(`galRep_eq_id_of_triv`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

/-- The stalk of `φ : M_Y ⟶ G` on the constant germ of `m` is the germ of `φ(m)` over the identity. -/
theorem stalkMap_constGerm {Y : Scheme.{u}} {M : ModuleCat.{u} Λ} {G : EtSh Λ Y} (φ : constSh Λ Y M ⟶ G)
    (t : GeomPt Y) (m : M) :
    ((t.stalkF Λ).map φ).hom ((constStalkIso Λ t M).inv.hom m) =
      (t.point.toPresheafFiber (etId Y) t.top G.obj).hom
        ((φ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m)) := by
  rw [← constUnit_germ t M (etId Y) t.top]
  change (constUnit M (etId Y) ≫ t.point.toPresheafFiber (etId Y) t.top (constSh Λ Y M).obj ≫
    t.point.presheafFiber.map φ.hom).hom m = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g]

/-- If `g^* F` is constant, every element of `F_(t ≫ g)` is a germ at the lift `t` over `Y → X`. -/
theorem exists_germ_of_triv (F : EtSh Λ X) (M : ModuleCat.{u} Λ) (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (t : GeomPt Y) (v : ((t.map g).stalkF Λ).obj F) :
    ∃ z : F.obj.obj (op ((etComp g).obj (etId Y))),
      ((t.map g).point.toPresheafFiber ((etComp g).obj (etId Y)) (liftX g t t.top) F.obj).hom z = v := by
  let e' : constSh Λ Y M ≅ (res g Λ).obj F := e.symm ≪≫ (pullIsoRes g Λ).app F
  let E : (t.stalkF Λ).obj ((res g Λ).obj F) ≅ M := (t.stalkF Λ).mapIso e'.symm ≪≫ constStalkIso Λ t M
  let w := (resFibIso g t Λ F).inv.hom v
  refine ⟨(e'.hom.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom (E.hom.hom w)), ?_⟩
  have hw : ((t.stalkF Λ).map e'.hom).hom ((constStalkIso Λ t M).inv.hom (E.hom.hom w)) = w := by
    change (E.hom ≫ E.inv).hom w = w
    rw [E.hom_inv_id]
    rfl
  have h1 := stalkMap_constGerm e'.hom t (E.hom.hom w)
  have h2 := resFib_germ g t Λ F (etId Y) t.top
    ((e'.hom.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom (E.hom.hom w)))
  have h3 : (resFib g t Λ F).hom w = v := by
    change ((resFibIso g t Λ F).inv ≫ (resFibIso g t Λ F).hom).hom v = v
    rw [Iso.inv_hom_id]
    rfl
  exact h2.symm.trans ((congrArg (resFib g t Λ F).hom (h1.symm.trans hw)).trans h3)

/-- An automorphism `τ` of `Spec Ω` fixing the geometric point `t` of a trivialising `Y` acts trivially on
`F_(t ≫ g)`. -/
theorem stalkAut_triv_eq_id (F : EtSh Λ X) (M : ModuleCat.{u} Λ) (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (t : GeomPt Y) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map g).pt = (t.map g).pt) (hfix : τ ≫ t.pt = t.pt) :
    (((t.map g).stalkAut Λ τ hτ).app F).hom = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨z, rfl⟩ := exists_germ_of_triv g F M e t v
  exact GeomPt.stalkAut_fix (t.map g) Λ τ hτ F _ (liftX g t t.top) z hfix

/-- The same for any geometric point `s` of `X` with a lift `l : Spec Ω ⟶ Y` fixed by `τ`. -/
theorem stalkAut_eq_id_of_lift (F : EtSh Λ X) (M : ModuleCat.{u} Λ) (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (s : GeomPt X) (l : Spec (CommRingCat.of s.Ω) ⟶ Y) (hl : l ≫ g = s.pt)
    (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt)
    (hfix : τ ≫ l = l) :
    ((s.stalkAut Λ τ hτ).app F).hom = LinearMap.id := by
  obtain ⟨Ω, pt⟩ := s
  change Spec (CommRingCat.of Ω) ⟶ Y at l
  change Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω) at τ
  revert pt
  intro pt hl hτ hfix
  change l ≫ g = pt at hl
  subst hl
  exact stalkAut_triv_eq_id g F M e ⟨Ω, l⟩ τ hτ hfix

/-- **HEADLINE (O10c, F3)**: if `g^* F` is constant and `σ ∈ Gal(κ(x)^sep/κ(x))` fixes a lift
`l : Spec κ(x)^sep ⟶ Y` of the geometric point `x̄`, then `σ` acts trivially on `F_x̄`. -/
theorem galRep_eq_id_of_triv (F : EtSh Λ X) (x : X) (M : ModuleCat.{u} Λ)
    (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (l : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ Y) (hl : l ≫ g = (geomPtAt x).pt)
    (σ : Gal x) (hσ : galSpec x σ ≫ l = l) :
    galRep Λ F x σ = LinearMap.id :=
  stalkAut_eq_id_of_lift g F M e (geomPtAt x) l hl (galSpec x σ) (galSpec_comp x σ) hσ

/-- **HEADLINE (O10c, F3), etale-neighbourhood form**: the same for `U : X.Etale` with `F|_U ≅ M_U`. -/
theorem galRep_eq_id_of_etale (F : EtSh Λ X) (x : X) (U : X.Etale) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M)
    (l : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ U.left)
    (hl : l ≫ U.hom = (geomPtAt x).pt) (σ : Gal x) (hσ : galSpec x σ ≫ l = l) :
    galRep Λ F x σ = LinearMap.id := by
  have : Etale U.hom := U.prop
  exact galRep_eq_id_of_triv U.hom F x M e l hl σ hσ

end RamanujanPetersson.EtSheaves


