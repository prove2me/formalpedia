-- Prove2me | Definitions.Def_RPLib_S4_EtShLocalEx
-- name    : RPLib_S4_EtShLocalEx
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:40:18.859893+00:00
-- url     : https://prove2.me/theorems/16727bc3-b1c8-42a1-b9d5-6b423a48999f
-- title:
--   Local existence of sections with prescribed generic germs
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. Let $f : F_{\bar x_0} \to G_{\bar x_0}$ be a $\mathrm{Gal}(\kappa(x_0)^{\mathrm{sep}}/\kappa(x_0))$-equivariant linear map between the stalks of two etale sheaves at $\bar x_0$. Let $h : T \to X$ be etale with $h^*G \cong M_T$ constant and with at most one point of $T$ over $x_0$. Then for every section $z \in F(T)$ there is $y \in G(T)$ whose germ at every lift $b$ of $\bar x_0$ to $T$ is $f$ of the germ of $z$ at $b$. (Any two lifts have the same centre, so differ by a Galois element, which moves germs of $F$ and $G$ alike.)
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShTrans
import Definitions.Def_RPLib_S4_EtShGenUniq

/-!
# S4-EtSheaves, O10f part c1: local existence of sections with prescribed generic germs

Let `f : F_x̄₀ → G_x̄₀` be a `Gal(κ(x0)^sep/κ(x0))`-equivariant linear map between the stalks of two etale sheaves at
the geometric point `x̄₀ = geomPtAt x0`. Let `h : T → X` be etale with `h^* G ≅ M_T` constant and with at most one point
of `T` over `x0`. Then for every section `z ∈ F(T)` there is `y ∈ G(T)` whose germ at every lift `b` of `x̄₀` to `T` is
`f` of the germ of `z` at `b` (`exists_good`).

Proof: fix one lift `b'`; every element of `G_x̄₀` is the germ at `b'` of a section over `T` (`G` is constant there), so
choose `y` with germ `f(z_{b'})`. Any other lift `b` has the same centre (the unique point over `x0`), hence differs
from `b'` by a Galois element `σ`, which moves germs of `F` and `G` alike; equivariance of `f` finishes.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace LocalEx

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X)

/-- Every lift of `geomPtAt x0` to an etale `W` has its centre over `x0`. -/
theorem centre_over (W : X.Etale) (b : (geomPtAt x0).point.fiber.obj W) :
    W.hom (((geomPtAt x0).liftOf b).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) =
      x0 := by
  have hw : ((geomPtAt x0).liftOf b).left ≫ W.hom = (geomPtAt x0).pt := Over.w ((geomPtAt x0).liftOf b)
  have h1 : (((geomPtAt x0).liftOf b).left ≫ W.hom)
      (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0))) =
      (geomPtAt x0).pt (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0))) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) hw
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (h1.trans ((congrArg (geomPtAt x0).pt (Subsingleton.elim _ _)).trans (center_geomPtAt x0)))

/-- The same for the chart `(etComp h).obj (etId T)`, read in `T`. -/
theorem centre_over_chart {T : Scheme.{u}} (h : T ⟶ X) [Etale h]
    (b : (geomPtAt x0).point.fiber.obj ((etComp h).obj (etId T))) :
    h (((geomPtAt x0).liftOf b).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) = x0 :=
  centre_over x0 ((etComp h).obj (etId T)) b

variable {F G : EtSh Λ X} (f : stalk Λ F x0 →ₗ[Λ] stalk Λ G x0)

/-- **Local existence**: on a chart trivialising `G` with at most one point over `x0`, every section of `F` has a
partner section of `G` whose generic germs are the images under the equivariant map `f`. -/
theorem exists_good (hf : ∀ (σ : Gal x0) (v : stalk Λ F x0), f (galRep Λ F x0 σ v) = galRep Λ G x0 σ (f v))
    {T : Scheme.{u}} (h : T ⟶ X) [Etale h] (M : ModuleCat.{u} Λ) (e : (pull h Λ).obj G ≅ constSh Λ T M)
    (huniq : ∀ w₁ w₂ : T, h w₁ = x0 → h w₂ = x0 → w₁ = w₂)
    (z : F.obj.obj (op ((etComp h).obj (etId T)))) :
    ∃ y : G.obj.obj (op ((etComp h).obj (etId T))),
      ∀ b : (geomPtAt x0).point.fiber.obj ((etComp h).obj (etId T)),
        ((geomPtAt x0).point.toPresheafFiber _ b G.obj).hom y =
          f (((geomPtAt x0).point.toPresheafFiber _ b F.obj).hom z) := by
  by_cases hne : Nonempty ((geomPtAt x0).point.fiber.obj ((etComp h).obj (etId T)))
  swap
  · exact ⟨0, fun b => (hne ⟨b⟩).elim⟩
  obtain ⟨b0⟩ := hne
  have hc0 : h (((geomPtAt x0).liftOf b0).left
      (IsLocalRing.closedPoint (SeparableClosure (X.residueField x0)))) = (geomPtAt x0).center :=
    (centre_over_chart x0 h b0).trans (center_geomPtAt x0).symm
  obtain ⟨t, -, htx⟩ := exists_geomPt_lift (Y := T) h (geomPtAt x0) _ hc0
  have key : ∀ P : GeomPt X, t.map h = P → ∃ b' : P.point.fiber.obj ((etComp h).obj (etId T)),
      ∀ v : (P.stalkF Λ).obj G, ∃ y : G.obj.obj (op ((etComp h).obj (etId T))),
        (P.point.toPresheafFiber _ b' G.obj).hom y = v := by
    rintro P rfl
    exact ⟨liftX h t t.top, fun v => exists_germ_of_triv h G M e t v⟩
  obtain ⟨b', hb'⟩ := key _ htx
  obtain ⟨y, hy⟩ := hb' (f (((geomPtAt x0).point.toPresheafFiber _ b' F.obj).hom z))
  refine ⟨y, fun b => ?_⟩
  have hab := huniq _ _ (centre_over_chart x0 h b') (centre_over_chart x0 h b)
  obtain ⟨σ, hσ⟩ := Trans.exists_germ_galRep x0 Λ ((etComp h).obj (etId T)) b' b hab
  exact (hσ G y).trans ((congrArg (galRep Λ G x0 σ) hy).trans ((hf σ _).symm.trans
    (congrArg f (hσ F z).symm)))

end LocalEx

end RamanujanPetersson.EtSheaves


