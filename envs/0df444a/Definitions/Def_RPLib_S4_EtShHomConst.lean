-- Prove2me | Definitions.Def_RPLib_S4_EtShHomConst
-- name    : RPLib_S4_EtShHomConst
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:28:24.928486+00:00
-- url     : https://prove2.me/theorems/f0b07189-23c2-463d-8161-2bff9635f352
-- title:
--   The internal Hom out of a constant etale sheaf
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For a $\Lambda$-module $M$ there is a natural isomorphism $\mathcal{H}om(M_X, G) \cong \mathrm{Hom}_\Lambda(M, G(-))$: over $V$, a map $M_V \to G|_V$ is the same as a map out of the constant presheaf (the sheafification unit restricts to a local isomorphism over $V$, because composition with $V \to X$ is cocontinuous), and a map out of a constant presheaf on the slice over $V$ is determined by its value at the terminal object.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IV; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShHom

/-!
# S4-EtSheaves, part 8: the internal Hom out of a constant sheaf

`Hom(M_X, G) ≅ Hom_Λ(M, G(-))` (`homConstIso`): over `V`, a map `M_V → G|_V` is the same as a map
from the constant presheaf (the sheafification unit restricts to a `J.W`-map on `V`, because
`etComp` is cocontinuous), and a map out of a constant presheaf on `Over V` is its value at the
terminal object `V`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- `etComp g` is cocontinuous: it is left adjoint to the cover-preserving `etPull g`. -/
instance etComp_isCocontinuous {U : Scheme.{u}} (g : U ⟶ X) [Etale g] :
    (etComp g).IsCocontinuous U.smallEtaleTopology X.smallEtaleTopology :=
  (Adjunction.isCocontinuous_iff_coverPreserving U.smallEtaleTopology X.smallEtaleTopology
    (etCompAdj g)).2 (etPull_coverPreserving g)

/-- Restriction along an etale `g` keeps `J.W` (whiskering by the cocontinuous `etComp g`
preserves locally bijective maps). -/
theorem etW_whisker {U : Scheme.{u}} (g : U ⟶ X) [Etale g] {P Q : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ}
    (f : P ⟶ Q) (hf : X.smallEtaleTopology.W f) :
    U.smallEtaleTopology.W (Functor.whiskerLeft (etComp g).op f) := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  have := h1
  have := h2
  exact ⟨Presheaf.isLocallyInjective_whisker U.smallEtaleTopology X.smallEtaleTopology (etComp g) f,
    Presheaf.isLocallySurjective_whisker U.smallEtaleTopology X.smallEtaleTopology (etComp g) f⟩

variable (M : ModuleCat.{u} Λ) (G : EtSh Λ X)

/-- The constant presheaf `M` on `X.Etale`. -/
abbrev constPre : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := (Functor.const _).obj M

/-- The unit `M ⟶ M_X(V)` of the sheafification. -/
abbrev constUnit (V : X.Etale) : M ⟶ (constSh Λ X M).obj.obj (op V) :=
  (toSheafify X.smallEtaleTopology (constPre M)).app (op V)

/-- The sheafification unit, restricted to `Over V`. -/
def constUnitOver (V : X.Etale) :
    (Functor.const (Over V)ᵒᵖ).obj M ⟶ (Over.forget V).op ⋙ (constSh Λ X M).obj :=
  Functor.whiskerLeft (Over.forget V).op (toSheafify X.smallEtaleTopology (constPre M))

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the restricted unit is bijective on maps into `G|_V`. -/
theorem bijective_constUnitOver_comp (V : X.Etale) :
    Function.Bijective (fun α : HomOver (constSh Λ X M) G V => constUnitOver M V ≫ α) := by
  let e₀ := presheafHomEquiv (constPre M) G.obj (overOf V)
  let e₁ := presheafHomEquiv (constSh Λ X M).obj G.obj (overOf V)
  have hW := etW_whisker V.hom _ (GrothendieckTopology.W_toSheafify X.smallEtaleTopology (constPre M))
  have hb := hW _ ((res V.hom Λ).obj G).property
  have key : (fun α : HomOver (constSh Λ X M) G V => constUnitOver M V ≫ α) =
      e₀.symm ∘ (fun β => Functor.whiskerLeft (etComp V.hom).op
        (toSheafify X.smallEtaleTopology (constPre M)) ≫ β) ∘ e₁ := by
    funext α
    apply e₀.injective
    rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
    rfl
  rw [key]
  exact e₀.symm.bijective.comp (hb.comp e₁.bijective)

theorem homEquiv_constUnitOver (V : X.Etale) (α : HomOver (constSh Λ X M) G V) :
    (constantPresheafAdj (ModuleCat.{u} Λ) (Over.mkIdTerminal (X := V))).homEquiv
      M ((Over.forget V).op ⋙ G.obj) (constUnitOver M V ≫ α) =
        constUnit M V ≫ α.app (op (Over.mk (𝟙 V))) := by
  rw [Adjunction.homEquiv_unit]
  exact Category.id_comp _

/-- `Hom(M_V, G|_V) ≃ Hom_Λ(M, G(V))`: precompose with the unit, evaluate at the terminal `V`. -/
def homConstEquiv (V : X.Etale) : HomOver (constSh Λ X M) G V ≃ₗ[Λ] (M ⟶ G.obj.obj (op V)) :=
  LinearEquiv.ofBijective
    { toFun := fun α => constUnit M V ≫ α.app (op (Over.mk (𝟙 V)))
      map_add' := fun α β => by
        simp only [NatTrans.app_add]
        exact Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun c α => by
        simp only [NatTrans.app_smul, RingHom.id_apply]
        exact Linear.comp_smul _ _ _ _ _ _ }
    (by
      have h := ((constantPresheafAdj (ModuleCat.{u} Λ) (Over.mkIdTerminal (X := V))).homEquiv
        M ((Over.forget V).op ⋙ G.obj)).bijective.comp (bijective_constUnitOver_comp M G V)
      have e : (fun α : HomOver (constSh Λ X M) G V => constUnit M V ≫ α.app (op (Over.mk (𝟙 V)))) =
          ((constantPresheafAdj (ModuleCat.{u} Λ) (Over.mkIdTerminal (X := V))).homEquiv
            M ((Over.forget V).op ⋙ G.obj)) ∘ (fun α => constUnitOver M V ≫ α) :=
        funext fun α => (homEquiv_constUnitOver M G V α).symm
      show Function.Bijective (fun α : HomOver (constSh Λ X M) G V =>
        constUnit M V ≫ α.app (op (Over.mk (𝟙 V))))
      rw [e]
      exact h)

theorem homConstEquiv_apply (V : X.Etale) (α : HomOver (constSh Λ X M) G V) :
    homConstEquiv M G V α = constUnit M V ≫ α.app (op (Over.mk (𝟙 V))) := rfl

theorem homConstEquiv_natural {V V' : X.Etale} (f : V' ⟶ V) (α : HomOver (constSh Λ X M) G V) :
    homConstEquiv M G V' (homOverMap _ _ f α) = homConstEquiv M G V α ≫ G.obj.map f.op := by
  rw [homConstEquiv_apply, homConstEquiv_apply]
  have h1 := α.naturality (Over.homMk f (by simp) :
    (Over.map f).obj (Over.mk (𝟙 V')) ⟶ Over.mk (𝟙 V)).op
  have h2 := (toSheafify X.smallEtaleTopology (constPre M)).naturality f.op
  change (constSh Λ X M).obj.map f.op ≫ α.app (op ((Over.map f).obj (Over.mk (𝟙 V')))) =
    α.app (op (Over.mk (𝟙 V))) ≫ G.obj.map f.op at h1
  change 𝟙 M ≫ constUnit M V' = constUnit M V ≫ (constSh Λ X M).obj.map f.op at h2
  refine Eq.symm ?_
  calc (constUnit M V ≫ α.app (op (Over.mk (𝟙 V)))) ≫ G.obj.map f.op
      = constUnit M V ≫ (α.app (op (Over.mk (𝟙 V))) ≫ G.obj.map f.op) := Category.assoc _ _ _
    _ = constUnit M V ≫ ((constSh Λ X M).obj.map f.op ≫
          α.app (op ((Over.map f).obj (Over.mk (𝟙 V'))))) := congrArg (constUnit M V ≫ ·) h1.symm
    _ = (constUnit M V ≫ (constSh Λ X M).obj.map f.op) ≫
          α.app (op ((Over.map f).obj (Over.mk (𝟙 V')))) := (Category.assoc _ _ _).symm
    _ = (𝟙 M ≫ constUnit M V') ≫ α.app (op ((Over.map f).obj (Over.mk (𝟙 V')))) :=
          congrArg (· ≫ α.app (op ((Over.map f).obj (Over.mk (𝟙 V'))))) h2.symm
    _ = constUnit M V' ≫ α.app (op ((Over.map f).obj (Over.mk (𝟙 V')))) :=
          congrArg (· ≫ α.app (op ((Over.map f).obj (Over.mk (𝟙 V'))))) (Category.id_comp _)

/-- **`Hom(M_X, G) ≅ Hom_Λ(M, G)`**: the internal Hom out of a constant sheaf is `G` followed by
`Hom_Λ(M, -)`. -/
def homConstIso : homSh (constSh Λ X M) G ≅ (sheafCompose X.smallEtaleTopology (ihom M)).obj G :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun V => ((Shrink.linearEquiv Λ _).trans (homConstEquiv M G V.unop)).toModuleIso) (by
      intro V V' f
      ext x
      change homConstEquiv M G V'.unop (Shrink.linearEquiv Λ _ (shrinkMap (homOverMap _ _ f.unop) x)) =
        homConstEquiv M G V.unop (Shrink.linearEquiv Λ _ x) ≫ G.obj.map f
      rw [shrinkMap_apply, LinearEquiv.apply_symm_apply, homConstEquiv_natural]
      rfl))

end RamanujanPetersson.EtSheaves


