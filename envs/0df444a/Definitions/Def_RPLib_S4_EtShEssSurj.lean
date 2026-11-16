-- Prove2me | Definitions.Def_RPLib_S4_EtShEssSurj
-- name    : RPLib_S4_EtShEssSurj
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:52:42.977206+00:00
-- url     : https://prove2.me/theorems/d22b2729-eb8a-4b3c-901e-e0d95c58ac99
-- title:
--   Lisse etale sheaves on $\mathrm{Spec}\,A$ are their generic Galois representations
-- statement:
--   Let $A$ be a noetherian integrally closed domain with fraction field $K$, $\eta$ the generic point of $\mathrm{Spec}\,A$ and $\bar\eta$ the generic geometric point. For lisse etale sheaves of $\Lambda$-modules on $\mathrm{Spec}\,A$: every Galois-equivariant map of generic stalks $F_{\bar\eta} \to G_{\bar\eta}$ is the stalk of a morphism of sheaves; the Galois action on $F_{\bar\eta}$ factors through $\pi_1(\mathrm{Spec}\,A)$ with open kernel; lisse sheaves with equivariantly isomorphic generic stalks are isomorphic; and every lisse $F$ is isomorphic to the sheaf $F_V$ of its fibre representation $V = F_{\bar\eta}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V, Section 8; M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IX; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShChartSch
import Definitions.Def_RPLib_S4_EtShGalSurj
import Definitions.Def_RPLib_S4_EtShUnramMain
import Definitions.Def_RPLib_S4_EtShUnramKer

/-!
# S4-EtSheaves, O10f part f: lisse sheaves on `Spec A` are their generic Galois representations

`A` is a noetherian integrally closed domain with fraction field `K`, `η` the generic point of `Spec A`.
* `full`: every Galois-equivariant map of generic stalks `F_η̄ → G_η̄` (`G` lisse) is the stalk of a sheaf map;
* `fibRep`: the Galois action on the generic stalk of a lisse `F` factors through `π₁ = Pi1 A K`, with open kernel
  (`isOpen_ker_fibRep`);
* `nonempty_iso_of_stalk`: lisse sheaves with equivariantly isomorphic generic stalks are isomorphic;
* **`essSurj`**: every lisse `F` is isomorphic to the sheaf `F_V` of its fibre representation `V = F_η̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.EssSurj

open GenBr TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

section Full

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {Λ : Type} [CommRing Λ]

/-- The generic point lies in every nonempty open subset of `Spec A`. -/
theorem genPt_mem (O : Set (Spec (CommRingCat.of A))) (hO : IsOpen O) (hne : O.Nonempty) : genPt A ∈ O := by
  rw [genPt_eq]
  exact ((genericPoint_spec (Spec (CommRingCat.of A))).mem_open_set_iff hO).2 (by simpa using hne)

/-- **Fullness of the generic fibre functor on `Spec A`.** -/
theorem full {F G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    (f : stalk Λ F (genPt A) →ₗ[Λ] stalk Λ G (genPt A))
    (hf : ∀ (σ : Gal (genPt A)) (v : stalk Λ F (genPt A)),
      f (galRep Λ F (genPt A) σ v) = galRep Λ G (genPt A) σ (f v)) :
    ∃ φ : F ⟶ G, (((geomPtAt (genPt A)).stalkF Λ).map φ).hom = f :=
  FullAbs.full (genPt A) f ⟨genPt_mem A, hG.isLocConst, ChartSch.hChart A G hG, hf⟩

/-- **Lisse sheaves on `Spec A` with equivariantly isomorphic generic stalks are isomorphic.** -/
theorem nonempty_iso_of_stalk {F G : EtSh Λ (Spec (CommRingCat.of A))} (hF : IsLisse Λ F) (hG : IsLisse Λ G)
    (e : stalk Λ F (genPt A) ≅ stalk Λ G (genPt A))
    (he : ∀ (σ : Gal (genPt A)) (v : stalk Λ F (genPt A)),
      e.hom.hom (galRep Λ F (genPt A) σ v) = galRep Λ G (genPt A) σ (e.hom.hom v)) :
    Nonempty (F ≅ G) := by
  have hinv : ∀ (σ : Gal (genPt A)) (w : stalk Λ G (genPt A)),
      e.inv.hom (galRep Λ G (genPt A) σ w) = galRep Λ F (genPt A) σ (e.inv.hom w) := by
    intro σ w
    have h := he σ (e.inv.hom w)
    rw [iso_inv_hom_apply] at h
    rw [← h, iso_hom_inv_apply]
  obtain ⟨φ, hφ⟩ := full A hG e.hom.hom he
  obtain ⟨ψ, hψ⟩ := full A hF e.inv.hom hinv
  let s := geomPtAt (genPt A)
  have h1 : φ ≫ ψ = 𝟙 F := stalk_faithful hF hF.isLocConst s (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    show ((s.stalkF Λ).map ψ).hom (((s.stalkF Λ).map φ).hom v) = v
    rw [hφ, hψ]
    exact iso_hom_inv_apply Λ e v)
  have h2 : ψ ≫ φ = 𝟙 G := stalk_faithful hG hG.isLocConst s (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
    show ((s.stalkF Λ).map φ).hom (((s.stalkF Λ).map ψ).hom w) = w
    rw [hφ, hψ]
    exact iso_inv_hom_apply Λ e w)
  exact ⟨⟨φ, ψ, h1, h2⟩⟩

end Full

section Rep

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

/-- `galRep` as a hom to units, killed by `ker genToPi1` (`galRep_unram`). -/
def fibRepU (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) :
    {g : Gal (genPt A) →* (Module.End Λ (stalk Λ F (genPt A)))ˣ // (genToPi1 A K).ker ≤ g.ker} :=
  ⟨(galRep Λ F (genPt A)).toHomUnits, fun σ hσ => MonoidHom.mem_ker.2 (Units.ext
    ((UnramMain.galRep_unram A K F hF σ (MonoidHom.mem_ker.1 hσ)).trans rfl))⟩

/-- The **fibre representation** of a lisse `F`: `π₁` acting on the generic stalk `F_η̄` (the Galois action
factors through `genToPi1` by `galRep_unram`). -/
def fibRep (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) :
    Representation Λ (Pi1 A K) (stalk Λ F (genPt A)) :=
  (Units.coeHom (Module.End Λ (stalk Λ F (genPt A)))).comp
    ((genToPi1 A K).liftOfSurjective (genToPi1_surjective A K) (fibRepU A K F hF))

theorem fibRep_genToPi1 (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) (σ : Gal (genPt A)) :
    fibRep A K F hF (genToPi1 A K σ) = galRep Λ F (genPt A) σ :=
  congrArg Units.val ((genToPi1 A K).liftOfRightInverse_comp_apply
    (Function.surjInv (genToPi1_surjective A K)) (Function.rightInverse_surjInv (genToPi1_surjective A K))
    (fibRepU A K F hF) σ)

/-- The fibre representation has open kernel. -/
theorem isOpen_ker_fibRep (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) :
    IsOpen ((fibRep A K F hF).ker : Set (Pi1 A K)) := by
  let H := (galRep Λ F (genPt A)).ker
  have hH : IsOpen (H : Set (Gal (genPt A))) := isOpen_ker_galRep hF (genPt A)
  have hk : (genToPi1 A K).ker ≤ H := fun σ hσ =>
    MonoidHom.mem_ker.2 ((UnramMain.galRep_unram A K F hF σ (MonoidHom.mem_ker.1 hσ)).trans rfl)
  have : T2Space (Pi1 A K) := krullTopology_t2
  have : Finite (Gal (genPt A) ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := H)
  have : (H.map (genToPi1 A K)).FiniteIndex :=
    ⟨by rw [H.index_map_eq (genToPi1_surjective A K) hk]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  refine Subgroup.isOpen_mono (fun τ hτ => ?_) (Subgroup.isOpen_of_isClosed_of_finiteIndex (H.map (genToPi1 A K)) ?_)
  · obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hτ
    rw [MonoidHom.mem_ker, fibRep_genToPi1]
    exact MonoidHom.mem_ker.1 hσ
  · rw [Subgroup.coe_map]
    exact ((H.isClosed_of_isOpen hH).isCompact.image (genToPi1_continuous A K)).isClosed

variable [IsNoetherianRing A]

/-- **Essential surjectivity (O10f)**: every lisse sheaf `F` on `Spec A` is isomorphic to the sheaf `F_V` of a
representation of a finite unramified Galois group `Gal(L/K)` on `V = F_η̄` inflating to the fibre
representation of `F`. -/
theorem essSurj (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
      (ρ : Representation Λ (coverOf A K L hL).G (stalk Λ F (genPt A))),
      piRep L hL Λ ρ = fibRep A K F hF ∧ Nonempty (F ≅ FV (coverOf A K L hL) Λ ρ) := by
  have : Module.Finite Λ (stalk Λ F (genPt A)) := hF.finite_stalkF _
  obtain ⟨L, hL, ρ, hρ, hlis, e, he⟩ :=
    exists_lisse_of_rep A K Λ (fibRep A K F hF) (isOpen_ker_fibRep A K F hF)
  have he' : ∀ (σ : Gal (genPt A)) (w : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A)),
      e.hom.hom (galRep Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) σ w) =
        galRep Λ F (genPt A) σ (e.hom.hom w) := fun σ w =>
    (he σ w).trans (LinearMap.congr_fun (fibRep_genToPi1 A K F hF σ) _)
  obtain ⟨E⟩ := nonempty_iso_of_stalk A hlis hF e he'
  exact ⟨L, hL, ρ, hρ, ⟨E.symm⟩⟩

end Rep

end RamanujanPetersson.EtSheaves.EssSurj


