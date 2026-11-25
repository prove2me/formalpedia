-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_042
-- name    : RPLib_FX_EtPBC_042
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:02:31.690443+00:00
-- url     : https://prove2.me/theorems/45ed94df-e382-5a5b-8fc9-da33e17e064a
-- title:
--   Proper base change for the projective line, library file 042
-- statement:
--   File 042 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovL2`: S4-EtPBC-A, R4-T2 (A1b): one step of the nilpotent lifting of a two-chart etale cover
--   * `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
--   * `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovAsN3`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian
--   * `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
--   * `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
--   * `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
--   * `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
--   * `S4.Def_RP_EtPBC_A_Inj0b`: S4-EtPBC-A, G1b: base change in degree `0` on sections
--   * `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
--   * `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
--   * `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
--   * `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
--   * `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
--   * `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
--   * `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2Km3`: S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
--   * `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
--   * `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
--   * `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
--   * `S4.Def_RP_EtPBC_A_O2Gl2f`: S4-EtPBC-A, O2 GLOB (O2Gl2f): the side conditions of stages S3-S4
--   * `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
--   * `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_035

/-!
# Proper base change for the projective line, library file 042

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovL2`: S4-EtPBC-A, R4-T2 (A1b): one step of the nilpotent lifting of a two-chart etale cover
* `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
* `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovAsN3`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian
* `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
* `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
* `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
* `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
* `S4.Def_RP_EtPBC_A_Inj0b`: S4-EtPBC-A, G1b: base change in degree `0` on sections
* `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
* `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
* `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
* `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
* `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
* `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
* `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2Km3`: S4-EtPBC-A, O2 M6 (O2Km3): an etale algebra over a PID splits into Dedekind domains
* `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
* `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
* `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
* `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
* `S4.Def_RP_EtPBC_A_O2Gl2f`: S4-EtPBC-A, O2 GLOB (O2Gl2f): the side conditions of stages S3-S4
* `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
* `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovL2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A1b): one step of the nilpotent lifting of a two-chart etale cover

Charts `B₀`, `B₁` with overlap `N`, `φᵢ : Bᵢ → N` away maps at `tᵢ` with unit images; surjections `πᵢ`, `π` onto a
lower level `b₀`, `b₁`, `n` with nilpotent kernels, compatible with the lower charts `φbᵢ`. A two-chart etale cover of
the lower level (`eᵢ` etale over `bᵢ`, `ψbᵢ : eᵢ → e` away maps compatible with `φbᵢ`) lifts (**`lift_step`**): `Eᵢ`
etale over `Bᵢ` (Mathlib-style presentation lift, `NilLift.exists_etale_lift`), `E = N ⊗[B₀] E₀`, and `ψ₁` from the
unique lift of `N ⊗[B₁] E₁ ≅ N ⊗[B₀] E₀` (`NilLift.exists_iso_lift`), with surjections `ρᵢ`, `ρ` compatible with all maps.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **One lifting step** for two-chart etale covers along nilpotent thickenings. -/
theorem lift_step {B₀ B₁ N b₀ b₁ n : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing b₀] [CommRing b₁]
    [CommRing n] (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N) (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀)
    (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀)) (hu₁ : IsUnit (φ₁ t₁))
    (π₀ : B₀ →+* b₀) (π₁ : B₁ →+* b₁) (π : N →+* n) (hπ₀ : Function.Surjective π₀)
    (hπ₁ : Function.Surjective π₁) (hk₀ : IsNilpotent (RingHom.ker π₀)) (hk₁ : IsNilpotent (RingHom.ker π₁))
    (φb₀ : b₀ →+* n) (φb₁ : b₁ →+* n) (hc₀ : φb₀.comp π₀ = π.comp φ₀) (hc₁ : φb₁.comp π₁ = π.comp φ₁)
    (e₀ e₁ e : Type u) [CommRing e₀] [CommRing e₁] [CommRing e] [Algebra b₀ e₀] [Algebra b₁ e₁] [Algebra n e]
    [Algebra.Etale b₀ e₀] [Algebra.Etale b₁ e₁] (ψb₀ : e₀ →+* e) (ψb₁ : e₁ →+* e)
    (hψb₀ : ψb₀.comp (algebraMap b₀ e₀) = (algebraMap n e).comp φb₀)
    (hψb₁ : ψb₁.comp (algebraMap b₁ e₁) = (algebraMap n e).comp φb₁)
    (aw₀ : IsAwayMap ψb₀ (algebraMap b₀ e₀ (π₀ t₀))) (aw₁ : IsAwayMap ψb₁ (algebraMap b₁ e₁ (π₁ t₁))) :
    ∃ (E₀ E₁ E : Type u) (_ : CommRing E₀) (_ : CommRing E₁) (_ : CommRing E) (_ : Algebra B₀ E₀)
      (_ : Algebra B₁ E₁) (_ : Algebra N E) (_ : Algebra.Etale B₀ E₀) (_ : Algebra.Etale B₁ E₁)
      (_ : Algebra.Etale N E) (ρ₀ : E₀ →+* e₀) (ρ₁ : E₁ →+* e₁) (ρ : E →+* e) (ψ₀ : E₀ →+* E) (ψ₁ : E₁ →+* E),
      Function.Surjective ρ₀ ∧ Function.Surjective ρ₁ ∧ Function.Surjective ρ ∧
      RingHom.ker ρ₀ = (RingHom.ker π₀).map (algebraMap B₀ E₀) ∧
      RingHom.ker ρ₁ = (RingHom.ker π₁).map (algebraMap B₁ E₁) ∧ RingHom.ker ρ = (RingHom.ker ρ₀).map ψ₀ ∧
      ρ₀.comp (algebraMap B₀ E₀) = (algebraMap b₀ e₀).comp π₀ ∧
      ρ₁.comp (algebraMap B₁ E₁) = (algebraMap b₁ e₁).comp π₁ ∧
      ρ.comp (algebraMap N E) = (algebraMap n e).comp π ∧
      ψ₀.comp (algebraMap B₀ E₀) = (algebraMap N E).comp φ₀ ∧
      ψ₁.comp (algebraMap B₁ E₁) = (algebraMap N E).comp φ₁ ∧
      IsAwayMap ψ₀ (algebraMap B₀ E₀ t₀) ∧ IsAwayMap ψ₁ (algebraMap B₁ E₁ t₁) ∧
      ρ.comp ψ₀ = ψb₀.comp ρ₀ ∧ ρ.comp ψ₁ = ψb₁.comp ρ₁ ∧
      (Module.Finite b₀ e₀ → Module.Finite B₀ E₀) ∧ (Module.Finite b₁ e₁ → Module.Finite B₁ E₁) := by
  obtain ⟨E₀, _, _, f₀, het₀, hs₀, hkf₀, hcf₀, hfin₀⟩ := NilLift.exists_etale_lift π₀ hπ₀ hk₀ e₀
  obtain ⟨E₁, _, _, f₁, het₁, hs₁, hkf₁, hcf₁, hfin₁⟩ := NilLift.exists_etale_lift π₁ hπ₁ hk₁ e₁
  letI : Algebra B₀ N := φ₀.toAlgebra
  letI : Algebra B₁ N := φ₁.toAlgebra
  haveI : IsLocalization.Away t₀ N := isLocalization_of_isAwayMap φ₀ t₀ hφ₀ hu₀
  haveI : IsLocalization.Away t₁ N := isLocalization_of_isAwayMap φ₁ t₁ hφ₁ hu₁
  haveI := het₀
  haveI := het₁
  -- the reductions of the localized lifts
  have hτ₀ : f₀ (algebraMap B₀ E₀ t₀) = algebraMap b₀ e₀ (π₀ t₀) := congrArg (fun k => k t₀) hcf₀
  have hτ₁ : f₁ (algebraMap B₁ E₁ t₁) = algebraMap b₁ e₁ (π₁ t₁) := congrArg (fun k => k t₁) hcf₁
  have hv₀ : ψb₀ (algebraMap b₀ e₀ (π₀ t₀)) = algebraMap n e (π (φ₀ t₀)) := by
    have h2 := RingHom.congr_fun hψb₀ (π₀ t₀)
    have h3 := RingHom.congr_fun hc₀ t₀
    simp only [RingHom.comp_apply] at h2 h3
    rw [h2, h3]
  have hv₁ : ψb₁ (algebraMap b₁ e₁ (π₁ t₁)) = algebraMap n e (π (φ₁ t₁)) := by
    have h2 := RingHom.congr_fun hψb₁ (π₁ t₁)
    have h3 := RingHom.congr_fun hc₁ t₁
    simp only [RingHom.comp_apply] at h2 h3
    rw [h2, h3]
  have hu₀' : IsUnit (ψb₀ (algebraMap b₀ e₀ (π₀ t₀))) := by rw [hv₀]; exact (hu₀.map π).map _
  have hu₁' : IsUnit (ψb₁ (algebraMap b₁ e₁ (π₁ t₁))) := by rw [hv₁]; exact (hu₁.map π).map _
  set r₀ := red N t₀ f₀ ψb₀ _ hτ₀ hu₀' with hr₀
  set r₁ := red N t₁ f₁ ψb₁ _ hτ₁ hu₁' with hr₁
  have hsr₀ : Function.Surjective r₀ := red_surj N t₀ f₀ ψb₀ _ hτ₀ hu₀' hs₀ aw₀.1
  have hsr₁ : Function.Surjective r₁ := red_surj N t₁ f₁ ψb₁ _ hτ₁ hu₁' hs₁ aw₁.1
  have hkf₀' : IsNilpotent (RingHom.ker f₀) := by rw [hkf₀]; exact NilLift.isNilpotent_map _ hk₀
  have hkf₁' : IsNilpotent (RingHom.ker f₁) := by rw [hkf₁]; exact NilLift.isNilpotent_map _ hk₁
  have hnr₀ : IsNilpotent (RingHom.ker r₀) := isNilpotent_ker_red N t₀ f₀ ψb₀ _ hτ₀ hu₀' aw₀.2 hkf₀'
  have hnr₁ : IsNilpotent (RingHom.ker r₁) := isNilpotent_ker_red N t₁ f₁ ψb₁ _ hτ₁ hu₁' aw₁.2 hkf₁'
  have hal₀ : r₀.comp (algebraMap N (N ⊗[B₀] E₀)) = (algebraMap n e).comp π := by
    refine red_alg N t₀ f₀ ψb₀ _ hτ₀ hu₀' _ ?_
    ext b
    have h1 := RingHom.congr_fun hcf₀ b
    have h2 := RingHom.congr_fun hψb₀ (π₀ b)
    have h3 := RingHom.congr_fun hc₀ b
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    change algebraMap n e (π (φ₀ b)) = _
    rw [h1, h2, h3]
  have hal₁ : r₁.comp (algebraMap N (N ⊗[B₁] E₁)) = (algebraMap n e).comp π := by
    refine red_alg N t₁ f₁ ψb₁ _ hτ₁ hu₁' _ ?_
    ext b
    have h1 := RingHom.congr_fun hcf₁ b
    have h2 := RingHom.congr_fun hψb₁ (π₁ b)
    have h3 := RingHom.congr_fun hc₁ b
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    change algebraMap n e (π (φ₁ b)) = _
    rw [h1, h2, h3]
  obtain ⟨iso, hiso⟩ := NilLift.exists_iso_lift (R := N) r₁ r₀ hsr₁ hsr₀ hnr₁ hnr₀ (hal₁.trans hal₀.symm)
  -- iso : N ⊗[B₁] E₁ ≃ₐ[N] N ⊗[B₀] E₀ with r₀ ∘ iso = r₁
  have hiso' : ∀ z, r₀ (iso z) = r₁ z := fun z => congrArg (fun k => k z) hiso
  refine ⟨E₀, E₁, N ⊗[B₀] E₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, het₀, het₁, inferInstance, f₀, f₁, r₀, algebraMap E₀ (N ⊗[B₀] E₀),
    iso.toRingEquiv.toRingHom.comp (algebraMap E₁ (N ⊗[B₁] E₁)), hs₀, hs₁, hsr₀, hkf₀, hkf₁,
    red_ker N t₀ f₀ ψb₀ _ hτ₀ hu₀' aw₀.2, hcf₀, hcf₁, hal₀, ?_, ?_, isAwayMap_tens N t₀,
    isAwayMap_comp_equiv _ _ (isAwayMap_tens N t₁) iso.toRingEquiv, red_comp N t₀ f₀ ψb₀ _ hτ₀ hu₀', ?_, hfin₀, hfin₁⟩
  · rw [← IsScalarTower.algebraMap_eq]
    exact IsScalarTower.algebraMap_eq B₀ N (N ⊗[B₀] E₀)
  · ext b
    change iso (algebraMap E₁ (N ⊗[B₁] E₁) (algebraMap B₁ E₁ b)) = algebraMap N (N ⊗[B₀] E₀) (algebraMap B₁ N b)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₁ N (N ⊗[B₁] E₁), AlgEquiv.commutes]
  · ext z
    change r₀ (iso (algebraMap E₁ (N ⊗[B₁] E₁) z)) = ψb₁ (f₁ z)
    rw [hiso', hr₁, red_eq]

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr13 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)

Over `A` with `χ : A →+* K`: `Ah` (the completion, residue `res`), `R'` (residue `χ'`, a section `s : K →+* R'`), a
chart `B`, a target `Q` with `ν : K →+* Q`, `βQ : B →+* Q` (`βQ ∘ algebraMap = ν ∘ χ`).
* `Jt B χ' = (ker χ') (R' ⊗ B)`; `tmul_mem_Jt`;
* **`kap`** `: R' ⊗[A] B →+* Q`, `r ⊗ b ↦ ν (χ' r) * βQ b` (`kap_tmul`), `Jt_le_ker_kap`;
* **`lamQ`** `: Ah ⊗[A] B →+* (R' ⊗[A] B) ⧸ Jt`, `â ⊗ b ↦ s (res â) ⊗ b` (`lamQ_tmul`), `lamQ_map`, `I_le_ker_lamQ`;
* `kap_map` (the two residues agree on `C ⊗ B`), **`exists_sec`** (the section for `resid_ker_pm`).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Tens

end Tens

section Lam

variable {K A R' B Ah : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K) (s : K →+* R')
  (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a) (hs : ∀ k, χ' (s k) = k)

theorem I_le_ker_lamQ (pI : Ideal Ah) (hp : ∀ x ∈ pI, res x = 0) :
    pI.map (Algebra.TensorProduct.includeLeftRingHom : Ah →+* Ah ⊗[A] B) ≤
      RingHom.ker (lamQ (B := B) χ χ' res s hres hχ' hs) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeftRingHom_apply, lamQ_tmul, hp x hx,
    map_zero, zero_tmul, map_zero]

variable {C : Type u} [CommRing C] [Algebra A C]

theorem lamQ_map (σh : C →ₐ[A] Ah) (σ : C →ₐ[A] R') (hσ : ∀ c, χ' (σ c) = res (σh c)) (x : C ⊗[A] B) :
    lamQ χ χ' res s hres hχ' hs (Algebra.TensorProduct.map σh (AlgHom.id A B) x) =
      Ideal.Quotient.mk (Jt B χ') (Algebra.TensorProduct.map σ (AlgHom.id A B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, lamQ_tmul,
      Ideal.Quotient.eq, ← sub_tmul, ← hσ]
    exact tmul_mem_Jt χ' _ (by rw [map_sub, hs, sub_self]) b
  | add x y hx hy => simp only [map_add, hx, hy]

variable {Q : Type u} [CommRing Q] (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))

/-- **The section**: every `a : R' ⊗ B` has a lift `x : Ah ⊗ B` with the same residue and `lamQ x ≡ a`. -/
theorem exists_sec (sh : K →+* Ah) (hsh : ∀ k, res (sh k) = k) (a : R' ⊗[A] B) :
    ∃ x : Ah ⊗[A] B, kap χ ν βQ hβ res hres x = kap χ ν βQ hβ χ' hχ' a ∧
      lamQ χ χ' res s hres hχ' hs x = Ideal.Quotient.mk (Jt B χ') a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp only [map_zero], by simp only [map_zero]⟩
  | tmul r b =>
    refine ⟨sh (χ' r) ⊗ₜ b, ?_, ?_⟩
    · rw [kap_tmul, kap_tmul, hsh]
    · rw [lamQ_tmul, hsh, Ideal.Quotient.eq, ← sub_tmul]
      exact tmul_mem_Jt χ' _ (by rw [map_sub, hs, sub_self]) b
  | add a a' ha ha' =>
    obtain ⟨x, hx1, hx2⟩ := ha
    obtain ⟨x', hx1', hx2'⟩ := ha'
    exact ⟨x + x', by rw [map_add, map_add, hx1, hx1'], by rw [map_add, map_add, hx2, hx2']⟩

end Lam

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions

For a two-chart cover `C` with ring maps `ιᵢ : R → Eᵢ` (agreeing on the overlap) and an ideal `I` of the overlap:
* **`TwoCov.Good C ι₀ I m y e`**: `E₀` is generated over `R[t]` by `m` modulo `ψ₀⁻¹ I`, and `ψ₀ mᵢ ≡ u^{eᵢ} ψ₁ yᵢ`
  modulo `I` (transition exponents `eᵢ`);
* **`TwoCov.h1_mod`**: then `H¹(O(d)) = 0` modulo `I` for `d ≥ max eᵢ`;
* **`TwoCov.good_zero`**: `Good` holds (any `I`, `I = ⊥` included) when `E₀` is finite over `R[t]`;
* **`TwoCovHom.good_lift`**: `Good` lifts along a transition with the SAME exponents (so `d` is uniform);
* **`TwoCovHom.hker_of_h1`**, **`TwoCovHom.secMap_surj_of_h1`**: `H¹ = 0` modulo `I'` and a kernel generated by
  `q` with `q · I' = 0` give the kernel hypothesis of `secMap_surj`: sections lift.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Good

variable {b₀ b₁ n : Type u} [CommRing b₀] [CommRing b₁] [CommRing n] {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n}
  {τ₀ : b₀} {τ₁ : b₁} (C : TwoCov φb₀ φb₁ τ₀ τ₁) {R : Type u} [CommRing R] (ι₀ : R →+* C.E₀) (I : Ideal C.E)

variable {C I} {d : ℕ}

variable (ι₁ : R →+* C.E₁) (hι : C.ψ₀.comp ι₀ = C.ψ₁.comp ι₁)
include hι

/-- **Serre vanishing modulo `I`**: every element of the overlap is a coboundary `ψ₀ x₀ - u^d ψ₁ x₁` modulo `I`. -/
theorem TwoCov.h1_mod (hv : C.u * C.ψ₁ (C.a₁ τ₁) = 1) {r : ℕ} {m : Fin r → C.E₀} {y : Fin r → C.E₁}
    {e : Fin r → ℕ} (hG : C.Good ι₀ I m y e) (hd : ∀ i, e i ≤ d) (z : C.E) :
    ∃ (x₀ : C.E₀) (x₁ : C.E₁), z - (C.ψ₀ x₀ - C.u ^ d * C.ψ₁ x₁) ∈ I := by
  obtain ⟨k, a, ha⟩ := C.aw₀.1 z
  obtain ⟨x₀, x₁, hx⟩ := TwoCov.PI_all ι₀ ι₁ hι hv hG hd a k
  refine ⟨x₀, x₁, ?_⟩
  have hz : C.ψ₁ (C.a₁ τ₁) ^ k * C.ψ₀ a = z := by
    rw [← ha]
    change C.ψ₁ (C.a₁ τ₁) ^ k * (C.u ^ k * z) = z
    have hp : (C.u * C.ψ₁ (C.a₁ τ₁)) ^ k = 1 := by rw [hv, one_pow]
    linear_combination z * hp
  rwa [hz] at hx

end Good

section Zero

end Zero

section Lift

end Lift

section Ker

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts

* **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`, `x ∈ Gam (a + b)`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**;
* `ρ₀_fB`, `ρ₁_fB`, **`famB_mem`**: `(fB₀ b₀, fB₁ b₁) ∈ Gam d` when `φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁`;
* **`liftN₀ : N →+* L₀`**, **`liftN₁ : N →+* L₁`** (from `N = B₀[1/t₀] = B₁[1/t₁]`), `liftN₀_φ₀`, `liftN₁_φ₁`,
  `liftN₀_inv`, `liftN₁_inv`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat2

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem liftN₀_φ₀ (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (b : B₀) :
    liftN₀ C hφ₀ hu₀ (φ₀ b) = jL₀ C (fB₀ C b) := by
  letI := φ₀.toAlgebra
  haveI := isLocalization_of_isAwayMap φ₀ t₀ hφ₀ hu₀
  exact IsLocalization.Away.lift_eq t₀ (g := (jL₀ C).comp (fB₀ C))
    (IsLocalization.Away.algebraMap_isUnit (tFm C)) b

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAsN3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian

* `map_Xid_hatPhi`: `(X_σ).map hatPhi = p Â`.
* `hatPhi_surjective` (`p = span (range a)` f.g.): `hatPhi a` is surjective
  (`surjective_of_mk_map_comp_surjective`, `isPrecomplete_Xid`, `ker_evalOneₐ_eq_map`).
* `hat_noeth_of_gen`, **`hat_noeth`**: `IsNoetherianRing (AdicCompletion p A)` for `A` noetherian.
-/

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u v

section HatN3

variable {A : Type u} [CommRing A] {σ : Type v} [Fintype σ] (a : σ → A)

theorem hat_noeth_of_gen [IsNoetherianRing A] :
    IsNoetherianRing (AdicCompletion (Ideal.span (Set.range a)) A) :=
  isNoetherianRing_of_surjective _ _ (hatPhi a) (hatPhi_surjective a (Ideal.fg_of_isNoetherianRing _))

end HatN3

/-- The `p`-adic completion of a noetherian ring is noetherian. -/
theorem hat_noeth {A : Type u} [CommRing A] [IsNoetherianRing A] (p : Ideal A) :
    IsNoetherianRing (AdicCompletion p A) := by
  obtain ⟨s, rfl⟩ := Ideal.fg_of_isNoetherianRing p
  have hr : Set.range (fun x : s => (x : A)) = (s : Set A) := by
    ext x
    simp
  have h := hat_noeth_of_gen (fun x : s => (x : A))
  rwa [hr] at h

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs4b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap

* `exists_presN`: if `E` is presented as `Pres g` over `P`, `f : P → P'` is a localization away from `t` with `f t` a
  unit, and `q : E → E'` is a localization away from `t` compatible with `bN : P' → E'`, then `E' ≅ Pres (gmap f g)`
  (via `presN`, bijective by `away_bij`).
* `exists_subst`: a `P`-isomorphism `Pres g ≅ Pres g'` is `presIso` of substitution data `u v` (with all four
  membership witnesses).
* `chart_pres`: a finite etale `b : P → E` is presented by a square system with etale and finite witnesses.
* **`two_chart_pres`**: the two charts `E₀, E₁` of a cover glued along `E`, their base changes to the overlap and
  substitution data between the two overlap presentations, all in one package.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section PresN

end PresN

section Subst

end Subst

set_option maxHeartbeats 400000 in
/-- **Presentations of a two-chart cover and of its overlap.** -/
theorem two_chart_pres {P₀ P₁ P' E₀ E₁ E : Type u} [CommRing P₀] [CommRing P₁] [CommRing P'] [CommRing E₀]
    [CommRing E₁] [CommRing E] (f₀ : P₀ →+* P') (f₁ : P₁ →+* P') (t₀ : P₀) (t₁ : P₁)
    (hf₀ : IsAwayMap f₀ t₀) (hf₁ : IsAwayMap f₁ t₁) (hu₀ : IsUnit (f₀ t₀)) (hu₁ : IsUnit (f₁ t₁))
    (b₀ : P₀ →+* E₀) (b₁ : P₁ →+* E₁) (bN : P' →+* E) (q₀ : E₀ →+* E) (q₁ : E₁ →+* E)
    (het₀ : b₀.Etale) (het₁ : b₁.Etale) (hfi₀ : b₀.Finite) (hfi₁ : b₁.Finite)
    (hq₀ : q₀.comp b₀ = bN.comp f₀) (hq₁ : q₁.comp b₁ = bN.comp f₁)
    (aw₀ : IsAwayMap q₀ (b₀ t₀)) (aw₁ : IsAwayMap q₁ (b₁ t₁)) :
    ∃ (r₀ r₁ : ℕ) (g₀ : Fin r₀ → MvPolynomial (Fin r₀) P₀) (g₁ : Fin r₁ → MvPolynomial (Fin r₁) P₁)
      (e₀ : Pres g₀ ≃+* E₀) (e₁ : Pres g₁ ≃+* E₁) (eN₀ : Pres (gmap f₀ g₀) ≃+* E)
      (eN₁ : Pres (gmap f₁ g₁) ≃+* E) (u : Fin r₀ → MvPolynomial (Fin r₁) P')
      (v : Fin r₁ → MvPolynomial (Fin r₀) P')
      (hu : ∀ j, MvPolynomial.bind₁ u (gmap f₀ g₀ j) ∈ Ideal.span (Set.range (gmap f₁ g₁)))
      (hv : ∀ i, MvPolynomial.bind₁ v (gmap f₁ g₁ i) ∈ Ideal.span (Set.range (gmap f₀ g₀)))
      (huv : ∀ i, MvPolynomial.bind₁ u (v i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap f₁ g₁)))
      (hvu : ∀ j, MvPolynomial.bind₁ v (u j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap f₀ g₀))),
      ((∃ w, jdet g₀ * w - 1 ∈ Ideal.span (Set.range g₀)) ∧
        (∀ j, ∃ q : Polynomial P₀, q.Monic ∧
          Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range g₀)) ∧
        (∃ w, jdet g₁ * w - 1 ∈ Ideal.span (Set.range g₁)) ∧
        (∀ j, ∃ q : Polynomial P₁, q.Monic ∧
          Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range g₁))) ∧
      ((∀ a, e₀ (algebraMap P₀ (Pres g₀) a) = b₀ a) ∧ (∀ a, e₁ (algebraMap P₁ (Pres g₁) a) = b₁ a) ∧
        (∀ a, eN₀ (algebraMap P' (Pres (gmap f₀ g₀)) a) = bN a) ∧
        (∀ a, eN₁ (algebraMap P' (Pres (gmap f₁ g₁)) a) = bN a)) ∧
      ((∀ x, eN₀ (presMap f₀ g₀ x) = q₀ (e₀ x)) ∧ (∀ x, eN₁ (presMap f₁ g₁ x) = q₁ (e₁ x)) ∧
        ∀ x, eN₀ (presIso (gmap f₁ g₁) (gmap f₀ g₀) u v hu hv huv hvu x) = eN₁ x) := by
  obtain ⟨r₀, g₀, e₀, hJ₀, hF₀, he₀⟩ := chart_pres b₀ het₀ hfi₀
  obtain ⟨r₁, g₁, e₁, hJ₁, hF₁, he₁⟩ := chart_pres b₁ het₁ hfi₁
  obtain ⟨eN₀, hN₀, hM₀⟩ := exists_presN f₀ g₀ bN t₀ hf₀ hu₀ b₀ q₀ hq₀ aw₀ e₀ he₀
  obtain ⟨eN₁, hN₁, hM₁⟩ := exists_presN f₁ g₁ bN t₁ hf₁ hu₁ b₁ q₁ hq₁ aw₁ e₁ he₁
  have hm : ∀ a, (eN₁.trans eN₀.symm) (algebraMap P' (Pres (gmap f₁ g₁)) a) =
      algebraMap P' (Pres (gmap f₀ g₀)) a := fun a => by
    rw [RingEquiv.trans_apply, hN₁, ← hN₀, RingEquiv.symm_apply_apply]
  obtain ⟨u, v, hu, hv, huv, hvu, hI⟩ := exists_subst (gmap f₁ g₁) (gmap f₀ g₀) (eN₁.trans eN₀.symm) hm
  exact ⟨r₀, r₁, g₀, g₁, e₀, e₁, eN₀, eN₁, u, v, hu, hv, huv, hvu, ⟨hJ₀, hF₀, hJ₁, hF₁⟩,
    ⟨he₀, he₁, hN₀, hN₁⟩,
    ⟨hM₀, hM₁, fun x => by rw [hI x, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]⟩⟩

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr14 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts

With `fh = σh ⊗ id : C ⊗ B → Ah ⊗ B`, `f' = σ ⊗ id : C ⊗ B → R' ⊗ B`, `θh : Pres (gmap fh gC) → Q` restricting to
`kap res` on `Ah ⊗ B`:
* `exists_cov`, **`hκT`** (the compatibility needed by `resid`), `lamT` (`lamT_apply`, `lamT_hlam`);
* **`resid_surj_T`**, **`resid_ker_T`**: the residue `resid fh f' gC θh (kap χ') _` is onto with kernel
  `Jt B χ' · Pres (gmap f' gC)`, when `ker θh = pI · Pres` with `pI ≤ ker res`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable {K A R' B Ah C Q : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] [CommRing C] [Algebra A C] [CommRing Q]
  (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K)
  (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)
  (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))

variable {r : ℕ} (σh : C →ₐ[A] Ah) (σ : C →ₐ[A] R') (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B))
  (θh : Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC) →+* Q)

/-- **The residue is onto.** -/
theorem resid_surj_T (s : K →+* R') (hs : ∀ k, χ' (s k) = k)
    (hθk : ∀ x, θh (algebraMap (Ah ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC))
      x) = kap χ ν βQ hβ res hres x) (hθ : Function.Surjective θh)
    (hκ : (kap χ ν βQ hβ χ' hχ').comp (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom =
      (θh.comp (algebraMap (Ah ⊗[A] B)
        (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC)))).comp
        (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom) :
    Function.Surjective (resid (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom
      (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC θh (kap χ ν βQ hβ χ' hχ') hκ) := by
  apply resid_surj _ _ gC θh _ hκ hθ
  intro x
  obtain ⟨a, ha⟩ := exists_cov χ χ' res hres hχ' ν βQ hβ s hs x
  exact ⟨a, ha.trans (hθk x).symm⟩

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCh =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`

For `V` affine, `π : Y ⟶ P¹_V` finite, a `K`-point `x` of `V` and a finite etale `q : T ⟶ Y_x`, the charts
`Γ(Y_x, fx⁻¹ Yᵢ)` and `Γ(T, q⁻¹ fx⁻¹ Yᵢ)` satisfy every hypothesis of `CoverLiftAt`. **`nonempty_liftD`**: under
`CoverLiftAt K Γ(V) χ` (`χ` the point `x`), the lift data `LiftD` (= `CoverLift` at these charts) exist.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

attribute [local instance] algKY

theorem hρ0 : (ρx0 K gV π x).comp ((fx K gV π x).app (Yc K gV π 0)).hom =
    ((fx K gV π x).app (Yc K gV π 0 ⊓ Yc K gV π 1)).hom.comp (φY0 K gV π).toRingHom := by
  ext b
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ b)
    (Scheme.Hom.naturality (fx K gV π x) (homOfLE inf_le_left : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 0).op)).symm

theorem hρ1 : (ρx1 K gV π x).comp ((fx K gV π x).app (Yc K gV π 1)).hom =
    ((fx K gV π x).app (Yc K gV π 0 ⊓ Yc K gV π 1)).hom.comp (φY1 K gV π).toRingHom := by
  ext b
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ b)
    (Scheme.Hom.naturality (fx K gV π x) (homOfLE inf_le_right : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 1).op)).symm

section Cover

attribute [local instance] algT

end Cover

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_StkBC =====
section

/-!
# S4-EtPBC-A, L1f: the base change map on stalks

Generic form: for `g : P ⟶ S`, a geometric point `s` of `S`, a sheaf `F` on `P`, `n : ℕ`, a presheaf `Q` on `S` and
additive bijections `e V : Q(V) ≃+ Ext^n(Λ[g⁻¹ V], F)` natural in `V` (`GermNat`), the germ maps
`germBC j = Delta.bc j ∘ e` (base change along the units `bcUnit`) are compatible, so they define `stalkBC` on the fibre
`Q_s` of `Q`. It is surjective / injective when base change is surjective / injective on germs (`BCSurj` / `BCInj`):
`stalkEquiv : Q_s ≃+ Ext^n(Λ_{P_s}, ι^* F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- Base change is injective on germs (degree `q`, sheaf `G`). -/
abbrev BCInj (q : ℕ) (G : EtSh Λ P) : Prop :=
  Delta.InjAt (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) q G

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0b =====
section

/-!
# S4-EtPBC-A, G1b: base change in degree `0` on sections

For `g : P ⟶ S`, a geometric point `s`, an etale neighbourhood `j = (V, v)` and a class
`α ∈ Ext^0(Λ[g⁻¹ V], G)`, let `sec0 α ∈ G(g⁻¹ V)` be the corresponding section.
* `bc_zero_eq`: `bc_j α = mk₀ (u_v ≫ ι^* α)`;
* **`sec_of_bc_zero`**: if `bc_j α = 0` then the section `σ_v^* η_G(sec0 α)` of `ι^* G` over `P_s` vanishes
  (`η` the unit of `ι^* ⊣ ι_*`, `σ_v = nbhdSec` the section of `ι⁻¹(g⁻¹ V) ⟶ P_s` given by `v`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.PtSec
  RamanujanPetersson.EtCompact.Supp

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- `ι^* α` on the unit section is `η_G` of the section of `α`. -/
theorem pull_unitSec (j : Nbhd s) (G : EtSh Λ P) (f : (nbhdSys Λ g s).obj j ⟶ G) :
    (((pull (fibι g s) Λ).map f).hom.app (op ((etPull (fibι g s)).obj ((etPull g).obj j.1)))).hom
        (unitSec Λ g s j) =
      ((((pullAdj (fibι g s) Λ).unit.app G).hom.app (op ((etPull g).obj j.1))).hom
        (freeEquiv Λ ((etPull g).obj j.1) G f)) := by
  have h1 := freeEquiv_comp Λ ((etPull g).obj j.1)
    ((pullAdj (fibι g s) Λ).unit.app ((nbhdSys Λ g s).obj j)) ((push (fibι g s) Λ).map ((pull (fibι g s) Λ).map f))
  have h2 := freeEquiv_comp Λ ((etPull g).obj j.1) f ((pullAdj (fibι g s) Λ).unit.app G)
  have h3 : (pullAdj (fibι g s) Λ).unit.app ((nbhdSys Λ g s).obj j) ≫
      (push (fibι g s) Λ).map ((pull (fibι g s) Λ).map f) = f ≫ (pullAdj (fibι g s) Λ).unit.app G :=
    (pullAdj (fibι g s) Λ).unit_naturality f
  exact h1.symm.trans ((congrArg (freeEquiv Λ ((etPull g).obj j.1) _) h3).trans h2)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Psi =====
section

/-!
# S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre

For `π : Y ⟶ P`, a geometric point `t` of `P` and `C = constSh Λ Y M`:
* `cval_sub`, `cval_res`, `germ_res` (restriction to a smaller neighbourhood);
* `cval_eq_of_germ_eq`: equal germs in `(π_* C)_t` have equal values along the fibre `fib π t`;
* **`germ_eq_of_cval`** (universally closed `π`): conversely, equal values give equal germs;
* `psi e x`: the value at `x ∈ fib π t` of a germ `e ∈ (π_* C)_t`; **`psi_germ`**;
* **`eq_of_psi`** (universally closed, quasi-compact `π`): germs with equal values at the closed points of the
  fibre are equal.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y P : Scheme.{u}} (π : Y ⟶ P) (t : GeomPt P) {M : ModuleCat.{u} Λ}

theorem psi_germ (j : Nbhd t) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj j.1))) (x : fib π t) :
    psi π t ((t.point.toPresheafFiber j.1 j.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom z) x =
      cval z (fibToNbhd π t j x) :=
  cval_eq_of_germ_eq π t _ z (exists_rep π t _).choose_spec.choose_spec x

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FinGenA =====
section

/-!
# S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes

* **`exists_affine_le`**: every etale neighbourhood of a geometric point is refined by one with affine total space;
* `exists_repG_aff`, `exists_pullRepG_aff`, `exists_fg_aff`: the representations of `FinGen` over affines;
* **`bcSurj_of_fg_aff`**: `BCSurj 0` for `G` from `BCSurj 0` for the subsheaves `ker (coker φ)` generated by finitely
  many sections `φ : ∐ Λ[W x] ⟶ G` with every `(W x).left` affine.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {X P : Scheme.{u}} (ι : X ⟶ P)

/-- **Finitely many sections over affines suffice** (`X` compact). -/
theorem exists_fg_aff [CompactSpace X] (G : EtSh Λ P) (b : unitSh Λ X ⟶ (pull ι Λ).obj G) :
    ∃ (t : Finset X) (W : X → P.Etale) (z : ∀ x, G.obj.obj (op (W x))), (∀ x, IsAffine (W x).left) ∧
      ∀ {Q : EtSh Λ P} (p : G ⟶ Q), (∀ x ∈ t, (p.hom.app (op (W x))).hom (z x) = 0) →
        b ≫ (pull ι Λ).map p = 0 := by
  choose W U h a z hW hz using fun x : X => exists_pullRepG_aff ι G (geomPtAt x) b
  have hx : ∀ x, x ∈ Set.range (U x).hom := fun x =>
    ⟨((geomPtAt x).liftOf (a x)).left (default : Spec (CommRingCat.of (geomPtAt x).Ω)),
      (congrArg (fun φ => φ.base (default : Spec (CommRingCat.of (geomPtAt x).Ω)))
        (Over.w ((geomPtAt x).liftOf (a x)))).trans (center_geomPtAt x)⟩
  have hopen : ∀ x, IsOpen (Set.range (U x).hom) := fun x => by
    have : Etale (U x).hom := (U x).prop
    exact (U x).hom.isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (U x).hom) hopen
    (fun y _ => Set.mem_iUnion.2 ⟨y, hx y⟩)
  refine ⟨t, W, z, hW, fun {Q} p hp => eq_zero_of _ fun y => ?_⟩
  obtain ⟨x, hxt, w, hw⟩ : ∃ x ∈ t, ∃ w, (U x).hom w = y := by
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hxt, w, hw⟩ := hy
    exact ⟨x, hxt, w, hw⟩
  refine ⟨U x, w, hw, ?_⟩
  have e1 : (((pull ι Λ).map p).hom.app (op ((etPull ι).obj (W x)))).hom
      ((((pullAdj ι Λ).unit.app G).hom.app (op (W x))).hom (z x)) = 0 := by
    have hn := congrArg (fun φ => (φ.hom.app (op (W x))).hom (z x)) ((pullAdj ι Λ).unit_naturality p)
    exact hn.trans ((congrArg (((pullAdj ι Λ).unit.app Q).hom.app (op (W x))).hom (hp x hxt)).trans (map_zero _))
  exact (congrArg (((pull ι Λ).map p).hom.app (op (U x))).hom (hz x)).trans
    ((app_map ((pull ι Λ).map p) (h x) _).trans
      ((congrArg (((pull ι Λ).obj Q).obj.map (h x).op).hom e1).trans (map_zero _)))

end Gen

section Red

end Red

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCa =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values

* `cval_uC`: values of `uC g M : M_X ⟶ g_* M_Y` (the section pulled back to `V ×_X Y`);
* `muU h Φ V : V ×_P U₁ ⟶ V ×_P U₂`, `kapU` (the same into `(V ×_P U₂) ×_{U₂} U₁`), `kapU_nat`;
* **`rU h Φ M : Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}`** with **`cval_rU`** (`cval (rU z) w = cval z (muU w)`);
* `nuU h Φ t : fib (h ≫ Φ) t ⟶ fib Φ t`, `muU_fibToNbhd`, **`cval_rU_fib`**;
* `muU_injective` for a closed immersion `h`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section RU

variable {U₁ U₂ P : Scheme.{u}} (h : U₁ ⟶ U₂) (Φ : U₂ ⟶ P)

/-- **Values of `rU` along the fibre.** -/
theorem cval_rU_fib (t : GeomPt P) (j : Nbhd t) (z : (constSh Λ U₂ M).obj.obj (op ((etPull Φ).obj j.1)))
    (x : fib (h ≫ Φ) t) :
    cval (((rU M h Φ).hom.app (op j.1)).hom z) (fibToNbhd (h ≫ Φ) t j x) =
      cval z (fibToNbhd Φ t j (nuU h Φ t x)) :=
  (cval_rU h Φ j.1 z _).trans (congrArg (cval z) (congrArg (fun φ => φ.base x) (muU_fibToNbhd h Φ t j)))

end RU

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCb =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective

`Φ : U ⟶ P` finite, `ι : Ps ⟶ P` a closed immersion, `h = pullback.fst Φ ι`, `t` a geometric point of `P`
through `Ps` (`σ₀ ≫ ι = t.pt`): the stalk map of `rU M h Φ` at `t` is bijective (`rStk_bijective`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section Stalk

variable {U P Ps : Scheme.{u}} (Φ : U ⟶ P) (ι : Ps ⟶ P)

theorem psi_rStk (t : GeomPt P)
    (e : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj ((push Φ Λ).obj (constSh Λ U M)).obj)
    (x : fib (pullback.fst Φ ι ≫ Φ) t) :
    psi (pullback.fst Φ ι ≫ Φ) t
        (((t.point.presheafFiber (A := ModuleCat.{u} Λ)).map (rU M (pullback.fst Φ ι) Φ).hom).hom e) x =
      psi Φ t e (nuU (pullback.fst Φ ι) Φ t x) := by
  obtain ⟨j, z, rfl⟩ := exists_rep Φ t e
  exact ((congrArg (fun e' => psi (pullback.fst Φ ι ≫ Φ) t e' x) (rStk_germ Φ ι t j z)).trans
    (psi_germ (pullback.fst Φ ι ≫ Φ) t j _ x)).trans
    ((cval_rU_fib (pullback.fst Φ ι) Φ t j z x).trans (psi_germ Φ t j z _).symm)

end Stalk

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCc =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion

`Φ : U ⟶ P` finite, `ι : Ps ⟶ P` a closed immersion, `φs = pullback.snd Φ ι : U ×_P Ps ⟶ Ps`:
* `rC M Φ ι : Φ_* M_U ⟶ ι_* φs_* M_{U_s}` (restriction of sections to `U_s`);
* `eC M Φ ι : ι^* Φ_* M_U ⟶ φs_* M_{U_s}` its adjoint;
* **`isIso_eC`**: `eC` is an isomorphism (stalks via `rStk_bijective`, closed-immersion counit iso).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section BC

variable {U P Ps : Scheme.{u}} (Φ : U ⟶ P) (ι : Ps ⟶ P)

variable (M) in
/-- **The base change map** `ι^* Φ_* M_U ⟶ φs_* M_{U_s}` (adjoint of `rC`). -/
def eC : (pull ι Λ).obj ((push Φ Λ).obj (constSh Λ U M)) ⟶
    (push (pullback.snd Φ ι) Λ).obj (constSh Λ (pullback Φ ι) M) :=
  ((pullAdj ι Λ).homEquiv _ _).symm (rC M Φ ι)

end BC

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dB =====
section

/-!
# S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`

* `isClosedImmersion_of_isIso_comp`: a point `σ : Spec Ω ⟶ V` with `σ ≫ gV` an isomorphism is a closed immersion;
* `sec_ext_cval`: sections of a constant sheaf are determined by their values;
* `rUq`, `cval_rUq`: restriction along a commutative triangle; `cval_pushCompIso_inv`;
* `resAdj_symm_app`, `mR_app`, `cval_mR`: the transpose `mR` on sections and values (kernel-cheap: generic lemmas);
* `mS : π_* M_Y ⟶ f_* Φ_* M_U` (restriction along `h : U ⟶ Y`, `h ≫ π = Φ ≫ f`), `mP := (f^* ⊣ f_*)`-adjoint;
* **`mono_mP`**: for `f` etale and `U ⟶ P' ×_P Y` surjective, `mP : f^* π_* M_Y ⟶ Φ_* M_U` is a monomorphism.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC

universe u

section Geo0

end Geo0

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section RUq

end RUq

section M

variable {P P' Y U : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y) (hh : h ≫ π = Φ ≫ f)

theorem cval_mS (V : P.Etale) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj V)))
    (w : ((etPull Φ).obj ((etPull f).obj V)).left) :
    cval (((mS M π f Φ h hh).hom.app (op V)).hom z) w =
      cval z (muq h π (Φ ≫ f) hh V (((etPullCompIso Φ f).inv.app V).left w)) :=
  (cval_pushCompIso_inv Φ f V _ w).trans (cval_rUq h π (Φ ≫ f) hh V z _)

end M

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dC =====
section

/-!
# S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly

`π : Y ⟶ P`, `f : P' ⟶ P`, `Φ : U ⟶ P'`, `h : U ⟶ Y` with `h ≫ π = Φ ≫ f`, `ι' : Ps ⟶ P'`, `ι = ι' ≫ f`:
* `hsU : U_s ⟶ Y_s` and `rUs : π_{s*} M_{Y_s} ⟶ φs_* M_{U_s}` (restriction on the fibre);
* **`C1`**: `eC M π ι ≫ rUs = ι^*(restriction) ≫ eC M Φ ι'` (both base change maps are restriction of sections);
* `HypT`: the input that T1 + T2 supply (every extension of `Λ` by `π_{s*} M_{Y_s}` is split by such data);
* **`bcSurj_one_push_of_hypT`**: base change is surjective in degree one for `π_* M_Y`, given `HypT`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC RamanujanPetersson.EtPBC.PushKill

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

theorem cval_rC {U P Ps : Scheme.{u}} (Φ : U ⟶ P) (ι : Ps ⟶ P) (V : P.Etale)
    (z : (constSh Λ U M).obj.obj (op ((etPull Φ).obj V)))
    (w : ((etPull (pullback.snd Φ ι)).obj ((etPull ι).obj V)).left) :
    cval (((rC M Φ ι).hom.app (op V)).hom z) w =
      cval z (muq (pullback.fst Φ ι) Φ (pullback.snd Φ ι ≫ ι) pullback.condition V
        (((etPullCompIso (pullback.snd Φ ι) ι).inv.app V).left w)) := by
  rw [rC_eq]
  exact (cval_pushCompIso_inv _ _ V _ w).trans (cval_rUq _ _ _ _ V z _)

section C1

end C1

section B3

end B3

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_DescK1 =====
section

/-!
# S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`

`0 → F → E → Λ_X → 0` short exact, `σ ∈ E(T)` with `b σ = 1`:
* `secT σ : Hom(Λ|_T, E|_T)` (the section `1 ↦ σ`), `secT_b`: `secT σ ≫ b = 1`;
* `retT : Hom(E|_T, F|_T)` with `a ≫ retT = 1` (`a_retT`): `x ↦ a⁻¹ (x - secT (b x))`;
* for `ψ : Z ⟶ T`, **`tau : E ⟶ (ψ ≫ T.hom)_* N_Z`** (`F = N_X`) with **`a_tau`**: `a ≫ tau = uC`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescK

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.SgUnit RamanujanPetersson.EtPBC

universe u

section Ret

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {F E : EtSh Λ X}
  (a : F ⟶ E) (b : E ⟶ unitSh Λ X) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  {T : X.Etale} (σ : E.obj.obj (op T))
  (hσ : (b.hom.app (op T)).hom σ = (constUnit (ModuleCat.of Λ Λ) T).hom 1)

theorem retT_app (W : (Over T)ᵒᵖ) (x : ((Over.forget T).op ⋙ E.obj).obj W) :
    ((wh a T).app W).hom (((retT a b hab hS σ hσ).app W).hom x) = piT b σ W x :=
  (exists_retT a b hab hS σ hσ W x).choose_spec

end Ret

section Tau

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {N : ModuleCat.{u} Λ} {E : EtSh Λ X}
  (a : constSh Λ X N ⟶ E) (b : E ⟶ unitSh Λ X) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  {T : X.Etale} (σ : E.obj.obj (op T))
  (hσ : (b.hom.app (op T)).hom σ = (constUnit (ModuleCat.of Λ Λ) T).hom 1) {Z : Scheme.{u}} (ψ : Z ⟶ T.left)

/-- **`τ : E ⟶ (ψ ≫ T)_* N_Z`**, through the retraction over `T`. -/
def tau : E ⟶ (push (ψ ≫ T.hom) Λ).obj (constSh Λ Z N) :=
  (resAdj T.hom Λ).unit.app E ≫
    (push T.hom Λ).map (homOverEquiv E (constSh Λ X N) T (retT a b hab hS σ hσ) ≫ d0 N ψ) ≫
      (pushCompIso Λ ψ T.hom).hom.app (constSh Λ Z N)

end Tau

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_FGS =====
section

/-!
# S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre

* `exists_affine_refine'`: finite affine refinement of a covering sieve of a COMPACT etale object;
* `exists_cover_lift`: for an epimorphism `S.g` and a global section `q` of `S.X₃` on a compact `Y`, an affine etale
  surjection `V ⟶ Y` and a section of `S.X₂` over `V` lifting `q`;
* `isAffine_nv1`: `V ×_Y V` is affine when `V` is affine and `V ⟶ Y` is an affine morphism;
* `exists_common_rep'`, `exists_fib_at`, `exists_pullRepS`: local representation of a section of `ι^* G` over `U`;
* **`exists_fg_sec`**: a section `d` of `ι^* G` over a compact `U` is killed by every `p : G ⟶ Q` that kills
  finitely many sections `z x ∈ G(W x)` over affines.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Refine

end Refine

section Gen

variable {Λ : Type u} [CommRing Λ] {X P : Scheme.{u}} (ι : X ⟶ P)

/-- **Finitely many sections over affines kill a section over a compact `U`.** -/
theorem exists_fg_sec (G : EtSh Λ P) (U : X.Etale) [CompactSpace U.left] (d : ((pull ι Λ).obj G).obj.obj (op U)) :
    ∃ (t : Finset U.left) (W : U.left → P.Etale) (z : ∀ x, G.obj.obj (op (W x))), (∀ x, IsAffine (W x).left) ∧
      ∀ {Q : EtSh Λ P} (p : G ⟶ Q), (∀ x ∈ t, (p.hom.app (op (W x))).hom (z x) = 0) →
        (((pull ι Λ).map p).hom.app (op U)).hom d = 0 := by
  choose w hw using fun x : U.left => exists_fib_at U x
  choose W U' h f₀ a z hW hfa hz using fun x : U.left => exists_pullRepS ι G (geomPtAt (U.hom x)) U (w x) d
  have hx : ∀ x, x ∈ Set.range (f₀ x).left := fun x =>
    ⟨fibPt _ (a x), (fibPt_map _ (f₀ x) (a x)).symm.trans ((congrArg (fibPt _) (hfa x)).trans (hw x))⟩
  have hopen : ∀ x, IsOpen (Set.range (f₀ x).left) := fun x => (f₀ x).left.isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (f₀ x).left) hopen
    (fun y _ => Set.mem_iUnion.2 ⟨y, hx y⟩)
  refine ⟨t, W, z, hW, fun {Q} p hp => ?_⟩
  refine sep_of_cover ((pull ι Λ).obj Q) (fun x : t => f₀ x.1) ?_ _ 0 fun x => ?_
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨⟨x, hxt⟩, hy⟩
  · have e1 : (((pull ι Λ).map p).hom.app (op ((etPull ι).obj (W x.1)))).hom
        ((((pullAdj ι Λ).unit.app G).hom.app (op (W x.1))).hom (z x.1)) = 0 := by
      have hn := congrArg (fun φ => (φ.hom.app (op (W x.1))).hom (z x.1)) ((pullAdj ι Λ).unit_naturality p)
      exact hn.trans ((congrArg (((pullAdj ι Λ).unit.app Q).hom.app (op (W x.1))).hom (hp x.1 x.2)).trans
        (map_zero _))
    rw [map_zero]
    exact ((app_map ((pull ι Λ).map p) (f₀ x.1) d).symm.trans (congrArg _ (hz x.1))).trans
      ((app_map ((pull ι Λ).map p) (h x.1) _).trans
        ((congrArg (((pull ι Λ).obj Q).obj.map (h x.1).op).hom e1).trans (map_zero _)))

end Gen

end RamanujanPetersson.EtPBC

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

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} (G : EtSh Λ P)

section Gsum

end Gsum

/-- Killing finitely many relations. -/
theorem exists_kill (x : P) {J : Type u} [Finite J] (W : J → P.Etale) [∀ j, QuasiCompact (W j).hom]
    (f : ∀ j, G.obj.obj (op (W j))) (s : Finset (FibPts x W →₀ Λ)) (hs : ∀ c ∈ s, GenAlg.rel W G f x c = 0) :
    ∃ (T : P.Etale) (t : (geomPtAt x).point.fiber.obj T) (τ : ∀ p : FibPts x W, T ⟶ W p.1),
      (∀ p, (geomPtAt x).point.fiber.map (τ p) t = p.2) ∧ ∀ c ∈ s, gsum G f τ c = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨T, t, τ, -, hτ⟩ := exists_split x W
    exact ⟨T, t, τ, hτ, fun c hc => absurd hc (Finset.notMem_empty c)⟩
  | insert c s hcs ih =>
    obtain ⟨T, t, τ, hτ, h0⟩ := ih fun d hd => hs d (Finset.mem_insert_of_mem hd)
    obtain ⟨T', t', ρ, hρ, h1⟩ := exists_refine G f t τ hτ c (hs c (Finset.mem_insert_self c s))
    refine ⟨T', t', fun p => ρ ≫ τ p, fun p => (map_comp_fib ρ (τ p) t').trans
      ((congrArg (fun z => (geomPtAt x).point.fiber.map (τ p) z) hρ).trans (hτ p)), ?_⟩
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h1
    · rw [gsum_comp, h0 d hd, map_zero]

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_EPsiRel =====
section

/-!
# S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres

For `π : Y ⟶ P` and `C = constSh Λ Y M`:
* `cval_smul`; `psi_add`, `psi_smul`, `psi_zero`: `psi` is linear;
* **`psi_rel`**: the value of `rel W (π_* C) f x l` at `q ∈ fib π x̄` is `Σ l(j, a) · cval (f j) (fibToNbhd ⟨W j, a⟩ q)`;
* **`rel_eq_zero_iff`** (`π` universally closed and quasi-compact): `rel W (π_* C) f x l = 0` iff these sums vanish
  at the closed points of the fibre.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenAlg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y P : Scheme.{u}} {M : ModuleCat.{u} Λ}

variable (π : Y ⟶ P) (t : GeomPt P)

theorem psi_add (e₁ e₂ : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj ((push π Λ).obj (constSh Λ Y M)).obj)
    (q : fib π t) : psi π t (e₁ + e₂) q = psi π t e₁ q + psi π t e₂ q := by
  obtain ⟨X, a, z₁, z₂, rfl, rfl⟩ := t.point.toPresheafFiber_jointly_surjective₂ e₁ e₂
  have h := psi_germ π t ⟨X, a⟩ (z₁ + z₂) q
  rw [map_add] at h
  rw [h, psi_germ π t ⟨X, a⟩ z₁ q, psi_germ π t ⟨X, a⟩ z₂ q]
  exact cval_add _ _ _

theorem psi_smul (c : Λ) (e : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj ((push π Λ).obj (constSh Λ Y M)).obj)
    (q : fib π t) : psi π t (c • e) q = c • psi π t e q := by
  obtain ⟨X, a, z, rfl⟩ := t.point.toPresheafFiber_jointly_surjective e
  have h := psi_germ π t ⟨X, a⟩ (c • z) q
  rw [map_smul] at h
  rw [h, psi_germ π t ⟨X, a⟩ z q]
  exact cval_smul _ _ _

end RamanujanPetersson.EtPBC.GenAlg

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

variable {Uo Uz : P.Opens} (h : Uo ≤ Uz) {D₁ D : P.Etale} (d : D₁ ⟶ D)

/-- **Shrinking `D`**: `ε_loc(D₁) ∘ Λ[prdMap d] = ε_loc(D)`. -/
theorem locC_shrink (hS₁ : (locC Λ D₁ h).ShortExact) (hS : (locC Λ D h).ShortExact) :
    hS₁.extClass.comp (Ext.mk₀ (freeMap Λ (prdMap d (opEt Uo)))) (add_zero 1) = hS.extClass := by
  have hnat := mv_naturality (prdMap d (opEt Uo)) d (𝟙 (opEt Uz)) (𝟙 (etId P)) (prdMap_prW d (opEt Uo))
    (by rw [Category.comp_id, ← Category.assoc, prdMap_prT]) (toTop_ext _ _) (toTop_ext _ _) hS₁ hS
  rw [freeMap_id, Ext.mk₀_id_comp] at hnat
  exact hnat

/-- The class of `κ` through `D` is the class of its pullback through `D₁`. -/
theorem locCls_shrink (hS₁ : (locC Λ D₁ h).ShortExact) (hS : (locC Λ D h).ShortExact) {F : EtSh Λ P}
    (κ : Ext.{u} (freeSh Λ (prd D (opEt Uo))) F 1) :
    hS.extClass.comp κ (show 1 + 1 = 2 from rfl) =
      hS₁.extClass.comp ((Ext.mk₀ (freeMap Λ (prdMap d (opEt Uo)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) := by
  rw [← locC_shrink h d hS₁ hS, Ext.comp_assoc_of_second_deg_zero]

end Shrink

section Opn

end Opn

section Res

end Res

end RamanujanPetersson.EtPBC.EtMV

end

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

end Dec

section Et

variable (A : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [IsJacobsonRing A] (hA : ¬IsField A)
  (C : Type*) [CommRing C] [Algebra A C] [Algebra.Etale A C]

include hA in
/-- **Local rings of an etale algebra over a Jacobson PID are domains** (at maximal ideals). -/
theorem isDomain_loc_of_etale (m : Ideal C) (hm : m.IsMaximal) : IsDomain (Localization.AtPrime m) := by
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType A (C ⧸ m) := Algebra.FiniteType.trans (S := C) inferInstance inferInstance
  have : Module.Finite A (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing A (C ⧸ m)
  have hcomap : ((⊥ : Ideal (C ⧸ m)).comap (algebraMap A (C ⧸ m))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ⊥
  have heq : (⊥ : Ideal (C ⧸ m)).comap (algebraMap A (C ⧸ m)) = m.under A := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot, Ideal.under]
    rw [IsScalarTower.algebraMap_apply A C (C ⧸ m), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  rw [heq] at hcomap
  have hspan : m.under A = Ideal.span {Submodule.IsPrincipal.generator (m.under A)} :=
    (Ideal.span_singleton_generator (m.under A)).symm
  have hπ0 : Submodule.IsPrincipal.generator (m.under A) ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hspan
    rw [hspan] at hcomap
    exact hA (Ring.isField_iff_maximal_bot.2 hcomap)
  exact isDomain_atPrime A C m _ hspan hπ0 hcomap

end Et

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E4 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`

For a presentation `IsLocAff` through `D = Spec B ⟶ A¹ ⟶ P` (`c` the chart, `t = φ (X - a)`):
* `locT φ a : B ⟶ B_t`, `W1 c φ a := Spec B_t` over `P`, `toD1 : W1 ⟶ chEt c φ`;
* `mem_Uo_iff`: a point `u` of `Spec B` lands in `Uo` iff `t ∉ u`;
* **`isoT`**: `W1 ≅ D ×_P Uo` in `P.Etale`, with `isoT_hom_prW`, `isoT_inv_toD1`;
* `locT_cls`: the class `ε_loc ∘ κ` is `εT ∘ κ₁` with `εT := ε_loc ∘ Λ[isoT.inv]`, `κ₁ := Λ[isoT.hom]^* κ`;
* `locT_res_D`, `locT_res_U`: classes restricted from `D` or from `Uz` die under `εT`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

section T

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)

variable {a}

variable {Uo : P.Opens} (hUo : ∀ u : Spec B, (chEt c φ).hom u ∈ Uo ↔ φ.hom (X - C a) ∉ u.asIdeal)

include hUo

theorem isoT_hom_prW : (isoT c φ hUo).hom ≫ prW (chEt c φ) (opEt Uo) = toD1 c φ a :=
  MorphismProperty.Over.Hom.ext (isoTl_fst c φ hUo)

theorem isoT_inv_toD1 : (isoT c φ hUo).inv ≫ toD1 c φ a = prW (chEt c φ) (opEt Uo) := by
  rw [← isoT_hom_prW c φ hUo, Iso.inv_hom_id_assoc]

section Cls

variable {Uz : P.Opens} (h : Uo ≤ Uz) (hS : (locC Λ (chEt c φ) h).ShortExact) {F : EtSh Λ P}

/-- **The class through `W₁`**: `ε_loc ∘ κ = εT ∘ κ₁`. -/
theorem locT_cls (κ : Ext.{u} (freeSh Λ (prd (chEt c φ) (opEt Uo))) F 1) :
    hS.extClass.comp κ (show 1 + 1 = 2 from rfl) =
      (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUo).inv)) (add_zero 1)).comp
        ((Ext.mk₀ (freeMap Λ (isoT c φ hUo).hom)).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) := by
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀_assoc, ← freeMap_comp, Iso.inv_hom_id, freeMap_id,
    Ext.mk₀_id_comp]

end Cls

end T

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km6 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`

`D = Spec B` etale over `𝔸¹ ⊆ P` (`chEt c φ`), `D_o := D ×_P Uo` affine, `R` etale over `P` with `R.left` affine and
constant geometric fibre size `n` over `D_o`; `W := D_o ×_P R` (the Shapiro scheme).
* generic instances: `W` affine, `W ⟶ D_o` quasi-compact and separated (from O2Km1);
* `shG : W.left ⟶ Spec k[X]`, **`etale_shG`**; `Γ(W, ⊤)` noetherian, `isDomain_loc_W` (localizations at maximal
  ideals are domains), `Γ(W, ⊤) ⧸ p` Dedekind (O2Km5 with `A = k[X]`);
* (the Kummer decomposition of `Ext¹(Λ[D_o], Λ[R]) ≃ H¹(W)` is `h1_exists_kappa (isDomain_loc_W ..)` / O2Km9; a
  separate `shap_exists_kappa` here cost 550 user-s under `lean -o` and was dropped).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur

universe u

section Inst

end Inst

section Assembly

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

variable [IsAffine (prd (chEt c φ) (opEt Uo)).left]

instance isDedekindDomain_W (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) :
    IsDedekindDomain (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) :=
  isDedekindDomain_gam (shG c φ R) (Polynomial.not_isField k) p

end Assembly

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTd =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks

For chart neighbourhoods `D = chEt c φ`, `D₁ = chEt c φ₁` and any `dm : D₁ ⟶ D` in `P.Etale`:
* `left_spec_map`: `dm.left ≫ Spec.map φ = Spec.map φ₁`; **`shG_wm`**: `wm (prdMap dm) ≫ shG c φ = shG c φ₁`;
* `sXW c φ R ζ0 ∈ Γ(W)` (the image of `ζ0 ∈ k`), `ζW_eq`, **`wm_appTop_sXW`**;
* **`locCls_kapS_chart`**: `locCls_kapS_shrink` (O2PPTc) with the roots of unity `ζW` of O2Km9a on both sides;
* **`piece_unique_away`**: if `Γ(X₁) = Γ(X)[1/s]` along `f`, at most one piece of `X₁` lies over a piece of `X`
  (applies to `toDF` by `isLocalization_away_toDF`, O2ZarCh).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Away

end Away

section Chart

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  {Uo : P.Opens} (R : P.Etale) [IsAffine R.left] (dm : chEt c φ₁ ⟶ chEt c φ)

set_option backward.isDefEq.respectTransparency false in
/-- **`shG` along a chart map.** -/
theorem shG_wm : (wm (R := R) (prdMap dm (opEt Uo))) ≫ shG c φ (Uo := Uo) R = shG c φ₁ (Uo := Uo) R := by
  rw [shG_eq, shG_eq, ← Category.assoc, wm_wD, Category.assoc, left_spec_map c φ φ₁ dm]

end Chart

section ChartPPT

end ChartPPT

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2b =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3

GLOB/REL PLAN v1, stage S3 (geometric part). `D_G := chEt c (k[X] ⟶ k[X]_G)` for `G = g₀ c₀' t` (`g₀ ∣ G`,
`t = X - a ∣ G`):
* `toDG : D_G ⟶ D_{g₀}`; `chG_mem`: `D_G` lies over `U₀` (no point over `z`), so `opnDg c G ≤ U₀`;
* `sigG : opEt (c(D(G))) ⟶ D_G ×_P U₀` and `mG := toOpEt ≫ sigG` (the map `m` of `uk_diff`), `mG_prT` (`hm`),
  `mG_prdMap` (`m ≫ (D_G ⟶ D_{g₀}) = (D₂ ⟶ D_{g₀})`, maps into `D ×_P X` are determined by `prT` for `D` open);
* `gamMap_shG`, `appTop_gamMap`, `isUnit_rho`: a divisor of `G^n` in `Γ(Y₀)` becomes a unit on `Y₁ = (D_G ×_P U₀) ×_P R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section Mono

end Mono

section ChG

end ChG

section Sec

end Sec

section Gam

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

set_option backward.isDefEq.respectTransparency false in
theorem gamMap_shG {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
    [IsAffine (prd (chEt c φ) (opEt Uo)).left] (r : k[X]) :
    gamMap (shG c φ (Uo := Uo) R) r = (bW (Spec.map φ ≫ c) (opEt Uo) R).hom (φ.hom r) := by
  show ((Scheme.ΓSpecIso _).inv ≫ (shG c φ (Uo := Uo) R).appTop).hom r =
    ((Scheme.ΓSpecIso B).inv ≫ (wD (chEt c φ) (opEt Uo) R).appTop).hom (φ.hom r)
  rw [shG_eq, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2f =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2f): the side conditions of stages S3-S4

* `mem_opnDg_prd` (`hD₂`): `D₂ ×_P U₀` lies over `c(D(g₀ c₀' t))` when `g₀, c₀'` are units on `D₂`;
* `not_isUnit_t`: `t = X - a` is not a unit on a chart with a point over `z = c(a)`;
* `etale_wD`, `injective_bW_piece`: for a domain `B`, `B ↪ Frac(Γ(W) ⧸ q)` on every piece (flatness), the `hinj` of
  `one_sub_mul_ne_zero` (O2Gl2c).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Pts

end Pts

section Inj

variable {P : Scheme.{0}}

/-- **`B ↪ Frac(Γ(W) ⧸ q)`** for a domain `B` (flatness of `W ⟶ Spec B`). -/
theorem injective_bW_piece {B : CommRingCat.{0}} [IsDomain B] (hB : Spec B ⟶ P) [Etale hB] (X R : P.Etale)
    [IsAffine ((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left]
    (q : minimalPrimes Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)) :
    Function.Injective fun b : B => toPiQ ((bW hB X R).hom b) q := by
  refine (injective_iff_map_eq_zero ((Pi.evalRingHom _ q).comp (toPiQ.comp (bW hB X R).hom))).2 fun b hb => ?_
  by_contra hb0
  let g : ((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left ⟶ Spec (CommRingCat.of B) := wD (Scheme.Etale.mk hB) X R
  have : Etale g := etale_wD (Scheme.Etale.mk hB) X R
  exact toPiQ_gamMap_ne_zero (A := B) g hb0 q hb

end Inj

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`

s128 fix of REL PLAN v2: a bad point `c(b)` has `g₀(b) = 0` (`c(D(g₀)) ⊆ U₀ ∪ {z}`), so no chart `D' ∋ b` maps to
`D_{g₀}`. The map `W(D') → Y₀` is `m^* ∘ ρ` instead (`m := mG : D' ×_P U₀ ⟶ D_G ×_P U₀`, `ρ := (prdMap (toDG c hG₀))^*`):
* **`wD_hom`**, **`shG_wm_any`**: `wm m ≫ shG φ₁ = shG φ₂` for ANY `m : D₂ ×_P U₀ ⟶ D₁ ×_P U₀` between chart products;
* **`mG_rho_gamMap`**, **`mG_H_any`**: `m^* (ρ r) = bW'(φ' r)`; the `H`-relation pulled back along `m`;
* **`exists_bad_e'`**: `exists_bad_e` (O2Bd2) without `d : D' ⟶ D_{g₀}`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) for a generic `G` (`hG₀ : g₀ ∣ G`), also returning `H ρ(t)^N = ρ(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section WDHom

end WDHom

section AnyM

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]

set_option backward.isDefEq.respectTransparency false in
/-- `shG` along ANY map of chart products over `P`. -/
theorem shG_wm_any (m : prd (chEt c φ₂) (opEt Uo) ⟶ prd (chEt c φ₁) (opEt Uo)) :
    wm (R := R) m ≫ shG c φ₁ (Uo := Uo) R = shG c φ₂ (Uo := Uo) R := by
  rw [shG_eq, shG_eq, ← cancel_mono c, Category.assoc, Category.assoc, Category.assoc]
  change wm (R := R) m ≫ wD (chEt c φ₁) (opEt Uo) R ≫ (chEt c φ₁).hom =
    wD (chEt c φ₂) (opEt Uo) R ≫ (chEt c φ₂).hom
  rw [wD_hom, wD_hom, ← Category.assoc, wm_snd, Category.assoc, MorphismProperty.Over.w m]

end AnyM

section BadChart'

end BadChart'

section S4H'

end S4H'

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals

REL PLAN v2 (s126) + s128 fix. At a bad point `c(b)` (`G = (X - C b)^m G_b`, `G_b(b) ≠ 0`, `c(b) ∉ U₀`), the chart
`D' := D_{G_b} = chEt c (locF G_b)` satisfies the hypotheses of `bad_term_zero'` (O2Bd5):
* fibres: **`subsingleton_fib_of_mono`**, **`nonempty_fib_of_mem`** (generic);
* **`bad_pt`**, **`badCh_r₁`** (`hDr₁`), **`badCh_r`** (`hDr`), **`badCh_D'`** (`hD'`), **`badCh_hUo`**, **`isAffine_badCh`**,
  **`badCh_hta`** (`hta`), **`badCh_n`** (`hDn`);
* CRT ideals `J b := (X - C b) S`: **`span_coprime_pow`** (`hJt`), **`pairwise_span_coprime`** (`hJ`) of `exists_S23_chart`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Fib

end Fib

section BadCh

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {G Gb : k[X]} {b : k} {m : ℕ}
  (hGf : G = (X - C b) ^ m * Gb)

variable {Uo : P.Opens} (hle : opnDg c G ≤ Uo) (hb : c (A1pt k b) ∉ Uo)

include hGf hle hb in
theorem isAffine_badCh : IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).left :=
  isAffine_prdUo c _ (badCh_hUo c hGf hle hb)

end BadCh

section BadCh2

end BadCh2

section JAlg

end JAlg

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2LocU =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class

GLOB/REL PLAN v1 (4). For `U₁ ≤ U₀ ≤ Uz` and `D : P.Etale`:
* `locC_opn`: `ε(D, U₁ ≤ Uz) ∘ Λ[prdMapR D (opEtMap h₁₀)] = ε(D, U₀ ≤ Uz)`;
* `locCls_opn`: `ε(D, U₀) ∘ κ = ε(D, U₁) ∘ Λ[prdMapR] ∘ κ`;
* **`locCls_opn_map`**: `ε(D, U₀) ∘ Λ[m] ∘ κ = ε(D, U₁) ∘ Λ[m'] ∘ κ` when `prdMapR ≫ m = m'`;
* **`locCls_opn_toOpEt`**: for `σ : opEt U₁ ⟶ T` and `D ×_P U₀` over `U₁`:
  `ε(D, U₀) ∘ Λ[toOpEt ≫ σ] ∘ κ = ε(D, U₁) ∘ Λ[prT ≫ σ] ∘ κ`.
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

section LocU

variable {U₁ U₀ Uz : P.Opens} (h₁₀ : U₁ ≤ U₀) (h : U₀ ≤ Uz) (h₁ : U₁ ≤ Uz) (D : P.Etale)

/-- `ε(D, U₁) ∘ Λ[prdMapR D (opEtMap h₁₀)] = ε(D, U₀)`. -/
theorem locC_opn (hS₁ : (locC Λ D h₁).ShortExact) (hS : (locC Λ D h).ShortExact) :
    hS₁.extClass.comp (Ext.mk₀ (freeMap Λ (prdMapR D (opEtMap h₁₀)))) (add_zero 1) = hS.extClass := by
  have hnat := mv_naturality (prdMapR D (opEtMap h₁₀)) (𝟙 D) (𝟙 (opEt Uz)) (𝟙 (etId P))
    ((prdMapR_prW D _).trans (Category.comp_id _).symm) (opEt_ext _ _) (toTop_ext _ _) (toTop_ext _ _) hS₁ hS
  rw [freeMap_id, Ext.mk₀_id_comp] at hnat
  exact hnat

end LocU

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP2 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)

GLOB/REL PLAN v1 stage S4 data: for `G = g₀ c₀' t` (an opaque variable with `hGdef`), the `D_G` and
`D₂ := D₁_{c₀'}` instances (`isAffine_prdG`, `isAffine_prdUo`, Km6 instances), the `D₂` fibre data (ZarCh) and `hD₂`,
`hR₂₁`, then `pp_core` (O2PP1).
* helpers: `dvd_of_Gdef`, `tdvd_of_Gdef`, `ne_zero_of_Gdef`, `hpt_of_ne_zero`, `isUnit_locF_self`, `hzU_of`,
  `hUo_of_range`, `mem_opnDg_or`, `mem_opnDg_prd'`, `nontrivial_of_fpt`;
* **`pp_G`** (DEF): the target class at `D₁` lies in `Gr`, from the S2-S3 output and `c₀'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Helpers

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {a : k} {Uo Uz : P.Opens}

/-- `hD₂` with `G` generic. -/
theorem mem_opnDg_prd' (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a)) {B : CommRingCat.{0}}
    (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {g₀ c₀' G : k[X]} (hg : IsUnit (φ.hom g₀))
    (hc : IsUnit (φ.hom c₀')) (hGdef : G = g₀ * c₀' * (X - C a)) (v : (prd (chEt c φ) (opEt Uo)).left) :
    (prd (chEt c φ) (opEt Uo)).hom v ∈ opnDg c G := by
  subst hGdef
  exact mem_opnDg_prd c h hz φ hg hc v

end Helpers

section PPG

end PPG

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2a =====
section

/-!
# S4-EtPBC-A, L3b (TB2a): section calculus for base change

* `etPull_hom_ext`: maps into `X ×_Y T` agree if their first components agree;
* `etIdPull g : etId X ≅ X ×_Y Y`, `pullUnit g : Λ_X ≅ g^*Λ_Y`, `pullUnit_one`;
* `unit_hom_ext`: maps out of `Λ_X` are determined by the image of `1`;
* transport of pulled-back sections along `pullIsoRes`, `pullCompIso`, `pullCongr`, `(pull g).map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

variable {Λ : Type u} [CommRing Λ]

theorem pullCompInv_pbSecO {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) {F : EtSh Λ C} {V : C.Etale}
    {Z : A.Etale} (a : op ((etPull g).obj ((etPull h).obj V)) ⟶ op Z) (x : F.obj.obj (op V)) :
    ((pullCompInv Λ g h F).hom.app (op Z)).hom
        ((((pull g Λ).obj ((pull h Λ).obj F)).obj.map a).hom (pbSec g (pbSec h x))) =
      ((((pull (g ≫ h) Λ).obj F).obj.map (((etPullCompIso g h).inv.app V).op ≫ a)).hom (pbSec (g ≫ h) x)) := by
  have e2 := (pullCompHom_pbSecO (Λ := Λ) (F := F) g h (((etPullCompIso g h).inv.app V).op ≫ a) x).trans
    (map_congr_apply _ (by rw [← Category.assoc, ← op_comp, Iso.inv_hom_id_app, op_id, Category.id_comp]) _)
  exact (congrArg (fun z => ((pullCompInv Λ g h F).hom.app (op Z)).hom z) e2).symm.trans
    (sh_hom_inv_apply ((pullCompIso Λ g h).app F) _ _)

end TB2o

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7a =====
section

/-!
# S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `Delta.bcImg`: the germ image `{β | ∃ j α, bc j α = β}` is an additive subgroup (cofiltered `J`);
* `etPullId`: `etPull (𝟙 X) ≅ 𝟭`; `pushId`: `push (𝟙 X) ≅ 𝟭`; `pushEquiv e` for an isomorphism `e`;
* **`pull_isEquivalence`**: `e^*` is an equivalence for an isomorphism `e`;
* **`pull_ext_bijective`**: `e^*` is bijective on `Ext^n`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

section L7a

variable {Λ : Type u} [CommRing Λ]

/-- **`e^*` is an equivalence** for an isomorphism `e`. -/
instance pull_isEquivalence {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] : (pull e Λ).IsEquivalence :=
  (pullAdj e Λ).isEquivalence_left_of_isEquivalence_right

/-- **`e^*` is bijective on `Ext^n`** for an isomorphism `e`. -/
theorem pull_ext_bijective {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (A B : EtSh Λ Y) (n : ℕ) :
    Function.Bijective (fun x : Ext.{u} A B n => x.mapExactFunctor (pull e Λ)) :=
  (pull e Λ).mapExt_bijective_of_preservesInjectiveObjects A B n

end L7a

end RamanujanPetersson.EtPBC.EtMV

end

end


