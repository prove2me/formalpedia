-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_04
-- name    : RPLib_FX_LisseDual_04
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T04:31:39.52269+00:00
-- url     : https://prove2.me/theorems/99a91d64-0f77-4721-803f-36147f806cfd
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, library file 04 of 7
-- statement:
--   File 04 of 7 of the lisse duality library for affine curves over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
--   * `S4.Def_RP_CupDuality_VCnt1`: S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)
--   * `S4.Def_RP_LisseDuality_Dev`: S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules
--   * `S4.Def_RP_LisseDuality_Base`: S4-CurveDuality O7c': the dévissage base reduces to the regular coinduced module `coindF Λ`
--   * `S4.Def_RP_LisseDuality_Push`: S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward
--   * `S4.Def_RP_LisseDuality_Proj`: S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing
--   * `S4.Def_RP_LisseDuality_ProjV`: S4-CurveDuality O7d-P3a(iii): the duality pairing of the cover `V`, through Shapiro
--   * `S4.Def_RP_LisseDuality_AmbCup`: S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group
--   * `S4.Def_RP_CupDuality_VFrobB`: S4-CurveDuality, O9b (Route G at `V`) part 6: boundary data of `V` for any `ψ ∈ K`, generic form
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_FX_LisseDual_03

/-!
# Poincaré duality with lisse coefficients on an affine curve over a finite field, library file 04 of 7

Declarations of the formalization of Poincaré duality for H¹ with lisse (finite, twisted) coefficients on an
affine curve over a finite field (the cochain duality map `alphaM` is bijective), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
* `S4.Def_RP_CupDuality_VCnt1`: S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)
* `S4.Def_RP_LisseDuality_Dev`: S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules
* `S4.Def_RP_LisseDuality_Base`: S4-CurveDuality O7c': the dévissage base reduces to the regular coinduced module `coindF Λ`
* `S4.Def_RP_LisseDuality_Push`: S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward
* `S4.Def_RP_LisseDuality_Proj`: S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing
* `S4.Def_RP_LisseDuality_ProjV`: S4-CurveDuality O7d-P3a(iii): the duality pairing of the cover `V`, through Shapiro
* `S4.Def_RP_LisseDuality_AmbCup`: S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group
* `S4.Def_RP_CupDuality_VFrobB`: S4-CurveDuality, O9b (Route G at `V`) part 6: boundary data of `V` for any `ψ ∈ K`, generic form
-/

set_option autoImplicit false

-- ===== S4.Def_RP_LisseDuality_VDat =====
section

/-!
# S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`

For residue data `D : ResDat π Γ I N T` (S4-PD) and `K = ker π`, the cover `V` (ambient group `K`, geometric group
`geoU Γ K = Γ ∩ K`) gets:
* `rdJ D K t = {h ∈ K | x_t⁻¹ h x_t ∈ I (sh t)}` (inertia of `V` at `t`), `rdX D t = x_t ∈ Γ`,
  `rdY D K hK t = y_t = x_t σ_s x_t⁻¹` (normalised generator);
* `inertiaLift_rd`, `dCover_rd`, `dDisj_rd`: the double-coset data of `ShapiroCone` (from `hrep`);
* **`rdConstData`**: `ConstData (σ|K) (Γ ∩ K) (rdJ D K) (rdY D K hK)` (`inj`/`surj` from `LocGen`,
  `resSum` from `hR`, `resOnto` from `hE`);
* `h2Van_geoU`, `isOpen_ker_comp`, **`rdCupHyp`**: `V`'s `CupHyp` from `H²(Γ ∩ K, σ) = 0` at the `G` level.
No connectedness is used here (`hrep` is stated through `Γ.map π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Gen

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) {Γ : Subgroup G}

end Gen

section RD

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Gf : Type} [Group Gf] {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} {N : ℕ} {T : Type} [Fintype T] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (D : ResDat π Γ I N T) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)

/-! ### Conjugation `J_s ≃ geoU Γ K ⊓ rdJ t` -/

/-! ### `Γ_H ≃ geoU Γ K` -/

theorem rdToV_y (t : T) : rdToV D K hK (D.y t) = tG (rdY D K hK) t :=
  Subtype.ext (Subtype.ext (D.hy t))

theorem rdFromV_tG (t : T) : rdFromV D K hK (tG (rdY D K hK) t) = D.y t :=
  Subtype.ext (D.hy t).symm

/-! ### The constant data of `V` -/

variable (σ : Representation Λ G Λ) (htriv : ∀ (g : Γ) (x : Λ), σ g x = x)

/-- `V`'s `CupHyp` from `H²(Γ ∩ K, σ) = 0`. -/
theorem rdCupHyp (hσ : IsOpen (σ.ker : Set G)) (hv : H2Van σ (Γ ⊓ K) ⊤) :
    CupHyp (Representation.trivial Λ K Λ) (σ.comp K.subtype) (σ.comp K.subtype) (LinearMap.mul Λ Λ)
      (geoU Γ K) :=
  constCupHyp (σ.comp K.subtype) (geoU Γ K) (isOpen_ker_comp K σ hσ) (h2Van_geoU K σ hv)

variable [NeZero N] (hN : (N : Λ) = 0)

include htriv hN in
theorem rd_resSum (d : Z1 (σ.comp K.subtype) (geoU Γ K)) :
    ∑ t, (d : geoU Γ K → Λ) (tG (rdY D K hK) t) = 0 := by
  have hlc := ((mem_Z1 _ _ _).1 d.2).1
  have h := sum_eq_zero_of_zmod D.y D.hR (rd_hM hN) (fun g => (d : geoU Γ K → Λ) (rdToV D K hK g))
    (hlc.comp_continuous (rdToV_cont D K hK))
    (fun a b => by
      simp only [rdToV_mul]
      exact z1_add_of_triv _ _ (rd_triv K σ htriv) d _ _)
  simpa only [rdToV_y] using h

include htriv hN in
theorem rd_resOnto (r : T → Λ) (hr : ∑ t, r t = 0) :
    ∃ d : Z1 (σ.comp K.subtype) (geoU Γ K), ∀ t, (d : geoU Γ K → Λ) (tG (rdY D K hK) t) = r t := by
  classical
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t0⟩⟩
  · exact ⟨0, fun t => isEmptyElim t⟩
  have hex : ∀ u : T, ∃ χ : D.ΓH → ZMod N, IsLocallyConstant χ ∧ (∀ a b, χ (a * b) = χ a + χ b) ∧
      ∀ t, χ (D.y t) = (if t = u then 1 else 0) - (if t = t0 then 1 else 0) := fun u =>
    D.hE _ (by simp [Finset.sum_sub_distrib])
  choose χ hχc hχ hχy using hex
  let dz : T → Z1 (σ.comp K.subtype) (geoU Γ K) := fun u =>
    ⟨fun h => zlift Λ N hN (χ u (rdFromV D K hK h)), (mem_Z1 _ _ _).2
      ⟨((hχc u).comp_continuous (rdFromV_cont D K hK)).comp (zlift Λ N hN), fun g h => by
        show zlift Λ N hN (χ u (rdFromV D K hK (g * h))) =
          zlift Λ N hN (χ u (rdFromV D K hK g)) + (σ.comp K.subtype) (g : K) (zlift Λ N hN (χ u (rdFromV D K hK h)))
        rw [rd_triv K σ htriv g, rdFromV_mul, hχ u, map_add]⟩⟩
  refine ⟨∑ u, r u • dz u, fun t => ?_⟩
  have hval : ∀ u, ((dz u : Z1 (σ.comp K.subtype) (geoU Γ K)) : geoU Γ K → Λ) (tG (rdY D K hK) t) =
      (if t = u then 1 else 0) - (if t = t0 then 1 else 0) := fun u => by
    show zlift Λ N hN (χ u (rdFromV D K hK (tG (rdY D K hK) t))) = _
    rw [rdFromV_tG, hχy u t, map_sub, zlift_ite, zlift_ite]
  have e1 : ∀ u, r u * ((if t = u then (1 : Λ) else 0) - (if t = t0 then 1 else 0)) =
      (if t = u then r u else 0) - r u * (if t = t0 then 1 else 0) := fun u => by
    rw [mul_sub, mul_ite, mul_one, mul_zero]
  calc ((∑ u, r u • dz u : Z1 (σ.comp K.subtype) (geoU Γ K)) : geoU Γ K → Λ) (tG (rdY D K hK) t)
      = ∑ u, r u * ((dz u : Z1 (σ.comp K.subtype) (geoU Γ K)) : geoU Γ K → Λ) (tG (rdY D K hK) t) := by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
    _ = r t := by
        simp only [hval, e1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte, ← Finset.sum_mul, hr, zero_mul, sub_zero]

include htriv hN in
/-- **P4**: the constant data of the cover `V` (ambient `K`, geometric group `Γ ∩ K`, inertia `rdJ`,
generators `y_t`) from `ResDat`. -/
theorem rdConstData : ConstData (σ.comp K.subtype) (geoU Γ K) (rdJ D K) (rdY D K hK) where
  triv := rd_triv K σ htriv
  inj := rd_inj D K hK σ htriv hN
  surj := rd_surj D K hK σ htriv hN
  resSum := rd_resSum D K hK σ htriv hN
  resOnto := rd_resOnto D K hK σ htriv hN

end RD

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VCnt1 =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)

* `resDatOfInj`: residue data change target along an injective hom `j` with `j ∘ π' = π`.
* `vResDat`: `V`'s residue data (`trResDat`) with the surjective `π_V = (piV π₂ K).rangeRestrict`.
* `exists_factor_rep`: a representation trivial on `ker f` (`f` onto) factors through `f`.
* **`vCount`**: for every finite representation `ρ` of `K` with open kernel containing `K ∩ ker π₂`,
  `H²(K)(ρ, Γ_V, I_V) ≃ H²_c(ρ, Γ_V)` (S4-PD item (4) at `V`), given `H2All` at `V`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

noncomputable section

section OfInj

variable {Gf Gf' : Type} [Group Gf] [Group Gf'] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ}
  {T : Type} [Fintype T] (D : ResDat π Γ I N T) (π' : G →* Gf') (j : Gf' →* Gf)
  (hj : Function.Injective j) (hjπ : ∀ g, j (π' g) = π g)

end OfInj

section Factor

end Factor

section Cnt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal]
  {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2]
  [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (RD : ResDat π Γ I N T) (D2 : ResDat π2 Γ I N T2) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)
  (hK2 : ∀ g, π2 g = 1 → g ∈ K)

include D2 hK hK2 in
/-- **The `H²` count at `V`**: `H²(K)(ρ, Γ_V, I_V) ≃ H²_c(ρ, Γ_V)` for `ρ` trivial on `K ∩ ker π₂`. -/
theorem vCount [NeZero N] [DecidableEq T] [Finite Gf2] (hπ2 : IsOpen (π2.ker : Set G))
    {Λ : Type} [CommRing Λ] [Finite Λ] (hN : (N : Λ) = 0) {l n : ℕ} (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (hallV : H2All Λ K (geoU Γ K) l n) (hallIV : ∀ t, H2All Λ K (geoU Γ K ⊓ rdJ RD K t) l n)
    {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (ρ : Representation Λ K M)
    (hρ : IsOpen (ρ.ker : Set K)) (hρ2 : ∀ g : K, π2 (g : G) = 1 → ρ g = 1) :
    Nonempty (H2K ρ (geoU Γ K) (rdJ RD K) hρ ≃ₗ[Λ] H2c ρ (geoU Γ K)) := by
  classical
  letI : Fintype (piV π2 K).range := Fintype.ofFinite _
  letI : Fintype ((geoU Γ K).map (piR π2 K)) := Fintype.ofFinite _
  letI : ∀ t, Fintype ((geoU Γ K ⊓ rdJ RD K t).map (piR π2 K)) := fun _ => Fintype.ofFinite _
  have hle : (piR π2 K).ker ≤ ρ.ker := fun g hg =>
    MonoidHom.mem_ker.2 (hρ2 g ((piR_eq_one_iff K g).1 (MonoidHom.mem_ker.1 hg)))
  obtain ⟨τ, rfl⟩ := exists_factor_rep (piR π2 K) (MonoidHom.rangeRestrict_surjective _) ρ hle
  exact ⟨((vResDat RD D2 K hK hK2).toResHyp hN (piR_ker_open K hπ2)).h2Equiv (piR_ker_open K hπ2) τ hΛ
    hallV hallIV⟩

end Cnt

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_LisseDuality_Dev =====
section

/-!
# S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules

Fix `σ : Representation Λ G Λ` (the twist `Λ(1)`), `H²(Γ, Λ(1)) = 0` and a trace `e : H²(K(Λ(1))) → Λ`. For a
representation `ρ` with open kernel the **duality map** is `alphaM : H¹_c(M) → Hom(H¹(M^∨(1)), Λ)`,
`x ↦ (y ↦ e (x ∪ y))` (`alpha_natural`: natural in `M`).

For representations `τ ∘ π` of a quotient `π : G →* Gf` with open kernel (lisse sheaves trivialised by `π`):
* `coindF M₀`: `Gf → M₀` with left translation (the push-forward of the constant sheaf `M₀` from the cover);
  `emb τ : M ↪ (Gf → M)`, `m ↦ (x ↦ τ(x⁻¹) m)`, equivariant; `quotRepF τ` the quotient representation;
* `alpha_injective_of_base`: `alphaM` injective on all coinduced modules ⇒ injective for every finite `τ`;
* `alpha_bijective_of_base`: `alphaM` bijective on all coinduced modules ⇒ bijective for every finite `τ`
  (`Λ` finite, self-injective and killed by `lⁿ`, `S` nonempty, cohomological dimension 1 via `H2All`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {σ : Representation Λ G Λ} {hσ : IsOpen (σ.ker : Set G)}
  {M : Type} [AddCommGroup M] [Module Λ M] {X : Type} [AddCommGroup X] [Module Λ X]

/-! ## Coinduced modules and the canonical embedding -/

variable {Gf : Type} [Group Gf]

/-! ## Dévissage -/

variable (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ) (π : G →* Gf) (hπ : IsOpen (π.ker : Set G))

/-- **Injectivity by dévissage**: injective on coinduced modules ⇒ injective for every `τ ∘ π`. -/
theorem alpha_injective_of_base [Nonempty S]
    (hbase : ∀ (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] [Finite M₀],
      Function.Injective (alphaM hv e ((coindF (Λ := Λ) M₀).comp π) (isOpen_comp π hπ (coindF (Λ := Λ) M₀))))
    [Finite M] (τ : Representation Λ Gf M) :
    Function.Injective (alphaM hv e (τ.comp π) (isOpen_comp π hπ τ)) := by
  have hf : IsEquivariant (τ.comp π) ((coindF (Λ := Λ) M).comp π) (emb τ) := fun g m => emb_equiv τ (π g) m
  exact injective_of_chase (mapH1c Γ I hf) (mapH1 Γ (transp_equivariant (σ := σ) hf)).dualMap
    (alphaM hv e (τ.comp π) (isOpen_comp π hπ τ)) (alphaM hv e ((coindF (Λ := Λ) M).comp π) (isOpen_comp π hπ (coindF (Λ := Λ) M)))
    (mapH1c_injective hf (emb_injective τ))
    (alpha_natural hv e (isOpen_comp π hπ τ) (isOpen_comp π hπ (coindF (Λ := Λ) M)) hf) (hbase M)

/-- **Lisse duality by dévissage**: bijective on coinduced modules ⇒ bijective for every finite `τ ∘ π`. -/
theorem alpha_bijective_of_base [Nonempty S] [Finite Λ] [Module.Injective Λ Λ] {l n : ℕ}
    (hall : H2All Λ G Γ l n) (hΛ : ∀ a : Λ, (l ^ n) • a = 0) [Finite Gf]
    (hbase : ∀ (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] [Finite M₀],
      Function.Bijective (alphaM hv e ((coindF (Λ := Λ) M₀).comp π) (isOpen_comp π hπ (coindF (Λ := Λ) M₀))))
    [Finite M] (τ : Representation Λ Gf M) :
    Function.Bijective (alphaM hv e (τ.comp π) (isOpen_comp π hπ τ)) := by
  have hf : IsEquivariant (τ.comp π) ((coindF (Λ := Λ) M).comp π) (emb τ) := fun g m => emb_equiv τ (π g) m
  set W := LinearMap.range (emb τ)
  have hq : IsEquivariant ((coindF (Λ := Λ) M).comp π) ((quotRepF τ).comp π) W.mkQ := fun g F => rfl
  have hqf : ∀ m, W.mkQ (emb τ m) = 0 := fun m => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ m
  have hex : Function.Exact (emb τ) W.mkQ := fun F => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  have : Finite ((Gf → M) ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  have hX := isOpen_comp π hπ (coindF (Λ := Λ) (Gf := Gf) M)
  have : Finite ((Gf → M) →ₗ[Λ] Λ) := finite_dual
  have htor : ∀ φ : (Gf → M) →ₗ[Λ] Λ, (l ^ n) • φ = 0 := fun φ => LinearMap.ext fun x => hΛ (φ x)
  have hsurj : Function.Surjective (mapH1 Γ (transp_equivariant (σ := σ) hf)) :=
    mapH1_surjective hall htor (isOpen_linHom_ker hX hσ) (transp_equivariant hf)
      (transp_surjective (emb_injective τ))
  have hbaseI : ∀ (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] [Finite M₀],
      Function.Injective (alphaM hv e ((coindF (Λ := Λ) M₀).comp π) (isOpen_comp π hπ (coindF (Λ := Λ) M₀))) :=
    fun M₀ _ _ _ => (hbase M₀).1
  exact bijective_of_chase (mapH1c Γ I hf) (mapH1c Γ I hq) (mapH1 Γ (transp_equivariant (σ := σ) hf)).dualMap
    (mapH1 Γ (transp_equivariant (σ := σ) hq)).dualMap (alphaM hv e (τ.comp π) (isOpen_comp π hπ τ))
    (alphaM hv e ((coindF (Λ := Λ) M).comp π) hX)
    (alphaM hv e ((quotRepF τ).comp π) (isOpen_comp π hπ (quotRepF τ)))
    (mapH1c_injective hf (emb_injective τ))
    (exact_mapH1c hX hf (emb_injective τ) hq (Submodule.mkQ_surjective W) hex)
    (LinearMap.dualMap_injective_of_surjective hsurj)
    (fun φ => LinearMap.ext fun y => by
      rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, mapH1_transp_comp hf hq hqf, map_zero,
        LinearMap.zero_apply])
    (alpha_natural hv e (isOpen_comp π hπ τ) hX hf)
    (alpha_natural hv e hX (isOpen_comp π hπ (quotRepF τ)) hq)
    (hbase M) (alpha_injective_of_base hv e π hπ hbaseI (quotRepF τ))

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Base =====
section

/-!
# S4-CurveDuality O7c': the dévissage base reduces to the regular coinduced module `coindF Λ`

* `sum_mapH1c_retract`, `sum_mapH1_retract`: `H¹_c` and `H¹` respect finite retract decompositions
  `Σᵢ injᵢ ∘ projᵢ = id`;
* `alpha_bijective_of_retract`: the duality map `alphaM` is bijective on `X` once it is bijective on a module `Y`
  of which `X` is a finite retract sum (covers equivariant isomorphisms, `ι = Unit`);
* `alpha_injective_of_emb`, `alpha_bijective_of_ses`: the two dévissage steps for an arbitrary short exact sequence;
* `SepDual Λ`: the `Λ`-dual separates points of finite modules (true for finite local self-injective `Λ`);
* `alpha_free_bijective`: bijective on `coindF Λ` ⇒ bijective on every `coindF (ι → Λ)`;
* `base_injective`, `base_bijective`: ⇒ bijective on every `coindF M₀`, `M₀` finite (via `M₀ ↪ (Dual M₀ → Λ)`);
* `alpha_bijective_of_regular`: lisse duality for every finite `τ ∘ π` from the single base case `coindF Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {σ : Representation Λ G Λ} {hσ : IsOpen (σ.ker : Set G)}
  {M : Type} [AddCommGroup M] [Module Λ M] {X : Type} [AddCommGroup X] [Module Λ X]
  {Y : Type} [AddCommGroup Y] [Module Λ Y] {Q : Type} [AddCommGroup Q] [Module Λ Q]
  {ρ : Representation Λ G M} {ρX : Representation Λ G X} {ρY : Representation Λ G Y}
  {ρQ : Representation Λ G Q}

/-! ## Retracts -/

section Retract

variable {ι : Type} [Fintype ι]

variable (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ)

/-- **Retract transfer**: `alphaM` bijective on `Y` ⇒ bijective on `X` when `Σᵢ injᵢ ∘ projᵢ = id_X`. -/
theorem alpha_bijective_of_retract (hX : IsOpen (ρX.ker : Set G)) (hY : IsOpen (ρY.ker : Set G))
    {inj : ι → (Y →ₗ[Λ] X)} {proj : ι → (X →ₗ[Λ] Y)}
    (hinj : ∀ i, IsEquivariant ρY ρX (inj i)) (hproj : ∀ i, IsEquivariant ρX ρY (proj i))
    (hsum : ∀ x, ∑ i, inj i (proj i x) = x) (hYb : Function.Bijective (alphaM hv e ρY hY)) :
    Function.Bijective (alphaM hv e ρX hX) := by
  have hsum' : ∀ ψ : X →ₗ[Λ] Λ, ∑ i, transp (proj i) (transp (inj i) ψ) = ψ := fun ψ => by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply]
    show ∑ i, ψ (inj i (proj i x)) = ψ x
    rw [← map_sum, hsum]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun φ => ?_⟩
  · have h0 : ∀ i, mapH1c Γ I (hproj i) z = 0 := fun i => hYb.1 (by
      rw [alpha_natural hv e hX hY (hproj i) z, hz]
      simp only [map_zero])
    rw [← sum_mapH1c_retract hinj hproj hsum z]
    simp only [h0, map_zero, Finset.sum_const_zero]
  · choose x hx using fun i => hYb.2 (φ ∘ₗ mapH1 Γ (transp_equivariant (σ := σ) (hproj i)))
    refine ⟨∑ i, mapH1c Γ I (hinj i) (x i), LinearMap.ext fun y => ?_⟩
    have h1 : ∀ i, alphaM hv e ρX hX (mapH1c Γ I (hinj i) (x i)) y =
        φ (mapH1 Γ (transp_equivariant (σ := σ) (hproj i))
          (mapH1 Γ (transp_equivariant (σ := σ) (hinj i)) y)) := fun i => by
      rw [alpha_natural hv e hY hX (hinj i), LinearMap.dualMap_apply, hx i, LinearMap.comp_apply]
    rw [map_sum, LinearMap.sum_apply]
    simp only [h1]
    rw [← map_sum, sum_mapH1_retract (fun i => transp_equivariant (σ := σ) (hproj i))
      (fun i => transp_equivariant (σ := σ) (hinj i)) hsum' y]

end Retract

/-! ## The two dévissage steps for a short exact sequence -/

variable (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ)

theorem alpha_injective_of_emb [Nonempty S] (hρ : IsOpen (ρ.ker : Set G)) (hX : IsOpen (ρX.ker : Set G))
    {f : M →ₗ[Λ] X} (hf : IsEquivariant ρ ρX f) (hinj : Function.Injective f)
    (hXi : Function.Injective (alphaM hv e ρX hX)) : Function.Injective (alphaM hv e ρ hρ) :=
  injective_of_chase (mapH1c Γ I hf) (mapH1 Γ (transp_equivariant (σ := σ) hf)).dualMap
    (alphaM hv e ρ hρ) (alphaM hv e ρX hX) (mapH1c_injective hf hinj) (alpha_natural hv e hρ hX hf) hXi

theorem alpha_bijective_of_ses [Nonempty S] [Finite Λ] [Module.Injective Λ Λ] {l n : ℕ}
    (hall : H2All Λ G Γ l n) (hΛ : ∀ a : Λ, (l ^ n) • a = 0) [Finite X] (hρ : IsOpen (ρ.ker : Set G))
    (hX : IsOpen (ρX.ker : Set G)) (hQ : IsOpen (ρQ.ker : Set G)) {f : M →ₗ[Λ] X}
    (hf : IsEquivariant ρ ρX f) (hinj : Function.Injective f) {q : X →ₗ[Λ] Q} (hq : IsEquivariant ρX ρQ q)
    (hsurj : Function.Surjective q) (hex : Function.Exact f q)
    (hXb : Function.Bijective (alphaM hv e ρX hX)) (hQi : Function.Injective (alphaM hv e ρQ hQ)) :
    Function.Bijective (alphaM hv e ρ hρ) := by
  have : Finite (X →ₗ[Λ] Λ) := finite_dual
  have htor : ∀ φ : X →ₗ[Λ] Λ, (l ^ n) • φ = 0 := fun φ => LinearMap.ext fun x => hΛ (φ x)
  have hqf : ∀ m, q (f m) = 0 := fun m => (hex (f m)).2 ⟨m, rfl⟩
  have hsurjH : Function.Surjective (mapH1 Γ (transp_equivariant (σ := σ) hf)) :=
    mapH1_surjective hall htor (isOpen_linHom_ker hX hσ) (transp_equivariant hf) (transp_surjective hinj)
  exact bijective_of_chase (mapH1c Γ I hf) (mapH1c Γ I hq) (mapH1 Γ (transp_equivariant (σ := σ) hf)).dualMap
    (mapH1 Γ (transp_equivariant (σ := σ) hq)).dualMap (alphaM hv e ρ hρ) (alphaM hv e ρX hX)
    (alphaM hv e ρQ hQ) (mapH1c_injective hf hinj) (exact_mapH1c hX hf hinj hq hsurj hex)
    (LinearMap.dualMap_injective_of_surjective hsurjH)
    (fun φ => LinearMap.ext fun y => by
      rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, mapH1_transp_comp hf hq hqf, map_zero,
        LinearMap.zero_apply])
    (alpha_natural hv e hρ hX hf) (alpha_natural hv e hX hQ hq) hXb hQi

/-! ## Coinduced maps and the reduction to `coindF Λ` -/

variable {Gf : Type} [Group Gf] (π : G →* Gf) (hπ : IsOpen (π.ker : Set G))

section CoindMap

variable {M₀ N₀ : Type} [AddCommGroup M₀] [Module Λ M₀] [AddCommGroup N₀] [Module Λ N₀]

end CoindMap

/-- **Bijective on `coindF Λ` ⇒ bijective on `coindF (ι → Λ)`** (retract sum over `ι`). -/
theorem alpha_free_bijective
    (hone : Function.Bijective (alphaM hv e ((coindF (Λ := Λ) Λ).comp π) (isOpen_comp π hπ _)))
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    Function.Bijective (alphaM hv e ((coindF (Λ := Λ) (ι → Λ)).comp π) (isOpen_comp π hπ _)) :=
  alpha_bijective_of_retract hv e _ _
    (inj := fun i => coindMap (LinearMap.single Λ (fun _ : ι => Λ) i))
    (proj := fun i => coindMap (LinearMap.proj i : (ι → Λ) →ₗ[Λ] Λ))
    (fun i => coindMap_equiv π _) (fun i => coindMap_equiv π _)
    (fun F => funext fun x => by
      rw [Finset.sum_apply]
      show ∑ i, Pi.single i (F x i) = F x
      exact Finset.univ_sum_single (F x)) hone

theorem base_injective [Nonempty S] [Finite Λ] (hsep : SepDual Λ)
    (hfree : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Function.Injective (alphaM hv e ((coindF (Λ := Λ) (ι → Λ)).comp π) (isOpen_comp π hπ _)))
    (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] [Finite M₀] :
    Function.Injective (alphaM hv e ((coindF (Λ := Λ) M₀).comp π) (isOpen_comp π hπ _)) := by
  classical
  have : Finite (Module.Dual Λ M₀) := finite_dual
  let _ : Fintype (Module.Dual Λ M₀) := Fintype.ofFinite _
  exact alpha_injective_of_emb hv e (isOpen_comp π hπ _) (isOpen_comp π hπ _)
    (coindMap_equiv π (dualEmb M₀)) (coindMap_injective (dualEmb_injective hsep M₀)) (hfree _)

theorem base_bijective [Nonempty S] [Finite Λ] [Module.Injective Λ Λ] {l n : ℕ}
    (hall : H2All Λ G Γ l n) (hΛ : ∀ a : Λ, (l ^ n) • a = 0) [Finite Gf] (hsep : SepDual Λ)
    (hfree : ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Function.Bijective (alphaM hv e ((coindF (Λ := Λ) (ι → Λ)).comp π) (isOpen_comp π hπ _)))
    (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] [Finite M₀] :
    Function.Bijective (alphaM hv e ((coindF (Λ := Λ) M₀).comp π) (isOpen_comp π hπ _)) := by
  classical
  have : Finite (Module.Dual Λ M₀) := finite_dual
  let _ : Fintype (Module.Dual Λ M₀) := Fintype.ofFinite _
  set W := LinearMap.range (dualEmb (Λ := Λ) M₀)
  have : Finite ((Module.Dual Λ M₀ → Λ) ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  have hex : Function.Exact (dualEmb (Λ := Λ) M₀) W.mkQ := fun F => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  exact alpha_bijective_of_ses hv e hall hΛ (isOpen_comp π hπ _) (isOpen_comp π hπ _)
    (isOpen_comp π hπ (coindF (Λ := Λ) ((Module.Dual Λ M₀ → Λ) ⧸ W)))
    (coindMap_equiv π (dualEmb M₀)) (coindMap_injective (dualEmb_injective hsep M₀))
    (coindMap_equiv π W.mkQ) (coindMap_surjective (Submodule.mkQ_surjective W)) (coindMap_exact hex)
    (hfree _) (base_injective hv e π hπ hsep (fun ι _ _ => (hfree ι).1) _)

/-- **Lisse duality from the regular base case**: `alphaM` bijective on `coindF Λ` (constant coefficients `Λ` on
the cover cut out by `π`) ⇒ bijective for every finite `τ ∘ π`. -/
theorem alpha_bijective_of_regular [Nonempty S] [Finite Λ] [Module.Injective Λ Λ] {l n : ℕ}
    (hall : H2All Λ G Γ l n) (hΛ : ∀ a : Λ, (l ^ n) • a = 0) [Finite Gf] (hsep : SepDual Λ)
    (hone : Function.Bijective (alphaM hv e ((coindF (Λ := Λ) Λ).comp π) (isOpen_comp π hπ _)))
    {N : Type} [AddCommGroup N] [Module Λ N] [Finite N] (τ : Representation Λ Gf N) :
    Function.Bijective (alphaM hv e (τ.comp π) (isOpen_comp π hπ τ)) :=
  alpha_bijective_of_base hv e π hπ hall hΛ
    (fun M₀ _ _ _ => base_bijective hv e π hπ hall hΛ hsep
      (fun ι _ _ => alpha_free_bijective hv e π hπ hone ι) M₀) τ

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Push =====
section

/-!
# S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward

* P0 (`alpha_bijective_of_regular_range`): the input `hone` of `alpha_bijective_of_regular` is only needed for a
  SURJECTIVE `π` (replace `π` by `π.rangeRestrict` and `τ` by `τ ∘ subtype`).
* P1 (`alpha_coindF_of_push`): for `π : G →* Gf` surjective with kernel `K`, `Fun(Gf, Λ) ∘ π ≅ f_* Λ = pushRep K Λ`
  (`F ↦ (x ↦ F (π x)⁻¹)`), so `hone` follows from duality for the pushforward of the constant sheaf along the
  cover with group `K` (no connectedness needed here; it enters only through Shapiro).
* `alpha_bijective_of_push`: lisse duality for every finite `τ ∘ π` from duality for `pushRep (ker π) Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {σ : Representation Λ G Λ} {hσ : IsOpen (σ.ker : Set G)}
  (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ) {Gf : Type} [Group Gf]

/-! ## P0 -/

/-! ## P1: `Fun(Gf, Λ) ∘ π ≅ pushRep (ker π) Λ` -/

section Push

variable (π : G →* Gf) (K : Subgroup G)

/-- **P1**: duality for `pushRep K Λ` gives `hone` for a surjective `π` with kernel `K`. -/
theorem alpha_coindF_of_push (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)
    (hπ : IsOpen (π.ker : Set G))
    (hY : Function.Bijective (alphaM hv e (pushRep K (Representation.trivial Λ K Λ)) (isOpen_push π K hK hπ))) :
    Function.Bijective (alphaM hv e ((coindF (Λ := Λ) Λ).comp π) (isOpen_comp π hπ _)) :=
  alpha_bijective_of_retract hv e _ _ (ι := Unit) (inj := fun _ => injP π K hs) (proj := fun _ => projP π K hK)
    (fun _ => injP_equiv π K hK hs) (fun _ => projP_equiv π K hK)
    (fun F => by rw [Fintype.sum_unique]; exact injP_projP π K hK hs F) hY

end Push

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Proj =====
section

/-!
# S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing

`π : G →* Gf` surjective onto a finite group, `K = ker π` (the cover `f : V → U`), `σ : Representation Λ G Λ`.
* `trP : f_*(σ|K) → σ`, `F ↦ Σ_y σ(s y)⁻¹ F(s y)` (`s` a section of `π`); equivariant (`trP_equiv`);
* `mulP : f_*Λ × f_*(σ|K) → f_*(σ|K)`, the pointwise product, equivariant (`mulP_equiv`);
  `phiP_eq_trP : phiP F' F = trP (F · F')`;
* `isOpen_pushS`, `mulHyp`: the cup-product hypotheses for `mulP`;
* `alphaM_eq_sum_trP`: for a primitive `U` of the `mulP`-cup product of `(c, psiP ∘ d)`, the duality pairing of
  `[(c, m)]` and `[d]` is `Σ_s trP (m_s · psiP (d t_s) - U t_s)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Proj

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)

include hK in
/-- The cup-product hypotheses for the pointwise product `mulP`. -/
theorem mulHyp (Γ : Subgroup G) (hπ : IsOpen (π.ker : Set G)) (hσ : IsOpen (σ.ker : Set G))
    (van : H2Van (pushRep K (σ.comp K.subtype)) Γ ⊤) :
    CupHyp (pushRep K (Representation.trivial Λ K Λ)) (pushRep K (σ.comp K.subtype))
      (pushRep K (σ.comp K.subtype)) (mulP σ K) Γ :=
  ⟨fun g F F' => mulP_equiv σ K g F F', isOpen_pushS σ π K hK hπ hσ, isOpen_pushS σ π K hK hπ hσ, van⟩

/-- **P3a**: the duality pairing on `f_* Λ` through the trace. -/
theorem alphaM_eq_sum_trP {Γ : Subgroup G} {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
    {t : (s : S) → ↥(Γ ⊓ I s)} (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) (hv : H2Van σ Γ ⊤)
    (hX : IsOpen ((pushRep K (Representation.trivial Λ K Λ)).ker : Set G))
    (p : Z1c (pushRep K (Representation.trivial Λ K Λ)) Γ I)
    (d : Z1 ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ)
    (U : Γ → Representation.coindV K.subtype (σ.comp K.subtype))
    (hU : IsPrim (pushRep K (σ.comp K.subtype)) (pushRep K (σ.comp K.subtype)) (mulP σ K) Γ
      p.1.1 ((psiP σ π K hK).compLeft Γ d.1) U) :
    alphaM hv (h2kEquiv D hσ).toLinearMap (pushRep K (Representation.trivial Λ K Λ)) hX
        (H1c.mk (pushRep K (Representation.trivial Λ K Λ)) Γ I p)
        (H1.mk ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ d) =
      ∑ s, trP σ π K hs (mulP σ K (p.1.2 s) (psiP σ π K hK (d.1 (tG t s))) - U (tG t s)) := by
  have hu : IsPrim ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) σ evalB Γ p.1.1 d.1
      (fun g => trP σ π K hs (U g)) := by
    refine ⟨hU.1.comp _, fun g h => ?_⟩
    have e := congrArg (trP σ π K hs) (hU.2 g h)
    rw [map_add, map_sub, trP_equiv σ π K hK hs g (U h)] at e
    refine Eq.trans ?_ e
    show ((pushRep K (Representation.trivial Λ K Λ)).linHom σ g (d.1 h)) (p.1.1 g) =
      trP σ π K hs (mulP σ K (p.1.1 g) (pushRep K (σ.comp K.subtype) g (psiP σ π K hK (d.1 h))))
    rw [← psiP_equiv σ π K hK g, ← phiP_eq_trP, phiP_psiP]
  show h2kEquiv D hσ (cupH (dualHyp hX hσ hv) p d) = _
  rw [cupH_eq _ p d _ hu, h2kEquiv_mk, evalSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [cupZ_apply, map_sub, ← phiP_eq_trP, phiP_psiP]
  rfl

end Proj

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_ProjV =====
section

/-!
# S4-CurveDuality O7d-P3a(iii): the duality pairing of the cover `V`, through Shapiro

`K = ker π` (the cover `f : V → U`), `J t ≤ K` the inertia at the boundary points `t` of `V`, `x_t = xT t`,
`InertiaLift`. For a relative cocycle `p = (c, m)` of `f_*Λ`, a cocycle `Dz` of `f_*(σ|K)` and a primitive `U` of the
pointwise (`mulP`) cup product of `(c, Dz)`:
* `primV`: `u'(h) := U(h)(1)` is a primitive of the `V`-level cup product of the Shapiro images;
* `keyV`: for `h ∈ (Γ ∩ K) ∩ J t` and `g = x_t⁻¹ h x_t`,
  `(m_{π t} · Dz(g) - U(g))(x_t) = b'_t · d'(h) - u'(h)`, `(c', b') = shapiroZ1c p`, `d' = shapiroZ1 Dz`;
* `constPairV_eq`: hence the constant-coefficient pairing of `V` on the Shapiro images is
  `Σ_t (m_{π t} · Dz(g_t) - U(g_t))(x_t)`, `g_t = x_t⁻¹ t'_t x_t` (`t'_t` the generators of `V`'s `ConstData`);
* `constPairV_dual`: the same with `Dz = psiP ∘ d` and `shapiroDual` (`shapiroDual_mk_eq`, by `rfl`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section ProjV

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation Λ G Λ} {K : Subgroup G} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}
  {T : Type} {J : T → Subgroup K} {πT : T → S} {xT : T → Γ}

variable [Fintype T] [Nonempty T]

/-- **(3)** The constant-coefficient pairing of `V` on the Shapiro images. -/
theorem constPairV_eq (hD : ∀ (g : Γ) (v : Λ), σ g v = v) (hJ : InertiaLift Γ K I J πT xT)
    {t' : (u : T) → ↥(geoU Γ K ⊓ J u)}
    (HV : CupHyp (Representation.trivial Λ K Λ) (σ.comp K.subtype) (σ.comp K.subtype) (LinearMap.mul Λ Λ)
      (geoU Γ K))
    (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t')
    (p : Z1c (pushRep K (Representation.trivial Λ K Λ)) Γ I)
    (Dz : Z1 (pushRep K (σ.comp K.subtype)) Γ) (U : Γ → Representation.coindV K.subtype (σ.comp K.subtype))
    (hU : IsPrim (pushRep K (σ.comp K.subtype)) (pushRep K (σ.comp K.subtype)) (mulP σ K) Γ p.1.1 Dz.1 U)
    (g : T → Γ) (hg : ∀ u, (g u : G) = (xT u : G)⁻¹ * (((tG t' u : geoU Γ K) : K) : G) * xT u) :
    constPair HV DV (shapiroH1c Γ K (Representation.trivial Λ K Λ) I J πT xT hJ
        (H1c.mk (pushRep K (Representation.trivial Λ K Λ)) Γ I p))
      (H1.mk (σ.comp K.subtype) (geoU Γ K) (shapiroZ1 Γ K (σ.comp K.subtype) Dz)) =
      ∑ u, ((mulP σ K (p.1.2 (πT u)) (Dz.1 (g u)) - U (g u) :
        Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT u) := by
  rw [shapiroH1c_mk, constPair_mk HV DV (shapiroZ1c Γ K (Representation.trivial Λ K Λ) I J πT xT hJ p)
    (shapiroZ1 Γ K (σ.comp K.subtype) Dz) (uV U) (primV p Dz U hU)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [keyV hD hJ p Dz U hU u (tG t' u) (Subgroup.mem_inf.1 (t' u).2).2 (g u) (hg u)]

end ProjV

section ProjVDual

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)
  (Γ : Subgroup G)

/-- **P3a(iii)** in the form used by P3b: the pairing of `V` on `(shapiroH1c x, shapiroDual y)`. -/
theorem constPairV_dual {S : Type} {I : S → Subgroup G} {T : Type} [Fintype T] [Nonempty T]
    {J : T → Subgroup K} {πT : T → S} {xT : T → Γ}
    (hD : ∀ (g : Γ) (v : Λ), σ g v = v) (hJ : InertiaLift Γ K I J πT xT)
    {t' : (u : T) → ↥(geoU Γ K ⊓ J u)}
    (HV : CupHyp (Representation.trivial Λ K Λ) (σ.comp K.subtype) (σ.comp K.subtype) (LinearMap.mul Λ Λ)
      (geoU Γ K))
    (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t')
    (R : CosetReps Γ K) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ) (hKo : IsOpen (K : Set G))
    (p : Z1c (pushRep K (Representation.trivial Λ K Λ)) Γ I)
    (d : Z1 ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ)
    (U : Γ → Representation.coindV K.subtype (σ.comp K.subtype))
    (hU : IsPrim (pushRep K (σ.comp K.subtype)) (pushRep K (σ.comp K.subtype)) (mulP σ K) Γ
      p.1.1 ((psiP σ π K hK).compLeft Γ d.1) U)
    (g : T → Γ) (hg : ∀ u, (g u : G) = (xT u : G)⁻¹ * (((tG t' u : geoU Γ K) : K) : G) * xT u) :
    constPair HV DV (shapiroH1c Γ K (Representation.trivial Λ K Λ) I J πT xT hJ
        (H1c.mk (pushRep K (Representation.trivial Λ K Λ)) Γ I p))
      (shapiroDual σ π K hK hs Γ R hcov hKo (H1.mk ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ d)) =
      ∑ u, ((mulP σ K (p.1.2 (πT u)) (psiP σ π K hK (d.1 (g u))) - U (g u) :
        Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT u) := by
  rw [shapiroDual_mk_eq]
  exact constPairV_eq hD hJ HV DV p (dZ σ π K hK Γ d) U hU g hg

end ProjVDual

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_AmbCup =====
section

/-!
# S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group

For `e : Δ₁ ≃ₜ* Δ₂` intertwining the representations (`Intw`) and the boundary subgroups (`IntwI`):
* `h2van_comp`: `H²(Δ₂, σ₂) = 0 → H²(Δ₁, σ₁) = 0`; `Intw.linHom`: `e` intertwines the internal Homs;
* `cupPair_tr`: `h2kTr (x ∪ y) = h1cTr x ∪ h1Tr y`, hence `pair_tr` for any functional on the cone `H²`;
* `constData_tr`, `h2kEquiv_tr`, `constPair_tr`, `constPair_bijective_tr`;
* `alphaM_tr`, `alphaM_bijective_tr`: the duality map `α` is bijective at `Δ₂` ⇒ at `Δ₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section AmbCup

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂}

variable {M M' L : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] [AddCommGroup L]
  [Module k L] {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M}
  {ρ₁' : Representation k G₁ M'} {ρ₂' : Representation k G₂ M'}
  {σ₁ : Representation k G₁ L} {σ₂ : Representation k G₂ L} {β : M →ₗ[k] M' →ₗ[k] L}

variable {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

theorem cupPair_tr (H₁ : CupHyp ρ₁ ρ₁' σ₁ β Δ₁) (H₂ : CupHyp ρ₂ ρ₂' σ₂ β Δ₂) (h : Intw ρ₁ ρ₂ e)
    (h' : Intw ρ₁' ρ₂' e) (hσ : Intw σ₁ σ₂ e) (hI : IntwI I₁ I₂ e) (x : H1c ρ₁ Δ₁ I₁) (y : H1 ρ₁' Δ₁) :
    h2kTr hσ hI H₁.openL H₂.openL (cupPair (I := I₁) H₁ x y) =
      cupPair (I := I₂) H₂ (h1cTr h hI x) (h1Tr h' y) := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨u, hu⟩ := exists_prim H₁ ((mem_Z1c ρ₁ Δ₁ I₁ _).1 p.2).1 d.2
  have hu' := isPrim_tr h' hσ hu
  show h2kTr hσ hI H₁.openL H₂.openL (cupH H₁ p d) = cupH H₂ (z1cTr h hI p) (z1Tr h' d)
  rw [cupH_eq H₁ p d u hu, cupH_eq H₂ (z1cTr h hI p) (z1Tr h' d) (u ∘ e.symm) hu', h2kTr_mk]
  rfl

/-- Any functional on the cone `H²` compatible with `h2kTr` gives compatible pairings. -/
theorem pair_tr (H₁ : CupHyp ρ₁ ρ₁' σ₁ β Δ₁) (H₂ : CupHyp ρ₂ ρ₂' σ₂ β Δ₂) (h : Intw ρ₁ ρ₂ e)
    (h' : Intw ρ₁' ρ₂' e) (hσ : Intw σ₁ σ₂ e) (hI : IntwI I₁ I₂ e) {R : Type} [AddCommGroup R] [Module k R]
    (f₁ : H2K σ₁ Δ₁ I₁ H₁.openL →ₗ[k] R) (f₂ : H2K σ₂ Δ₂ I₂ H₂.openL →ₗ[k] R)
    (hf : ∀ z, f₁ z = f₂ (h2kTr hσ hI H₁.openL H₂.openL z)) (x : H1c ρ₁ Δ₁ I₁) (y : H1 ρ₁' Δ₁) :
    (cupPair (I := I₁) H₁).compr₂ f₁ x y = (cupPair (I := I₂) H₂).compr₂ f₂ (h1cTr h hI x) (h1Tr h' y) := by
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, hf, cupPair_tr H₁ H₂ h h' hσ hI]

end AmbCup

/-! ## The duality map `α` -/

section Alpha

variable {Λ : Type} [CommRing Λ] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁}
  {I₂ : S → Subgroup G₂} {σ₁ : Representation Λ G₁ Λ} {σ₂ : Representation Λ G₂ Λ}
  {hσ₁ : IsOpen (σ₁.ker : Set G₁)} {hσ₂ : IsOpen (σ₂.ker : Set G₂)}
  {M : Type} [AddCommGroup M] [Module Λ M]

theorem alphaM_tr (hs : Intw σ₁ σ₂ e) (hI : IntwI I₁ I₂ e) (hv₁ : H2Van σ₁ Δ₁ ⊤) (hv₂ : H2Van σ₂ Δ₂ ⊤)
    (f₁ : H2K σ₁ Δ₁ I₁ hσ₁ →ₗ[Λ] Λ) (f₂ : H2K σ₂ Δ₂ I₂ hσ₂ →ₗ[Λ] Λ)
    (hf : ∀ z, f₁ z = f₂ (h2kTr hs hI hσ₁ hσ₂ z)) {ρ₁ : Representation Λ G₁ M} {ρ₂ : Representation Λ G₂ M}
    (h : Intw ρ₁ ρ₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁)) (hρ₂ : IsOpen (ρ₂.ker : Set G₂))
    (x : H1c ρ₁ Δ₁ I₁) (y : H1 (ρ₁.linHom σ₁) Δ₁) :
    alphaM hv₁ f₁ ρ₁ hρ₁ x y = alphaM hv₂ f₂ ρ₂ hρ₂ (h1cTr h hI x) (h1Tr (h.linHom hs) y) :=
  pair_tr (dualHyp hρ₁ hσ₁ hv₁) (dualHyp hρ₂ hσ₂ hv₂) h (h.linHom hs) hs hI f₁ f₂ hf x y

/-- **`α` under a change of ambient group**: bijective at `Δ₂` ⇒ bijective at `Δ₁`. -/
theorem alphaM_bijective_tr (hs : Intw σ₁ σ₂ e) (hI : IntwI I₁ I₂ e) (hv₁ : H2Van σ₁ Δ₁ ⊤)
    (hv₂ : H2Van σ₂ Δ₂ ⊤) (f₁ : H2K σ₁ Δ₁ I₁ hσ₁ →ₗ[Λ] Λ) (f₂ : H2K σ₂ Δ₂ I₂ hσ₂ →ₗ[Λ] Λ)
    (hf : ∀ z, f₁ z = f₂ (h2kTr hs hI hσ₁ hσ₂ z)) {ρ₁ : Representation Λ G₁ M} {ρ₂ : Representation Λ G₂ M}
    (h : Intw ρ₁ ρ₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁)) (hρ₂ : IsOpen (ρ₂.ker : Set G₂))
    (hb : Function.Bijective (alphaM hv₂ f₂ ρ₂ hρ₂)) : Function.Bijective (alphaM hv₁ f₁ ρ₁ hρ₁) :=
  bijective_of_equiv_pair _ _ (h1cTr h hI) (h1Tr (h.linHom hs))
    (alphaM_tr hs hI hv₁ hv₂ f₁ f₂ hf h hρ₁ hρ₂) hb

end Alpha

/-! ## Constant coefficients -/

section Const

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁}
  {I₂ : S → Subgroup G₂} {σ₁ : Representation k G₁ k} {σ₂ : Representation k G₂ k}

variable [Fintype S]

theorem h2kEquiv_tr [Nonempty S] (hσ : Intw σ₁ σ₂ e) (hI : IntwI I₁ I₂ e) {t₁ : (s : S) → ↥(Δ₁ ⊓ I₁ s)}
    {t₂ : (s : S) → ↥(Δ₂ ⊓ I₂ s)} (ht : ∀ s, infTr hI s (t₁ s) = t₂ s) (D₁ : ConstData σ₁ Δ₁ I₁ t₁)
    (D₂ : ConstData σ₂ Δ₂ I₂ t₂) (hσ₁ : IsOpen (σ₁.ker : Set G₁)) (hσ₂ : IsOpen (σ₂.ker : Set G₂))
    (z : H2K σ₁ Δ₁ I₁ hσ₁) : h2kEquiv D₁ hσ₁ z = h2kEquiv D₂ hσ₂ (h2kTr hσ hI hσ₁ hσ₂ z) := by
  obtain rfl : (fun s => infTr hI s (t₁ s)) = t₂ := funext ht
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  show evalSum σ₁ Δ₁ I₁ t₁ x = evalSum σ₂ Δ₂ I₂ _ (piTr hσ hI x)
  simp only [evalSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  show _ = (x s : ↥(Δ₁ ⊓ I₁ s) → k) ((infTr hI s).symm (infTr hI s (t₁ s)))
  rw [ContinuousMulEquiv.symm_apply_apply]

variable [Nonempty S]

theorem constPair_tr (H₁ : CupHyp (Representation.trivial k G₁ k) σ₁ σ₁ (LinearMap.mul k k) Δ₁)
    (H₂ : CupHyp (Representation.trivial k G₂ k) σ₂ σ₂ (LinearMap.mul k k) Δ₂) (hσ : Intw σ₁ σ₂ e)
    (hI : IntwI I₁ I₂ e) {t₁ : (s : S) → ↥(Δ₁ ⊓ I₁ s)} {t₂ : (s : S) → ↥(Δ₂ ⊓ I₂ s)}
    (ht : ∀ s, infTr hI s (t₁ s) = t₂ s) (D₁ : ConstData σ₁ Δ₁ I₁ t₁) (D₂ : ConstData σ₂ Δ₂ I₂ t₂)
    (x : H1c (Representation.trivial k G₁ k) Δ₁ I₁) (y : H1 σ₁ Δ₁) :
    constPair H₁ D₁ x y = constPair H₂ D₂ (h1cTr (intw_trivial (k := k)) hI x) (h1Tr hσ y) :=
  pair_tr H₁ H₂ intw_trivial hσ hσ hI _ _ (h2kEquiv_tr hσ hI ht D₁ D₂ H₁.openL H₂.openL) x y

/-- **The constant pairing under a change of ambient group**: bijective at `Δ₂` ⇒ bijective at `Δ₁`. -/
theorem constPair_bijective_tr (H₁ : CupHyp (Representation.trivial k G₁ k) σ₁ σ₁ (LinearMap.mul k k) Δ₁)
    (H₂ : CupHyp (Representation.trivial k G₂ k) σ₂ σ₂ (LinearMap.mul k k) Δ₂) (hσ : Intw σ₁ σ₂ e)
    (hI : IntwI I₁ I₂ e) {t₁ : (s : S) → ↥(Δ₁ ⊓ I₁ s)} {t₂ : (s : S) → ↥(Δ₂ ⊓ I₂ s)}
    (ht : ∀ s, infTr hI s (t₁ s) = t₂ s) (D₁ : ConstData σ₁ Δ₁ I₁ t₁) (D₂ : ConstData σ₂ Δ₂ I₂ t₂)
    (hb : Function.Bijective (constPair H₂ D₂)) : Function.Bijective (constPair H₁ D₁) :=
  bijective_of_equiv_pair _ _ (h1cTr (intw_trivial (k := k)) hI) (h1Tr hσ) (constPair_tr H₁ H₂ hσ hI ht D₁ D₂) hb

end Const

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VFrobB =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 6: boundary data of `V` for any `ψ ∈ K`, generic form

`G` acts on a type `X` (the boundary primes), `P : S → X` represents the geometric boundary points, `I s` is the
inertia at `P s`. From the `U`-level facts
* `hcov`: every `a⁻¹ • P s` is `h • P u` with `h ∈ Γ` (orbit cover), `hin`: inertia transforms by conjugation,
* `hfix` (inertia fixes `P s`), `hdis` (`Γ`-orbits are disjoint), `hstab` (`Γ`-stabilisers lie in inertia),
and `RD : ResDat π Γ I N T` (the cover `V`, `K = ker π`), for `ψ ∈ K` and `t : T` over `s`:
`ψ⁻¹ x_t • P s = h • P u` (`fbU`, `fbH`), `h = k x_{t''} i` by `RD.hrep` (`fbT`, `fbI`, `fbK ∈ Γ ∩ K`).
* `fb_conj`: EXACT conjugation `x_t⁻¹ y x_t ∈ I s ↔ x_{t''}⁻¹ (k⁻¹ ψ⁻¹ y ψ k) x_{t''} ∈ I (sh t'')`;
* `fbT_injective` (from `hfix`, `hdis`, `hstab` and `hrep` uniqueness);
* **`vBdry`**: `BdryCompat (geoU Γ K) (rdJ RD K) ψ τ h`, `τ` bijective, and the reverse inclusion `hex` of
  `constPair_frob_unit` (VFrobA).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

noncomputable section

section FB

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Gf : Type} [Group Gf] {π : G →* Gf} {Γ : Subgroup G} [hΓ : Γ.Normal]
  {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T : Type} [Fintype T]
  [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (RD : ResDat π Γ I N T) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)
  {X : Type} [MulAction G X] (P : S → X)
  (hcov : ∀ (a : G) (s : S), ∃ u, ∃ h ∈ Γ, a⁻¹ • P s = h • P u)

/-- The boundary point `u` with `ψ⁻¹ x_t • P s ∈ Γ • P u`. -/
def fbU (ψ : G) (t : T) : S := (hcov ((RD.x t)⁻¹ * ψ) (RD.sh t)).choose

theorem fbH_ex (ψ : G) (t : T) :
    ∃ h ∈ Γ, ((RD.x t)⁻¹ * ψ)⁻¹ • P (RD.sh t) = h • P (fbU RD P hcov ψ t) :=
  (hcov ((RD.x t)⁻¹ * ψ) (RD.sh t)).choose_spec

/-- The correcting element `h ∈ Γ`. -/
def fbH (ψ : G) (t : T) : G := (fbH_ex RD P hcov ψ t).choose

theorem fbH_mem (ψ : G) (t : T) : fbH RD P hcov ψ t ∈ Γ := (fbH_ex RD P hcov ψ t).choose_spec.1

theorem fbH_spec (ψ : G) (t : T) :
    ((RD.x t)⁻¹ * ψ)⁻¹ • P (RD.sh t) = fbH RD P hcov ψ t • P (fbU RD P hcov ψ t) :=
  (fbH_ex RD P hcov ψ t).choose_spec.2

theorem fbT_ex (ψ : G) (t : T) : ∃! t2, RD.sh t2 = fbU RD P hcov ψ t ∧
    (π (RD.x t2))⁻¹ * π (fbH RD P hcov ψ t) ∈ (Γ ⊓ I (fbU RD P hcov ψ t)).map π :=
  RD.hrep _ _ (Subgroup.mem_map_of_mem π (fbH_mem RD P hcov ψ t))

/-- The boundary permutation of `V`. -/
def fbT (ψ : G) (t : T) : T := (fbT_ex RD P hcov ψ t).exists.choose

theorem fbT_spec (ψ : G) (t : T) : RD.sh (fbT RD P hcov ψ t) = fbU RD P hcov ψ t ∧
    (π (RD.x (fbT RD P hcov ψ t)))⁻¹ * π (fbH RD P hcov ψ t) ∈ (Γ ⊓ I (fbU RD P hcov ψ t)).map π :=
  (fbT_ex RD P hcov ψ t).exists.choose_spec

theorem fbI_ex (ψ : G) (t : T) : ∃ i, i ∈ Γ ⊓ I (fbU RD P hcov ψ t) ∧
    π i = (π (RD.x (fbT RD P hcov ψ t)))⁻¹ * π (fbH RD P hcov ψ t) :=
  Subgroup.mem_map.1 (fbT_spec RD P hcov ψ t).2

/-- `i ∈ Γ ⊓ I u` with `h = k x_{t''} i`. -/
def fbI (ψ : G) (t : T) : G := (fbI_ex RD P hcov ψ t).choose

theorem fbI_mem (ψ : G) (t : T) : fbI RD P hcov ψ t ∈ Γ ⊓ I (fbU RD P hcov ψ t) :=
  (fbI_ex RD P hcov ψ t).choose_spec.1

theorem fbI_pi (ψ : G) (t : T) :
    π (fbI RD P hcov ψ t) = (π (RD.x (fbT RD P hcov ψ t)))⁻¹ * π (fbH RD P hcov ψ t) :=
  (fbI_ex RD P hcov ψ t).choose_spec.2

/-- `k = h i⁻¹ x_{t''}⁻¹ ∈ Γ ∩ K`. -/
def fbK (ψ : G) (t : T) : G :=
  fbH RD P hcov ψ t * (fbI RD P hcov ψ t)⁻¹ * (RD.x (fbT RD P hcov ψ t))⁻¹

include hK in
theorem fbK_memK (ψ : G) (t : T) : fbK RD P hcov ψ t ∈ K := by
  rw [hK, fbK]
  simp only [map_mul, map_inv, fbI_pi]
  group

theorem fbK_memΓ (ψ : G) (t : T) : fbK RD P hcov ψ t ∈ Γ :=
  Γ.mul_mem (Γ.mul_mem (fbH_mem RD P hcov ψ t) (Γ.inv_mem (Subgroup.mem_inf.1 (fbI_mem RD P hcov ψ t)).1))
    (Γ.inv_mem (RD.hx _))

theorem fbH_eq (ψ : G) (t : T) :
    fbH RD P hcov ψ t = fbK RD P hcov ψ t * RD.x (fbT RD P hcov ψ t) * fbI RD P hcov ψ t := by
  rw [fbK]
  group

/-- **Exact conjugation** of the boundary inertia of `V` under `ψ`. -/
theorem fb_conj (hin : ∀ (g : G) (s u : S), P u = g⁻¹ • P s → ∀ x, x ∈ I u ↔ g * x * g⁻¹ ∈ I s)
    (ψ : G) (t : T) (y : G) : (RD.x t)⁻¹ * y * RD.x t ∈ I (RD.sh t) ↔
      (RD.x (fbT RD P hcov ψ t))⁻¹ * ((fbK RD P hcov ψ t)⁻¹ * (ψ⁻¹ * y * ψ) * fbK RD P hcov ψ t) *
        RD.x (fbT RD P hcov ψ t) ∈ I (RD.sh (fbT RD P hcov ψ t)) := by
  have hsh := (fbT_spec RD P hcov ψ t).1
  have hiI : fbI RD P hcov ψ t ∈ I (fbU RD P hcov ψ t) := (Subgroup.mem_inf.1 (fbI_mem RD P hcov ψ t)).2
  have hPu : P (fbU RD P hcov ψ t) = ((RD.x t)⁻¹ * ψ * fbH RD P hcov ψ t)⁻¹ • P (RD.sh t) := by
    rw [mul_inv_rev, mul_smul, fbH_spec, inv_smul_smul]
  have key := hin _ _ _ hPu ((fbH RD P hcov ψ t)⁻¹ * (ψ⁻¹ * y * ψ) * fbH RD P hcov ψ t)
  have e2 : (RD.x (fbT RD P hcov ψ t))⁻¹ * ((fbK RD P hcov ψ t)⁻¹ * (ψ⁻¹ * y * ψ) * fbK RD P hcov ψ t) *
      RD.x (fbT RD P hcov ψ t) = fbI RD P hcov ψ t * ((fbH RD P hcov ψ t)⁻¹ * (ψ⁻¹ * y * ψ) *
        fbH RD P hcov ψ t) * (fbI RD P hcov ψ t)⁻¹ := by
    rw [fbK]
    group
  have e1 : (RD.x t)⁻¹ * ψ * fbH RD P hcov ψ t * ((fbH RD P hcov ψ t)⁻¹ * (ψ⁻¹ * y * ψ) * fbH RD P hcov ψ t) *
      ((RD.x t)⁻¹ * ψ * fbH RD P hcov ψ t)⁻¹ = (RD.x t)⁻¹ * y * RD.x t := by group
  rw [hsh, e2, mul_mem_cancel_right ((I _).inv_mem hiI), mul_mem_cancel_left hiI, key, e1]

/-- `ψ⁻¹ x_t • P s = k x_{t''} • P (sh t'')`. -/
theorem fb_smul (hfix : ∀ s, ∀ g ∈ I s, g • P s = P s) (ψ : G) (t : T) :
    ((RD.x t)⁻¹ * ψ)⁻¹ • P (RD.sh t) =
      fbK RD P hcov ψ t • RD.x (fbT RD P hcov ψ t) • P (RD.sh (fbT RD P hcov ψ t)) := by
  rw [fbH_spec, (fbT_spec RD P hcov ψ t).1, fbH_eq, mul_smul, mul_smul,
    hfix _ _ (Subgroup.mem_inf.1 (fbI_mem RD P hcov ψ t)).2]

include hK in
theorem fbT_injective (hfix : ∀ s, ∀ g ∈ I s, g • P s = P s)
    (hdis : ∀ s s', ∀ g ∈ Γ, P s' = g • P s → s = s')
    (hstab : ∀ s, ∀ g ∈ Γ, g • P s = P s → g ∈ I s) {ψ : G} (hψ : ψ ∈ K) :
    Function.Injective (fbT RD P hcov ψ) := by
  intro t1 t2 h12
  have e1 := fb_smul RD P hcov hfix ψ t1
  have e2 := fb_smul RD P hcov hfix ψ t2
  rw [h12] at e1
  set k1 := fbK RD P hcov ψ t1
  set k2 := fbK RD P hcov ψ t2
  set g : G := ((RD.x t2)⁻¹ * ψ) * k2 * k1⁻¹ * ((RD.x t1)⁻¹ * ψ)⁻¹ with hg_def
  have hP : P (RD.sh t2) = g • P (RD.sh t1) := by
    have e3 : RD.x (fbT RD P hcov ψ t2) • P (RD.sh (fbT RD P hcov ψ t2)) =
        k1⁻¹ • ((RD.x t1)⁻¹ * ψ)⁻¹ • P (RD.sh t1) := by
      rw [e1, inv_smul_smul]
    calc P (RD.sh t2) = ((RD.x t2)⁻¹ * ψ) • ((RD.x t2)⁻¹ * ψ)⁻¹ • P (RD.sh t2) := (smul_inv_smul _ _).symm
      _ = ((RD.x t2)⁻¹ * ψ) • k2 • RD.x (fbT RD P hcov ψ t2) • P (RD.sh (fbT RD P hcov ψ t2)) := by
        rw [e2]
      _ = ((RD.x t2)⁻¹ * ψ) • k2 • k1⁻¹ • ((RD.x t1)⁻¹ * ψ)⁻¹ • P (RD.sh t1) := by rw [e3]
      _ = g • P (RD.sh t1) := by simp only [hg_def, mul_smul]
  have hg' : g = (RD.x t2)⁻¹ * (ψ * (k2 * k1⁻¹) * ψ⁻¹) * RD.x t1 := by
    rw [hg_def]
    group
  have hk1 : k1 ∈ Γ := fbK_memΓ RD P hcov ψ t1
  have hk2 : k2 ∈ Γ := fbK_memΓ RD P hcov ψ t2
  have hgΓ : g ∈ Γ := by
    rw [hg']
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (RD.hx t2)) (hΓ.conj_mem _ (Γ.mul_mem hk2 (Γ.inv_mem hk1)) ψ))
      (RD.hx t1)
  have hπg : π g = (π (RD.x t2))⁻¹ * π (RD.x t1) := by
    have hk1π : π k1 = 1 := (hK _).1 (fbK_memK RD K hK P hcov ψ t1)
    have hk2π : π k2 = 1 := (hK _).1 (fbK_memK RD K hK P hcov ψ t2)
    rw [hg']
    simp only [map_mul, map_inv, hk1π, hk2π, (hK _).1 hψ, inv_one, mul_one]
  have hs : RD.sh t1 = RD.sh t2 := hdis _ _ g hgΓ hP
  rw [← hs] at hP
  have hgI : g ∈ I (RD.sh t1) := hstab _ g hgΓ hP.symm
  obtain ⟨t0, -, hu⟩ := RD.hrep (RD.sh t1) (π (RD.x t1)) (Subgroup.mem_map_of_mem π (RD.hx t1))
  have a1 : t1 = t0 := hu t1 ⟨rfl, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  have a2 : t2 = t0 := hu t2 ⟨hs.symm, Subgroup.mem_map.2 ⟨g, Subgroup.mem_inf.2 ⟨hgΓ, hgI⟩, hπg⟩⟩
  exact a1.trans a2.symm

/-- `k` as an element of `geoU Γ K`. -/
def fbKV (ψ : G) (t : T) : geoU Γ K :=
  ⟨⟨fbK RD P hcov ψ t, fbK_memK RD K hK P hcov ψ t⟩, Subgroup.mem_subgroupOf.2 (fbK_memΓ RD P hcov ψ t)⟩

theorem fbKV_coe (ψ : G) (t : T) : (((fbKV RD K hK P hcov ψ t : geoU Γ K) : K) : G) = fbK RD P hcov ψ t := rfl

include hK hcov in
/-- **VFrobB.** Boundary data of `V` for `ψ ∈ K`: compatibility, bijective permutation, reverse inclusion. -/
theorem vBdry (hin : ∀ (g : G) (s u : S), P u = g⁻¹ • P s → ∀ x, x ∈ I u ↔ g * x * g⁻¹ ∈ I s)
    (hfix : ∀ s, ∀ g ∈ I s, g • P s = P s) (hdis : ∀ s s', ∀ g ∈ Γ, P s' = g • P s → s = s')
    (hstab : ∀ s, ∀ g ∈ Γ, g • P s = P s → g ∈ I s) (ψ : K) :
    ∃ (τ : T → T) (h : T → geoU Γ K), BdryCompat (geoU Γ K) (rdJ RD K) ψ τ h ∧ Function.Bijective τ ∧
      ∀ t (g : K), g ∈ geoU Γ K → g ∈ rdJ RD K (τ t) → (ψ * h t) * g * (ψ * h t)⁻¹ ∈ rdJ RD K t := by
  refine ⟨fbT RD P hcov (ψ : G), fbKV RD K hK P hcov (ψ : G), fun t g hg => ?_,
    Finite.injective_iff_bijective.1 (fbT_injective RD K hK P hcov hfix hdis hstab ψ.2), fun t g _ hgJ => ?_⟩
  · have h1 := (fb_conj RD P hcov hin (ψ : G) t ((g : K) : G)).1 ((mem_rdJ RD K t _).1 hg)
    refine (mem_rdJ RD K _ _).2 ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, fbKV_coe]
    exact h1
  · have h2 := (mem_rdJ RD K _ _).1 hgJ
    refine (mem_rdJ RD K t _).2 ((fb_conj RD P hcov hin (ψ : G) t _).2 ?_)
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, fbKV_coe]
    group

end FB

end

end RamanujanPetersson.CupDuality


end


