-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_02
-- name    : RPLib_FX_LisseDual_02
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T03:08:20.425475+00:00
-- url     : https://prove2.me/theorems/bea092f7-31f9-5d39-adbd-866d11801673
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, library file 02 of 7
-- statement:
--   File 02 of 7 of the lisse duality library for affine curves over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CurveCoh_Shapiro`: S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1
--   * `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
--   * `S4.Def_RP_CupDuality_VS3a`: S4-CurveDuality, O9b (Route G at `V`) part 8: topology and density at `K`, generic form
--   * `S4.Def_RP_CupDuality_VTr1`: S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer
--   * `S4.Def_RP_CupDuality_VLift`: S4-CurveDuality, O9b (V-free) part 2: parabolic homomorphisms to `ℤ/l` lift to `ℤ/lⁿ`
--   * `S4.Def_RP_LisseDuality_Push`: S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward
--   * `S4.Def_RP_LisseDuality_Dual`: S4-CurveDuality O7d-P2: the dual of a finite push-forward, and Shapiro on the dual side
--   * `S4.Def_RP_LisseDuality_Proj`: S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing
--   * `S4.Def_RP_LisseDuality_ProjV`: S4-CurveDuality O7d-P3a(iii): the duality pairing of the cover `V`, through Shapiro
--   * `S4.Def_RP_LisseDuality_Trans`: S4-CurveDuality O7d-P3b T1: local traces are weighted `V`-level residues
--   * `S4.Def_RP_LisseDuality_AmbCup`: S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group
--   * `S4.Def_RP_LisseDuality_AmbRes`: S4-CurveDuality O7d-P1d (T4): restricting the cover data to a subgroup `H ⊇ Γ, K`
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_F2_017
import Definitions.Def_RPLib_FX_LisseDual_01

/-!
# Poincaré duality with lisse coefficients on an affine curve over a finite field, library file 02 of 7

Declarations of the formalization of Poincaré duality for H¹ with lisse (finite, twisted) coefficients on an
affine curve over a finite field (the cochain duality map `alphaM` is bijective), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CurveCoh_Shapiro`: S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1
* `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
* `S4.Def_RP_CupDuality_VS3a`: S4-CurveDuality, O9b (Route G at `V`) part 8: topology and density at `K`, generic form
* `S4.Def_RP_CupDuality_VTr1`: S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer
* `S4.Def_RP_CupDuality_VLift`: S4-CurveDuality, O9b (V-free) part 2: parabolic homomorphisms to `ℤ/l` lift to `ℤ/lⁿ`
* `S4.Def_RP_LisseDuality_Push`: S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward
* `S4.Def_RP_LisseDuality_Dual`: S4-CurveDuality O7d-P2: the dual of a finite push-forward, and Shapiro on the dual side
* `S4.Def_RP_LisseDuality_Proj`: S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing
* `S4.Def_RP_LisseDuality_ProjV`: S4-CurveDuality O7d-P3a(iii): the duality pairing of the cover `V`, through Shapiro
* `S4.Def_RP_LisseDuality_Trans`: S4-CurveDuality O7d-P3b T1: local traces are weighted `V`-level residues
* `S4.Def_RP_LisseDuality_AmbCup`: S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group
* `S4.Def_RP_LisseDuality_AmbRes`: S4-CurveDuality O7d-P1d (T4): restricting the cover data to a subgroup `H ⊇ Γ, K`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CurveCoh_Shapiro =====
section

/-!
# S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1

A finite etale cover `f : U → V` corresponds to an open subgroup `H = π₁(U)` of finite index in `G = π₁(V)`.
For a representation `σ` of `H` on `M` (a lisse sheaf on `U`), `f_* M` is the coinduced representation
`pushRep Γ H σ` of `G` on `coindV H.subtype σ`: `H`-equivariant functions `F : G → M`, `(g • F) x = F (x * g)`.
The geometric fundamental group of `U` is `Γ ∩ H` (`geoU Γ H`), and `U` is geometrically connected over the
constant field of `V` exactly when `G = H Γ` (hypothesis `hcov`).

Results (over any commutative ring `k`):
* `shapiroH0Equiv : H⁰(Γ, f_* M) ≃ₗ H⁰(Γ ∩ H, M)` (`F ↦ F 1`);
* `shapiroH1 : H¹(Γ, f_* M) →ₗ H¹(Γ ∩ H, M)` (restrict to `Γ ∩ H`, evaluate at `1`): injective (`hcov`), surjective
  (`hcov`, `H` open, representatives of `(Γ ∩ H) \ Γ`, which exist for finite index: `exists_cosetReps`), hence
  `shapiroH1Equiv`;
* `shapiroH1_frobH1`: Shapiro commutes with the operators `T_ψ`, `ψ ∈ H`; in particular with the GEOMETRIC Frobenius
  `F = T_{φ⁻¹}` for a Frobenius lift `φ ∈ π₁(U)` (which is also one for `V`), so purity is preserved.
Part 5 (`Def_RP_CurveCoh_ShapiroCone`) treats the cone `H¹_c`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

open Representation

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (Γ H : Subgroup G) (σ : Representation k H M)

/-! ## Extension from `Γ` to `G = H Γ` -/

section Ext

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

end Ext

/-! ## Degree 0 -/

/-! ## Degree 1: the map -/

theorem shapiroH1_injective (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ) :
    Function.Injective (shapiroH1 Γ H σ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨c, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  have hx' : Submodule.Quotient.mk (p := (B1 σ (geoU Γ H)).comap (Z1 σ (geoU Γ H)).subtype)
      (shapiroZ1 Γ H σ ⟨c, hz⟩) = 0 := hx
  have hB0 := (Submodule.Quotient.mk_eq_zero _).mp hx'
  have hB : resEv Γ H σ c ∈ B1 σ (geoU Γ H) := hB0
  obtain ⟨-, m, hm⟩ := (mem_B1 _ _ _).mp hB
  have hφ : EquivOnΓ Γ H σ (fun y => m + ((c y : coindV H.subtype σ) : G → M) 1) := by
    intro h y y' hy
    have hhΓ : (h : G) ∈ Γ := by
      have : (h : G) = y' * (y : G)⁻¹ := by rw [hy]; group
      rw [this]; exact Γ.mul_mem y'.2 (Γ.inv_mem y.2)
    let u : geoU Γ H := ⟨h, Subgroup.mem_subgroupOf.mpr hhΓ⟩
    have hy' : y' = geoToΓ Γ H u * y := Subtype.ext hy
    have key := Z1_coind_apply Γ H σ hz (geoToΓ Γ H u) y 1
    rw [← hy'] at key
    have e1 : ((c (geoToΓ Γ H u) : coindV H.subtype σ) : G → M) 1 = σ h m - m := hm u
    have e2 : ((c y : coindV H.subtype σ) : G → M) (1 * ((geoToΓ Γ H u : Γ) : G)) =
        σ h (((c y : coindV H.subtype σ) : G → M) 1) := by
      rw [one_mul]; exact coind_apply_of_mem _ h
    change m + _ = σ h (m + _)
    rw [key, e1, e2, map_add]; abel
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine (mem_B1 _ _ _).mpr ⟨hz, coindOf Γ H σ hcov _ hφ, fun g => coind_ext_Γ Γ H σ hcov fun y => ?_⟩
  show ((c g : coindV H.subtype σ) : G → M) y =
    ((coindOf Γ H σ hcov _ hφ : coindV H.subtype σ) : G → M) ((y : G) * g) -
      ((coindOf Γ H σ hcov _ hφ : coindV H.subtype σ) : G → M) y
  rw [show (y : G) * g = ((y * g : Γ) : G) from rfl]
  simp only [coindOf_apply]
  rw [Z1_coind_apply Γ H σ hz, one_mul]
  abel

/-! ## Degree 1: surjectivity (the Shapiro lift) -/

variable {Γ H} (R : CosetReps Γ H)

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

include R hcov in
theorem shapiroH1_surjective [IsTopologicalGroup G] (hHo : IsOpen (H : Set G)) :
    Function.Surjective (shapiroH1 Γ H σ) := by
  intro x
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  have hz : liftZ1 σ R hcov a ∈ Z1 (pushRep H σ) Γ :=
    (mem_Z1 _ _ _).mpr ⟨liftZ1_isLocallyConstant σ R hcov hHo ha, liftZ1_cocycle σ R hcov ha⟩
  refine ⟨H1.mk (pushRep H σ) Γ ⟨_, hz⟩, ?_⟩
  rw [shapiroH1_mk]
  exact congrArg (H1.mk σ (geoU Γ H)) (Subtype.ext (funext fun h => resEv_liftZ1 σ R hcov a h))

variable (Γ H)

/-- **Shapiro, degree 1** (`U` geometrically connected, `H` open): `H¹(Γ, f_* M) ≃ H¹(Γ ∩ H, M)`. -/
def shapiroH1Equiv [IsTopologicalGroup G] (hHo : IsOpen (H : Set G)) :
    H1 (pushRep H σ) Γ ≃ₗ[k] H1 σ (geoU Γ H) :=
  LinearEquiv.ofBijective _ ⟨shapiroH1_injective Γ H σ hcov, shapiroH1_surjective σ R hcov hHo⟩

end

end CurveCoh
end RamanujanPetersson


end

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

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf : Type} [Group Gf] {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T : Type} [Fintype T] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)

/-! ### Conjugation `J_s ≃ geoU Γ K ⊓ rdJ t` -/

/-! ### `Γ_H ≃ geoU Γ K` -/

/-! ### The constant data of `V` -/

variable (σ : Representation Λ G Λ) (htriv : ∀ (g : Γ) (x : Λ), σ g x = x)

include htriv in
theorem rd_triv (g : geoU Γ K) (x : Λ) : (σ.comp K.subtype) (g : K) x = x :=
  htriv ⟨((g : K) : G), Subgroup.mem_subgroupOf.1 g.2⟩ x

variable [NeZero N] (hN : (N : Λ) = 0)

end RD

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VS3a =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 8: topology and density at `K`, generic form

For an open subgroup `K` of a compact group `G`:
* `compactSpace_of_isOpen`: `K` is compact;
* `hbasis_subgroup`: if open normal subgroups form a basis at `1` in `G`, they do in `K` (`N ↦ N ∩ K`);
* **`exists_dens_sub`**: if `G = φ^ℕ · Γ · N` for every open `N` (`Γ` normal) and `K = ker π` with `π` onto a finite
  group, then `K = φ_V^ℕ · (Γ ∩ K) · N` for every open `N ≤ K`, where `φ_V = γ₀⁻¹ φ^f ∈ K`, `f` the least `f > 0`
  with `π(φ)^f ∈ π(Γ)` (`π(φ)^j ∈ π(Γ) → f ∣ j`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Density at `K`**: `K = φ_V^ℕ · (Γ ∩ K) · N` for every open `N ≤ K`. -/
theorem exists_dens_sub {Γ : Subgroup G} [hΓ : Γ.Normal] {φ : G}
    (hd : ∀ N : Subgroup G, IsOpen (N : Set G) → ∀ r : G, ∃ j : ℕ, ∃ γ ∈ Γ, ∃ n ∈ N, r = φ ^ j * γ * n)
    {Gf : Type} [Group Gf] [Finite Gf] (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)
    (hKo : IsOpen (K : Set G)) :
    ∃ φV : K, ∀ N : Subgroup K, IsOpen (N : Set K) → ∀ r : K,
      ∃ j : ℕ, ∃ γ ∈ geoU Γ K, ∃ m ∈ N, r = φV ^ j * γ * m := by
  obtain ⟨f, -, hfP, hdvd⟩ := exists_least_pow (π φ) (Γ.map π)
  obtain ⟨γ0, hγ0, hγ0π⟩ := Subgroup.mem_map.1 hfP
  have hφV : γ0⁻¹ * φ ^ f ∈ K := (hK _).2 (by rw [map_mul, map_inv, hγ0π, map_pow, inv_mul_cancel])
  refine ⟨⟨_, hφV⟩, fun N hN r => ?_⟩
  have hq : (QuotientGroup.mk (φ ^ f) : G ⧸ Γ) = QuotientGroup.mk (γ0⁻¹ * φ ^ f) := by
    rw [QuotientGroup.eq]
    have e : (φ ^ f)⁻¹ * (γ0⁻¹ * φ ^ f) = (φ ^ f)⁻¹ * γ0⁻¹ * ((φ ^ f)⁻¹)⁻¹ := by group
    rw [e]
    exact hΓ.conj_mem _ (Γ.inv_mem hγ0) _
  have hpow : ∀ a : ℕ, ((γ0⁻¹ * φ ^ f) ^ a)⁻¹ * (φ ^ f) ^ a ∈ Γ := fun a => by
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow, QuotientGroup.mk_pow, hq]
  have hNo : IsOpen ((N.map K.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hKo.isOpenMap_subtype_val _ hN
  obtain ⟨j, γ, hγ, n, hn, hr⟩ := hd _ hNo (r : G)
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
  have hπj : π φ ^ j ∈ Γ.map π := by
    have h1 := congrArg π hr
    rw [map_mul, map_mul, map_pow, (hK _).1 r.2, Subgroup.coe_subtype, (hK _).1 m.2, mul_one] at h1
    have h2 : π φ ^ j = π γ⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left h1.symm
    rw [h2]
    exact Subgroup.mem_map_of_mem π (Γ.inv_mem hγ)
  obtain ⟨a, rfl⟩ := hdvd j hπj
  have hcK : ((γ0⁻¹ * φ ^ f) ^ a)⁻¹ * (φ ^ f) ^ a * γ ∈ K := by
    have e : ((γ0⁻¹ * φ ^ f) ^ a)⁻¹ * (φ ^ f) ^ a * γ = ((γ0⁻¹ * φ ^ f) ^ a)⁻¹ * (r : G) * (m : G)⁻¹ := by
      rw [hr, Subgroup.coe_subtype, pow_mul]
      group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.inv_mem (K.pow_mem hφV a)) r.2) (K.inv_mem m.2)
  refine ⟨a, ⟨_, hcK⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (hpow a) hγ), m, hm, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
  rw [hr, Subgroup.coe_subtype, pow_mul]
  simp only [mul_assoc, mul_inv_cancel_left]

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_CupDuality_VTr1 =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer

Setting (session 49 design, "V-count"): `RD : ResDat π Γ I N T` is the residue data of the cover `V`
(`K = ker π`, boundary points `t : T` over `RD.sh t` with conjugators `x_t`), and `D2 : ResDat π₂ Γ I N T₂` is residue
data of a finer cover (`ker π₂ ≤ K`). On `V` (ambient group `K`, geometric group `geoU Γ K`, inertia `rdJ RD K`,
boundary `T`) with `π_V = π₂|_K`:
* `trJ t = geoU Γ K ⊓ rdJ RD K t ⊓ ker π_V`, which is `x_t J₂(sh t) x_t⁻¹` (`mem_trJ_iff`);
* `trSig t = x_t σ₂(sh t) x_t⁻¹` and its `LocGen` (`trLoc`), from `locGen_conjK` (transport of `LocGen` along
  conjugation by `x` into a subgroup `K`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

noncomputable section

section LocConj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K J I' : Subgroup G}
  {JV IV : Subgroup K} {N : ℕ}

end LocConj

section Tr

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hK2 : ∀ g, π2 g = 1 → g ∈ K)

/-- `Γ_H` of `V`: `geoU Γ K ⊓ ker π_V`. -/
def trΓH : Subgroup K := geoU Γ K ⊓ (piV π2 K).ker

theorem mem_trΓH (g : K) : g ∈ trΓH K (Γ := Γ) (π2 := π2) ↔ g ∈ geoU Γ K ∧ piV π2 K g = 1 := by
  rw [trΓH, Subgroup.mem_inf, MonoidHom.mem_ker]

end Tr

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_CupDuality_VLift =====
section

/-!
# S4-CurveDuality, O9b (V-free) part 2: parabolic homomorphisms to `ℤ/l` lift to `ℤ/lⁿ`

Route L (session 50; replaces the counting steps V-perf/V-lev of the session-49 design). `σ` trivial on `Γ`.
* `exists_lift_hom`: if `H²(Γ, ℤ/lⁿ) = 0` (`H2Van`), every locally constant homomorphism `χ : Γ → ℤ/l` lifts to one
  `Γ → ℤ/lⁿ`: the integer carry `c(g, h) = (χ̃ g + χ̃ h - χ̃(gh)) / l` is a 2-cocycle, `c = δb`, `χ' = χ̃ - l b`.
* `exists_parLift`: with the residue data `ConstData` at level `lⁿ`, a lift of a parabolic `χ` can be made parabolic:
  its residues `χ'(t_s) = l y_s` are corrected by `l d` with `d(t_s) = y'_s`, `Σ y'_s = 0` (`resOnto`), and a
  cocycle on `Γ ⊓ I s` vanishing at `t_s` is zero (`inj`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

section VLift

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G} {l n : ℕ}
  [Fact l.Prime]

/-- **Lifting homomorphisms** `Γ → ℤ/l` to `Γ → ℤ/lⁿ` when `H²(Γ, ℤ/lⁿ) = 0`. -/
theorem exists_lift_hom (hn : n ≠ 0) {σ : Representation (ZMod (l ^ n)) G (ZMod (l ^ n))}
    (htriv : ∀ (g : Γ) (x : ZMod (l ^ n)), σ g x = x) (hvan : H2Van σ Γ ⊤) {χ : Γ → ZMod l}
    (hlc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) :
    ∃ χ' : Γ → ZMod (l ^ n), IsLocallyConstant χ' ∧ (∀ a b, χ' (a * b) = χ' a + χ' b) ∧
      ∀ g, redL l hn (χ' g) = χ g := by
  have hlcf : IsLocallyConstant (fun x : Γ × Γ => ((carry χ x : ℕ) : ZMod (l ^ n))) :=
    (hlc.comp_continuous continuous_fst).comp₂ (hlc.comp_continuous continuous_snd)
      (fun u v : ZMod l => (((u.val + v.val) / l : ℕ) : ZMod (l ^ n)))
  obtain ⟨b, hb, -, hfb⟩ := hvan (fun x => ((carry χ x : ℕ) : ZMod (l ^ n))) hlcf (fun _ => Submodule.mem_top)
    (fun g h j => by
      show ((carry χ (g * h, j) : ℕ) : ZMod (l ^ n)) + (carry χ (g, h) : ℕ) =
        σ g ((carry χ (h, j) : ℕ) : ZMod (l ^ n)) + (carry χ (g, h * j) : ℕ)
      rw [htriv, ← Nat.cast_add, ← Nat.cast_add, carry_cocycle hχ])
  refine ⟨fun g => (((χ g).val : ℕ) : ZMod (l ^ n)) - (l : ZMod (l ^ n)) * b g,
    (hlc.comp fun z : ZMod l => ((z.val : ℕ) : ZMod (l ^ n))).comp₂ hb (fun u v => u - (l : ZMod (l ^ n)) * v),
    fun a c => ?_, fun g => ?_⟩
  · have hf : ((carry χ (a, c) : ℕ) : ZMod (l ^ n)) = b c - b (a * c) + b a := by
      have := hfb a c
      rwa [htriv] at this
    have e' : (l : ZMod (l ^ n)) * ((carry χ (a, c) : ℕ) : ZMod (l ^ n)) + (((χ (a * c)).val : ℕ) : ZMod (l ^ n)) =
        (((χ a).val : ℕ) : ZMod (l ^ n)) + (((χ c).val : ℕ) : ZMod (l ^ n)) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (l ^ n)) (carry_spec hχ a c)
    show (((χ (a * c)).val : ℕ) : ZMod (l ^ n)) - (l : ZMod (l ^ n)) * b (a * c) =
      ((((χ a).val : ℕ) : ZMod (l ^ n)) - (l : ZMod (l ^ n)) * b a) +
        ((((χ c).val : ℕ) : ZMod (l ^ n)) - (l : ZMod (l ^ n)) * b c)
    linear_combination e' - (l : ZMod (l ^ n)) * hf
  · show redL l hn ((((χ g).val : ℕ) : ZMod (l ^ n)) - (l : ZMod (l ^ n)) * b g) = χ g
    rw [map_sub, map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul, sub_zero, ZMod.natCast_zmod_val]

variable {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

end VLift

end RamanujanPetersson.CupDuality


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

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {σ : Representation Λ G Λ} {hσ : IsOpen (σ.ker : Set G)} (hv : H2Van σ Γ ⊤) {Gf : Type} [Group Gf]

/-! ## P0 -/

/-! ## P1: `Fun(Gf, Λ) ∘ π ≅ pushRep (ker π) Λ` -/

section Push

variable (π : G →* Gf) (K : Subgroup G)

theorem projP_equiv (hK : ∀ g, g ∈ K ↔ π g = 1) :
    IsEquivariant ((coindF (Λ := Λ) Λ).comp π) (pushRep K (Representation.trivial Λ K Λ)) (projP π K hK) :=
  fun g F => Subtype.ext (funext fun x => by
    show F ((π g)⁻¹ * (π x)⁻¹) = F (π (x * g))⁻¹
    rw [map_mul, mul_inv_rev])

theorem injP_equiv (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π) :
    IsEquivariant (pushRep K (Representation.trivial Λ K Λ)) ((coindF (Λ := Λ) Λ).comp π) (injP π K hs) :=
  fun g F' => funext fun y => by
    show (F' : G → Λ) (Function.surjInv hs y⁻¹ * g) = (F' : G → Λ) (Function.surjInv hs ((π g)⁻¹ * y)⁻¹)
    exact coindV_triv_eq π K hK F'
      (by rw [map_mul, Function.surjInv_eq hs, Function.surjInv_eq hs, mul_inv_rev, inv_inv])

theorem isOpen_push (hK : ∀ g, g ∈ K ↔ π g = 1) (hπ : IsOpen (π.ker : Set G)) :
    IsOpen ((pushRep K (Representation.trivial Λ K Λ)).ker : Set G) :=
  Subgroup.isOpen_mono (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    refine LinearMap.ext fun F' => Subtype.ext (funext fun x => ?_)
    show (F' : G → Λ) (x * g) = (F' : G → Λ) x
    exact coindV_triv_eq π K hK F' (by rw [map_mul, hg, mul_one])) hπ

end Push

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Dual =====
section

/-!
# S4-CurveDuality O7d-P2: the dual of a finite push-forward, and Shapiro on the dual side

Let `π : G →* Gf` be surjective onto a finite group with kernel `K` (the cover `f : V → U` with group `Gf`), and
`σ : Representation Λ G Λ` the twist `Λ(1)`. Then `(f_* Λ)^∨(1) ≅ f_* (σ|K)` as representations of `G`:
* `psiP : (coindV K Λ →ₗ Λ) → coindV K (σ|K)`, `φ ↦ (x ↦ σ x (φ δ_x))`, `δ_x` the indicator of the coset `K x`
  (`deltaP`); equivariant (`psiP_equiv`);
* `phiP` its inverse, `F' ↦ (F ↦ Σ_{y : Gf} F (s y) * σ (s y)⁻¹ (F' (s y)))` for a section `s` of `π`;
* `dualPushEquiv`: the equivariant isomorphism; `mapH1Equiv`: `H¹` of an equivariant linear isomorphism;
* `shapiroDual : H¹(Γ, (f_* Λ)^∨(1)) ≃ H¹(Γ ∩ K, σ|K)` (`hcov`, `K` open), `shapiroDual_mk`: on cocycles
  `d ↦ (h ↦ d h δ_K)`;
* `bijective_of_equiv_pair`: a duality map is bijective once it agrees, through isomorphisms on both sides, with a
  bijective one (used to move `alphaM` to the cover).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

/-! ## `H¹` of an equivariant linear isomorphism -/

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
  {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {ρ : Representation k G M} {ρ' : Representation k G N}

end Gen

/-! ## `(f_* Λ)^∨(1) ≅ f_* (σ|K)` -/

section Dual

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)

theorem deltaP_shift (g x : G) :
    pushRep K (Representation.trivial Λ K Λ) g⁻¹ (deltaP π K hK x) = deltaP π K hK (x * g) :=
  Subtype.ext (funext fun z => by
    show (if π (z * g⁻¹) = π x then (1 : Λ) else 0) = if π z = π (x * g) then 1 else 0
    simp only [map_mul, map_inv, mul_inv_eq_iff_eq_mul])

theorem psiP_equiv : IsEquivariant ((pushRep K (Representation.trivial Λ K Λ)).linHom σ)
    (pushRep K (σ.comp K.subtype)) (psiP σ π K hK) := fun g φ => Subtype.ext (funext fun x => by
  show σ x (((pushRep K (Representation.trivial Λ K Λ)).linHom σ g φ) (deltaP π K hK x)) =
    σ (x * g) (φ (deltaP π K hK (x * g)))
  rw [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, deltaP_shift, map_mul,
    Module.End.mul_apply])

theorem dualPushEquiv_equiv : IsEquivariant ((pushRep K (Representation.trivial Λ K Λ)).linHom σ)
    (pushRep K (σ.comp K.subtype)) (dualPushEquiv σ π K hK hs).toLinearMap :=
  psiP_equiv σ π K hK

/-! ## Shapiro on the dual side -/

variable (Γ : Subgroup G) (R : CosetReps Γ K)
  (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ) (hKo : IsOpen (K : Set G))

/-- **Shapiro on the dual side**: `H¹(Γ, (f_* Λ)^∨(1)) ≃ H¹(Γ ∩ K, σ|K)`. -/
def shapiroDual : H1 ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ ≃ₗ[Λ]
    H1 (σ.comp K.subtype) (geoU Γ K) :=
  (mapH1Equiv Γ (dualPushEquiv σ π K hK hs) (dualPushEquiv_equiv σ π K hK hs)).trans
    (shapiroH1Equiv (Γ := Γ) (H := K) (σ := σ.comp K.subtype) (R := R) (hcov := hcov) (hHo := hKo))

end Dual

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
theorem trP_equiv : IsEquivariant (pushRep K (σ.comp K.subtype)) σ (trP σ π K hs) := fun g F => by
  rw [trP_apply, trP_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (π g)) _ _ fun y => ?_
  simp only [Equiv.coe_mulRight]
  have e1 : π (Function.surjInv hs y * g) = π (Function.surjInv hs (y * π g)) := by
    rw [map_mul, Function.surjInv_eq hs, Function.surjInv_eq hs]
  have e2 : σ (Function.surjInv hs y)⁻¹ = σ g * σ (Function.surjInv hs y * g)⁻¹ := by
    rw [← map_mul]; congr 1; group
  show σ (Function.surjInv hs y)⁻¹ ((F : G → Λ) (Function.surjInv hs y * g)) =
    σ g (σ (Function.surjInv hs (y * π g))⁻¹ ((F : G → Λ) (Function.surjInv hs (y * π g))))
  rw [← hP_eq σ π K hK F e1, e2, Module.End.mul_apply]

theorem mulP_equiv (g : G) (F : Representation.coindV K.subtype (Representation.trivial Λ K Λ))
    (F' : Representation.coindV K.subtype (σ.comp K.subtype)) :
    mulP σ K (pushRep K (Representation.trivial Λ K Λ) g F) (pushRep K (σ.comp K.subtype) g F') =
      pushRep K (σ.comp K.subtype) g (mulP σ K F F') :=
  Subtype.ext (funext fun _ => rfl)

include hK in
theorem pushS_ker (g : G) (hg : g ∈ K) (hσg : σ g = 1) : g ∈ (pushRep K (σ.comp K.subtype)).ker := by
  rw [MonoidHom.mem_ker]
  refine LinearMap.ext fun F => Subtype.ext (funext fun x => ?_)
  show (F : G → Λ) (x * g) = (F : G → Λ) x
  have hk : x * g * x⁻¹ ∈ K :=
    (hK _).2 (by rw [map_mul, map_mul, (hK g).1 hg, mul_one, map_inv, mul_inv_cancel])
  have h1 := F.2 ⟨x * g * x⁻¹, hk⟩ x
  have hx : K.subtype ⟨x * g * x⁻¹, hk⟩ * x = x * g := by simp
  rw [hx] at h1
  rw [h1, MonoidHom.comp_apply]
  show σ (x * g * x⁻¹) ((F : G → Λ) x) = (F : G → Λ) x
  rw [map_mul, map_mul, hσg, mul_one, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

include hK in
theorem isOpen_pushS (hπ : IsOpen (π.ker : Set G)) (hσ : IsOpen (σ.ker : Set G)) :
    IsOpen ((pushRep K (σ.comp K.subtype)).ker : Set G) := by
  have hKo : IsOpen (K : Set G) := by
    have e : (K : Set G) = (π.ker : Set G) := Set.ext fun g => (hK g).trans MonoidHom.mem_ker.symm
    rw [e]; exact hπ
  refine Subgroup.isOpen_mono (show K ⊓ σ.ker ≤ (pushRep K (σ.comp K.subtype)).ker from
    fun g hg => pushS_ker σ π K hK g (Subgroup.mem_inf.1 hg).1
      (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).2)) ?_
  rw [Subgroup.coe_inf]
  exact hKo.inter hσ

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

/-- `u'(h) = U(h)(1)` on `Γ ∩ K`. -/
def uV (U : Γ → Representation.coindV K.subtype (σ.comp K.subtype)) : geoU Γ K → Λ :=
  fun h => ((U (geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1

theorem uV_apply (U : Γ → Representation.coindV K.subtype (σ.comp K.subtype)) (h : geoU Γ K) :
    uV U h = ((U (geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 := rfl

/-- **(1)** `u'` is a primitive of the `V`-level cup product. -/
theorem primV (p : Z1c (pushRep K (Representation.trivial Λ K Λ)) Γ I)
    (Dz : Z1 (pushRep K (σ.comp K.subtype)) Γ) (U : Γ → Representation.coindV K.subtype (σ.comp K.subtype))
    (hU : IsPrim (pushRep K (σ.comp K.subtype)) (pushRep K (σ.comp K.subtype)) (mulP σ K) Γ p.1.1 Dz.1 U) :
    IsPrim (σ.comp K.subtype) (σ.comp K.subtype) (LinearMap.mul Λ Λ) (geoU Γ K)
      (resEv Γ K (Representation.trivial Λ K Λ) p.1.1) (shapiroZ1 Γ K (σ.comp K.subtype) Dz).1 (uV U) := by
  refine ⟨(hU.1.comp_continuous (continuous_geoToΓ Γ K)).comp
    (fun F : Representation.coindV K.subtype (σ.comp K.subtype) => (F : G → Λ) 1), fun g h => ?_⟩
  have e : ((p.1.1 (geoToΓ Γ K g) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) 1 *
      ((Dz.1 (geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ)
        (1 * ((geoToΓ Γ K g : Γ) : G)) =
      ((U (geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ)
        (1 * ((geoToΓ Γ K g : Γ) : G)) -
      ((U (geoToΓ Γ K g * geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 +
      ((U (geoToΓ Γ K g) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 :=
    congrArg (fun F : Representation.coindV K.subtype (σ.comp K.subtype) => (F : G → Λ) 1)
      (hU.2 (geoToΓ Γ K g) (geoToΓ Γ K h))
  rw [one_mul, geoToΓ_coe, coind_apply_of_mem, coind_apply_of_mem, ← geoToΓ_mul] at e
  exact e

/-- **(2)** The key identity: the `G`-level boundary cochain at `x_t⁻¹ h x_t`, evaluated at `x_t`, is the `V`-level
boundary cochain at `h`. -/
theorem keyV (hD : ∀ (g : Γ) (v : Λ), σ g v = v) (hJ : InertiaLift Γ K I J πT xT)
    (p : Z1c (pushRep K (Representation.trivial Λ K Λ)) Γ I)
    (Dz : Z1 (pushRep K (σ.comp K.subtype)) Γ) (U : Γ → Representation.coindV K.subtype (σ.comp K.subtype))
    (hU : IsPrim (pushRep K (σ.comp K.subtype)) (pushRep K (σ.comp K.subtype)) (mulP σ K) Γ p.1.1 Dz.1 U)
    (t : T) (h : geoU Γ K) (hh : (h : K) ∈ J t) (g : Γ)
    (hg : (g : G) = (xT t : G)⁻¹ * ((h : K) : G) * xT t) :
    ((mulP σ K (p.1.2 (πT t)) (Dz.1 g) - U g : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ)
        (xT t) =
      ((shapiroZ1c Γ K (Representation.trivial Λ K Λ) I J πT xT hJ p : (geoU Γ K → Λ) × (T → Λ)).2 t) *
        (shapiroZ1 Γ K (σ.comp K.subtype) Dz : geoU Γ K → Λ) h - uV U h := by
  have hσh : ∀ v : Λ, (σ.comp K.subtype) (h : K) v = v := fun v => hD (geoToΓ Γ K h) v
  have hxg : xT t * g = geoToΓ Γ K h * xT t := Subtype.ext (by
    show ((xT t : Γ) : G) * (g : G) = ((h : K) : G) * ((xT t : Γ) : G)
    rw [hg]; group)
  have hc0 : ((p.1.1 (geoToΓ Γ K h) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) :
      G → Λ) 1 = 0 := by
    have e := ((mem_Z1c _ _ _ _).mp (shapiroZ1c Γ K (Representation.trivial Λ K Λ) I J πT xT hJ p).2).2 t h hh
    rw [Representation.trivial_apply, sub_self] at e
    exact e
  have a1 : ((Dz.1 (xT t * g) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 =
      ((Dz.1 (xT t) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 +
      ((Dz.1 g : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (1 * ((xT t : Γ) : G)) :=
    Z1_coind_apply Γ K (σ.comp K.subtype) Dz.2 (xT t) g 1
  have a2 := Z1_coind_apply Γ K (σ.comp K.subtype) Dz.2 (geoToΓ Γ K h) (xT t) 1
  rw [one_mul, geoToΓ_coe, coind_apply_of_mem, hσh] at a2
  rw [hxg, one_mul, a2] at a1
  have b1 : ((p.1.1 (xT t) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) 1 *
      ((Dz.1 g : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (1 * ((xT t : Γ) : G)) =
      ((U g : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (1 * ((xT t : Γ) : G)) -
      ((U (xT t * g) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 +
      ((U (xT t) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 :=
    congrArg (fun F : Representation.coindV K.subtype (σ.comp K.subtype) => (F : G → Λ) 1) (hU.2 (xT t) g)
  have b2 : ((p.1.1 (geoToΓ Γ K h) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) :
        G → Λ) 1 *
      ((Dz.1 (xT t) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ)
        (1 * ((geoToΓ Γ K h : Γ) : G)) =
      ((U (xT t) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ)
        (1 * ((geoToΓ Γ K h : Γ) : G)) -
      ((U (geoToΓ Γ K h * xT t) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 +
      ((U (geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 :=
    congrArg (fun F : Representation.coindV K.subtype (σ.comp K.subtype) => (F : G → Λ) 1)
      (hU.2 (geoToΓ Γ K h) (xT t))
  rw [hc0, zero_mul, one_mul, geoToΓ_coe, coind_apply_of_mem, hσh] at b2
  rw [one_mul, hxg] at b1
  show ((p.1.2 (πT t) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) (xT t) *
      ((Dz.1 g : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT t) -
      ((U g : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT t) =
    (((p.1.2 (πT t) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) (xT t) -
      ((p.1.1 (xT t) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) 1) *
      ((Dz.1 (geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1 -
      ((U (geoToΓ Γ K h) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) 1
  linear_combination
    (((p.1.1 (xT t) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) 1 -
      ((p.1.2 (πT t) : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) (xT t)) * a1 +
      b1 - b2

variable [Fintype T] [Nonempty T]

end ProjV

section ProjVDual

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)
  (Γ : Subgroup G)

/-- The pushed dual cocycle `psiP ∘ d ∈ Z¹(Γ, f_*(σ|K))`. -/
def dZ (d : Z1 ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ) : Z1 (pushRep K (σ.comp K.subtype)) Γ :=
  ⟨(psiP σ π K hK).compLeft Γ d.1, push_mem_Z1 Γ (psiP_equiv σ π K hK) d.2⟩

theorem dZ_apply (d : Z1 ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ) (g : Γ) :
    (dZ σ π K hK Γ d).1 g = psiP σ π K hK (d.1 g) := rfl

theorem shapiroDual_mk_eq (R : CosetReps Γ K) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ)
    (hKo : IsOpen (K : Set G)) (d : Z1 ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ) :
    shapiroDual σ π K hK hs Γ R hcov hKo (H1.mk ((pushRep K (Representation.trivial Λ K Λ)).linHom σ) Γ d) =
      H1.mk (σ.comp K.subtype) (geoU Γ K) (shapiroZ1 Γ K (σ.comp K.subtype) (dZ σ π K hK Γ d)) := rfl

end ProjVDual

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Trans =====
section

/-!
# S4-CurveDuality O7d-P3b T1: local traces are weighted `V`-level residues

`π : G →* Gf` finite quotient, `K = ker π`, `σ` a character of `G` trivial on `Γ`. For
`e ∈ Z¹(Γ ⊓ I s, f_*(σ|K))` put `E(g)(y) = σ(r)⁻¹ e(g)(r)` (`π r = y`, `EP`), so `trP (e g) = Σ_y E(g)(y)`.
* `sum_eq_sum_quot_zpowers`: `Σ_y f y = Σ_{q ∈ Gf ⧸ ⟨a⟩} Σ_{j < ord a} f (q.out a^j)`;
* `EP_mul`, `EP_pow`, `trP_eq_sum_quot`: `trP (e t) = Σ_q E(t^m)(q.out)`, `m = ord (π t)`;
* `Z1_conj_apply`: `e(g k g⁻¹)(x) = e(k)(x g)` for `k ∈ K`;
* `locZ`, `locZ_mem`: `Z'(h) = e(x⁻¹ h x)(x)` is a cocycle on `B ≤ K`;
* `eq_mul_of_constData`: under `V`'s `ConstData` every such cocycle is `Z'(t'_u) · ε_u`;
* **`trP_local`**, **`sum_trP_eq_lam`** (T1): weights `λ : T → Λ`, independent of `e`, with
  `Σ_s trP (e_s t_s) = Σ_u λ_u · e_{π u}(x_u⁻¹ t'_u x_u)(x_u)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Orbit

variable {Gf : Type} [Group Gf] [Fintype Gf] {M : Type} [AddCommMonoid M]

end Orbit

section Trans

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)

section Coc

variable {A : Subgroup G} (hA : ∀ (g : A) (v : Λ), σ g v = v)
  {e : A → Representation.coindV K.subtype (σ.comp K.subtype)} (he : e ∈ Z1 (pushRep K (σ.comp K.subtype)) A)

include hK hA he in
theorem EP_mul (g h : A) (y : Gf) :
    EP σ π K hs (e (g * h)) y = EP σ π K hs (e g) y + EP σ π K hs (e h) (y * π g) := by
  obtain ⟨r, hr⟩ := hs y
  have hrg : π (r * g) = y * π g := by rw [map_mul, hr]
  rw [EP_eq σ π K hK hs _ hr, EP_eq σ π K hK hs _ hr, EP_eq σ π K hK hs _ hrg,
    Z1_coind_apply A K (σ.comp K.subtype) he g h r, map_add, mul_inv_rev, map_mul, Module.End.mul_apply]
  congr 1
  exact (hA g⁻¹ _).symm

include hK hA he in
theorem EP_pow (g : A) (y : Gf) (n : ℕ) :
    EP σ π K hs (e (g ^ n)) y = ∑ j ∈ Finset.range n, EP σ π K hs (e g) (y * π g ^ j) := by
  induction n with
  | zero => rw [pow_zero, Z1_one _ _ he, Finset.sum_range_zero, EP_zero]
  | succ n ih =>
    rw [pow_succ g n, EP_mul σ π K hK hs hA he, ih, Finset.sum_range_succ,
      show ((g ^ n : A) : G) = (g : G) ^ n from rfl, map_pow]

include hK hA he in
theorem trP_eq_sum_quot (g : A) :
    trP σ π K hs (e g) =
      ∑ q : Gf ⧸ Subgroup.zpowers (π g), EP σ π K hs (e (g ^ orderOf (π g))) q.out := by
  rw [trP_eq_sum_EP, sum_eq_sum_quot_zpowers (π g)]
  exact Finset.sum_congr rfl fun q _ => (EP_pow σ π K hK hs hA he g q.out _).symm

include hA he in
theorem Z1_conj_apply (hKn : K.Normal) (g k : A) (hk : (k : G) ∈ K) (x : G) :
    ((e (g * k * g⁻¹) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) x =
      ((e k : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (x * g) := by
  have h2 := Z1_coind_apply A K (σ.comp K.subtype) he g g⁻¹ x
  rw [mul_inv_cancel, Z1_one _ _ he] at h2
  have h0 : ((0 : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) x = 0 := rfl
  rw [h0] at h2
  have hm : x * (g : G) * (k : G) * (x * (g : G))⁻¹ ∈ K := hKn.conj_mem _ hk _
  have hk1 : σ (k : G) = 1 := LinearMap.ext (hA k)
  have hσ1 : σ (x * (g : G) * (k : G) * (x * (g : G))⁻¹) = 1 := by
    rw [map_mul, map_mul, hk1, mul_one, ← map_mul σ, mul_inv_cancel, map_one]
  have h1 : ((e g⁻¹ : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (x * ((g * k : A) : G)) =
      ((e g⁻¹ : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (x * g) := by
    have hx : x * ((g * k : A) : G) =
        ((⟨x * (g : G) * (k : G) * (x * (g : G))⁻¹, hm⟩ : K) : G) * (x * g) := by
      show x * ((g : G) * (k : G)) = x * (g : G) * (k : G) * (x * (g : G))⁻¹ * (x * g)
      group
    rw [hx, coind_mul_apply]
    show σ (x * (g : G) * (k : G) * (x * (g : G))⁻¹) _ = _
    rw [hσ1, Module.End.one_apply]
  rw [Z1_coind_apply A K (σ.comp K.subtype) he, Z1_coind_apply A K (σ.comp K.subtype) he, h1]
  linear_combination -h2

include he in
theorem locZ_mem (x : G) (B : Subgroup K) (hB : ∀ h : B, x⁻¹ * ((h : K) : G) * x ∈ A) :
    locZ σ K x B hB e ∈ Z1 (σ.comp K.subtype) B := by
  refine (mem_Z1 _ _ _).mpr ⟨?_, fun h1 h2 => ?_⟩
  · have hc : Continuous (fun h : B => (⟨x⁻¹ * ((h : K) : G) * x, hB h⟩ : A)) :=
      ((continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
        continuous_const).subtype_mk _
    exact (((mem_Z1 _ _ e).mp he).1.comp_continuous hc).comp
      (fun F : Representation.coindV K.subtype (σ.comp K.subtype) => (F : G → Λ) x)
  · have hsplit : (⟨x⁻¹ * (((h1 * h2 : B) : K) : G) * x, hB (h1 * h2)⟩ : A) =
        ⟨x⁻¹ * ((h1 : K) : G) * x, hB h1⟩ * ⟨x⁻¹ * ((h2 : K) : G) * x, hB h2⟩ :=
      Subtype.ext (by
        show x⁻¹ * (((h1 : K) : G) * ((h2 : K) : G)) * x =
          x⁻¹ * ((h1 : K) : G) * x * (x⁻¹ * ((h2 : K) : G) * x)
        group)
    have hx : x * ((⟨x⁻¹ * ((h1 : K) : G) * x, hB h1⟩ : A) : G) = ((h1 : K) : G) * x := by
      show x * (x⁻¹ * ((h1 : K) : G) * x) = _
      group
    have key := Z1_coind_apply A K (σ.comp K.subtype) he ⟨x⁻¹ * ((h1 : K) : G) * x, hB h1⟩
      ⟨x⁻¹ * ((h2 : K) : G) * x, hB h2⟩ x
    rw [← hsplit, hx, coind_mul_apply] at key
    exact key

end Coc

theorem eq_mul_of_constData {Γ : Subgroup G} {T : Type} [Fintype T] {J : T → Subgroup K}
    {t' : (u : T) → ↥(geoU Γ K ⊓ J u)} (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t') (u : T)
    (z : ↥(geoU Γ K ⊓ J u) → Λ) (hz : z ∈ Z1 (σ.comp K.subtype) (geoU Γ K ⊓ J u))
    (ε : Z1 (σ.comp K.subtype) (geoU Γ K ⊓ J u)) (hε : (ε : ↥(geoU Γ K ⊓ J u) → Λ) (t' u) = 1)
    (h : ↥(geoU Γ K ⊓ J u)) :
    z h = z (t' u) * (ε : ↥(geoU Γ K ⊓ J u) → Λ) h := by
  have h0 := DV.inj u (⟨z, hz⟩ - z (t' u) • ε) (by
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hε,
      mul_one, sub_self])
  have h1 := congrArg (fun w : Z1 (σ.comp K.subtype) (geoU Γ K ⊓ J u) =>
    (w : ↥(geoU Γ K ⊓ J u) → Λ) h) h0
  simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_zero, Pi.zero_apply] at h1
  exact sub_eq_zero.mp h1

section Local

variable {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {T : Type} [Fintype T]
  {J : T → Subgroup K} {πT : T → S} {xT : T → Γ}

theorem conj_mem_inf (hJ : InertiaLift Γ K I J πT xT) (v : T) (h : ↥(geoU Γ K ⊓ J v)) :
    ((xT v : Γ) : G)⁻¹ * ((h : K) : G) * (xT v : G) ∈ Γ ⊓ I (πT v) :=
  Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (xT v).2)
    (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 h.2).1)) (xT v).2,
    (hJ v ⟨h, (Subgroup.mem_inf.1 h.2).1⟩).1 (Subgroup.mem_inf.1 h.2).2⟩

/-- `x_u⁻¹ t'_u x_u ∈ Γ ⊓ I (π u)`. -/
def gI (hJ : InertiaLift Γ K I J πT xT) (t' : (u : T) → ↥(geoU Γ K ⊓ J u)) (u : T) : ↥(Γ ⊓ I (πT u)) :=
  ⟨((xT u : Γ) : G)⁻¹ * ((t' u : K) : G) * (xT u : G), conj_mem_inf K hJ u (t' u)⟩

variable {t' : (u : T) → ↥(geoU Γ K ⊓ J u)}

include hK in
/-- **T1, one boundary point `s` of `U`.** -/
theorem trP_local (hD : ∀ (g : Γ) (v : Λ), σ g v = v) (hJ : InertiaLift Γ K I J πT xT)
    (hDC : DCover Γ K I πT xT) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ)
    (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t') (s : S) (ts : ↥(Γ ⊓ I s)) :
    ∃ lam : T → Λ, (∀ u, πT u ≠ s → lam u = 0) ∧
      ∀ e : Z1 (pushRep K (σ.comp K.subtype)) (Γ ⊓ I s),
        trP σ π K hs ((e : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype)) ts) =
          ∑ u, lam u * ((extZ σ K (e : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype))
            (((xT u : Γ) : G)⁻¹ * ((t' u : K) : G) * (xT u : G)) : G → Λ) (xT u)) := by
  classical
  have hKn : K.Normal := ⟨fun n hn g => (hK _).2 (by
    rw [map_mul, map_mul, map_inv, (hK n).1 hn, mul_one, mul_inv_cancel])⟩
  have hA : ∀ (g : ↥(Γ ⊓ I s)) (v : Λ), σ g v = v := fun g v => hD ⟨g, (Subgroup.mem_inf.1 g.2).1⟩ v
  have hγ : ∀ q : Gf ⧸ Subgroup.zpowers (π (ts : G)), ∃ γ : Γ, π (γ : G) = q.out := fun q => by
    obtain ⟨h, γ, hx⟩ := hcov (Function.surjInv hs q.out)
    refine ⟨γ, ?_⟩
    have e1 := congrArg π hx
    rw [Function.surjInv_eq hs, map_mul, (hK _).1 h.2, one_mul] at e1
    exact e1.symm
  choose γ hγ using hγ
  have hdc : ∀ q : Gf ⧸ Subgroup.zpowers (π (ts : G)), ∃ u : T, πT u = s ∧ ∃ (h : geoU Γ K) (g : Γ),
      (g : G) ∈ I s ∧ ((γ q : Γ) : G) = ((h : K) : G) * xT u * g := fun q => hDC s (γ q)
  choose u hu h' g hg hγe using hdc
  obtain ⟨gA, hgA⟩ : ∃ gA : Gf ⧸ Subgroup.zpowers (π (ts : G)) → ↥(Γ ⊓ I s),
      ∀ q, ((gA q : ↥(Γ ⊓ I s)) : G) = (g q : G) :=
    ⟨fun q => ⟨g q, Subgroup.mem_inf.2 ⟨(g q).2, hg q⟩⟩, fun q => rfl⟩
  obtain ⟨tm, htm⟩ : ∃ tm : ↥(Γ ⊓ I s), tm = ts ^ orderOf (π (ts : G)) := ⟨_, rfl⟩
  have htmK : (tm : G) ∈ K := by
    rw [htm]
    exact (hK _).2 (by rw [show ((ts ^ orderOf (π (ts : G)) : ↥(Γ ⊓ I s)) : G) =
      (ts : G) ^ orderOf (π (ts : G)) from rfl, map_pow, pow_orderOf_eq_one])
  obtain ⟨w, hw⟩ : ∃ w : Gf ⧸ Subgroup.zpowers (π (ts : G)) → K, ∀ q, ((w q : K) : G) =
      (xT (u q) : G) * ((gA q * tm * (gA q)⁻¹ : ↥(Γ ⊓ I s)) : G) * ((xT (u q) : Γ) : G)⁻¹ :=
    ⟨fun q => ⟨(xT (u q) : G) * ((gA q * tm * (gA q)⁻¹ : ↥(Γ ⊓ I s)) : G) * ((xT (u q) : Γ) : G)⁻¹,
      hKn.conj_mem _ (hKn.conj_mem (tm : G) htmK (gA q : G)) _⟩, fun q => rfl⟩
  have hwB : ∀ q, w q ∈ geoU Γ K ⊓ J (u q) := fun q => by
    have hY := (gA q * tm * (gA q)⁻¹).2
    have hgeo : w q ∈ geoU Γ K := Subgroup.mem_subgroupOf.2 (by
      rw [hw q]
      exact Γ.mul_mem (Γ.mul_mem (xT (u q)).2 (Subgroup.mem_inf.1 hY).1) (Γ.inv_mem (xT (u q)).2))
    refine Subgroup.mem_inf.2 ⟨hgeo, (hJ (u q) ⟨w q, hgeo⟩).2 ?_⟩
    show ((xT (u q) : Γ) : G)⁻¹ * ((w q : K) : G) * (xT (u q) : G) ∈ I (πT (u q))
    rw [hu q, hw q, show ∀ a b : G, a⁻¹ * (a * b * a⁻¹) * a = b from fun a b => by group]
    exact (Subgroup.mem_inf.1 hY).2
  choose ε hε using fun v => DV.surj v 1
  refine ⟨fun v => ∑ q ∈ Finset.univ.filter (fun q => u q = v),
    extL K (ε (u q) : ↥(geoU Γ K ⊓ J (u q)) → Λ) (w q), fun v hv => ?_, fun e => ?_⟩
  · refine Finset.sum_eq_zero fun q hq => ?_
    exact (hv ((Finset.mem_filter.1 hq).2 ▸ hu q)).elim
  have key : ∀ q, EP σ π K hs ((e : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype)) tm)
      q.out = extL K (ε (u q) : ↥(geoU Γ K ⊓ J (u q)) → Λ) (w q) *
        ((extZ σ K (e : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype))
          (((xT (u q) : Γ) : G)⁻¹ * ((t' (u q) : K) : G) * (xT (u q) : G)) : G → Λ) (xT (u q))) := by
    intro q
    have hB : ∀ h : ↥(geoU Γ K ⊓ J (u q)), ((xT (u q) : Γ) : G)⁻¹ * ((h : K) : G) * (xT (u q) : G) ∈
        Γ ⊓ I s := fun h => hu q ▸ conj_mem_inf K hJ (u q) h
    have hz : gA q * tm * (gA q)⁻¹ =
        ⟨((xT (u q) : Γ) : G)⁻¹ * ((w q : K) : G) * (xT (u q) : G), hB ⟨w q, hwB q⟩⟩ :=
      Subtype.ext (by
        show ((gA q * tm * (gA q)⁻¹ : ↥(Γ ⊓ I s)) : G) =
          ((xT (u q) : Γ) : G)⁻¹ * ((w q : K) : G) * (xT (u q) : G)
        rw [hw q]
        group)
    have h1 : EP σ π K hs ((e : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype)) tm)
        q.out = locZ σ K (xT (u q) : G) (geoU Γ K ⊓ J (u q)) hB e ⟨w q, hwB q⟩ := by
      rw [EP_eq σ π K hK hs _ (hγ q), show σ ((γ q : Γ) : G)⁻¹ = 1 from LinearMap.ext (hD (γ q)⁻¹),
        Module.End.one_apply, hγe q,
        show ((h' q : K) : G) * (xT (u q) : G) * (g q : G) = ((h' q : K) : G) * ((xT (u q) : G) * (g q : G))
          from mul_assoc _ _ _, coind_mul_apply,
        show (σ.comp K.subtype) ((h' q : geoU Γ K) : K) = 1 from LinearMap.ext (hD (geoToΓ Γ K (h' q))),
        Module.End.one_apply, ← hgA q, ← Z1_conj_apply σ K hA e.2 hKn (gA q) tm htmK, hz]
      rfl
    rw [h1, eq_mul_of_constData σ K DV (u q) _ (locZ_mem σ K e.2 _ _ hB) (ε (u q)) (hε (u q))
      ⟨w q, hwB q⟩, extL_of_mem K _ (hwB q), extZ_of_mem σ K _ (hB (t' (u q)))]
    exact mul_comm _ _
  rw [trP_eq_sum_quot σ π K hK hs hA e.2 ts, ← htm, Finset.sum_congr rfl fun q _ => key q,
    ← Finset.sum_fiberwise Finset.univ u]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [(Finset.mem_filter.1 hq).2]

include hK in
/-- **T1**: `Σ_s trP (e_s t_s) = Σ_u λ_u · e_{π u}(x_u⁻¹ t'_u x_u)(x_u)` with `λ` independent of `e`. -/
theorem sum_trP_eq_lam [Fintype S] (hD : ∀ (g : Γ) (v : Λ), σ g v = v) (hJ : InertiaLift Γ K I J πT xT)
    (hDC : DCover Γ K I πT xT) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ)
    (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t') (t : (s : S) → ↥(Γ ⊓ I s)) :
    ∃ lam : T → Λ, ∀ e : (s : S) → Z1 (pushRep K (σ.comp K.subtype)) (Γ ⊓ I s),
      ∑ s, trP σ π K hs ((e s : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype)) (t s)) =
        ∑ u, lam u * (((e (πT u) : ↥(Γ ⊓ I (πT u)) → Representation.coindV K.subtype (σ.comp K.subtype))
          (gI K hJ t' u) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT u) := by
  classical
  choose lam hlam0 hlam using fun s => trP_local σ π K hK hs hD hJ hDC hcov DV s (t s)
  refine ⟨fun u => lam (πT u) u, fun e => ?_⟩
  rw [Finset.sum_congr rfl fun s _ => hlam s (e s), Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single (πT u) (fun s _ hs => by rw [hlam0 s u (Ne.symm hs), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), extZ_of_mem σ K _ (conj_mem_inf K hJ u (t' u))]
  rfl

end Local

end Trans

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

theorem h2van_comp {L : Type} [AddCommGroup L] [Module k L] {σ₁ : Representation k G₁ L}
    {σ₂ : Representation k G₂ L} (h : Intw σ₁ σ₂ e) (hv : H2Van σ₂ Δ₂ ⊤) : H2Van σ₁ Δ₁ ⊤ := by
  intro f hf _ hc
  have h' := h.symm
  obtain ⟨b, hb, -, hfb⟩ := hv (fun x => f (e.symm x.1, e.symm x.2))
    (hf.comp_continuous ((map_continuous e.symm).prodMap (map_continuous e.symm)))
    (fun _ => Submodule.mem_top) (fun a a' a'' => by
      simp only [map_mul]
      rw [h' a]
      exact hc _ _ _)
  refine ⟨b ∘ e, hb.comp_continuous (map_continuous e), fun _ => Submodule.mem_top, fun g j => ?_⟩
  have := hfb (e g) (e j)
  simp only [ContinuousMulEquiv.symm_apply_apply] at this
  rw [this, h g]
  simp only [Function.comp_apply, map_mul]

variable {M M' L : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] [AddCommGroup L]
  [Module k L] {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M}
  {ρ₁' : Representation k G₁ M'} {ρ₂' : Representation k G₂ M'}
  {σ₁ : Representation k G₁ L} {σ₂ : Representation k G₂ L} {β : M →ₗ[k] M' →ₗ[k] L}

theorem isPrim_tr (h' : Intw ρ₁' ρ₂' e) (hσ : Intw σ₁ σ₂ e) {c : Δ₁ → M} {d : Δ₁ → M'} {u : Δ₁ → L}
    (hu : IsPrim ρ₁' σ₁ β Δ₁ c d u) : IsPrim ρ₂' σ₂ β Δ₂ (c ∘ e.symm) (d ∘ e.symm) (u ∘ e.symm) := by
  refine ⟨hu.1.comp_continuous (map_continuous e.symm), fun g j => ?_⟩
  have := hu.2 (e.symm g) (e.symm j)
  simp only [cupCochain, Function.comp_apply, map_mul] at this ⊢
  rw [h'.symm g, hσ.symm g]
  exact this

variable {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

end AmbCup

/-! ## The duality map `α` -/

section Alpha

variable {Λ : Type} [CommRing Λ] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁}
  {I₂ : S → Subgroup G₂} {σ₁ : Representation Λ G₁ Λ} {σ₂ : Representation Λ G₂ Λ}
  {hσ₁ : IsOpen (σ₁.ker : Set G₁)} {hσ₂ : IsOpen (σ₂.ker : Set G₂)}
  {M : Type} [AddCommGroup M] [Module Λ M]

end Alpha

/-! ## Constant coefficients -/

section Const

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁}
  {I₂ : S → Subgroup G₂} {σ₁ : Representation k G₁ k} {σ₂ : Representation k G₂ k}

theorem tG_tr (hI : IntwI I₁ I₂ e) (t₁ : (s : S) → ↥(Δ₁ ⊓ I₁ s)) (s : S) :
    tG (fun s => infTr hI s (t₁ s)) s = e (tG t₁ s) := rfl

variable [Fintype S]

theorem constData_tr' (hσ : Intw σ₁ σ₂ e) (hI : IntwI I₁ I₂ e) {t₁ : (s : S) → ↥(Δ₁ ⊓ I₁ s)}
    (D : ConstData σ₁ Δ₁ I₁ t₁) : ConstData σ₂ Δ₂ I₂ (fun s => infTr hI s (t₁ s)) where
  triv g x := by
    rw [hσ.symm g]
    exact D.triv _ x
  inj s c hc := (LinearEquiv.map_eq_zero_iff (z1Tr (hσ.inf hI s)).symm).1 (D.inj s _ hc)
  surj s a := by
    obtain ⟨c, hc⟩ := D.surj s a
    refine ⟨z1Tr (hσ.inf hI s) c, ?_⟩
    show (c : ↥(Δ₁ ⊓ I₁ s) → k) ((infTr hI s).symm (infTr hI s (t₁ s))) = a
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact hc
  resSum d := D.resSum ((z1Tr hσ).symm d)
  resOnto r hr := by
    obtain ⟨d, hd⟩ := D.resOnto r hr
    refine ⟨z1Tr hσ d, fun s => ?_⟩
    show (d : Δ₁ → k) (e.symm (e (tG t₁ s))) = r s
    rw [ContinuousMulEquiv.symm_apply_apply]
    exact hd s

variable [Nonempty S]

end Const

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_AmbRes =====
section

/-!
# S4-CurveDuality O7d-P1d (T4): restricting the cover data to a subgroup `H ⊇ Γ, K`

For `Γ, K ≤ H ≤ G` the groups `Γ₁ = Γ.subgroupOf H`, `K₁ = K.subgroupOf H` and `I₁ s = (I s).subgroupOf H` carry
the same data as `Γ, K, I`:
* `eSub : Γ.subgroupOf H ≃ₜ* Γ` and `eGeo : geoU Γ₁ K₁ ≃ₜ* geoU Γ K`, intertwining the restricted representations
  (`intw_sub`, `intw_geo`) and boundary subgroups (`intwI_sub`, `intwI_geo` with `J₁ t = (J t).comap (kMap K)`);
* `inertiaLift_sub`, `dCover_sub`, `dDisj_sub`: the Shapiro data transported to `H`;
* `inf_subgroupOf'`: `(A ⊓ B).subgroupOf H = A.subgroupOf H ⊓ B.subgroupOf H`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Res

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}

/-- `geoU (Γ.subgroupOf H) (K.subgroupOf H) ≃ₜ* geoU Γ K` for `K ≤ H`. -/
def eGeo (Γ K : Subgroup G) (hK : K ≤ H) : geoU (Γ.subgroupOf H) (K.subgroupOf H) ≃ₜ* geoU Γ K where
  toFun a := ⟨⟨(((a : K.subgroupOf H) : H) : G), (a : K.subgroupOf H).2⟩, a.2⟩
  invFun b := ⟨⟨⟨((b : K) : G), hK (b : K).2⟩, (b : K).2⟩, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val) _) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _) _) _

variable {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]

theorem intw_geo (σ : Representation k G M) (Γ K : Subgroup G) (hK : K ≤ H) :
    Intw ((σ.comp H.subtype).comp (K.subgroupOf H).subtype) (σ.comp K.subtype) (eGeo Γ K hK) := fun _ => rfl

theorem intwI_geo {T : Type} (Γ K : Subgroup G) (hK : K ≤ H) (J : T → Subgroup K) :
    IntwI (fun t => (J t).comap (kMap K)) J (eGeo Γ K hK) := fun _ _ => Iff.rfl

variable {S T : Type} {Γ K : Subgroup G} {I : S → Subgroup G} {J : T → Subgroup K} {πT : T → S} {xT : T → Γ}

theorem inertiaLift_sub (hΓ : Γ ≤ H) (hK : K ≤ H) (hJ : InertiaLift Γ K I J πT xT) :
    InertiaLift (Γ.subgroupOf H) (K.subgroupOf H) (fun s => (I s).subgroupOf H) (fun t => (J t).comap (kMap K))
      πT (fun t => toSubOf hΓ (xT t)) :=
  fun t h => hJ t (eGeo Γ K hK h)

theorem dCover_sub (hΓ : Γ ≤ H) (hK : K ≤ H) (hDC : DCover Γ K I πT xT) :
    DCover (Γ.subgroupOf H) (K.subgroupOf H) (fun s => (I s).subgroupOf H) πT (fun t => toSubOf hΓ (xT t)) := by
  intro s y
  obtain ⟨t, ht, h, g, hg, hy⟩ := hDC s (ofSubOf y)
  exact ⟨t, ht, (eGeo Γ K hK).symm h, toSubOf hΓ g, hg, Subtype.ext hy⟩

theorem dDisj_sub (hΓ : Γ ≤ H) (hK : K ≤ H) (hDD : DDisj Γ K I πT xT) :
    DDisj (Γ.subgroupOf H) (K.subgroupOf H) (fun s => (I s).subgroupOf H) πT (fun t => toSubOf hΓ (xT t)) :=
  fun t t' hπ h g hg he => hDD t t' hπ (eGeo Γ K hK h) (ofSubOf g) hg (congrArg Subtype.val he)

end Res

end

end CupDuality
end RamanujanPetersson


end


