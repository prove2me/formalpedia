-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_06
-- name    : RPLib_FX_LisseDual_06
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T04:47:44.470384+00:00
-- url     : https://prove2.me/theorems/e0531d20-6fec-498b-b716-3050f23c61de
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, library file 06 of 7
-- statement:
--   File 06 of 7 of the lisse duality library for affine curves over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CupDuality_VS3b`: S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart
--   * `S4.Def_RP_CupDuality_VFinal`: S4-CurveDuality, O9b (Route G at `V`) part 10: `V`'s parabolic block is perfect (S3 chart)
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_F2_043
import Definitions.Def_RPLib_FX_LisseDual_05

/-!
# Poincaré duality with lisse coefficients on an affine curve over a finite field, library file 06 of 7

Declarations of the formalization of Poincaré duality for H¹ with lisse (finite, twisted) coefficients on an
affine curve over a finite field (the cochain duality map `alphaM` is bijective), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CupDuality_VS3b`: S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart
* `S4.Def_RP_CupDuality_VFinal`: S4-CurveDuality, O9b (Route G at `V`) part 10: `V`'s parabolic block is perfect (S3 chart)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CupDuality_VS3b =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart

For an open subgroup `K` of `π₁(U)` (the cover `V`, `K = ker π`):
* `hbasis_S3`: open normal subgroups form a basis at `1` in `π₁(U)` (Krull topology);
* `hallV_S3`, `hallIV_S3`: `H²(Γ_V, -) = 0` and `H²(Γ_V ∩ I_V(t), -) = 0` at `V` (`h2All_closed` for the closed
  subgroups `Γ ∩ K` and `K ∩ x_t (Γ ∩ I_s) x_t⁻¹`, then `h2All_subgroupOf`);
* **`hcount_S3`**: `H²(K)(ρ) ≃ H²_c(ρ)` at `V` for every finite `ρ` with open kernel: a finer unramified cover `L` with
  `ker(π₁ ↠ Gal(L/F)) ⊆ ker ρ` (`exists_resL_ker_le`), its residue data (`exists_resDat_tw`), then `vCount`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

attribute [local instance] GalCover.grp GalCover.fG

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **The `H²` count at `V`** in the S3 chart: `H²(K)(ρ, Γ_V, I_V) ≃ H²_c(ρ, Γ_V)` for finite `ρ`, open kernel. -/
theorem hcount_S3 {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Gf : Type} [Group Gf] {π : Pi1 (Places.Rfin Fq F) F →* Gf}
    (hπ : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F))) {T : Type} [Fintype T] [DecidableEq T]
    [Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π)]
    (RD : ResDat π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia (l ^ n) T)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (hallV : H2All Λ π.ker (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker) l n)
    (hallIV : ∀ t, H2All Λ π.ker (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker ⊓ rdJ RD π.ker t) l n)
    {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (ρ : Representation Λ π.ker M)
    (hρ : IsOpen (ρ.ker : Set π.ker)) :
    Nonempty (H2K ρ (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker) (rdJ RD π.ker) hρ ≃ₗ[Λ]
      H2c ρ (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker)) := by
  classical
  have hK : ∀ g, g ∈ π.ker ↔ π g = 1 := fun _ => MonoidHom.mem_ker
  have hW : IsOpen ((ρ.ker.map π.ker.subtype : Subgroup _) : Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hπ.isOpenMap_subtype_val _ hρ
  obtain ⟨L, hL, hk⟩ := EtSheaves.TorSec.exists_resL_ker_le (Places.Rfin Fq F) F _ hW
  have hK2 : ∀ g, EtSheaves.TorSec.resL (Places.Rfin Fq F) F L hL g = 1 → g ∈ π.ker := fun g hg => by
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 (hk (MonoidHom.mem_ker.2 hg))
    exact x.2
  have hρ2 : ∀ g : π.ker, EtSheaves.TorSec.resL (Places.Rfin Fq F) F L hL (g : Pi1 (Places.Rfin Fq F) F) = 1 →
      ρ g = 1 := fun g hg => by
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 (hk (MonoidHom.mem_ker.2 hg))
    have hxe : x = g := Subtype.ext hxg
    rw [← hxe]
    exact MonoidHom.mem_ker.1 hx
  let _ : Fintype (CosT (EtSheaves.TorSec.resL (Places.Rfin Fq F) F L hL)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Fintype.ofFinite _
  have hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (D.P s) := fun s => (hDB _).1 (D.mem s)
  have hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • D.P s :=
    fun Q hQ => D.cover Q ((hDB Q).2 hQ)
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨D2, -⟩ := exists_resDat_tw hq he hNF hPic hL (EtSheaves.TorSec.le_maxUnram (Places.Rfin Fq F) F L hL)
    (EtSheaves.TorSec.resL (Places.Rfin Fq F) F L hL) (resL_eq_one_iff L hL) D.P hP hcov D.disj D.inertia
    (fun _ => rfl)
  exact vCount RD D2 π.ker hK hK2 (EtSheaves.TorSec.isOpen_ker_resL (Places.Rfin Fq F) F L hL) hΛ hΛ
    hallV hallIV ρ hρ hρ2

end S3

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VFinal =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 10: `V`'s parabolic block is perfect (S3 chart)

For a finite quotient `π : π₁(U) → Gf` with open kernel `K` (the cover `V`) and residue data `RD` of level `lⁿ`,
the parabolic block of `V`'s constant pairing (`rdCupHyp`, `rdConstData`) is perfect over any finite `Λ` with
`lⁿ = 0` (**`parabolicPerfect_V_S3`**, the hypothesis `hB` of `lisse_bijective`). It carries the finiteness of the
`ℤ/l`-valued parabolic homomorphisms of `V` (`[Finite (parMod ..)]`, Route L) besides `hPicU`, `hPic`.
Proof: `parabolic_of_count` at the ambient group `K`, with the count `hcount_S3`, the basis `hbasis_S3`, the density
`exists_dens_sub` (from a Frobenius lift), and `V`'s boundary data `vBdry` at `φ_V⁻¹` and `φ_V`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

attribute [local instance] GalCover.grp GalCover.fG

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **O9b.** The parabolic block of the cover `V = ker π` is perfect in the S3 chart, for any finite `Λ` with
`lⁿ = 0` and any character `σ` trivial on `π₁^geo`: this is `hB` of `lisse_bijective`. -/
theorem parabolicPerfect_V_S3 (hk : Places.constField Fq F = ⊥) {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) [NeZero (l ^ n)]
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Gf : Type} [Group Gf] [Finite Gf] {π : Pi1 (Places.Rfin Fq F) F →* Gf}
    (hπ : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    {T : Type} [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π)]
    (RD : ResDat π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia (l ^ n) T)
    [Finite ↥(parMod (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker) (rdJ RD π.ker) l)]
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ) (hσ : IsOpen (σ.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    (htriv : ∀ (g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (x : Λ), σ g x = x)
    (hv : H2Van σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) ⊤) :
    ParabolicPerfect (rdCupHyp π.ker σ hσ hv) (rdConstData RD π.ker (fun _ => MonoidHom.mem_ker) σ htriv hΛ) := by
  classical
  letI : MulAction (Pi1 (Places.Rfin Fq F) F) (Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) :=
    Residue.instMA (Places.Rfin Fq F) F (Places.Rinf Fq F)
  have hK : ∀ g, g ∈ π.ker ↔ π g = 1 := fun _ => MonoidHom.mem_ker
  have : CompactSpace π.ker := compactSpace_of_isOpen π.ker hπ
  have hbasis := hbasis_subgroup hbasis_S3 π.ker
  -- density at `V`
  obtain ⟨φ, hφ⟩ := exists_frobLift hk hq he
  have hd : ∀ N : Subgroup (Pi1 (Places.Rfin Fq F) F), IsOpen (N : Set (Pi1 (Places.Rfin Fq F) F)) →
      ∀ r : Pi1 (Places.Rfin Fq F) F, ∃ j : ℕ, ∃ γ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        ∃ m ∈ N, r = φ ^ j * γ * m :=
    fun N hN r => exists_frobPow_mul hφ N hN r
  obtain ⟨φV, hdens⟩ := exists_dens_sub hd π π.ker hK hπ
  -- boundary data at `V`
  have hcov : ∀ (a : Pi1 (Places.Rfin Fq F) F) (s : S), ∃ u, ∃ h ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      a⁻¹ • D.P s = h • D.P u := fun a s => bdry_exists_true D a s
  have hin : ∀ (g : Pi1 (Places.Rfin Fq F) F) (s u : S), D.P u = g⁻¹ • D.P s →
      ∀ x, x ∈ D.inertia u ↔ g * x * g⁻¹ ∈ D.inertia s := fun _ _ _ h x => inert_conj_iff h x
  have hfix : ∀ s, ∀ g ∈ D.inertia s, g • D.P s = D.P s := fun s g hg => stabI_gen (D.P s) g hg
  have hstab : ∀ s, ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), g • D.P s = D.P s →
      g ∈ D.inertia s :=
    fun s g hg hf => Lefschetz.stab_mem_inertia_K Fq F hq he (D.P s) ((hDB _).1 (D.mem s)) g hg hf
  obtain ⟨τ, h, hI, hτ, hex⟩ := vBdry RD π.ker hK D.P hcov hin hfix D.disj hstab φV⁻¹
  obtain ⟨τ2, h2, hI2, -, -⟩ := vBdry RD π.ker hK D.P hcov hin hfix D.disj hstab φV
  -- the `ℤ/lⁿ` data with trivial character
  let σ0 := Representation.trivial (ZMod (l ^ n)) (Pi1 (Places.Rfin Fq F) F) (ZMod (l ^ n))
  have hσ0 : IsOpen (σ0.ker : Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [show σ0.ker = ⊤ from eq_top_iff.2 fun g _ => MonoidHom.mem_ker.2 (LinearMap.ext fun _ => rfl),
      Subgroup.coe_top]
    exact isOpen_univ
  have hΛ0 : ((l ^ n : ℕ) : ZMod (l ^ n)) = 0 := ZMod.natCast_self _
  have hL0 : ∀ m : ZMod (l ^ n), (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ n)), hΛ0, zero_smul]
  have : Finite (Pi1 (Places.Rfin Fq F) F ⧸ π.ker) := Subgroup.quotient_finite_of_isOpen _ hπ
  have hcl : IsClosed ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker : Subgroup _) :
      Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [Subgroup.coe_inf]
    exact (pi1geo_isClosed _ _ _).inter (π.ker.isClosed_of_isOpen hπ)
  have hall0 := CdOne.h2All_closed (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU _ hcl inf_le_left (ZMod (l ^ n)) n
  have H0 := rdCupHyp π.ker σ0 hσ0 (h2Van_top_of_all hall0 hL0 hσ0)
  have D0 := rdConstData RD π.ker hK σ0 (fun _ _ => rfl) hΛ0
  have hcount : ∀ {ι : Type} [Fintype ι]
      (ρ : Representation (ZMod (l ^ n)) π.ker ((ι → ZMod (l ^ n)) × (ι → ZMod (l ^ n))))
      (hρ : IsOpen (ρ.ker : Set π.ker)),
      Nonempty (H2K ρ (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker) (rdJ RD π.ker) hρ ≃ₗ[ZMod (l ^ n)]
        H2c ρ (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) π.ker)) :=
    fun ρ hρ => hcount_S3 hq he hl n hPic D hDB hπ RD hΛ0 (hallV_S3 hq he hl hPicU π.ker hπ _ n)
      (fun t => hallIV_S3 hq he hl hPicU D RD π.ker hπ _ n t) ρ hρ
  exact parabolic_of_count hn (ZMod.castHom (ringChar.dvd hΛ) Λ) H0 D0 (rdCupHyp π.ker σ hσ hv)
    (rdConstData RD π.ker hK σ htriv hΛ) (fun _ _ => rfl) hcount hbasis hdens hI hτ hex hI2

end S3

end

end CupDuality
end RamanujanPetersson


end


