-- Prove2me | Definitions.Def_RPLib_FX_GOSC_13
-- name    : RPLib_FX_GOSC_13
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:41:17.394324+00:00
-- url     : https://prove2.me/theorems/d3ae9598-38e1-539d-84f2-89447380dad3
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 13 of 14
-- statement:
--   File 13 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_GOS_C_EUL`: S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_050
import Definitions.Def_RPLib_FX_GOSC_12

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 13 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_GOS_C_EUL`: S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_GOS_C_EUL =====
section

/-!
# S4-GOS-C, part EUL: the Euler characteristic of the perfect complex is `h²_c - h¹_c`

`finrank_euler3`: for a complex `K⁰ → K¹ → K²` of finite-dimensional spaces with `d⁰` injective,
`dim K⁰ - dim K¹ + dim K² = dim H² - dim H¹`. With the term isomorphisms `pcIso0/1/2`, `H¹ = H¹_c` (`hc1Equiv`) and
`H² ≅ H²_c` (`h2Equiv_lisse`): **`chi_eq_h2c_sub_h1c`**: `Σ_i (-1)^i dim (PC i ⊗ M)_{Gf} = h²_c(M) - h¹_c(M)` over `ℤ/l`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Dim

variable {k : Type*} [Field k] {K0 K1 K2 : Type*} [AddCommGroup K0] [Module k K0] [AddCommGroup K1]
  [Module k K1] [AddCommGroup K2] [Module k K2] [FiniteDimensional k K0] [FiniteDimensional k K1]
  [FiniteDimensional k K2]

end Dim

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **`χ(τ) = h²_c - h¹_c`** for the perfect complex of the cover over `ℤ/l`. -/
theorem chi_eq_h2c_sub_h1c (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Module.Finite (ZMod (l ^ 1)) M]
    (τ : Representation (ZMod (l ^ 1)) Gf M) :
    ∑ i ∈ Finset.range 3, (-1 : ℤ) ^ i *
        (Module.finrank (ZMod (l ^ 1)) (Coinvariants ((ρPC (ZMod (l ^ 1)) π (pi1geo (Rfin Fq K) K
          (Fintype.card Fq)) (bdryInf Fq K).inertia i).tprod τ)) : ℤ) =
      (Module.finrank (ZMod (l ^ 1)) (H2c (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))) : ℤ) -
        Module.finrank (ZMod (l ^ 1))
          (H1c (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia) := by
  classical
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hl⟩
  haveI : Finite M := Module.finite_of_finite (ZMod (l ^ 1))
  have hl0 : (l : K) ≠ 0 := by
    have h1 := cast_ne_zero_of_not_dvd (F := K) hq he hlq 1
    rwa [pow_one] at h1
  have hPicU := picDivU Fq K l hlq
  have hΛ : ((l ^ 1 : ℕ) : ZMod (l ^ 1)) = 0 := ZMod.natCast_self _
  have hall := CdOne.h2All_geo (Rfin Fq K) Fq he hq (Kummer.perfect_Rfin Fq K) l (isUnit_cast_Rfin hl0) hPicU
    (ZMod (l ^ 1)) 1
  have hallI : ∀ s, H2All (ZMod (l ^ 1)) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l 1 :=
    fun s => cone_h3_eq_zero hq he hl0 hPicU (bdryInf Fq K) s (ZMod (l ^ 1)) 1
  obtain ⟨⟨-, hfin⟩, -⟩ := pc_lev Fq K hq he l 1 one_pos hlq hM hMU π hπM hπ
  have hcf : ∀ i, Module.Finite (ZMod (l ^ 1)) (Coinvariants ((ρPC (ZMod (l ^ 1)) π
      (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i).tprod τ)) := fun i => by
    haveI := hfin i
    exact Module.Finite.quotient (ZMod (l ^ 1)) (Coinvariants.ker _)
  have hρ := isOpen_comp_ker π τ hπ
  have e0 := pcIso0 π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia τ
  have e1 := pcIso1 π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia τ hΛ hall hπ
  have e2 := pcIso2 π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia τ hΛ hallI hπ
  haveI := hcf 1
  haveI := hcf 2
  haveI : Module.Finite (ZMod (l ^ 1)) (Z1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) ×
    (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K) → M)) := Module.Finite.equiv e1
  haveI : Module.Finite (ZMod (l ^ 1)) ((s : BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K)) →
    Z1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s)) := Module.Finite.equiv e2
  haveI : Nonempty (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K)) :=
    nonempty_bdry (bdryInf Fq K) (fun _ => Iff.rfl)
  have hE := finrank_euler3 (cx0 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))
    (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K)) hρ)
    (cx1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia hρ)
    (cx1_cx0 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia hρ)
    (cx0_injective (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))
      (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K)) hρ)
  obtain ⟨E, -⟩ := h2Equiv_lisse hq he hl0 1 hPicU (picDivX Fq K l hlq 1) (bdryInf Fq K) (fun _ => Iff.rfl)
    hΛ (τ.comp π) hρ
  rw [(hc1Equiv (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia hρ).finrank_eq,
    E.finrank_eq] at hE
  exact alt_sum_three _ e0.finrank_eq e1.finrank_eq e2.finrank_eq hE

end

end RamanujanPetersson.GOS


end


