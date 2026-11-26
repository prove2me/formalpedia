-- Prove2me | Definitions.Def_RPLib_FX_GOSC_BR
-- name    : RPLib_FX_GOSC_BR
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:06:19.024094+00:00
-- url     : https://prove2.me/theorems/6c3f97a7-b6e0-57b5-b3d2-421271675872
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, top file
-- statement:
--   Top file of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: the elementwise form `GOSCU.main` of the library theorem `GOS.gos_A1`. For a finite Galois cover $M_f$ of $\mathbb A^1_{\mathbb F_q}$ unramified over $\mathbb F_q[x]$, a surjection $\pi$ of the fundamental group onto a finite group $G_f$ with kernel $\mathrm{Gal}(K_U/M_f)$ and a representation $\tau$ of $G_f$ on a finite $\mathbb Z/\ell$-module $M$, it gives $\dim M_\Gamma-\dim H^1_c=\dim M-\mathrm{Sw}_\infty(M)$.
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_FX_GOSC_GL

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field: top file

`GOSCU.main`, the elementwise form of the library theorem `GOS.gos_A1`: for a finite Galois cover `M_f` of the
affine line over `F_q` unramified over `F_q[x]`, a surjection `π` from the Galois group of the maximal extension
unramified over `F_q[x]` onto a finite group `G_f` with kernel `Gal(K_U/M_f)`, and a representation `τ` of `G_f` on a
finite `ZMod l`-module `M` (`l` prime to `q`), `dim M_Γ - dim H¹_c = dim M - Sw_∞(M)`, with `H¹_c` the relative
cochain cohomology `Z / (B ∩ Z)` and the Swan conductor written with the ideal-power lower ramification groups at
any place of `M_f` over infinity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.defProp false

section Main
open scoped Pointwise

namespace RamanujanPetersson.GOSCU

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 6000000 in
noncomputable def main
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (KU : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hKU : KU = ⨆ L : {L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) //
        FiniteDimensional (RatFunc Fq) L ∧ IsGalois (RatFunc Fq) L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc Fq] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L,
              ∃ c ∈ P, (c : L) = g b - b) → g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hΓ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (S : Type)
    (P : S → Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring
      (RatFunc Fq)) KU))
    (hP : ∀ s, (P s).IsPrime ∧ P s ≠ ⊥)
    (hcover : ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring
        (RatFunc Fq)) KU),
      Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
        ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
          b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU))
    (hdisj : ∀ s s', ∀ g ∈ Γ,
      (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
        b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s')
    (I : S → Subgroup (KU ≃ₐ[RatFunc Fq] KU))
    (hI : ∀ s (g : KU ≃ₐ[RatFunc Fq] KU), g ∈ I s ↔
      ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq)) KU,
        ∃ c ∈ P s, (c : KU) = g (b : KU) - b)
    (Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))
    (hMf : FiniteDimensional (RatFunc Fq) Mf ∧ IsGalois (RatFunc Fq) Mf ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) Mf), P.IsPrime →
        ∀ g : Mf ≃ₐ[RatFunc Fq] Mf,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) Mf,
            ∃ c ∈ P, (c : Mf) = g b - b) → g = 1)
    (Gf : Type) [Group Gf] [Finite Gf] (π : (KU ≃ₐ[RatFunc Fq] KU) →* Gf)
    (hπ : ∀ g : KU ≃ₐ[RatFunc Fq] KU, π g = 1 ↔ ∀ x : KU, (x : AlgebraicClosure (RatFunc Fq)) ∈ Mf → g x = x)
    (hπs : Function.Surjective π)
    (ι : (Mf ≃ₐ[RatFunc Fq] Mf) →* Gf)
    (hι : ∀ (g : KU ≃ₐ[RatFunc Fq] KU) (σ : Mf ≃ₐ[RatFunc Fq] Mf),
      (∀ (x : KU) (hx : (x : AlgebraicClosure (RatFunc Fq)) ∈ Mf),
        ((g x : KU) : AlgebraicClosure (RatFunc Fq)) = ((σ ⟨x, hx⟩ : Mf) : AlgebraicClosure (RatFunc Fq))) →
      π g = ι σ)
    (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq)
    (M : Type) [AddCommGroup M] [Module (ZMod l) M] [Module.Finite (ZMod l) M]
    (τ : Representation (ZMod l) Gf M)
    (Z : Submodule (ZMod l) ((Γ → M) × (S → M)))
    (hZ : ∀ x : (Γ → M) × (S → M), x ∈ Z ↔
      IsLocallyConstant x.1 ∧ (∀ g h : Γ, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
        ∀ s (g : Γ), (g : KU ≃ₐ[RatFunc Fq] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s)
    (B : Submodule (ZMod l) ((Γ → M) × (S → M)))
    (hB : ∀ x : (Γ → M) × (S → M), x ∈ B ↔
      ∃ m : M, (∀ g : Γ, x.1 g = τ (π g) m - m) ∧ ∀ s, x.2 s = m)
    (Q0 : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf)) :
    (Module.finrank (ZMod l) (Representation.Coinvariants ((τ.comp π).comp Γ.subtype)) : ℚ) -
        Module.finrank (ZMod l) (Z ⧸ B.comap Z.subtype) =
      Module.finrank (ZMod l) M -
        ∑ᶠ i : ℕ,
          (Nat.card {σ : Mf ≃ₐ[RatFunc Fq] Mf //
              ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal ^ (i + 2), (c : Mf) = σ b - b} : ℚ) /
            (Nat.card {σ : Mf ≃ₐ[RatFunc Fq] Mf //
              ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal, (c : Mf) = σ b - b} : ℚ) *
          ((Module.finrank (ZMod l) M : ℚ) -
            Module.finrank (ZMod l) ↥(⨅ (σ : Mf ≃ₐ[RatFunc Fq] Mf)
              (_ : ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring Mf,
                ∃ c ∈ Q0.asIdeal ^ (i + 2), (c : Mf) = σ b - b),
              LinearMap.ker (τ (ι σ) - 1))) := by
  classical
  obtain ⟨n, hp, hn⟩ := FiniteField.card Fq (ringChar Fq)
  haveI : Fact (ringChar Fq).Prime := ⟨hp⟩
  haveI : CharP (RatFunc Fq) (ringChar Fq) :=
    charP_of_injective_algebraMap (algebraMap Fq (RatFunc Fq)).injective _
  have he : 0 < (n : ℕ) := n.pos
  have hq : Fintype.card Fq = ringChar Fq ^ (n : ℕ) := hn
  -- `K_U = maxUnram`
  have hset : unramSet (FunctionField.ringOfIntegers Fq (RatFunc Fq)) (RatFunc Fq) =
      {L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)) |
        FiniteDimensional (RatFunc Fq) L ∧ IsGalois (RatFunc Fq) L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L), P.IsPrime →
          ∀ g : L ≃ₐ[RatFunc Fq] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq (RatFunc Fq)) L,
              ∃ c ∈ P, (c : L) = g b - b) → g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (unram_iff _ _ L))
  have hKU' : KU = maxUnram (FunctionField.ringOfIntegers Fq (RatFunc Fq)) (RatFunc Fq) := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have hΓ' : Γ = CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq (RatFunc Fq)) (RatFunc Fq)
      (Fintype.card Fq) := by
    ext g
    rw [hΓ, CurveCoh.mem_pi1geo]
    rfl
  subst hΓ'
  -- boundary data
  let D : CurveCoh.BdryData (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq)
      (Places.Rinf Fq (RatFunc Fq)) S :=
    { B := CurveCoh.IsBdryPrime (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Places.Rinf Fq (RatFunc Fq))
      B_smul := fun g Q hQ => CurveCoh.isBdryPrime_smul _ _ _ g hQ
      P := P
      mem := hP
      cover := fun Q hQ => by
        obtain ⟨s, g, hg, hb⟩ := hcover Q hQ.1 hQ.2
        exact ⟨s, g, hg, Ideal.ext fun b => (hb b).trans (mem_smul_iff _ g (P s) b).symm⟩
      disj := fun s s' g hg he => hdisj s s' g hg fun b => by
        rw [he]
        exact mem_smul_iff _ g (P s) b }
  have hI' : I = D.inertia := by
    funext s
    ext g
    rw [hI]
    show _ ↔ g ∈ CurveCoh.BdryData.inertia D s
    rw [CurveCoh.BdryData.inertia, AddSubgroup.mem_inertia]
    refine forall_congr' fun b => ⟨fun ⟨c, hc, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
    have : c = g • b - b := Subtype.ext he
    rwa [← this]
  subst hI'
  -- the cover `M_f`
  have hM : Mf ∈ unramSet (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) := by
    show Mf ∈ unramSet (FunctionField.ringOfIntegers Fq (RatFunc Fq)) (RatFunc Fq)
    rw [hset]
    exact hMf
  have hMU : Mf ≤ maxUnram (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) :=
    le_iSup (fun L : unramSet (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) =>
      (L : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq)))) ⟨Mf, hM⟩
  have hπM : ∀ g, π g = 1 ↔ g ∈ (IntermediateField.restrict hMU).fixingSubgroup := fun g => by
    rw [hπ g, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h x ((IntermediateField.mem_restrict hMU x).1 hx),
      fun h x hx => h x ((IntermediateField.mem_restrict hMU x).2 hx)⟩
  haveI : FiniteDimensional (RatFunc Fq) Mf := hMf.1
  haveI : IsGalois (RatFunc Fq) Mf := hMf.2.1
  have : FiniteDimensional (RatFunc Fq) (IntermediateField.restrict hMU) :=
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv hMU).toLinearEquiv
  have hπo : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq))) := by
    have hk2 : (π.ker : Set (Pi1 (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq))) =
        ((IntermediateField.restrict hMU).fixingSubgroup :
          Set (Pi1 (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq))) := by
      ext g
      exact hπM g
    rw [hk2]
    exact (IntermediateField.restrict hMU).fixingSubgroup_isOpen
  haveI : Fintype Gf := Fintype.ofFinite _
  haveI := CP4a.finite_bdryS (F := RatFunc Fq) hq he
  haveI : Fintype (CP4a.BdryS (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq)
      (Places.Rinf Fq (RatFunc Fq))) := Fintype.ofFinite _
  obtain ⟨φ, hφ⟩ := CP4a.exists_frobLift (GOS.constField_rat Fq) hq he
  -- `ι = iotaG`
  have hιeq : GOS.iotaG Fq hMU π hπM = ι := by
    refine MonoidHom.ext fun σ => ?_
    obtain ⟨g, rfl⟩ := Lefschetz.resPt_surjective (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU σ
    rw [GOS.iotaG_resPt]
    exact hι g _ fun x hx => (Lefschetz.resPt_apply (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) hMU g
      ⟨x, hx⟩).symm
  -- the library theorem, over `ZMod (l ^ 1)`
  have key : ∀ (m : ℕ) (_ : m = l ^ 1) [Fact m.Prime] (M' : Type) [AddCommGroup M'] [Module (ZMod m) M']
      [Module.Finite (ZMod m) M'] (τ' : Representation (ZMod m) Gf M'),
      ((Module.finrank (ZMod m) (CurveCoh.H2c (τ'.comp π)
          (CurveCoh.pi1geo (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq))) : ℚ) -
        Module.finrank (ZMod m) (CurveCoh.H1c (τ'.comp π)
          (CurveCoh.pi1geo (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq))
          (CP4a.bdryInf Fq (RatFunc Fq)).inertia)) =
      Module.finrank (ZMod m) M' -
        GOS.swanQ Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) (GOS.iotaG Fq hMU π hπM) τ' Q0 := by
    intro m hm _ M' _ _ _ τ'
    subst hm
    exact GOS.gos_A1 Fq hq he hM hMU π hπM hπo hπs hφ l hlq τ' Q0
  have hmain := key l (pow_one l).symm M τ
  -- `H¹_c`: the given cocycle quotient is the library `H¹_c` for the boundary data `D`
  have hZ1 : ∀ v, v ∈ Z ↔ v ∈ CurveCoh.Z1c (τ.comp π)
      (CurveCoh.pi1geo (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq)) D.inertia :=
    fun v => (hZ v).trans and_assoc.symm
  have hH1 : Module.finrank (ZMod l) (Z ⧸ B.comap Z.subtype) =
      Module.finrank (ZMod l) (CurveCoh.H1c (τ.comp π)
        (CurveCoh.pi1geo (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq))
        (CP4a.bdryInf Fq (RatFunc Fq)).inertia) := by
    rw [finrank_quot_eq (LinearEquiv.refl (ZMod l) _) Z B
      (CurveCoh.Z1c (τ.comp π)
        (CurveCoh.pi1geo (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq)) D.inertia)
      (CurveCoh.B1c (τ.comp π)
        (CurveCoh.pi1geo (Places.Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq)) D.inertia) hZ1
      (fun v hv => (hB v).trans ⟨fun h => ⟨(hZ1 v).1 hv, h⟩, fun h => h.2⟩)]
    exact finrank_h1c_bdry D (CP4a.bdryInf Fq (RatFunc Fq)) (fun _ h => h) (fun _ h => h) (τ.comp π)
  have hsw := swanQ_eq_finsum Fq (RatFunc Fq) Mf (Mf ≃ₐ[RatFunc Fq] Mf) ι τ Q0
  rw [hH1]
  rw [hιeq] at hmain
  refine hmain.trans ?_
  exact congrArg (fun x : ℚ => (Module.finrank (ZMod l) M : ℚ) - x) hsw

end RamanujanPetersson.GOSCU

end Main


