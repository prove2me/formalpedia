-- Prove2me | Definitions.Def_RPLib_FX_GOSC_06
-- name    : RPLib_FX_GOSC_06
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:04:12.426787+00:00
-- url     : https://prove2.me/theorems/f97ea5c4-cd61-49a2-aa60-736677505025
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 06 of 14
-- statement:
--   File 06 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
--   * `S4.Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
--   * `S4.Def_RP_CupDuality_VFrobA`: S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form
--   * `S4.Def_RP_GOS_C_LIFTa`: S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules
--   * `S4.Def_RP_GOS_B_Cov`: S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)
--   * `S4.Def_RP_GOS_B_GPt`: S4-GOS-B, part GPt: Lefschetz count on the concrete cover `M ⊇ M^H` (O6c, per point)
--   * `S4.Def_RP_GOS_C_GOSI`: S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_025
import Definitions.Def_RPLib_FX_GOSC_05

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 06 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
* `S4.Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
* `S4.Def_RP_CupDuality_VFrobA`: S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form
* `S4.Def_RP_GOS_C_LIFTa`: S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules
* `S4.Def_RP_GOS_B_Cov`: S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)
* `S4.Def_RP_GOS_B_GPt`: S4-GOS-B, part GPt: Lefschetz count on the concrete cover `M ⊇ M^H` (O6c, per point)
* `S4.Def_RP_GOS_C_GOSI`: S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover
-/

set_option autoImplicit false

-- ===== S4.Def_RP_HattoriStallings_SES =====
section

/-!
# Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules

* `avg ρ σ f = ∑_g σ g ∘ f ∘ ρ g⁻¹` is always equivariant; `IsHigman ρ E ↔ avg ρ ρ E = id`.
* `exists_equivariant_lift`: a projective (Higman) representation lifts equivariantly along
  equivariant surjections.
* `exists_equivariant_splitting`: a short exact sequence with projective quotient splits equivariantly.
* `hs_ses`: additivity of the HS trace on short exact sequences (and the sub is projective).
* `isHigman_of_basis`, `isProj_permRep`: permutation modules of free `G`-sets are projective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap

section Avg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {T : Type*} [AddCommGroup T] [Module R T]
variable {ρ : Representation R G P} {σ : Representation R G Q} {τ : Representation R G T}

lemma IsEquivariant.comp_avg {π : Q →ₗ[R] T} (hπ : IsEquivariant σ τ π) (f : P →ₗ[R] Q) :
    π ∘ₗ avg ρ σ f = avg ρ τ (π ∘ₗ f) := by
  ext v
  simp [avg_apply, map_sum, hπ.apply]

lemma IsEquivariant.avg_comp {u : P →ₗ[R] Q} (hu : IsEquivariant ρ σ u) (f : P →ₗ[R] P) :
    avg ρ σ (u ∘ₗ f) = u ∘ₗ avg ρ ρ f := by
  ext v
  simp [avg_apply, map_sum, hu.apply]

/-- Equivariant lifting property of a Higman representation along equivariant surjections. -/
theorem exists_equivariant_lift [Module.Projective R P] {E : P →ₗ[R] P} (hE : IsHigman ρ E)
    {π : Q →ₗ[R] T} (hπ : IsEquivariant σ τ π) (hsurj : Function.Surjective π)
    {u : P →ₗ[R] T} (hu : IsEquivariant ρ τ u) :
    ∃ h : P →ₗ[R] Q, IsEquivariant ρ σ h ∧ π ∘ₗ h = u := by
  obtain ⟨w, hw⟩ := Module.projective_lifting_property π u hsurj
  refine ⟨avg ρ σ (w ∘ₗ E), isEquivariant_avg _, ?_⟩
  have hE' : avg ρ ρ E = LinearMap.id := hE
  rw [hπ.comp_avg, ← LinearMap.comp_assoc, hw, hu.avg_comp, hE', LinearMap.comp_id]

end Avg

section SES

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P' : Type*} [AddCommGroup P'] [Module R P'] {P : Type*} [AddCommGroup P] [Module R P]
variable {P'' : Type*} [AddCommGroup P''] [Module R P'']
variable {ρ' : Representation R G P'} {ρ : Representation R G P} {ρ'' : Representation R G P''}

variable [Module.Free R P'] [Module.Finite R P'] [Module.Free R P] [Module.Finite R P]
  [Module.Free R P''] [Module.Finite R P'']

end SES

section Perm

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

end Perm

end RamanujanPetersson.HattoriStallings


end

-- ===== S4.Def_RP_PerfectCx_RedPC =====
section

/-!
# S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)

Termwise reductions `redA`, `red1`, `red2` of `PC Λ → PC Λ'` are onto with kernel `t • PC` (`H2All`), commute with
the `Gf`-actions, the Frobenius and the differentials, so `Λ' ⊗ PC Λ i ≃ PC Λ' i` (`pcRed0`, `pcRed1`, `pcRed2`,
compatibilities via `redEquiv_comm`) and the Lefschetz numbers of the Frobenius reduce (`lefschetz_frob_red`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct

noncomputable section

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

section Frob

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

end Frob

section Red

variable [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ'))
  (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ}
  (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

/-- `Λ' ⊗ P¹_Λ ≃ P¹_Λ'`. -/
def pcRed1 : Λ' ⊗[Λ] (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) ≃ₗ[Λ'] Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf) :=
  redEquiv ϖ hsurj ht (red1 Λ Λ' π Γ) (red1_surjective π Γ hsurj hΛ hall hπ) (red1_ker π Γ hk hΛ hall hπ)

/-- `Λ' ⊗ P²_Λ ≃ P²_Λ'`. -/
def pcRed2 : Λ' ⊗[Λ] ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ≃ₗ[Λ'] ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) :=
  redEquiv ϖ hsurj ht (red2 Λ Λ' π Γ I) (red2_surjective π Γ I hsurj hΛ hallI hπ) (red2_ker π Γ I hk hΛ hallI hπ)

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

end Red

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VFrobA =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form

`H²(K)` of the constant cone is `≅ k` (`h2kEquiv`), so every `k`-linear endomorphism of it is a scalar
(`endo_eq_smul`), and the scalar is a unit when the endomorphism is onto (`isUnit_of_surjective`). Frobenius on
`H²(K)` is onto when `frob2` is, which holds when `τ` is bijective and conjugation by `ψ h_s` maps
`Γ ⊓ I (τ s)` back into `I s` (exact boundary conjugation, `hex`). **`constPair_frob_unit`**: then
`⟨F x, F y⟩ = c ⟨x, y⟩` with `c` a unit, which is all `inR_conj` needs (no twist identity).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M)

/-- `conjMap x` is onto when `x` also conjugates `Δ'` back into `Δ`. -/
theorem conjMap_conjMap_inv (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ')
    (hx' : ∀ g ∈ Δ', x⁻¹⁻¹ * g * x⁻¹ ∈ Δ) (d : Z1 ρ Δ) : conjMap ρ x hx (conjMap ρ x⁻¹ hx' d) = d := by
  apply Subtype.ext
  funext g
  rw [conjMap_apply, conjMap_apply]
  have e : conjSub x⁻¹ hx' (conjSub x hx g) = g := Subtype.ext (by
    simp only [conjSub_val]
    group)
  rw [e, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable (Γ : Subgroup G) [hΓ : Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (τ : S → S) (h : S → Γ)

/-- `frob2` is onto for exact boundary conjugation and bijective `τ`. -/
theorem frob2_surjective (hI : BdryCompat Γ I ψ τ h) (hτ : Function.Bijective τ)
    (hex : ∀ s (g : G), g ∈ Γ → g ∈ I (τ s) → (ψ * h s) * g * (ψ * h s)⁻¹ ∈ I s) :
    Function.Surjective (frob2 ρ Γ I ψ τ h hI) := by
  intro f
  have hx' : ∀ s, ∀ g ∈ Γ ⊓ I (τ s), (ψ * (h s : G))⁻¹⁻¹ * g * (ψ * (h s : G))⁻¹ ∈ Γ ⊓ I s := by
    intro s g hg
    rw [inv_inv]
    obtain ⟨hgΓ, hgI⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hΓ.conj_mem g hgΓ _, hex s g hgΓ hgI⟩
  let gs : (s : S) → Z1 ρ (Γ ⊓ I (τ s)) := fun s => conjMap ρ (ψ * (h s : G))⁻¹ (hx' s) (f s)
  let eτ : S ≃ S := Equiv.ofBijective τ hτ
  let e : (u : S) → Z1 ρ (Γ ⊓ I u) := Equiv.piCongrLeft (fun u => Z1 ρ (Γ ⊓ I u)) eτ gs
  refine ⟨e, funext fun s => ?_⟩
  have he : e (τ s) = gs s := Equiv.piCongrLeft_apply_apply (fun u => Z1 ρ (Γ ⊓ I u)) eτ gs s
  show conjMap ρ (ψ * h s) (bdry_mem Γ I ψ τ h hI s) (e (τ s)) = f s
  rw [he]
  exact conjMap_conjMap_inv ρ _ _ _ (f s)

variable (hρ : IsOpen (ρ.ker : Set G))

end H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S]
  {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_C_LIFTa =====
section

/-!
# S4-GOS-C, part LIFTa: permutation modules and reduction maps for lifting projective modules

* `leftAct`: `G` acts on `G × ι` by left multiplication on `G` (freely, `leftAct_free`);
* `permRepM`: the permutation representation on `X → M` over `Λ`;
* `red X : (X → Λ) → (X → Λ')` (coefficientwise `algebraMap`): equivariant, onto, kernel `t • _`;
* `pMap σ' b : (G × ι → Λ') → Y'`, `f ↦ ∑ f (h, i) • σ' h (b i)`: equivariant and onto for a basis `b`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

open HattoriStallings

attribute [local instance] leftAct

section Red

variable {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ']

theorem red_equivariant {G : Type*} [Group G] [Fintype G] (X : Type*) [MulAction G X] :
    IsEquivariant (permRep Λ G X) (permRepM Λ G X Λ') (red X) := fun _ => LinearMap.ext fun _ => rfl

end Red

section PMap

variable {Λ' : Type*} [CommRing Λ'] {G : Type*} [Group G] [Fintype G] {Y' : Type*} [AddCommGroup Y']
  [Module Λ' Y'] {ι : Type*} [Fintype ι]

theorem pMap_equivariant (σ' : Representation Λ' G Y') (b : ι → Y') :
    IsEquivariant (permRep Λ' G (G × ι)) σ' (pMap σ' b) := by
  intro g
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.comp_apply, pMap, Fintype.linearCombination_apply, permRep_apply, map_sum, map_smul]
  refine Fintype.sum_equiv (MulAction.toPerm g⁻¹ : Equiv.Perm (G × ι)) _ _ (fun x => ?_)
  simp only [MulAction.toPerm_apply, leftAct_smul, rep_apply_apply, mul_inv_cancel_left]

end PMap

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Cov =====
section

/-!
# S4-GOS-B, part Cov: the concrete cover `M ⊆ K_U` over `K = 𝔽_q(X)` (O4u, O8b)

`M` finite Galois over `K = RatFunc 𝔽_q`, `G = Gal(M/K)`:
* `rfinEquiv`: `R_fin(M) ≃ O_M` (the integral closure of `R_fin(K)` in `M` used by S4-Lefschetz), `G`-equivariant
  (`rfinEquiv_smul`);
* `hun_rfin`: every prime of `R_fin(M)` has trivial inertia if `M` is unramified over `R_fin(K)`;
  **`hfin_of_unram`** (O4u): the `hfin` hypothesis of `chiPC_eq_Phi_of`;
* `iotaG`: `Gal(M/K) →* Gf` with `iotaG (resPt σ) = π σ` (O8b), injective; surjective if `π` is.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh Lefschetz

section Cov

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (M : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))) [FiniteDimensional (RatFunc Fq) M]
  [IsGalois (RatFunc Fq) M]

theorem rfinEquiv_val (x : Rfin Fq M) :
    ((rfinEquiv Fq M x : integralClosure (Rfin Fq (RatFunc Fq)) M) : M) = (x : M) :=
  IsIntegralClosure.algebraMap_equiv (Rfin Fq (RatFunc Fq)) (Rfin Fq M) M
    (integralClosure (Rfin Fq (RatFunc Fq)) M) x

theorem rfinEquiv_smul (g : M ≃ₐ[RatFunc Fq] M) (x : Rfin Fq M) :
    letI := actRfin Fq (RatFunc Fq) M (M ≃ₐ[RatFunc Fq] M)
    rfinEquiv Fq M (g • x) = g • rfinEquiv Fq M x := by
  letI := actRfin Fq (RatFunc Fq) M (M ≃ₐ[RatFunc Fq] M)
  apply Subtype.ext
  rw [rfinEquiv_val]
  show g • (x : M) = g • ((rfinEquiv Fq M x : integralClosure (Rfin Fq (RatFunc Fq)) M) : M)
  rw [rfinEquiv_val]

/-- Every prime of `R_fin(M)` has trivial inertia when `M` is unramified over `R_fin(K)`. -/
theorem hun_rfin (hun : IsUnramifiedSub (Rfin Fq (RatFunc Fq)) (RatFunc Fq) M) :
    letI := actRfin Fq (RatFunc Fq) M (M ≃ₐ[RatFunc Fq] M)
    ∀ Q : Ideal (Rfin Fq M), Q.IsPrime → Q.inertia (M ≃ₐ[RatFunc Fq] M) = ⊥ := by
  letI := actRfin Fq (RatFunc Fq) M (M ≃ₐ[RatFunc Fq] M)
  intro Q hQ
  let e := (rfinEquiv Fq M).toRingEquiv
  have hQ' : (Q.map (e : Rfin Fq M →+* integralClosure (Rfin Fq (RatFunc Fq)) M)).IsPrime :=
    Ideal.map_isPrime_of_equiv e
  have h := hun _ hQ'
  rw [eq_bot_iff] at h ⊢
  intro σ hσ
  apply h
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have h1 : σ • e x - e x = e (σ • x - x) := by
    rw [map_sub]
    congr 1
    exact (rfinEquiv_smul Fq M σ x).symm
  have h2 : e (σ • x - x) ∈ Ideal.map (e : Rfin Fq M →+* integralClosure (Rfin Fq (RatFunc Fq)) M) Q :=
    Ideal.mem_map_of_mem _ (hσ x)
  rw [← h1] at h2
  exact h2

/-- **O4u**: the finite places of an unramified cover have trivial inertia. -/
theorem hfin_of_unram (hun : IsUnramifiedSub (Rfin Fq (RatFunc Fq)) (RatFunc Fq) M) :
    letI := actRfin Fq (RatFunc Fq) M (M ≃ₐ[RatFunc Fq] M)
    ∀ Q : HeightOneSpectrum (Rfin Fq M), Q.asIdeal.inertia (M ≃ₐ[RatFunc Fq] M) = ⊥ :=
  fun Q => hun_rfin Fq M hun Q.asIdeal Q.isPrime

variable {M} (hMU : M ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))

variable {Gf : Type} [Group Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)

end Cov

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_GPt =====
section

/-!
# S4-GOS-B, part GPt: Lefschetz count on the concrete cover `M ⊇ M^H` (O6c, per point)

`K = RatFunc 𝔽_q`, `M ⊆ K_U` finite Galois and unramified over `R_fin(K)`, `G = Gal(M/K)`, `H ≤ G`,
`E' = M^H` (`fixF`). For a point `u : R_fin(K) → K̄` with finite image and a lift `w` of `u` to the pro-chart on
which `F ∈ π_1` acts as `Fr`:
**`card_conj_mem_eq`**: `#{x ∈ G | x⁻¹ F|_M x ∈ H} = #{v : R_fin(E') → K̄ over u | Fr ∘ v = v} · |H|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh Lefschetz CupDuality

section GPt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {M : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) M]
  [IsGalois (RatFunc Fq) M]

set_option synthInstance.maxHeartbeats 400000 in
theorem isScalarTower_rfin_fixF (H : Subgroup (M ≃ₐ[RatFunc Fq] M)) :
    IsScalarTower (Rfin Fq (RatFunc Fq)) (Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H)) (Rfin Fq M) :=
  IsScalarTower.of_algebraMap_eq fun a =>
    Subtype.ext (IsScalarTower.algebraMap_apply (RatFunc Fq) (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) M (a : RatFunc Fq))

set_option synthInstance.maxHeartbeats 400000 in
theorem faithfulSMul_rfin_fixF (H : Subgroup (M ≃ₐ[RatFunc Fq] M)) :
    FaithfulSMul (Rfin Fq (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H)) (Rfin Fq M) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b hab
  have h1 := congrArg Subtype.val hab
  rw [algebraMap_rfin, algebraMap_rfin] at h1
  exact Subtype.ext ((algebraMap (fixF Fq M (M ≃ₐ[RatFunc Fq] M) H) M).injective h1)

variable (hun : IsUnramifiedSub (Rfin Fq (RatFunc Fq)) (RatFunc Fq) M)
  (hMU : M ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))

end GPt

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_GOSI =====
section

/-!
# S4-GOS-C, part GOSI: the integer Grothendieck-Ogg-Shafarevich identity on the concrete cover

`K = RatFunc 𝔽_q`, `G = Gal(M_f/K) ≅ Gf` (via `iotaG`), `τ` a representation of `Gf` on a finite `ℤ/l`-module `M`
(`l ∤ q`). With `χ(τ) = Σ_i (-1)^i dim (PC i ⊗ M)_{Gf}`, `W_Q(j) = G_{Q,j+1}` and `d_{Q,j} = dim M_{ι W_Q(j)}`:
**`gos_int`**: `|Gf| χ(τ) = |G| χ_c(K) dim M - Σ_{Q | ∞} Σ_{j < J} deg Q |W_Q(j)| (dim M - d_{Q,j})` in `ℤ`,
from Brauer's formula at every level `ℤ/l^n` (`brauer_lev`), `chiPC_eq_Phi`, `Φ = Σ_Q Σ_j [· ∈ W_Q(j)] deg Q`,
`Σ Φ = |G| χ_c(K)` and the wild groups being `p`-groups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue Lefschetz

section Transfer

variable {G Gf : Type*} [Group G] [Group Gf] [Fintype G] {Λ : Type*} [AddCommMonoid Λ]

end Transfer

section GOSI

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {p e : ℕ} [Fact p.Prime] [CharP (RatFunc Fq) p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable [Fintype (BdryS (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) (Rinf Fq (RatFunc Fq)))]
  [DecidableEq (BdryS (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) (Rinf Fq (RatFunc Fq)))]
  {Mf : IntermediateField (RatFunc Fq) (AlgebraicClosure (RatFunc Fq))} [FiniteDimensional (RatFunc Fq) Mf]
  [IsGalois (RatFunc Fq) Mf] (hM : Mf ∈ unramSet (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  (hMU : Mf ≤ maxUnram (Rfin Fq (RatFunc Fq)) (RatFunc Fq))
  {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq) →* Gf)
  (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
  (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)))) (hπs : Function.Surjective π)
  {φ : Pi1 (Rfin Fq (RatFunc Fq)) (RatFunc Fq)}
  (hφ : IsFrobLift (Rfin Fq (RatFunc Fq)) (RatFunc Fq) (Fintype.card Fq) φ)

theorem mem_WQ_iff {K L : Type*} [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
    [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
    [Algebra.IsSeparable (RatFunc Fq) K] [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
    [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
    [Algebra.IsSeparable (RatFunc Fq) L] [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L]
    [IsScalarTower (RatFunc Fq) K L] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G L]
    [IsGaloisGroup G K L] (Q : HeightOneSpectrum (Rinf Fq L)) (j : ℕ) (g : G) :
    g ∈ WQ Fq K L G Q j ↔ g ∈ lowerQ Fq K L G Q (j + 1) := by
  simp [WQ]

end GOSI

end

end RamanujanPetersson.GOS


end


