-- Prove2me | Definitions.Def_RPLib_F2_005
-- name    : RPLib_F2_005
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T03:33:35.631196+00:00
-- url     : https://prove2.me/theorems/6ea42f4c-aaac-4929-8a8b-f93141b8e30e
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 005 of 70
-- statement:
--   File 005 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
--   * `S4.Def_RP_Lefschetz_AGTrace`: S4-Lefschetz, L3e2c3: the block trace on `A_Γ = Λ[Gf]_Γ`
--   * `S4.Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
--   * `S4.Def_RP_Lefschetz_ShapFrob`: S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius
--   * `S4.Def_RP_Lefschetz_AmbSub`: S4-Lefschetz, L4i part 1: Shapiro with Frobenius inside an ambient subgroup `G' ≤ G`
--   * `S4.Def_RP_Lefschetz_ConstExt`: S4-Lefschetz L4a: a function field over its full constant field
--   * `S4.Def_RP_Lefschetz_UnrTower`: S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure
--   * `S4.Def_RP_Lefschetz_OinfInt`: S4-Lefschetz L4b, part 1: `O_∞(k)` is integral over `O_∞(𝔽_q)` for a finite extension `k / 𝔽_q`
--   * `S4.Def_RP_Lefschetz_UnrIn`: S4-Lefschetz L4c (part 2): unramified subextensions in any algebraically closed field
--   * `S4.Def_RP_Lefschetz_UnrExt`: S4-Lefschetz L4d (part 1): `K_U` is unramified over a finite subextension `E ⊆ K_U`
--   * `S4.Def_RP_Lefschetz_UnrFix`: S4-Lefschetz L4d (part 2a): helpers for "unramified over `E ⊆ K_U` implies inside `K_U`"
--   * `S4.Def_RP_Lefschetz_UnrMax`: S4-Lefschetz L4c+d (part 2b): `K_U` is also the maximal unramified extension of a finite `E ⊆ K_U`
--   * `S4.Def_RP_Lefschetz_Pi1Geo`: S4-Lefschetz L4f: geometric `π₁` and Frobenius lifts under `theta` and under a change of `A`
--   * `S4.Def_RP_Lefschetz_ChartE2`: S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover
--   * `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
--   * `S4.Def_RP_Lefschetz_BlockE`: S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart
--   * `S4.Def_RP_Lefschetz_BlockGrp`: S4-Lefschetz, L3d3a: the block subgroup `H_ω`
--   * `S4.Def_RP_Lefschetz_BlockCov`: S4-Lefschetz, L3f2a: block data in the `Rfin` chart
--   * `S4.Def_RP_Lefschetz_Euler`: S4-Lefschetz L1: Euler characteristic of traces for a three-term complex
--   * `S4.Def_RP_Lefschetz_BlockLef`: S4-Lefschetz, L3f1: the Euler characteristic of one fixed block
--   * `S4.Def_RP_Lefschetz_Cancel`: S4-Lefschetz (L2): cancelling a non-unit factor by lifting the coefficient level
--   * `S4.Def_RP_Lefschetz_Pow`: S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius
--   * `S4.Def_RP_Lefschetz_ClassCount`: S4-Lefschetz L2b: class traces of `F^m` from twisted counts
--   * `S4.Def_RP_Lefschetz_FrobSpec`: S4-Lefschetz, L4h part 3: Frobenius data at the boundary
--   * `S4.Def_RP_Lefschetz_H1Les`: S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free
--   * `S4.Def_RP_Lefschetz_H2Sh`: S4-Lefschetz, L4i3: `H²_c` of an induced trivial module
--   * `S4.Def_RP_Lefschetz_PtTorsor`: S4-Lefschetz, L5a: points of an unramified Galois cover form a torsor
--   * `S4.Def_RP_Lefschetz_PtCount`: S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_003

/-!
# Ramanujan-Petersson curve library (flat edition), file 005 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
* `S4.Def_RP_Lefschetz_AGTrace`: S4-Lefschetz, L3e2c3: the block trace on `A_Γ = Λ[Gf]_Γ`
* `S4.Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
* `S4.Def_RP_Lefschetz_ShapFrob`: S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius
* `S4.Def_RP_Lefschetz_AmbSub`: S4-Lefschetz, L4i part 1: Shapiro with Frobenius inside an ambient subgroup `G' ≤ G`
* `S4.Def_RP_Lefschetz_ConstExt`: S4-Lefschetz L4a: a function field over its full constant field
* `S4.Def_RP_Lefschetz_UnrTower`: S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure
* `S4.Def_RP_Lefschetz_OinfInt`: S4-Lefschetz L4b, part 1: `O_∞(k)` is integral over `O_∞(𝔽_q)` for a finite extension `k / 𝔽_q`
* `S4.Def_RP_Lefschetz_UnrIn`: S4-Lefschetz L4c (part 2): unramified subextensions in any algebraically closed field
* `S4.Def_RP_Lefschetz_UnrExt`: S4-Lefschetz L4d (part 1): `K_U` is unramified over a finite subextension `E ⊆ K_U`
* `S4.Def_RP_Lefschetz_UnrFix`: S4-Lefschetz L4d (part 2a): helpers for "unramified over `E ⊆ K_U` implies inside `K_U`"
* `S4.Def_RP_Lefschetz_UnrMax`: S4-Lefschetz L4c+d (part 2b): `K_U` is also the maximal unramified extension of a finite `E ⊆ K_U`
* `S4.Def_RP_Lefschetz_Pi1Geo`: S4-Lefschetz L4f: geometric `π₁` and Frobenius lifts under `theta` and under a change of `A`
* `S4.Def_RP_Lefschetz_ChartE2`: S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover
* `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
* `S4.Def_RP_Lefschetz_BlockE`: S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart
* `S4.Def_RP_Lefschetz_BlockGrp`: S4-Lefschetz, L3d3a: the block subgroup `H_ω`
* `S4.Def_RP_Lefschetz_BlockCov`: S4-Lefschetz, L3f2a: block data in the `Rfin` chart
* `S4.Def_RP_Lefschetz_Euler`: S4-Lefschetz L1: Euler characteristic of traces for a three-term complex
* `S4.Def_RP_Lefschetz_BlockLef`: S4-Lefschetz, L3f1: the Euler characteristic of one fixed block
* `S4.Def_RP_Lefschetz_Cancel`: S4-Lefschetz (L2): cancelling a non-unit factor by lifting the coefficient level
* `S4.Def_RP_Lefschetz_Pow`: S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius
* `S4.Def_RP_Lefschetz_ClassCount`: S4-Lefschetz L2b: class traces of `F^m` from twisted counts
* `S4.Def_RP_Lefschetz_FrobSpec`: S4-Lefschetz, L4h part 3: Frobenius data at the boundary
* `S4.Def_RP_Lefschetz_H1Les`: S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free
* `S4.Def_RP_Lefschetz_H2Sh`: S4-Lefschetz, L4i3: `H²_c` of an induced trivial module
* `S4.Def_RP_Lefschetz_PtTorsor`: S4-Lefschetz, L5a: points of an unramified Galois cover form a torsor
* `S4.Def_RP_Lefschetz_PtCount`: S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_FrobCong =====
section

/-!
# S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`

Generic (any topological group `G`, normal `Γ`, boundary subgroups `I`):
* `twistc_comp`, `bdryCompat_comp`, `frobH1c_comp`: the composite of two cone Frobenii is the cone Frobenius of the
  product, with correcting elements `s ↦ ψ'⁻¹ h_s ψ' · h'_{τ s}`;
* `frobH1c_inner`: an element `γ0 ∈ Γ` (with `τ = id`, `h = γ0⁻¹`) acts trivially on `H¹_c`;
  `frobH1c_mul_geo`: `F(ψ γ0) = F(ψ)` (correcting elements `γ0⁻¹ h_s`);
* `hpow`, `bdryCompat_pow`, `frobH1c_pow`: `F(ψ, τ, h)^m = F(ψ^m, τ^[m], hpow m)`;
* `frobH1c_congr_h`: `F(ψ, τ, h)` only depends on `h_s` modulo `I (τ s)` on the right;
* `frobH2c_comp`, `frobH2c_geo`, `frobH2c_pow`, `frobH2c_mul_geo`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) [hΓ : Γ.Normal]
  {S : Type} (I : S → Subgroup G)

/-! ## Composition -/

/-! ## Inner twists act trivially -/

theorem bdryCompat_inner (γ0 : Γ) : BdryCompat Γ I (γ0 : G) id (fun _ => γ0⁻¹) := by
  intro s g hg
  have e : ((γ0⁻¹ : Γ) : G)⁻¹ * ((γ0 : G)⁻¹ * g * γ0) * ((γ0⁻¹ : Γ) : G) = g := by
    simp only [Subgroup.coe_inv, inv_inv]
    group
  beta_reduce
  rw [e]
  exact hg

theorem frobH1c_inner (γ0 : Γ) :
    frobH1c ρ Γ I (γ0 : G) id (fun _ => γ0⁻¹) (bdryCompat_inner Γ I γ0) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun p => ?_)
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk p
  have hc : (p : (Γ → M) × (S → M)).1 ∈ Z1 ρ Γ := p.2.1
  refine (Submodule.Quotient.eq _).mpr (Submodule.mem_comap.mpr ((mem_B1c ρ Γ I _).mpr
    ⟨(Z1c ρ Γ I).sub_mem (twistc_mem_Z1c ρ Γ I _ _ _ (bdryCompat_inner Γ I γ0) p.2) p.2, (p : (Γ → M) × (S → M)).1 γ0, fun g => ?_, fun s => ?_⟩))
  · change (twistc ρ Γ (γ0 : G) id (fun _ => γ0⁻¹) (p : (Γ → M) × (S → M)) - (p : (Γ → M) × (S → M))).1 g = _
    simp only [Prod.fst_sub, Pi.sub_apply, twistc_fst, twist_apply]
    have e : (γ0 * conjΓ Γ (γ0 : G) g : Γ) = g * γ0 := by
      ext
      simp [mul_assoc]
    have h1 := hc.2 γ0 (conjΓ Γ (γ0 : G) g)
    rw [e, hc.2 g γ0, eq_comm, ← sub_eq_iff_eq_add'] at h1
    rw [← h1]
    abel
  · have h2 := hc.2 γ0 γ0⁻¹
    rw [mul_inv_cancel, Z1_one ρ Γ hc] at h2
    change (twistc ρ Γ (γ0 : G) id (fun _ => γ0⁻¹) (p : (Γ → M) × (S → M)) - (p : (Γ → M) × (S → M))).2 s = _
    simp only [Prod.snd_sub, Pi.sub_apply, twistc_snd, id_eq, map_sub, Subgroup.coe_inv,
      Representation.self_inv_apply]
    rw [eq_neg_of_add_eq_zero_right h2.symm]
    abel

/-! ## Powers -/

/-- The correcting elements of `F(ψ, τ, h)^m`. -/
def hpow (ψ : G) (τ : S → S) (h : S → Γ) : ℕ → S → Γ
  | 0 => fun _ => 1
  | m + 1 => fun s => conjΓ Γ (ψ ^ m) (h s) * hpow ψ τ h m (τ s)

/-! ## Changing the correcting elements inside the inertia -/

theorem twistc_congr_h (ψ : G) (τ : S → S) (h h' : S → Γ) (hh : ∀ s, (((h s)⁻¹ * h' s : Γ) : G) ∈ I (τ s))
    {p : (Γ → M) × (S → M)} (hp : p ∈ Z1c ρ Γ I) : twistc ρ Γ ψ τ h' p = twistc ρ Γ ψ τ h p := by
  refine Prod.ext rfl (funext fun s => ?_)
  rw [twistc_snd, twistc_snd]
  congr 1
  rw [← mul_inv_cancel_left (h s) (h' s), hp.1.2, hp.2 (τ s) _ (hh s)]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
  abel

theorem frobH1c_congr_h (ψ : G) (τ : S → S) (h h' : S → Γ) (hh : ∀ s, (((h s)⁻¹ * h' s : Γ) : G) ∈ I (τ s))
    (hI : BdryCompat Γ I ψ τ h) (hI' : BdryCompat Γ I ψ τ h') :
    frobH1c ρ Γ I ψ τ h' hI' = frobH1c ρ Γ I ψ τ h hI := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun p => ?_)
  show H1c.mk ρ Γ I _ = H1c.mk ρ Γ I _
  exact congrArg (H1c.mk ρ Γ I) (Subtype.ext (twistc_congr_h ρ Γ I ψ τ h h' hh p.2))

/-! ## `H²_c` -/

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_AGTrace =====
section

/-!
# S4-Lefschetz, L3e2c3: the block trace on `A_Γ = Λ[Gf]_Γ`

* `qΓ ω : A_Γ → Λ`, `[F] ↦ Σ_{x ∈ ω} F_x` and `jΓ a : Λ → A_Γ`, `r ↦ r [a]`: `qΓ ω ∘ jΓ a = id` and
  `eBΓ ω = jΓ a ∘ qΓ ω` for `a ∈ ω` (`[x] = [a]` in `A_Γ` for `x, a` in one block: `mk_single_eq`).
* `aΓEquiv : A_Γ ≃ (Blk (π Γ) → Λ)`, so `A_Γ` is free and finite; `H²K` of the total cone is free and finite
  (`cokE`), and so is the retract `H²K` of the `G'`-cone (`h2Q ∘ h2J = id`, free over a local ring).
* `trace_aΓ_blk`: for `π(ψ^m) a γ a⁻¹ ∈ π(Γ)`, `Tr(eBΓ [a] ∘ rRepΓ γ⁻¹ ∘ (c • lftΓ ψ)^m | A_Γ) = c^m`;
  with `trace_h2_tot`: `trace_h2_tot_blk`, `Tr(h2PB [a] ∘ h2Op γ ψ^m | H²K) = c^m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh MonoidAlgebra Representation

section TotC

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf]

variable (Λ Gf) in
/-- The sum of all coefficients. -/
def totC : MonoidAlgebra Λ Gf →ₗ[Λ] Λ where
  toFun F := ∑ x, F.coeff x
  map_add' F F' := by
    simp only [coeff_add, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r F := by
    simp only [coeff_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem totC_apply (F : MonoidAlgebra Λ Gf) : totC Λ Gf F = ∑ x, F.coeff x := rfl

theorem totC_single_mul (u : Gf) (F : MonoidAlgebra Λ Gf) : totC Λ Gf (single u 1 * F) = totC Λ Gf F := by
  simp only [totC_apply, coeff_single_mul_apply, one_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft u⁻¹) _ _ fun x => rfl

theorem totC_mul_single (v : Gf) (F : MonoidAlgebra Λ Gf) : totC Λ Gf (F * single v 1) = totC Λ Gf F := by
  simp only [totC_apply, coeff_mul_single_apply, mul_one]
  exact Fintype.sum_equiv (Equiv.mulRight v⁻¹) _ _ fun x => rfl

theorem totC_single (x : Gf) (r : Λ) : totC Λ Gf (single x r) = r := by
  classical
  rw [totC_apply, Fintype.sum_eq_single x, coeff_single, Finsupp.single_eq_same]
  intro y hy
  rw [coeff_single, Finsupp.single_apply, if_neg (Ne.symm hy)]

end TotC

section Blocks

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] [Fintype (Γ.map π)]

end Blocks

section Trace

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] [Fintype (Γ.map π)]

end Trace

section TotH2

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] (hπ : IsOpen (π.ker : Set G))

variable (γ : Gf) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (c : Λ) (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π) (ht : Function.Bijective t)

end TotH2

section KN

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G) {H G' : Subgroup G} (σH : Representation Λ (H.subgroupOf G') Λ) (hπ : IsOpen (π.ker : Set G)) (hΓ : Γ ≤ G') (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H) (hσ : ∀ h, σH h = 1) (a : Gf)

end KN

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Amb =====
section

/-!
# S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group

For subgroups `Δ₁ ≤ G₁`, `Δ₂ ≤ G₂`, a continuous isomorphism `e : Δ₁ ≃ₜ* Δ₂` intertwining `ρ₁` and `ρ₂`
(`Intw`) and matching the boundary subgroups (`IntwI`), the cocycle and cohomology groups are transported:
`z1Tr : Z¹(Δ₁, ρ₁) ≃ Z¹(Δ₂, ρ₂)`, `h1Tr`, `z1cTr`, `h1cTr` and (with `infTr` on `Δ ⊓ I s`) `h2kTr` on the cone `H²`.
Used for the ambient change `G ⇝ K·Γ` in the disconnected case of lisse duality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh

noncomputable section

section Tr

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] {M : Type} [AddCommGroup M] [Module k M]
  {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M} {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂}

/-- `e` intertwines `ρ₁` and `ρ₂`. -/
def Intw (ρ₁ : Representation k G₁ M) (ρ₂ : Representation k G₂ M) (e : Δ₁ ≃ₜ* Δ₂) : Prop :=
  ∀ g : Δ₁, ρ₁ g = ρ₂ (e g)

theorem Intw.symm {e : Δ₁ ≃ₜ* Δ₂} (h : Intw ρ₁ ρ₂ e) : Intw ρ₂ ρ₁ e.symm := fun g => by
  rw [h (e.symm g), ContinuousMulEquiv.apply_symm_apply]

variable {e : Δ₁ ≃ₜ* Δ₂}

theorem z1_comp (h : Intw ρ₁ ρ₂ e) {c : Δ₂ → M} (hc : c ∈ Z1 ρ₂ Δ₂) : c ∘ e ∈ Z1 ρ₁ Δ₁ := by
  obtain ⟨hl, hco⟩ := (mem_Z1 ρ₂ Δ₂ c).1 hc
  refine (mem_Z1 ρ₁ Δ₁ _).2 ⟨hl.comp_continuous (map_continuous e), fun a b => ?_⟩
  simp only [Function.comp_apply, map_mul, hco, h a]

theorem b1_comp (h : Intw ρ₁ ρ₂ e) {c : Δ₂ → M} (hc : c ∈ B1 ρ₂ Δ₂) : c ∘ e ∈ B1 ρ₁ Δ₁ := by
  obtain ⟨hz, m, hm⟩ := (mem_B1 ρ₂ Δ₂ c).1 hc
  exact (mem_B1 ρ₁ Δ₁ _).2 ⟨z1_comp h hz, m, fun g => by simp only [Function.comp_apply, hm, h g]⟩

theorem comp_symm_comp {X : Type} (c : Δ₂ → X) : (c ∘ e) ∘ e.symm = c :=
  funext fun g => by simp

theorem comp_comp_symm {X : Type} (c : Δ₁ → X) : (c ∘ e.symm) ∘ e = c :=
  funext fun g => by simp

/-- `Z¹` transported along `e`: `c ↦ c ∘ e⁻¹`. -/
def z1Tr (h : Intw ρ₁ ρ₂ e) : Z1 ρ₁ Δ₁ ≃ₗ[k] Z1 ρ₂ Δ₂ where
  toFun c := ⟨(c : Δ₁ → M) ∘ e.symm, z1_comp h.symm c.2⟩
  invFun c := ⟨(c : Δ₂ → M) ∘ e, z1_comp h c.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (comp_comp_symm (e := e) _)
  right_inv _ := Subtype.ext (comp_symm_comp (e := e) _)

theorem z1Tr_apply (h : Intw ρ₁ ρ₂ e) (c : Z1 ρ₁ Δ₁) (g : Δ₂) :
    (z1Tr h c : Δ₂ → M) g = (c : Δ₁ → M) (e.symm g) := rfl

theorem z1Tr_symm_apply (h : Intw ρ₁ ρ₂ e) (c : Z1 ρ₂ Δ₂) (g : Δ₁) :
    ((z1Tr h).symm c : Δ₁ → M) g = (c : Δ₂ → M) (e g) := rfl

/-- `H¹` transported along `e`. -/
def h1Tr (h : Intw ρ₁ ρ₂ e) : H1 ρ₁ Δ₁ ≃ₗ[k] H1 ρ₂ Δ₂ :=
  Submodule.Quotient.equiv _ _ (z1Tr h) (by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    constructor
    · intro hx
      have := b1_comp h.symm hx
      show (x : Δ₂ → M) ∈ B1 ρ₂ Δ₂
      rw [← comp_symm_comp (e := e) (x : Δ₂ → M)]
      exact this
    · exact b1_comp h)

theorem h1Tr_mk (h : Intw ρ₁ ρ₂ e) (c : Z1 ρ₁ Δ₁) :
    h1Tr h (Submodule.Quotient.mk c) = Submodule.Quotient.mk (z1Tr h c) := rfl

/-! ## The compactly supported part -/

variable {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

/-- `e` matches the boundary subgroups. -/
def IntwI (I₁ : S → Subgroup G₁) (I₂ : S → Subgroup G₂) (e : Δ₁ ≃ₜ* Δ₂) : Prop :=
  ∀ (s : S) (g : Δ₁), (g : G₁) ∈ I₁ s ↔ ((e g : Δ₂) : G₂) ∈ I₂ s

theorem IntwI.symm (hI : IntwI I₁ I₂ e) : IntwI I₂ I₁ e.symm := fun s g => by
  rw [hI s (e.symm g), ContinuousMulEquiv.apply_symm_apply]

theorem z1c_comp (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) {p : (Δ₂ → M) × (S → M)} (hp : p ∈ Z1c ρ₂ Δ₂ I₂) :
    (p.1 ∘ e, p.2) ∈ Z1c ρ₁ Δ₁ I₁ := by
  obtain ⟨hz, hb⟩ := (mem_Z1c ρ₂ Δ₂ I₂ p).1 hp
  refine (mem_Z1c ρ₁ Δ₁ I₁ _).2 ⟨z1_comp h hz, fun s g hg => ?_⟩
  simp only [Function.comp_apply, hb s (e g) ((hI s g).1 hg), h g]

theorem b1c_comp (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) {p : (Δ₂ → M) × (S → M)} (hp : p ∈ B1c ρ₂ Δ₂ I₂) :
    (p.1 ∘ e, p.2) ∈ B1c ρ₁ Δ₁ I₁ := by
  obtain ⟨hz, m, hm, hm'⟩ := hp
  exact ⟨z1c_comp h hI hz, m, fun g => by simp only [Function.comp_apply, hm, h g], hm'⟩

/-- `Z¹_c` transported along `e`: `(c, m) ↦ (c ∘ e⁻¹, m)`. -/
def z1cTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) : Z1c ρ₁ Δ₁ I₁ ≃ₗ[k] Z1c ρ₂ Δ₂ I₂ where
  toFun p := ⟨((p : (Δ₁ → M) × (S → M)).1 ∘ e.symm, (p : (Δ₁ → M) × (S → M)).2), z1c_comp h.symm hI.symm p.2⟩
  invFun p := ⟨((p : (Δ₂ → M) × (S → M)).1 ∘ e, (p : (Δ₂ → M) × (S → M)).2), z1c_comp h hI p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (Prod.ext (comp_comp_symm (e := e) _) rfl)
  right_inv _ := Subtype.ext (Prod.ext (comp_symm_comp (e := e) _) rfl)

theorem z1cTr_apply (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (p : Z1c ρ₁ Δ₁ I₁) :
    (z1cTr h hI p : (Δ₂ → M) × (S → M)) =
      ((p : (Δ₁ → M) × (S → M)).1 ∘ e.symm, (p : (Δ₁ → M) × (S → M)).2) := rfl

/-- `H¹_c` transported along `e`. -/
def h1cTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) : H1c ρ₁ Δ₁ I₁ ≃ₗ[k] H1c ρ₂ Δ₂ I₂ :=
  Submodule.Quotient.equiv _ _ (z1cTr h hI) (by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    constructor
    · intro hx
      have := b1c_comp h.symm hI.symm hx
      have key : (((x : (Δ₂ → M) × (S → M)).1 ∘ e) ∘ e.symm, (x : (Δ₂ → M) × (S → M)).2) =
          (x : (Δ₂ → M) × (S → M)) := Prod.ext (comp_symm_comp (e := e) _) rfl
      show (x : (Δ₂ → M) × (S → M)) ∈ B1c ρ₂ Δ₂ I₂
      rw [← key]
      exact this
    · exact b1c_comp h hI)

theorem h1cTr_mk (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (p : Z1c ρ₁ Δ₁ I₁) :
    h1cTr h hI (Submodule.Quotient.mk p) = Submodule.Quotient.mk (z1cTr h hI p) := rfl

/-! ## The boundary groups and the cone `H²` -/

variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

end Tr

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ShapFrob =====
section

/-!
# S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius

Setting of `Def_RP_CurveCoh_ShapiroCone`: `H = π₁(U) ≤ G = π₁(V)`, `Γ = π₁^geo(V)` normal, boundary data
`I`, `J`, `π`, `xT`. A Frobenius lift `ψ ∈ H` acts on the cone complex of `V` (with boundary data `τ`, `h`) and on the
cone complex of `U` (with `τ'`, `h'`).

* `FrobMatch`: the two sets of boundary data match: `π (τ' t) = τ (π t)` and
  `(h'_t x_{τ' t})⁻¹ (ψ⁻¹ x_t ψ h_{π t}) ∈ I (τ (π t))`;
* `resEvc_twistc` (cocycle level, exact equality) and `shapiroH1c_frob`:
  `shapiroH1c ∘ frobH1c(f_* M; ψ, τ, h) = frobH1c(M; ψ, τ', h') ∘ shapiroH1c`;
* `trace_pow_eq_of_comm`, `trace_frob_shapiro`: equal traces of all powers through `shapiroH1cEquiv`;
* `conjΓ_tr`, `h1cTr_frob`: the ambient transport `h1cTr` (along `e : Δ₁ ≃ₜ* Δ₂` restricting `E : G₁ ≃* G₂`)
  commutes with the Frobenius on `H¹_c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Representation

/-! ## Traces through a linear equivalence -/

theorem conj_pow_end {k : Type} [CommRing k] {N₁ N₂ : Type} [AddCommGroup N₁] [Module k N₁] [AddCommGroup N₂]
    [Module k N₂] (e : N₁ ≃ₗ[k] N₂) (f : Module.End k N₁) (m : ℕ) : e.conj (f ^ m) = e.conj f ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    ext x
    simp [LinearEquiv.conj_apply]
  | succ m ih =>
    rw [pow_succ, pow_succ, ← ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearEquiv.conj_comp]

theorem trace_pow_eq_of_comm {k : Type} [CommRing k] {N₁ N₂ : Type} [AddCommGroup N₁] [Module k N₁]
    [AddCommGroup N₂] [Module k N₂] (e : N₁ ≃ₗ[k] N₂) (f : Module.End k N₁) (g : Module.End k N₂)
    (hfg : ∀ x, e (f x) = g (e x)) (m : ℕ) :
    LinearMap.trace k N₁ (f ^ m) = LinearMap.trace k N₂ (g ^ m) := by
  have hc : e.conj f = g := by
    ext x
    simp [LinearEquiv.conj_apply, hfg]
  rw [← hc, ← conj_pow_end, LinearMap.trace_conj']

/-! ## Shapiro and Frobenius -/

section Shap

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (Γ H : Subgroup G) [Γ.Normal] (σ : Representation k H M)
  {S T : Type} (I : S → Subgroup G) (J : T → Subgroup H) (π : T → S) (xT : T → Γ)

end Shap

/-! ## Ambient transport commutes with Frobenius -/

section Amb

open CupDuality

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] {M : Type} [AddCommGroup M] [Module k M]
  {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M} {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂}
  [Δ₁.Normal] [Δ₂.Normal] {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

theorem conjΓ_tr (E : G₁ ≃* G₂) (hE : ∀ g : Δ₁, ((e g : Δ₂) : G₂) = E g) (ψ : G₁) (g : Δ₂) :
    conjΓ Δ₁ ψ (e.symm g) = e.symm (conjΓ Δ₂ (E ψ) g) := by
  have key : E ((e.symm g : Δ₁) : G₁) = (g : G₂) := by
    rw [← hE, ContinuousMulEquiv.apply_symm_apply]
  have h1 : e (conjΓ Δ₁ ψ (e.symm g)) = conjΓ Δ₂ (E ψ) g :=
    Subtype.ext (by rw [hE, conjΓ_val, conjΓ_val, map_mul, map_mul, map_inv, key])
  rw [← h1, ContinuousMulEquiv.symm_apply_apply]

/-- **Ambient transport commutes with Frobenius**: if `e : Δ₁ ≃ₜ* Δ₂` is the restriction of `E : G₁ ≃* G₂` and
`ρ₁ ψ = ρ₂ (E ψ)`, then `h1cTr ∘ frobH1c(ρ₁; ψ, τ, h) = frobH1c(ρ₂; E ψ, τ, e ∘ h) ∘ h1cTr`. -/
theorem h1cTr_frob (hρ : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (E : G₁ ≃* G₂)
    (hE : ∀ g : Δ₁, ((e g : Δ₂) : G₂) = E g) (ψ : G₁) (hψ : ρ₁ ψ = ρ₂ (E ψ)) (τ : S → S) (h₁ : S → Δ₁)
    (hI₁ : BdryCompat Δ₁ I₁ ψ τ h₁) (hI₂ : BdryCompat Δ₂ I₂ (E ψ) τ (fun s => e (h₁ s)))
    (x : H1c ρ₁ Δ₁ I₁) :
    h1cTr hρ hI (frobH1c ρ₁ Δ₁ I₁ ψ τ h₁ hI₁ x) =
      frobH1c ρ₂ Δ₂ I₂ (E ψ) τ (fun s => e (h₁ s)) hI₂ (h1cTr hρ hI x) := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
  refine congrArg (H1c.mk ρ₂ Δ₂ I₂) (Subtype.ext (Prod.ext (funext fun g => ?_) (funext fun s => ?_)))
  · change ρ₁ ψ ((p : (Δ₁ → M) × (S → M)).1 (conjΓ Δ₁ ψ (e.symm g))) =
      ρ₂ (E ψ) ((p : (Δ₁ → M) × (S → M)).1 (e.symm (conjΓ Δ₂ (E ψ) g)))
    rw [hψ, conjΓ_tr E hE]
  · change ρ₁ ψ (ρ₁ (h₁ s) ((p : (Δ₁ → M) × (S → M)).2 (τ s)) - (p : (Δ₁ → M) × (S → M)).1 (h₁ s)) =
      ρ₂ (E ψ) (ρ₂ (e (h₁ s)) ((p : (Δ₁ → M) × (S → M)).2 (τ s)) -
        (p : (Δ₁ → M) × (S → M)).1 (e.symm (e (h₁ s))))
    rw [hψ, hρ (h₁ s), ContinuousMulEquiv.symm_apply_apply]

end Amb

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_AmbSub =====
section

/-!
# S4-Lefschetz, L4i part 1: Shapiro with Frobenius inside an ambient subgroup `G' ≤ G`

The cone Shapiro isomorphism `shapiroH1cEquiv` needs `G = H·Γ`. For a cover `E` whose constant field is `𝔽_{q^d}`
this holds only inside the ambient subgroup `G' = H·Γ` (the degree-divisible-by-`d` part of `G`). Here every piece
of Shapiro data for `(G, Γ, H, I, J, π, x)` is moved to `(G', Γ ∩ G', H ∩ G', I ∩ G', J, π, x)` (all by definitional
unfolding: the coercions are literal), and `Γ ∩ H` computed inside `G'` is identified with `Γ ∩ H` by `eGeoT`.

* `inertiaLift_sub`, `dCover_sub`, `dDisj_sub`, `cosetReps_sub`, `hcov_sub` (`hcov'_of_le_sup`), `isOpen_sub`,
  `bdryCompat_sub`, `bdryCompat_geo_sub`, `frobMatch_sub`;
* `eGeoT : (Γ ∩ G') ∩ (H ∩ G') ≃ₜ* Γ ∩ H`, `EH : H ∩ G' ≃* H`, `intw_sub`, `intwI_sub`, `trace_geo_sub`;
* **`trace_shapiro_sub`**: `Tr(F^m | H¹_c(G'; Ind_H^{G'} σ)) = Tr(F^m | H¹_c(Γ ∩ H; σ))` for `G' = H·Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Representation CupDuality

section AmbSub

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] {Γ H G' : Subgroup G}
  {S T : Type} {I : S → Subgroup G} {J : T → Subgroup H} {π : T → S} {xT : T → Γ}

variable (H G') in
/-- `H ∩ G'` (inside `G'`) maps to `H`. -/
def downH : H.subgroupOf G' →* H where
  toFun x := ⟨((x : G') : G), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `H → H ∩ G'`. -/
def upH (hH : H ≤ G') (x : H) : H.subgroupOf G' := ⟨⟨x, hH x.2⟩, x.2⟩

/-! ## Shapiro data inside `G'` -/

theorem hcov'_of_le_sup [Γ.Normal] (hle : G' ≤ H ⊔ Γ) : ∀ x ∈ G', ∃ a ∈ H, ∃ b ∈ Γ, x = a * b := by
  intro x hx
  have h1 : x ∈ ((H ⊔ Γ : Subgroup G) : Set G) := hle hx
  rw [Subgroup.mul_normal H Γ] at h1
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 h1
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem isOpen_sub (hHo : IsOpen (H : Set G)) : IsOpen ((H.subgroupOf G' : Subgroup G') : Set G') :=
  hHo.preimage continuous_subtype_val

section Top

variable [IsTopologicalGroup G]

/-- The ambient isomorphism `H ∩ G' ≃* H`. -/
def EH (hH : H ≤ G') : H.subgroupOf G' ≃* H where
  toFun := downH H G'
  invFun := upH hH
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem EH_apply (hH : H ≤ G') (x : H.subgroupOf G') : EH hH x = downH H G' x := rfl

variable [Γ.Normal]

end Top

end AmbSub

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ConstExt =====
section

/-!
# S4-Lefschetz L4a: a function field over its full constant field

Let `E` be a function field over `𝔽_q` in the coordinates of S3-Places (`Algebra 𝔽_q[X] E`, `Algebra 𝔽_q(X) E`,
finite separable over `𝔽_q(X)`), but with an arbitrary constant field. Its full constant field
`k' = constField 𝔽_q E` is finite, `x = X_E` is transcendental over `k'`, and with `k'[X] → E`, `k'(X) → E` given by
`X ↦ X_E` the field `E` is a function field over `k'` (finite separable over `k'(X)`) whose full constant field is `k'`
itself (`constField_eq_bot`). So every covering curve of `U` satisfies the hypotheses of S4-CP4 over its own constant
field (`cp4_constExt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped nonZeroDivisors

namespace RamanujanPetersson
namespace Lefschetz

open Places CurveCoh GalCover CP4a

noncomputable section

section ConstExt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

/-- The full constant field `k'` of `E`, as a type. -/
abbrev Kc : Type := constField Fq E

instance decEq_ratFunc_Kc : DecidableEq (RatFunc (Kc Fq E)) := Classical.decEq _

/-- `𝔽_q(X) → k'(X)` (coefficientwise). -/
def mapPoly : Fq[X] →+* (Kc Fq E)[X] := Polynomial.mapRingHom (algebraMap Fq (Kc Fq E))

end ConstExt

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrTower =====
section

/-!
# S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure

`IsUnramifiedSub A K L` asks that the inertia groups of `Gal(L/K)` on the integral closure of `A` in `L` vanish.
If `R → S → K` is a tower with `S` integral over `R`, the integral closures of `R` and `S` in `L` are the same
subring of `L` (as `Gal(L/K)`-rings), so `unramSet S K = unramSet R K` and `maxUnram S K = maxUnram R K`.
Applications: `maxUnram (Rfin 𝔽_q F) F = maxUnram 𝔽_q[X] F`, and for a covering function field `E` with full
constant field `k'` (L4a) `maxUnram (Rfin k' E) E = maxUnram 𝔽_q[X] E` (`k'[X]` is integral over `𝔽_q[X]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover

noncomputable section

/-! ### Inertia transport along an equivariant ring isomorphism -/

section InertiaTransport

variable {G B B' : Type} [Group G] [CommRing B] [CommRing B'] [MulSemiringAction G B]
  [MulSemiringAction G B']

theorem inertia_eq_bot_of_equiv (f : B ≃+* B') (hf : ∀ (σ : G) (b : B), f (σ • b) = σ • f b)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) (Q' : Ideal B') (hQ' : Q'.IsPrime) :
    Q'.inertia G = ⊥ := by
  have hP : (Q'.comap f).IsPrime := Ideal.IsPrime.comap _
  rw [eq_bot_iff]
  intro σ hσ
  have hin : σ ∈ (Q'.comap f).inertia G := by
    intro y
    show f (σ • y - y) ∈ Q'
    rw [map_sub, hf]
    exact hσ (f y)
  rw [h _ hP] at hin
  exact hin

theorem inertia_eq_bot_iff_of_equiv (f : B ≃+* B') (hf : ∀ (σ : G) (b : B), f (σ • b) = σ • f b) :
    (∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) ↔
      (∀ Q' : Ideal B', Q'.IsPrime → Q'.inertia G = ⊥) := by
  refine ⟨inertia_eq_bot_of_equiv f hf, inertia_eq_bot_of_equiv f.symm ?_⟩
  intro σ b
  apply f.injective
  rw [hf, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end InertiaTransport

/-! ### Integral towers `R → S → K` give the same `K_U` -/

section Tower

variable (R S K : Type) [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] [Algebra.IsIntegral R S]

theorem isScalarTower_sub (L : IntermediateField K (AlgebraicClosure K)) : IsScalarTower R S L :=
  IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    show algebraMap R (AlgebraicClosure K) r = algebraMap S (AlgebraicClosure K) (algebraMap R S r)
    rw [IsScalarTower.algebraMap_apply R K (AlgebraicClosure K),
      IsScalarTower.algebraMap_apply S K (AlgebraicClosure K), ← IsScalarTower.algebraMap_apply R S K]

theorem isIntegral_iff_tower (L : IntermediateField K (AlgebraicClosure K)) (x : L) :
    IsIntegral S x ↔ IsIntegral R x := by
  have := isScalarTower_sub R S K L
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

/-- The integral closures of `S` and of `R` in `L` are the same subring. -/
def intClEquiv (L : IntermediateField K (AlgebraicClosure K)) :
    integralClosure S L ≃+* integralClosure R L where
  toFun x := ⟨x.1, (isIntegral_iff_tower R S K L x.1).1 x.2⟩
  invFun x := ⟨x.1, (isIntegral_iff_tower R S K L x.1).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem intClEquiv_val (L : IntermediateField K (AlgebraicClosure K)) (x : integralClosure S L) :
    ((intClEquiv R S K L x : L)) = (x : L) := rfl

theorem intClEquiv_smul (L : IntermediateField K (AlgebraicClosure K)) (σ : L ≃ₐ[K] L)
    (y : integralClosure S L) : intClEquiv R S K L (σ • y) = σ • intClEquiv R S K L y :=
  Subtype.ext rfl

theorem isUnramifiedSub_iff_tower (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub S K L ↔ IsUnramifiedSub R K L :=
  inertia_eq_bot_iff_of_equiv (intClEquiv R S K L) (intClEquiv_smul R S K L)

theorem unramSet_eq_tower : unramSet S K = unramSet R K := by
  ext L
  exact and_congr Iff.rfl (and_congr Iff.rfl (isUnramifiedSub_iff_tower R S K L))

theorem maxUnram_eq_tower : maxUnram S K = maxUnram R K := by
  rw [maxUnram_eq_sSup, maxUnram_eq_sSup, unramSet_eq_tower R S K]

end Tower

/-! ### Applications: `Rfin`, and `k'[X]` over `𝔽_q[X]` -/

section Apps

variable (Fq : Type) [Field Fq] [Fintype Fq]

theorem maxUnram_rfin (F : Type) [Field F] [Algebra Fq[X] F] :
    maxUnram (FunctionField.ringOfIntegers Fq F) F = maxUnram Fq[X] F :=
  have : Algebra.IsIntegral Fq[X] (FunctionField.ringOfIntegers Fq F) :=
    integralClosure.AlgebraIsIntegral
  maxUnram_eq_tower Fq[X] (FunctionField.ringOfIntegers Fq F) F

variable [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

/-- `𝔽_q[X] → k'[X]` (coefficientwise), as an algebra (local use only). -/
abbrev algPolyPoly : Algebra Fq[X] (Kc Fq E)[X] := (mapPoly Fq E).toAlgebra

end Apps

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_OinfInt =====
section

/-!
# S4-Lefschetz L4b, part 1: `O_∞(k)` is integral over `O_∞(𝔽_q)` for a finite extension `k / 𝔽_q`

* `frobK`, `mem_range_of_pow_card`: the elements of `k` fixed by `x ↦ x^q` are those of `𝔽_q`.
* `conjPoly`, `exists_rationalize`: every `Q ≠ 0` in `k[X]` has a multiple `Q N = R` with `R ∈ 𝔽_q[X]`
  (`R = ∏_j Q^{σ^j}`, the norm).
* `isIntegral_of_mem_Oinf`: for any algebra `𝔽_q(X) → k(X)` extending `𝔽_q[X] → k[X]`, every `f ∈ O_∞(k)`
  is integral over `O_∞(𝔽_q)` (`f = P N / R` with `deg (P N) ≤ deg R`, a sum of constants times `X^n / R`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places

noncomputable section

section Frob

variable (Fq k : Type) [Field Fq] [Fintype Fq] [Field k] [Fintype k] [Algebra Fq k]

/-- The `q`-Frobenius of `k / 𝔽_q`. -/
def frobK : k ≃ₐ[Fq] k := FiniteField.frobeniusAlgEquivOfAlgebraic Fq k

theorem frobK_apply (x : k) : frobK Fq k x = x ^ Fintype.card Fq := rfl

theorem frobK_pow_finrank : frobK Fq k ^ Module.finrank Fq k = 1 := by
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (K := Fq) (L := k)]
  exact pow_orderOf_eq_one (FiniteField.frobeniusAlgEquivOfAlgebraic Fq k)

theorem mem_range_of_pow_card (x : k) (hx : x ^ Fintype.card Fq = x) :
    x ∈ Set.range (algebraMap Fq k) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro f
  obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (K := Fq) (L := k)).2 f
  show (FiniteField.frobeniusAlgEquivOfAlgebraic Fq k ^ n.1) x = x
  generalize n.1 = m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, AlgEquiv.mul_apply, show FiniteField.frobeniusAlgEquivOfAlgebraic Fq k x = x from hx, ih]

/-- The Frobenius conjugates `Q^{σ^j}` of a polynomial. -/
def conjPoly (Q : k[X]) (j : ℕ) : k[X] := Q.map ((frobK Fq k ^ j : k ≃ₐ[Fq] k) : k →+* k)

theorem conjPoly_coeff (Q : k[X]) (j n : ℕ) :
    (conjPoly Fq k Q j).coeff n = (frobK Fq k ^ j) (Q.coeff n) := by
  rw [conjPoly, Polynomial.coeff_map]
  rfl

theorem conjPoly_zero (Q : k[X]) : conjPoly Fq k Q 0 = Q := by
  ext n
  rw [conjPoly_coeff, pow_zero]
  rfl

theorem conjPoly_finrank (Q : k[X]) : conjPoly Fq k Q (Module.finrank Fq k) = Q := by
  ext n
  rw [conjPoly_coeff, frobK_pow_finrank]
  rfl

theorem conjPoly_succ (Q : k[X]) (j : ℕ) :
    (conjPoly Fq k Q j).map ((frobK Fq k : k ≃ₐ[Fq] k) : k →+* k) = conjPoly Fq k Q (j + 1) := by
  ext n
  rw [Polynomial.coeff_map, conjPoly_coeff, conjPoly_coeff, pow_succ', AlgEquiv.mul_apply]
  rfl

theorem conjPoly_ne_zero {Q : k[X]} (hQ : Q ≠ 0) (j : ℕ) : conjPoly Fq k Q j ≠ 0 :=
  (Polynomial.map_ne_zero_iff (RingHom.injective _)).2 hQ

theorem conjPoly_prod_fixed (Q : k[X]) (hQ : Q ≠ 0) :
    (∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j).map
        ((frobK Fq k : k ≃ₐ[Fq] k) : k →+* k) =
      ∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j := by
  rw [Polynomial.map_prod]
  simp only [conjPoly_succ]
  have h1 := Finset.prod_range_succ' (conjPoly Fq k Q) (Module.finrank Fq k)
  have h2 := Finset.prod_range_succ (conjPoly Fq k Q) (Module.finrank Fq k)
  have h3 := h1.symm.trans h2
  rw [conjPoly_zero, conjPoly_finrank] at h3
  exact mul_right_cancel₀ hQ h3

/-- Rationalizing a denominator: `Q * N ∈ 𝔽_q[X]`. -/
theorem exists_rationalize (Q : k[X]) (hQ : Q ≠ 0) :
    ∃ (N : k[X]) (R : Fq[X]), R ≠ 0 ∧ Q * N = R.map (algebraMap Fq k) := by
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank Fq k = d + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := Fq) (M := k)).ne'
  have hmem : (∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j) ∈
      (Polynomial.mapRingHom (algebraMap Fq k)).range := by
    rw [Polynomial.mem_map_range]
    intro n
    have h := congrArg (fun p : k[X] => p.coeff n) (conjPoly_prod_fixed Fq k Q hQ)
    simp only [Polynomial.coeff_map] at h
    obtain ⟨c, hc⟩ := mem_range_of_pow_card Fq k _ h
    exact ⟨c, hc⟩
  obtain ⟨R, hR⟩ := hmem
  have hne : (∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => conjPoly_ne_zero Fq k hQ j
  have hR' : R.map (algebraMap Fq k) = ∏ j ∈ Finset.range (Module.finrank Fq k), conjPoly Fq k Q j := hR
  refine ⟨∏ j ∈ Finset.range d, conjPoly Fq k Q (j + 1), R, ?_, ?_⟩
  · rintro rfl
    apply hne
    rw [← hR', Polynomial.map_zero]
  · rw [hR', hd, Finset.prod_range_succ' (conjPoly Fq k Q) d, conjPoly_zero, mul_comm]

end Frob

section OinfInt

variable (Fq k : Type) [Field Fq] [Fintype Fq] [Field k] [Fintype k] [Algebra Fq k]
  [DecidableEq (RatFunc Fq)] [DecidableEq (RatFunc k)] [Algebra (RatFunc Fq) (RatFunc k)]
  (hι : ∀ p : Fq[X], algebraMap (RatFunc Fq) (RatFunc k) (algebraMap Fq[X] (RatFunc Fq) p) =
    algebraMap k[X] (RatFunc k) (p.map (algebraMap Fq k)))

theorem isIntegral_const (c : k) : IsIntegral (Oinf Fq) (algebraMap k (RatFunc k) c) := by
  refine ⟨X ^ Fintype.card k - X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub (by rw [degree_X]; exact_mod_cast Fintype.one_lt_card)
  · rw [eval₂_sub, eval₂_X_pow, eval₂_X, ← map_pow, FiniteField.pow_card, sub_self]

include hι in
/-- **L4b core**: `O_∞(k)` is integral over `O_∞(𝔽_q)`. -/
theorem isIntegral_of_mem_Oinf (f : RatFunc k) (hf : f ∈ Oinf k) : IsIntegral (Oinf Fq) f := by
  classical
  by_cases h0 : f = 0
  · rw [h0]
    exact isIntegral_zero
  have hP0 : f.num ≠ 0 := RatFunc.num_ne_zero h0
  have hdeg : (f.num.natDegree : ℤ) - f.denom.natDegree ≤ 0 := by
    have h := (mem_Oinf_iff' k h0).1 hf
    rwa [← RatFunc.num_div_denom f, intDegree_div_polys k hP0 (RatFunc.denom_ne_zero f)] at h
  obtain ⟨N, R, hR0, hQN⟩ := exists_rationalize Fq k f.denom (RatFunc.denom_ne_zero f)
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hQN
    exact hR0 (Polynomial.map_injective _ (algebraMap Fq k).injective (by rw [← hQN, Polynomial.map_zero]))
  have h3 : (f.denom * N).natDegree = R.natDegree := by
    rw [hQN, natDegree_map_eq_of_injective (algebraMap Fq k).injective R]
  have hQNdeg : (f.denom * N).natDegree = f.denom.natDegree + N.natDegree :=
    natDegree_mul (RatFunc.denom_ne_zero f) hN0
  have hA : ∀ p : k[X], p ≠ 0 → algebraMap k[X] (RatFunc k) p ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2 hp
  have hf' : f = algebraMap k[X] (RatFunc k) (f.num * N) /
      algebraMap k[X] (RatFunc k) (R.map (algebraMap Fq k)) := by
    rw [← hQN, map_mul, map_mul, mul_div_mul_right _ _ (hA N hN0), RatFunc.num_div_denom]
  rw [hf', as_sum_support_C_mul_X_pow (f.num * N), map_sum, Finset.sum_div]
  refine IsIntegral.sum _ fun n hn => ?_
  have hn' : n ≤ R.natDegree := by
    have h1 := le_natDegree_of_mem_supp n hn
    have h2 := natDegree_mul_le (p := f.num) (q := N)
    omega
  rw [map_mul, mul_div_assoc]
  refine IsIntegral.mul ?_ ?_
  · have hc : algebraMap k[X] (RatFunc k) (C ((f.num * N).coeff n)) =
        algebraMap k (RatFunc k) ((f.num * N).coeff n) := by
      rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
    rw [hc]
    exact isIntegral_const Fq k _
  · have hXn : algebraMap Fq[X] (RatFunc Fq) (X ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).2 (pow_ne_zero n X_ne_zero)
    have hRn : algebraMap Fq[X] (RatFunc Fq) R ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).2 hR0
    have hz : algebraMap Fq[X] (RatFunc Fq) (X ^ n) / algebraMap Fq[X] (RatFunc Fq) R ∈ Oinf Fq := by
      rw [mem_Oinf_iff' Fq (div_ne_zero hXn hRn), intDegree_div_polys Fq (pow_ne_zero n X_ne_zero) hR0,
        natDegree_X_pow]
      omega
    have hz' : algebraMap k[X] (RatFunc k) (X ^ n) / algebraMap k[X] (RatFunc k) (R.map (algebraMap Fq k)) =
        algebraMap (Oinf Fq) (RatFunc k) ⟨_, hz⟩ := by
      rw [IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) (RatFunc k)]
      show _ = algebraMap (RatFunc Fq) (RatFunc k)
        (algebraMap Fq[X] (RatFunc Fq) (X ^ n) / algebraMap Fq[X] (RatFunc Fq) R)
      rw [map_div₀, hι, hι, Polynomial.map_pow, Polynomial.map_X]
    rw [hz']
    exact isIntegral_algebraMap

end OinfInt

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrIn =====
section

/-!
# S4-Lefschetz L4c (part 2): unramified subextensions in any algebraically closed field

`UnrIn A K Ω L`: `L` is a finite Galois subextension of `Ω/K` whose inertia groups on the integral closure of `A`
vanish. For `Ω = K̄` (`AlgebraicClosure K`) this is `unramSet A K` (`unramSet_eq_unrIn`, by `rfl`). The predicate is
transported along any `K`-isomorphism `ι : Ω₁ ≃ₐ[K] Ω₂` (`unrIn_map_iff`), and membership in `K_U` is membership
in one unramified `L` (`mem_maxUnram_iff`), so `y ∈ K_U ↔ ∃ L, UnrIn A K Ω₂ L ∧ ι y ∈ L` (`mem_maxUnram_iff_of_equiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

/-! ### Inertia transport along an equivariant ring isomorphism and a group isomorphism -/

section InertiaTransport2

variable {G G' B B' : Type} [Group G] [Group G'] [CommRing B] [CommRing B'] [MulSemiringAction G B]
  [MulSemiringAction G' B']

theorem inertia_eq_bot_of_equiv₂ (f : B ≃+* B') (g : G ≃* G') (hf : ∀ (σ : G) (b : B), f (σ • b) = g σ • f b)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) (Q' : Ideal B') (hQ' : Q'.IsPrime) :
    Q'.inertia G' = ⊥ := by
  have hP : (Q'.comap f).IsPrime := Ideal.IsPrime.comap _
  rw [eq_bot_iff]
  intro σ' hσ'
  have hin : g.symm σ' ∈ (Q'.comap f).inertia G := by
    intro y
    show f (g.symm σ' • y - y) ∈ Q'
    rw [map_sub, hf, MulEquiv.apply_symm_apply]
    exact hσ' (f y)
  rw [h _ hP, Subgroup.mem_bot] at hin
  rw [Subgroup.mem_bot, ← g.apply_symm_apply σ', hin, map_one]

end InertiaTransport2

/-! ### `UnrIn` and its transport -/

section UnrIn

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- `L` is a finite Galois subextension of `Ω/K`, unramified over `A`. -/
def UnrIn (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
    (L : IntermediateField K Ω) : Prop :=
  FiniteDimensional K L ∧ IsGalois K L ∧
    ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.inertia (L ≃ₐ[K] L) = ⊥

theorem unramSet_eq_unrIn : unramSet A K = {L | UnrIn A K (AlgebraicClosure K) L} := rfl

variable {A K} {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [Algebra K Ω₁] [Algebra K Ω₂] [Algebra A Ω₁]
  [Algebra A Ω₂] [IsScalarTower A K Ω₁] [IsScalarTower A K Ω₂]

/-- The integral closures of `A` in `L` and in its image under `e`. -/
def intClMap {L₁ : IntermediateField K Ω₁} {L₂ : IntermediateField K Ω₂} (e : L₁ ≃ₐ[K] L₂) :
    integralClosure A L₁ ≃+* integralClosure A L₂ where
  toFun x := ⟨e x, x.2.map (e.toAlgHom.restrictScalars A)⟩
  invFun x := ⟨e.symm x, x.2.map (e.symm.toAlgHom.restrictScalars A)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv x := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

theorem intClMap_smul {L₁ : IntermediateField K Ω₁} {L₂ : IntermediateField K Ω₂} (e : L₁ ≃ₐ[K] L₂)
    (σ : L₁ ≃ₐ[K] L₁) (y : integralClosure A L₁) :
    intClMap (A := A) e (σ • y) = AlgEquiv.autCongr e σ • intClMap (A := A) e y := by
  apply Subtype.ext
  show e (σ (y : L₁)) = (AlgEquiv.autCongr e σ) (e (y : L₁))
  simp [AlgEquiv.autCongr_apply]

theorem unrIn_of_algEquiv {L₁ : IntermediateField K Ω₁} {L₂ : IntermediateField K Ω₂} (e : L₁ ≃ₐ[K] L₂)
    (h : UnrIn A K Ω₁ L₁) : UnrIn A K Ω₂ L₂ := by
  obtain ⟨hfd, hgal, hun⟩ := h
  refine ⟨LinearEquiv.finiteDimensional e.toLinearEquiv, IsGalois.of_algEquiv e, ?_⟩
  exact inertia_eq_bot_of_equiv₂ (intClMap (A := A) e) (AlgEquiv.autCongr e) (intClMap_smul e) hun

theorem map_map_symm (ι : Ω₁ ≃ₐ[K] Ω₂) (L : IntermediateField K Ω₁) :
    (L.map (ι : Ω₁ →ₐ[K] Ω₂)).map (ι.symm : Ω₂ →ₐ[K] Ω₁) = L := by
  ext x
  simp only [IntermediateField.mem_map]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨ι x, ⟨x, hx, rfl⟩, by simp⟩

theorem unrIn_map_iff (ι : Ω₁ ≃ₐ[K] Ω₂) (L : IntermediateField K Ω₁) :
    UnrIn A K Ω₂ (L.map (ι : Ω₁ →ₐ[K] Ω₂)) ↔ UnrIn A K Ω₁ L := by
  refine ⟨fun h => ?_, fun h => unrIn_of_algEquiv (L.equivMap (ι : Ω₁ →ₐ[K] Ω₂)) h⟩
  have h' := unrIn_of_algEquiv ((L.map (ι : Ω₁ →ₐ[K] Ω₂)).equivMap (ι.symm : Ω₂ →ₐ[K] Ω₁)) h
  rwa [map_map_symm] at h'

/-- Unramified subextensions containing a point correspond under `ι`. -/
theorem exists_unrIn_iff (ι : Ω₁ ≃ₐ[K] Ω₂) (y : Ω₁) :
    (∃ L : IntermediateField K Ω₁, UnrIn A K Ω₁ L ∧ y ∈ L) ↔
      (∃ L : IntermediateField K Ω₂, UnrIn A K Ω₂ L ∧ ι y ∈ L) := by
  constructor
  · rintro ⟨L, hL, hy⟩
    exact ⟨L.map (ι : Ω₁ →ₐ[K] Ω₂), (unrIn_map_iff ι L).2 hL, ⟨y, hy, rfl⟩⟩
  · rintro ⟨L, hL, hy⟩
    refine ⟨L.map (ι.symm : Ω₂ →ₐ[K] Ω₁), ?_, ⟨ι y, hy, by simp⟩⟩
    exact (unrIn_map_iff ι.symm L).2 hL

end UnrIn

/-! ### Membership in `K_U` -/

section MemMax

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

theorem mem_maxUnram_iff (y : AlgebraicClosure K) :
    y ∈ maxUnram A K ↔ ∃ L ∈ unramSet A K, y ∈ L := by
  have hdir : Directed (· ≤ ·)
      (fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K))) :=
    directedOn_iff_directed.mp (directedOn_unramSet A K)
  have : Nonempty (unramSet A K) := ⟨⟨⊥, bot_mem_unramSet A K⟩⟩
  rw [← SetLike.mem_coe, maxUnram, IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion]
  exact ⟨fun ⟨L, h⟩ => ⟨L, L.2, h⟩, fun ⟨L, hL, h⟩ => ⟨⟨L, hL⟩, h⟩⟩

/-- `y ∈ K_U` iff `ι y` lies in some `A`-unramified finite Galois subextension of `Ω/K`. -/
theorem mem_maxUnram_iff_of_equiv {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
    (ι : AlgebraicClosure K ≃ₐ[K] Ω) (y : AlgebraicClosure K) :
    y ∈ maxUnram A K ↔ ∃ L : IntermediateField K Ω, UnrIn A K Ω L ∧ ι y ∈ L := by
  rw [mem_maxUnram_iff, ← exists_unrIn_iff ι y]
  rfl

end MemMax

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrExt =====
section

/-!
# S4-Lefschetz L4d (part 1): `K_U` is unramified over a finite subextension `E ⊆ K_U`

Easy direction of "`K_U` is the maximal unramified extension of `E` too": for `E ≤ M` with `M` unramified finite
Galois over `K`, `M` viewed over `E` (`IntermediateField.extendScalars h`) is unramified finite Galois over `E`
(`unrIn_extendScalars`): `Gal(M/E) → Gal(M/K)` is injective and maps inertia into inertia (`mem_inertia_comap`,
`inertia_eq_bot_of_injective`). Hence every point of `K_U` lies in an `E`-unramified finite Galois subextension
(`exists_unrIn_of_mem`), when `E ⊆ K_U` is finite over `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

section InertiaHom

variable {G G' B B' : Type} [Group G] [Group G'] [CommRing B] [CommRing B'] [MulSemiringAction G B]
  [MulSemiringAction G' B']

/-- A compatible pair (ring map `f`, group map `r`) maps inertia into inertia. -/
theorem mem_inertia_comap (f : B →+* B') (r : G' → G) (hf : ∀ (σ : G') (b : B), f (r σ • b) = σ • f b)
    (Q' : Ideal B') {σ : G'} (hσ : σ ∈ Q'.inertia G') : r σ ∈ (Q'.comap f).inertia G := by
  intro y
  show f (r σ • y - y) ∈ Q'
  rw [map_sub, hf]
  exact hσ (f y)

theorem inertia_eq_bot_of_injective (f : B →+* B') (r : G' →* G) (hr : Function.Injective r)
    (hf : ∀ (σ : G') (b : B), f (r σ • b) = σ • f b)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) (Q' : Ideal B') (hQ' : Q'.IsPrime) :
    Q'.inertia G' = ⊥ := by
  have hP : (Q'.comap f).IsPrime := Ideal.IsPrime.comap _
  rw [eq_bot_iff]
  intro σ hσ
  have hin := mem_inertia_comap f r hf Q' hσ
  rw [h _ hP, Subgroup.mem_bot] at hin
  rw [Subgroup.mem_bot]
  exact hr (hin.trans r.map_one.symm)

end InertiaHom

section Ext

variable (A : Type) {K Ω : Type} [CommRing A] [Field K] [Algebra A K] [Field Ω] [Algebra K Ω] [Algebra A Ω]
  [IsScalarTower A K Ω]
instance isScalarTower_A_E (E : IntermediateField K Ω) : IsScalarTower A E Ω :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {E M : IntermediateField K Ω} (h : E ≤ M)

/-- `M` and `IntermediateField.extendScalars h` are the same field. -/
def eExt : M ≃ₐ[K] IntermediateField.extendScalars h where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- `Gal(M/E) → Gal(M/K)`. -/
def galExt : (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) →* (M ≃ₐ[K] M) where
  toFun σ := (eExt h).trans ((σ.restrictScalars K).trans (eExt h).symm)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem galExt_apply (σ : IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) (x : M) :
    ((galExt h σ x : M) : Ω) = (σ (eExt h x) : Ω) := rfl

theorem galExt_injective : Function.Injective (galExt h) := by
  intro σ τ hστ
  ext x
  exact congrArg (fun ρ : M ≃ₐ[K] M => ((ρ ((eExt h).symm x) : M) : Ω)) hστ

/-- The integral closures of `A` in `M` and in `IntermediateField.extendScalars h` (same values). -/
def intClExt : integralClosure A M →+* integralClosure A (IntermediateField.extendScalars h) where
  toFun x := ⟨eExt h x, IntermediateField.coe_isIntegral_iff.mp
    (IntermediateField.coe_isIntegral_iff.mpr x.2 : IsIntegral A ((x : M) : Ω))⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem unrIn_extendScalars (hM : UnrIn A K Ω M) : UnrIn A E Ω (IntermediateField.extendScalars h) := by
  obtain ⟨hfd, hgal, hun⟩ := hM
  have : FiniteDimensional K (IntermediateField.extendScalars h) := LinearEquiv.finiteDimensional (eExt h).toLinearEquiv
  have : IsGalois K (IntermediateField.extendScalars h) := IsGalois.of_algEquiv (eExt h)
  refine ⟨Module.Finite.of_restrictScalars_finite K E _, IsGalois.tower_top_of_isGalois K E _, ?_⟩
  exact inertia_eq_bot_of_injective (intClExt A h) (galExt h) (galExt_injective h) (fun _ _ => rfl) hun

end Ext

section Mem

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

end Mem

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrFix =====
section

/-!
# S4-Lefschetz L4d (part 2a): helpers for "unramified over `E ⊆ K_U` implies inside `K_U`"

* `conj_mem_inertia`: inertia is stable under conjugation (translate the prime by the conjugating element).
* `mem_fixingSubgroup_iSup`: an automorphism fixes a compositum iff it fixes every piece.
* `exists_unramSet_ge`: a finite `E ⊆ K_U` lies in one unramified finite Galois `N`.
* `fix_of_unram`, `fix_of_unrIn`: an automorphism of `K̄` whose restriction to `M` is inertial fixes every unramified
  Galois `L ⊆ M` over `K`, and (if it fixes `E`) every unramified Galois `L' ⊆ M` over `E`.
* `le_sepCl_of_unrIn`: a Galois extension `L'` of `E ⊆ N` is separable over `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

section Conj

variable {G B : Type} [Group G] [CommRing B] [MulSemiringAction G B]

/-- Inertia is stable under conjugation: `g⁻¹ σ g` is inertial at the prime translated by `g`. -/
theorem conj_mem_inertia (g : G) (Q : Ideal B) {σ : G} (hσ : σ ∈ Q.inertia G) :
    g⁻¹ * σ * g ∈ (Q.comap (MulSemiringAction.toRingHom G B g)).inertia G :=
  mem_inertia_comap (MulSemiringAction.toRingHom G B g) (fun τ => g⁻¹ * τ * g)
    (fun τ b => by
      rw [MulSemiringAction.toRingHom_apply, MulSemiringAction.toRingHom_apply, smul_smul, smul_smul]
      congr 1
      group) Q hσ

end Conj

theorem mem_fixingSubgroup_iSup {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type}
    (t : ι → IntermediateField F E) (σ : E ≃ₐ[F] E) :
    σ ∈ (⨆ i, t i).fixingSubgroup ↔ ∀ i, σ ∈ (t i).fixingSubgroup := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]
  simp only [IntermediateField.le_iff_le, Subgroup.zpowers_le]

section Fix

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- An automorphism of `K̄` whose restriction to `M` is inertial fixes every unramified Galois `L ⊆ M`. -/
theorem fix_of_unram {L M : IntermediateField K (AlgebraicClosure K)} (hle : L ≤ M) [IsGalois K L] [Normal K M]
    (uL : IsUnramifiedSub A K L) (Q : Ideal (integralClosure A M)) [Q.IsPrime]
    (ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hρ : AlgEquiv.restrictNormalHom M ρ ∈ Q.inertia (M ≃ₐ[K] M)) : ∀ x ∈ L, ρ x = x := by
  have hP : (Q.comap (incl A K hle)).IsPrime := Ideal.IsPrime.comap _
  have hin : AlgEquiv.restrictNormalHom L ρ ∈ (Q.comap (incl A K hle)).inertia (L ≃ₐ[K] L) := by
    intro y
    show (incl A K hle) (AlgEquiv.restrictNormalHom L ρ • y - y) ∈ Q
    have h : AlgEquiv.restrictNormalHom M ρ • incl A K hle y - incl A K hle y ∈ Q := hρ (incl A K hle y)
    convert h using 2
    apply Subtype.ext; apply Subtype.ext
    show ((AlgEquiv.restrictNormalHom L ρ (y : L) : L) : AlgebraicClosure K) - ((y : L) : AlgebraicClosure K)
      = ((AlgEquiv.restrictNormalHom M ρ (incl A K hle y : M) : M) : AlgebraicClosure K)
        - ((y : L) : AlgebraicClosure K)
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    rfl
  rw [uL _ hP, Subgroup.mem_bot] at hin
  intro x hx
  have h1 := AlgEquiv.restrictNormalHom_apply L ρ ⟨x, hx⟩
  rw [hin] at h1
  exact h1.symm

/-- Same over `E`: if `ρ` also fixes `E`, it fixes every `E`-unramified Galois `L' ⊆ M`. -/
theorem fix_of_unrIn {E M : IntermediateField K (AlgebraicClosure K)} (L' : IntermediateField E (AlgebraicClosure K))
    (hL' : UnrIn A E (AlgebraicClosure K) L') (hLM : ∀ x ∈ L', x ∈ M) [Normal K M]
    (Q : Ideal (integralClosure A M)) [Q.IsPrime] (ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hρE : ∀ x ∈ E, ρ x = x)
    (hρ : AlgEquiv.restrictNormalHom M ρ ∈ Q.inertia (M ≃ₐ[K] M)) : ∀ x ∈ L', ρ x = x := by
  obtain ⟨-, hgal, hun⟩ := hL'
  let ρE : AlgebraicClosure K ≃ₐ[E] AlgebraicClosure K :=
    { ρ.toRingEquiv with commutes' := fun e => hρE e e.2 }
  let fE : integralClosure A L' →+* integralClosure A M :=
    { toFun := fun y => ⟨⟨((y : L') : AlgebraicClosure K), hLM _ (y : L').2⟩,
        IntermediateField.coe_isIntegral_iff.mp
          (IntermediateField.coe_isIntegral_iff.mpr y.2 : IsIntegral A ((y : L') : AlgebraicClosure K))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hP : (Q.comap fE).IsPrime := Ideal.IsPrime.comap _
  have hin : AlgEquiv.restrictNormalHom L' ρE ∈ (Q.comap fE).inertia (L' ≃ₐ[E] L') := by
    intro y
    show fE (AlgEquiv.restrictNormalHom L' ρE • y - y) ∈ Q
    have h : AlgEquiv.restrictNormalHom M ρ • fE y - fE y ∈ Q := hρ (fE y)
    convert h using 2
    apply Subtype.ext; apply Subtype.ext
    show ((AlgEquiv.restrictNormalHom L' ρE (y : L') : L') : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
      = ((AlgEquiv.restrictNormalHom M ρ (fE y : M) : M) : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    rfl
  rw [hun _ hP, Subgroup.mem_bot] at hin
  intro x hx
  have h1 := AlgEquiv.restrictNormalHom_apply L' ρE ⟨x, hx⟩
  rw [hin] at h1
  exact h1.symm

/-- A Galois extension `L'` of `E ⊆ N` (`N` Galois over `K`) is separable over `K`. -/
theorem le_sepCl_of_unrIn {E N : IntermediateField K (AlgebraicClosure K)} (hN : N ∈ unramSet A K) (hEN : E ≤ N)
    (L' : IntermediateField E (AlgebraicClosure K)) [Algebra.IsSeparable E L'] :
    L'.restrictScalars K ≤ separableClosure K (AlgebraicClosure K) := by
  have := hN.2.1
  have : Algebra.IsSeparable K E :=
    Algebra.IsSeparable.of_algHom (F := K) (E' := N) (f := IntermediateField.inclusion hEN)
  intro x hx
  rw [mem_separableClosure_iff]
  have h1 : IsSeparable E (L'.val ⟨x, (IntermediateField.mem_restrictScalars K).1 hx⟩) :=
    IsSeparable.map L'.val L'.val.toRingHom.injective (Algebra.IsSeparable.isSeparable E _)
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable K h1

end Fix

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrMax =====
section

/-!
# S4-Lefschetz L4c+d (part 2b): `K_U` is also the maximal unramified extension of a finite `E ⊆ K_U`

* `unram_normalClosure`: the normal closure `M` of `P` is unramified as soon as every automorphism of `K̄` with
  inertial restriction to `M` fixes `P` (conjugates of an inertia element are inertial at translated primes).
* `le_maxUnram_of_unrIn` (D2): for `E ⊆ K_U` finite over `K`, every finite Galois `L'/E` unramified over `A` lies in
  `K_U` (take `N ⊇ E` in `unramSet`, `M` = normal closure of `L' ⊔ N`).
* `mem_maxUnram_iff_of_sub`: `y ∈ maxUnram A E ↔ ι y ∈ maxUnram A K` for any `ι : Ē ≃ₐ[E] K̄` (D1 + D2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

section Max

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- The normal closure of `P` is unramified if every automorphism with inertial restriction fixes `P`. -/
theorem unram_normalClosure (P : IntermediateField K (AlgebraicClosure K))
    (hkey : ∀ (Q : Ideal (integralClosure A (IntermediateField.normalClosure K P (AlgebraicClosure K)))), Q.IsPrime →
      ∀ ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      AlgEquiv.restrictNormalHom (IntermediateField.normalClosure K P (AlgebraicClosure K)) ρ ∈
        Q.inertia (IntermediateField.normalClosure K P (AlgebraicClosure K) ≃ₐ[K] IntermediateField.normalClosure K P (AlgebraicClosure K)) →
      ∀ x ∈ P, ρ x = x) :
    IsUnramifiedSub A K (IntermediateField.normalClosure K P (AlgebraicClosure K)) := by
  intro Q hQ
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ y : ↥(IntermediateField.normalClosure K P (AlgebraicClosure K)),
      σ (y : AlgebraicClosure K) = ((τ y : IntermediateField.normalClosure K P (AlgebraicClosure K)) : AlgebraicClosure K) :=
    ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
  have hrσ : AlgEquiv.restrictNormalHom (IntermediateField.normalClosure K P (AlgebraicClosure K)) σ = τ := by
    ext y
    rw [AlgEquiv.restrictNormalHom_apply, hσ]
  have key : ∀ φ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x ∈ P, (φ⁻¹ * σ * φ) x = x := by
    intro φ
    refine hkey (Q.comap (MulSemiringAction.toRingHom _ _
      (AlgEquiv.restrictNormalHom (IntermediateField.normalClosure K P (AlgebraicClosure K)) φ))) (Ideal.IsPrime.comap _) _ ?_
    rw [map_mul, map_mul, map_inv, hrσ]
    exact conj_mem_inertia _ Q hτ
  have hfixM : σ ∈ (IntermediateField.normalClosure K P (AlgebraicClosure K)).fixingSubgroup := by
    rw [IntermediateField.normalClosure_def'', mem_fixingSubgroup_iSup]
    intro φ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    have h2 : φ ((φ⁻¹ * σ * φ) y) = φ y := congrArg φ (key φ y hy)
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h2
    exact (AlgEquiv.apply_symm_apply φ _).symm.trans h2
  ext y
  rw [AlgEquiv.one_apply, ← hσ]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfixM y y.2

end Max

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Pi1Geo =====
section

/-!
# S4-Lefschetz L4f: geometric `π₁` and Frobenius lifts under `theta` and under a change of `A`

* `fixConst_iff_of_conj` / `frobConst_iff_of_conj`: "fixes the constants" and "acts as `x ↦ x^q` on the constants"
  are invariant under conjugation by a ring isomorphism.
* `kE : K_U ≃+* K_U(E)` with `theta σ = kE⁻¹ σ kE`; `theta_mem_pi1geo_iff`, `theta_isFrobLift_iff`.
* `isConst_pow_iff`, `pi1geo_pow`: the constants of level `q^d` are those of level `q` (`d ≥ 1`);
  `IsFrobLift.pow'`: `φ^d` is a `q^d`-Frobenius lift.
* `pi1Congr h : π₁(A) ≃ₜ* π₁(B)` for `h : K_U(A) = K_U(B)`, compatible with `pi1geo` and `IsFrobLift`.
* `pi1Kc : π₁(Rfin k' E) ≃ₜ* π₁(𝔽_q[X], E)` for the full constant field `k' = Kc 𝔽_q E`, with
  `pi1Kc_mem_pi1geo_iff` (level `#k'` on the left, `q` on the right) and `pi1Kc_isFrobLift_iff`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh Topology

noncomputable section

/-! ### Conjugation invariance -/

section Conj

variable {L₁ L₂ : Type} [Field L₁] [Field L₂] (k : L₁ ≃+* L₂) (q : ℕ)

theorem isConst_iff_of_ringEquiv (x : L₁) : IsConst q (k x) ↔ IsConst q x :=
  ⟨fun h => by simpa using h.map k.symm, fun h => h.map k⟩

theorem fixConst_iff_of_conj (σ₁ : L₁ → L₁) (σ₂ : L₂ → L₂) (h : ∀ x, σ₂ (k x) = k (σ₁ x)) :
    (∀ x, IsConst q x → σ₁ x = x) ↔ (∀ y, IsConst q y → σ₂ y = y) := by
  constructor
  · intro h1 y hy
    have hy' : IsConst q (k.symm y) :=
      (isConst_iff_of_ringEquiv k q _).1 (by rwa [RingEquiv.apply_symm_apply])
    have h3 := h (k.symm y)
    rw [RingEquiv.apply_symm_apply, h1 _ hy', RingEquiv.apply_symm_apply] at h3
    exact h3
  · intro h2 x hx
    apply k.injective
    rw [← h, h2 _ ((isConst_iff_of_ringEquiv k q x).2 hx)]

theorem frobConst_iff_of_conj (σ₁ : L₁ → L₁) (σ₂ : L₂ → L₂) (h : ∀ x, σ₂ (k x) = k (σ₁ x)) :
    (∀ x, IsConst q x → σ₁ x = x ^ q) ↔ (∀ y, IsConst q y → σ₂ y = y ^ q) := by
  constructor
  · intro h1 y hy
    have hy' : IsConst q (k.symm y) :=
      (isConst_iff_of_ringEquiv k q _).1 (by rwa [RingEquiv.apply_symm_apply])
    have h3 := h (k.symm y)
    rw [RingEquiv.apply_symm_apply, h1 _ hy', map_pow, RingEquiv.apply_symm_apply] at h3
    exact h3
  · intro h2 x hx
    apply k.injective
    rw [← h, h2 _ ((isConst_iff_of_ringEquiv k q x).2 hx), map_pow]

end Conj

/-! ### Levels `q^d` versus `q` -/

section Pow

theorem pow_pow_mul_self {L : Type} [Monoid L] {x : L} {Q n : ℕ} (h : x ^ Q ^ n = x) (k : ℕ) :
    x ^ Q ^ (n * k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem isConst_pow_of {L : Type} [Field L] {q : ℕ} {x : L} (d : ℕ) (hx : IsConst q x) :
    IsConst (q ^ d) x := by
  obtain ⟨n, hn, h⟩ := hx
  refine ⟨n, hn, ?_⟩
  rw [← pow_mul, mul_comm]
  exact pow_pow_mul_self h d

theorem isConst_pow_iff {L : Type} [Field L] (q : ℕ) {d : ℕ} (hd : 0 < d) (x : L) :
    IsConst (q ^ d) x ↔ IsConst q x := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨d * n, Nat.mul_pos hd hn, by rwa [pow_mul]⟩
  · exact isConst_pow_of d

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

theorem pi1geo_pow (q : ℕ) {d : ℕ} (hd : 0 < d) : pi1geo A K (q ^ d) = pi1geo A K q := by
  ext σ
  rw [mem_pi1geo, mem_pi1geo]
  simp only [isConst_pow_iff q hd]

end Pow

/-! ### `theta` -/

section Theta

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K) [FiniteDimensional K E]

variable (Δ : Subgroup (Pi1 A K))
  (hΔ : ∀ τ : Pi1 A K, τ ∈ Δ ↔ ∀ x (hx : x ∈ E), τ ⟨x, hE hx⟩ = ⟨x, hE hx⟩)

end Theta

/-! ### Changing `A` with the same `K_U` -/

section Congr

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

/-- Conjugation by `equivOfEq` is continuous (after `subst` it is the identity). -/
theorem autCongr_equivOfEq_continuous {M₁ M₂ : IntermediateField K (AlgebraicClosure K)} (h : M₁ = M₂) :
    Continuous (IntermediateField.equivOfEq h).autCongr := by
  subst h
  rw [IntermediateField.equivOfEq_rfl, AlgEquiv.autCongr_refl]
  exact continuous_id

end Congr

/-! ### The full constant field -/

section KcPi1

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

end KcPi1

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ChartE2 =====
section

/-!
# S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover

`E ⊆ K_U` a finite subextension of `K̄`, `k' = Kc 𝔽_q E`. Value lemmas for `jE`, `theta`, `pi1CongrEquiv`
(proved generically, never through `equivOfEq` composites), then:
* `thetaE_val`, `uE_smul`: `uE (σ y) = thetaE σ (uE y)`;
* `isIntegral_chartE_iff`: `IsIntegral R_∞(k', E) y ↔ IsIntegral O_∞(𝔽_q) (y : Ē)`; `isIntegral_iotaE_iff`;
* `chartE : proChart(E) ≃+* proChart(K)` (charts over `∞`), `chartE_smul`, `chartE_symm_smul`;
* boundary primes and inertia correspond: `chartQ`/`chartP`, `isBdryPrime_chartQ/P`, `mem_inertia_chartQ_iff`
  (generic forms `isBdryPrime_comap`, `mem_inertia_comap_iff` for any isomorphism of pro-charts).
Concrete `Ideal.inertia` statements on these charts need `(α := proChart ..)` explicitly (else `α` stays a
metavariable: the chart's `Subalgebra.toSemiring` does not unify with `Ring.toSemiring ?_`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh

noncomputable section

section ValGen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K) [FiniteDimensional K E]

theorem eExt_val (x : maxUnram A K) :
    ((eExt hE x : IntermediateField.extendScalars hE) : AlgebraicClosure K) = (x : AlgebraicClosure K) := rfl

end ValGen

section EqVal

variable {F L : Type} [Field F] [Field L] [Algebra F L]

/-- Generic in `S T` (a `rfl` at `S, T = maxUnram ..` makes the kernel unfold `maxUnram`: deterministic timeout). -/
theorem equivOfEq_symm_coe {S T : IntermediateField F L} (h : S = T) (x : T) :
    (((IntermediateField.equivOfEq h).symm x : S) : L) = (x : L) := by
  subst h
  rfl

theorem autCongr_equivOfEq_coe {S T : IntermediateField F L} (h : S = T) (τ : S ≃ₐ[F] S) (x : T) :
    (((IntermediateField.equivOfEq h).autCongr τ x : T) : L) =
      ((τ ((IntermediateField.equivOfEq h).symm x) : S) : L) := by
  subst h
  rfl

end EqVal

section CongrVal

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

theorem equivOfEq_symm_val (h : maxUnram A K = maxUnram B K) (x : maxUnram B K) :
    (((IntermediateField.equivOfEq h).symm x : maxUnram A K) : AlgebraicClosure K) = (x : AlgebraicClosure K) :=
  equivOfEq_symm_coe h x

end CongrVal

section ChartGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

/-- Boundary primes pull back along an isomorphism of pro-charts. -/
theorem isBdryPrime_comap (e : proChart A K R0 ≃+* proChart A' K' R0') {Q : Ideal (proChart A' K' R0')}
    (hQ : IsBdryPrime A' K' R0' Q) : IsBdryPrime A K R0 (Q.comap e) := by
  have := hQ.1
  refine ⟨Ideal.IsPrime.comap e, fun h => hQ.2 ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have h1 : e.symm x ∈ Q.comap e := by
    rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
    exact hx
  rw [h, Ideal.mem_bot] at h1
  rw [Ideal.mem_bot, ← e.apply_symm_apply x, h1, map_zero]

/-- Inertia corresponds along an equivariant isomorphism of pro-charts. -/
theorem mem_inertia_comap_iff (e : proChart A K R0 ≃+* proChart A' K' R0') (r : Pi1 A' K' → Pi1 A K)
    (he : ∀ σ x, e (r σ • x) = σ • e x) (Q : Ideal (proChart A' K' R0')) (σ : Pi1 A' K') :
    σ ∈ Q.inertia (Pi1 A' K') ↔ r σ ∈ (Q.comap e).inertia (Pi1 A K) := by
  constructor
  · intro h x
    show e (r σ • x - x) ∈ Q
    rw [map_sub, he]
    exact h _
  · intro h y
    have h1 : e (r σ • e.symm y - e.symm y) ∈ Q := h (e.symm y)
    rw [map_sub, he, RingEquiv.apply_symm_apply] at h1
    exact h1

end ChartGen

section ChartE2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

/-! ### The chart of `E` over `∞` -/

/-! ### Boundary primes and inertia -/

end ChartE2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ShapData =====
section

/-!
# S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover

Generic part (`ShapGen`): two pro-charts with boundary data `D` (of `V`) and `D'` (of `U`), an isomorphism
`f : proChart(V) ≃+* proChart(U)` equivariant along an injective `r : π₁(U) →* π₁(V)` with `r⁻¹(Γ) = Γ_U`, and
"stabiliser in `Γ` ⇒ inertia" on `V`. Then `gπ`, `gxT` (from `D.cover`), `gJ` satisfy the three Shapiro
hypotheses `InertiaLift`, `DCover`, `DDisj` of `CurveCoh_ShapiroCone` for `H = range r`.

Concrete part (`ShapE`): `V = K`, `U = E ⊆ K_U` over `k' = Kc 𝔽_q E`, `f = chartE.symm`, `r = thetaE`:
`thetaE_mem_pi1geo_iff`, `thetaE_injective`, `stab_mem_inertia_K`, the objects `bdPiE`, `bdxE`, `bdJE` and
`shap_inertiaLift`, `shap_dCover`, `shap_dDisj`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh CP4a

noncomputable section

section ShapGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

theorem comap_comap_symm (f : proChart A K R0 ≃+* proChart A' K' R0') (Q : Ideal (proChart A K R0)) :
    (Q.comap f.symm).comap f = Q := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.symm_apply_apply]

theorem comap_injective_equiv (f : proChart A K R0 ≃+* proChart A' K' R0')
    {Q₁ Q₂ : Ideal (proChart A' K' R0')} (h : Q₁.comap f = Q₂.comap f) : Q₁ = Q₂ := by
  ext y
  constructor
  · intro hy
    have h1 : f.symm y ∈ Q₁.comap f := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hy
    rw [h, Ideal.mem_comap, RingEquiv.apply_symm_apply] at h1
    exact h1
  · intro hy
    have h1 : f.symm y ∈ Q₂.comap f := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hy
    rw [← h, Ideal.mem_comap, RingEquiv.apply_symm_apply] at h1
    exact h1

/-- Pulling back along an equivariant isomorphism commutes with the pointwise action. -/
theorem comap_smul_equiv (f : proChart A K R0 ≃+* proChart A' K' R0') (r : Pi1 A' K' →* Pi1 A K)
    (hf : ∀ σ x, f (r σ • x) = σ • f x) (σ : Pi1 A' K') (Q : Ideal (proChart A' K' R0')) :
    (σ • Q).comap f = r σ • Q.comap f := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_comap, ← map_inv r σ, hf]

/-- Inertia of a translated prime is the conjugate inertia group. -/
theorem mem_inertia_smul_iff (x : Pi1 A K) (Q : Ideal (proChart A K R0)) (g : Pi1 A K) :
    g ∈ (x • Q).inertia (Pi1 A K) ↔ x⁻¹ * g * x ∈ Q.inertia (Pi1 A K) := by
  constructor
  · intro h
    exact inv_conj_mem_inertia A K R0 (σ := x) (Q' := Q) rfl h
  · intro h
    have h1 := conj_mem_inertia_smul A K R0 x h
    rwa [show x * (x⁻¹ * g * x) * x⁻¹ = g by group] at h1

variable {q q' : ℕ} {S T : Type} (D : BdryData A K q R0 S) (D' : BdryData A' K' q' R0' T)
  (f : proChart A K R0 ≃+* proChart A' K' R0')
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) (hD'B : ∀ Q, D'.B Q ↔ IsBdryPrime A' K' R0' Q)

include hDB hD'B in
theorem exists_cover_comap (t : T) : ∃ s, ∃ g ∈ pi1geo A K q, (D'.P t).comap f = g • D.P s :=
  D.cover _ ((hDB _).2 (isBdryPrime_comap f ((hD'B _).1 (D'.mem t))))

/-- The boundary point of `V` under the boundary point `t` of `U`. -/
def gπ (t : T) : S := (exists_cover_comap D D' f hDB hD'B t).choose

/-- A representative `x_t ∈ Γ` with `f^*(P'_t) = x_t • P_{π t}`. -/
def gxT (t : T) : pi1geo A K q :=
  ⟨(exists_cover_comap D D' f hDB hD'B t).choose_spec.choose,
    (exists_cover_comap D D' f hDB hD'B t).choose_spec.choose_spec.1⟩

theorem gxT_spec (t : T) :
    (D'.P t).comap f = (gxT D D' f hDB hD'B t : Pi1 A K) • D.P (gπ D D' f hDB hD'B t) :=
  (exists_cover_comap D D' f hDB hD'B t).choose_spec.choose_spec.2

/-- The inertia at `t`, as a subgroup of `H = range r`. -/
def gJ (r : Pi1 A' K' →* Pi1 A K) (t : T) : Subgroup r.range := ((D'.inertia t).map r).subgroupOf r.range

variable (r : Pi1 A' K' →* Pi1 A K) (hf : ∀ σ x, f (r σ • x) = σ • f x) (hr : Function.Injective r)
  (hgeo : ∀ σ, r σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A' K' q')
  (hstab : ∀ Q, IsBdryPrime A K R0 Q → ∀ σ ∈ pi1geo A K q, σ • Q = Q → σ ∈ Q.inertia (Pi1 A K))

end ShapGen

section ShapE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end ShapE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockE =====
section

/-!
# S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart

For an open `H ≤ π₁(U)` (`U = Spec Rfin`): `exists_E_of_open` gives a finite separable `E ⊆ K_U` with
`range thetaE = H`, every `τ ∈ H` fixing `E` and every point of `K_U` fixed by `H` lying in `E` (Galois
correspondence through `pi1Congr`). `thetaE_isFrobLift_iff` transports Frobenius lifts along `thetaE` at any level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section Val

variable {K : Type} [Field K]

/-- `autCongr (equivOfEq h)` acts on underlying points of `K̄` as the original automorphism (after `subst`, so the
kernel never compares the two subtypes). -/
theorem autCongr_val {M₁ M₂ : IntermediateField K (AlgebraicClosure K)} (h : M₁ = M₂) (σ : M₁ ≃ₐ[K] M₁) (x : M₁)
    (y : M₂) (hxy : (x : AlgebraicClosure K) = y) :
    ((((IntermediateField.equivOfEq h).autCongr σ) y : M₂) : AlgebraicClosure K) = (σ x : AlgebraicClosure K) := by
  subst h
  have e : y = x := Subtype.ext hxy.symm
  subst e
  rw [IntermediateField.equivOfEq_rfl]
  rfl

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A K] [Algebra B K]

end Val

section BlockE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

end BlockE

section FixGen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- `exists_sub_of_isOpen` plus: the points of `K_U` fixed by `Δ` lie in `E`. -/
theorem exists_sub_fix (Δ : Subgroup (Pi1 A K)) (hΔ : IsOpen (Δ : Set (Pi1 A K))) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K), FiniteDimensional K E ∧
      (∀ τ : Pi1 A K, τ ∈ Δ ↔ ∀ x (hx : x ∈ E), τ ⟨x, hE hx⟩ = ⟨x, hE hx⟩) ∧
      (∀ y : maxUnram A K, (∀ τ ∈ Δ, τ y = y) → (y : AlgebraicClosure K) ∈ E) := by
  let F₀ := IntermediateField.fixedField Δ
  have hfix : F₀.fixingSubgroup = Δ :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨Δ, Subgroup.isClosed_of_isOpen Δ hΔ⟩
  have hfd : FiniteDimensional K F₀ := (InfiniteGalois.isOpen_iff_finite F₀).1 (by rw [hfix]; exact hΔ)
  refine ⟨F₀.map (maxUnram A K).val, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := (IntermediateField.mem_map _).1 hx
    exact y.2
  · exact (IntermediateField.equivMap F₀ (maxUnram A K).val).toLinearEquiv.finiteDimensional
  · intro τ
    rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
      exact h y hy
    · intro h y hy
      exact h y.1 ((IntermediateField.mem_map _).2 ⟨y, hy, rfl⟩)
  · intro y hy
    exact (IntermediateField.mem_map _).2 ⟨y, (IntermediateField.mem_fixedField_iff _ _).2 hy, rfl⟩

/-- A subfield of `K_U` is separable over `K`. -/
theorem isSeparable_of_le_maxUnram (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K) :
    Algebra.IsSeparable K E :=
  Algebra.IsSeparable.of_algHom (F := K) (E' := maxUnram A K) (f := IntermediateField.inclusion hE)

end FixGen

section CongrGen

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

/-- Generic coercion lemma (so the kernel never unfolds a concrete `pi1Congr` to compare coercions). -/
theorem cme_toMonoidHom_apply {M N : Type} [Group M] [Group N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M ≃ₜ* N) (x : M) : f.toMulEquiv.toMonoidHom x = f x := rfl

end CongrGen

section EOpen

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

end EOpen

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockGrp =====
section

/-!
# S4-Lefschetz, L3d3a: the block subgroup `H_ω`

For `g` whose inverse acts on constants as `x ↦ x ^ (q ^ m)` (e.g. `g = c0⁻¹ (φ⁻¹)^m`, `ginv_apply`), a finite
quotient `π : π₁ → Gf` and a primitive `((q^m)^|Gf| - 1)`-th root of unity `ζ` in `K_U`:
`blkH π g ζ hζ = {x | ∃ k : ℤ, π x = π g ^ k ∧ x ζ = g ^ k ζ}` is an open subgroup (`isOpen_blkH`) containing `g`
(`g_mem_blkH`) with `blkH ⊓ π₁^geo = π₁^geo ⊓ ker π` (`mem_blkH_geo_iff`), and it fixes `𝔽_{q^m}` (`blkH_fix`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh GalCover

section BlockGrp

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- Two automorphisms that agree on a primitive root `ζ` agree on every conjugate `τ ζ`. -/
theorem agree_apply_of_prim {ζ : maxUnram A K} {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N)
    {σ ρ : Pi1 A K} (h : σ ζ = ρ ζ) (τ : Pi1 A K) : σ (τ ζ) = ρ (τ ζ) := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  rw [← hi, map_pow, map_pow, h]

/-- A primitive `(Q - 1)`-th root of unity satisfies `ζ ^ Q = ζ`. -/
theorem prim_pow_fix {L : Type} [Field L] {ζ : L} {Q : ℕ} (hQ : 1 ≤ Q) (hζ : IsPrimitiveRoot ζ (Q - 1)) :
    ζ ^ Q = ζ :=
  calc ζ ^ Q = ζ ^ (Q - 1 + 1) := by rw [Nat.sub_add_cancel hQ]
  _ = ζ := by rw [pow_succ, hζ.pow_eq_one, one_mul]

/-- A Frobenius lift acts on constants as `x ↦ x ^ (q ^ n)` through its `n`-th power. -/
theorem frob_pow_apply {q : ℕ} {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) {x : maxUnram A K} (hx : IsConst q x)
    (n : ℕ) : (φ ^ n) x = x ^ (q ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hφ x hx, ← pow_mul, ← pow_succ']

/-- For `g = c0⁻¹ (φ⁻¹)^m` (`c0` geometric, `φ` a Frobenius lift), `g⁻¹` acts on constants as `x ↦ x ^ (q ^ m)`. -/
theorem ginv_apply {q : ℕ} {φ c0 : Pi1 A K} (hφ : IsFrobLift A K q φ) (hc0 : c0 ∈ pi1geo A K q) (m : ℕ)
    (x : maxUnram A K) (hx : IsConst q x) : (c0⁻¹ * φ⁻¹ ^ m)⁻¹ x = x ^ (q ^ m) := by
  rw [mul_inv_rev, inv_inv, inv_pow, inv_inv, AlgEquiv.mul_apply, (mem_pi1geo A K q c0).1 hc0 x hx,
    frob_pow_apply hφ hx m]

variable {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (g : Pi1 A K) (ζ : maxUnram A K)

/-- The block subgroup `H_ω`: `x` with `π x = π g ^ k` and `x ζ = g ^ k ζ` for one `k : ℤ`. -/
def blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) : Subgroup (Pi1 A K) where
  carrier := {x | ∃ k : ℤ, π x = π g ^ k ∧ x ζ = (g ^ k) ζ}
  one_mem' := by
    show ∃ k : ℤ, π 1 = π g ^ k ∧ (1 : Pi1 A K) ζ = (g ^ k) ζ
    exact ⟨0, by rw [map_one, zpow_zero], by rw [zpow_zero]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨k, hk1, hk2⟩ := hx
    obtain ⟨k', hk1', hk2'⟩ := hy
    show ∃ k : ℤ, π (x * y) = π g ^ k ∧ (x * y) ζ = (g ^ k) ζ
    refine ⟨k + k', by rw [map_mul, hk1, hk1', zpow_add], ?_⟩
    rw [AlgEquiv.mul_apply, hk2', zpow_add, AlgEquiv.mul_apply]
    exact agree_apply_of_prim hζ hk2 _
  inv_mem' := by
    intro x hx
    obtain ⟨k, hk1, hk2⟩ := hx
    show ∃ k : ℤ, π x⁻¹ = π g ^ k ∧ x⁻¹ ζ = (g ^ k) ζ
    refine ⟨-k, by rw [map_inv, hk1, zpow_neg], ?_⟩
    have h := agree_apply_of_prim hζ hk2 (g ^ (-k))
    rw [← AlgEquiv.mul_apply (g ^ k), ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply] at h
    apply (x : maxUnram A K ≃ₐ[K] maxUnram A K).injective
    rw [← AlgEquiv.mul_apply x x⁻¹, mul_inv_cancel, AlgEquiv.one_apply, h]

theorem mem_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) {x : Pi1 A K} :
    x ∈ blkH π g ζ hζ ↔ ∃ k : ℤ, π x = π g ^ k ∧ x ζ = (g ^ k) ζ := Iff.rfl

theorem g_mem_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) : g ∈ blkH π g ζ hζ :=
  (mem_blkH π g ζ hζ).2 ⟨1, by rw [zpow_one], by rw [zpow_one]⟩

theorem ker_inf_le_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) :
    π.ker ⊓ fixElt A K ζ ≤ blkH π g ζ hζ := fun x hx =>
  (mem_blkH π g ζ hζ).2 ⟨0, by rw [zpow_zero]; exact hx.1, by rw [zpow_zero, AlgEquiv.one_apply]; exact hx.2⟩

/-- `H_ω` is open (it contains `ker π ∩ Stab ζ`). -/
theorem isOpen_blkH {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N) (hπ : IsOpen (π.ker : Set (Pi1 A K))) :
    IsOpen (blkH π g ζ hζ : Set (Pi1 A K)) :=
  Subgroup.isOpen_mono (ker_inf_le_blkH π g ζ hζ)
    (by rw [Subgroup.coe_inf]; exact hπ.inter (fixElt_isOpen A K ζ))

/-- `g ^ k ζ = ζ` forces `(g⁻¹) ^ |k| ζ = ζ`. -/
theorem gpow_fix_natAbs (k : ℤ) (h : (g ^ k) ζ = ζ) : (g⁻¹ ^ k.natAbs) ζ = ζ := by
  have h' : (g ^ (-k)) ζ = ζ := by
    conv_lhs => rw [← h]
    rw [← AlgEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, AlgEquiv.one_apply]
  rcases Int.natAbs_eq k with hk | hk
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow] at h'
    exact h'
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow] at h
    exact h

theorem ginv_pow_apply {q Q : ℕ} (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ Q) (hζc : IsConst q ζ)
    (n : ℕ) : (g⁻¹ ^ n) ζ = ζ ^ (Q ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hg ζ hζc, map_pow, ih, ← pow_mul, ← pow_succ]

/-- `ζ ^ (Q ^ n) = ζ` for a primitive `(Q^r - 1)`-th root forces `r ∣ n`. -/
theorem dvd_of_pow_fix {L : Type} [Field L] {ζ : L} {Q r n : ℕ} (hQ : 2 ≤ Q) (hr : 0 < r)
    (hζ : IsPrimitiveRoot ζ (Q ^ r - 1)) (h : ζ ^ (Q ^ n) = ζ) : r ∣ n := by
  have hQr : 2 ≤ Q ^ r := le_trans hQ (Nat.le_self_pow hr.ne' Q)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have h1 : ζ ^ (Q ^ n - 1) = 1 := by
    have e : ζ ^ (Q ^ n - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), h, one_mul]
    exact mul_right_cancel₀ hζ0 e
  have h2 : Q ^ r - 1 ∣ Q ^ n - 1 := (hζ.pow_eq_one_iff_dvd _).1 h1
  have h3 : Nat.gcd (Q ^ r - 1) (Q ^ n - 1) = Q ^ r - 1 := Nat.gcd_eq_left h2
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h3
  have h4 : Q ^ Nat.gcd r n = Q ^ r := by
    have a1 := Nat.one_le_pow (Nat.gcd r n) Q (by omega)
    have a2 := Nat.one_le_pow r Q (by omega)
    generalize Q ^ Nat.gcd r n = X at *
    generalize Q ^ r = Y at *
    omega
  have h5 : Nat.gcd r n = r := Nat.pow_right_injective hQ h4
  rw [← h5]
  exact Nat.gcd_dvd_right r n

variable [Fintype Gf]

/-- The primitive root is a constant. -/
theorem isConst_zeta {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1)) : IsConst q ζ := by
  have hr : 0 < Fintype.card Gf := Fintype.card_pos
  refine ⟨m * Fintype.card Gf, Nat.mul_pos hm hr, ?_⟩
  rw [pow_mul]
  exact prim_pow_fix (Nat.one_le_pow _ _ (pow_pos (by omega) m)) hζ

/-- **`H_ω ⊓ π₁^geo = π₁^geo ⊓ ker π`** (`hHΓ` of BlockIso / BlockCone2). -/
theorem mem_blkH_geo_iff {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ (q ^ m))
    [NeZero ((q ^ m) ^ Fintype.card Gf - 1)] (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1))
    {x : Pi1 A K} (hx : x ∈ pi1geo A K q) : x ∈ blkH π g ζ hζ ↔ π x = 1 := by
  have hr : 0 < Fintype.card Gf := Fintype.card_pos
  have hζc : IsConst q ζ := isConst_zeta (Gf := Gf) hq2 hm hζ
  have hxζ : x ζ = ζ := (mem_pi1geo A K q x).1 hx ζ hζc
  constructor
  · intro hmem
    obtain ⟨k, hk1, hk2⟩ := (mem_blkH π g ζ hζ).1 hmem
    have h1 : (g ^ k) ζ = ζ := hk2.symm.trans hxζ
    have h2 := gpow_fix_natAbs g ζ k h1
    rw [ginv_pow_apply g ζ hg hζc] at h2
    have h3 : Fintype.card Gf ∣ k.natAbs :=
      dvd_of_pow_fix (le_trans hq2 (Nat.le_self_pow hm.ne' q)) hr hζ h2
    obtain ⟨t, ht⟩ := h3
    have hp : π g ^ k.natAbs = 1 := by rw [ht, pow_mul, pow_card_eq_one, one_pow]
    rw [hk1]
    rcases Int.natAbs_eq k with h | h
    · rw [h, zpow_natCast, hp]
    · rw [h, zpow_neg, zpow_natCast, hp, inv_one]
  · intro h1
    exact (mem_blkH π g ζ hζ).2 ⟨0, by rw [h1, zpow_zero], by rw [zpow_zero, AlgEquiv.one_apply, hxζ]⟩

/-- **`H_ω` fixes `𝔽_{q^m}`**: every `τ ∈ H_ω` fixes every `y` with `y ^ (q ^ m) = y`. -/
theorem blkH_fix {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ (q ^ m))
    [NeZero ((q ^ m) ^ Fintype.card Gf - 1)] (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1))
    {τ : Pi1 A K} (hτ : τ ∈ blkH π g ζ hζ) {y : maxUnram A K} (hy : y ^ (q ^ m) = y) : τ y = y := by
  obtain ⟨k, -, hk⟩ := (mem_blkH π g ζ hζ).1 hτ
  have hyc : IsConst q y := ⟨m, hm, hy⟩
  have hgi : g⁻¹ ∈ fixElt A K y := by
    show g⁻¹ y = y
    rw [hg y hyc, hy]
  have hgy : g ∈ fixElt A K y := by simpa using inv_mem hgi
  have hgk : (g ^ k) y = y := Subgroup.zpow_mem _ hgy k
  by_cases h0 : y = 0
  · rw [h0, map_zero]
  have hQ1 : 1 ≤ (q ^ m) ^ Fintype.card Gf := Nat.one_le_pow _ _ (pow_pos (by omega) m)
  have hyQ : ∀ j : ℕ, y ^ ((q ^ m) ^ j) = y := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_one]
    | succ j ih => rw [pow_succ, pow_mul, ih, hy]
  have hyr : y ^ ((q ^ m) ^ Fintype.card Gf - 1) = 1 := by
    have e : y ^ ((q ^ m) ^ Fintype.card Gf - 1) * y = 1 * y := by
      rw [← pow_succ, Nat.sub_add_cancel hQ1, hyQ, one_mul]
    exact mul_right_cancel₀ h0 e
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hyr
  rw [← hi, map_pow, hk, ← map_pow, hi]
  exact hgk

end BlockGrp

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockCov =====
section

/-!
# S4-Lefschetz, L3f2a: block data in the `Rfin` chart

`coind_triv_eq_one` / `isOpen_ker_coind_triv`: the coinduced trivial representation from an open subgroup of a compact
group has open kernel. `isLocalRing_zmod_pow`: `ℤ/l^n` is local. `exists_block_c0`: a fixed block gives
`ψ^m = c0 g` with `c0 ∈ Γ`, `π g = a γ⁻¹ a⁻¹`. `exists_blockCover`: for `g = c0⁻¹ φ⁻¹^m` the cover `E` with
`#k'_E = q^m`, a Frobenius lift `σ` of `E` with `thetaE σ = g⁻¹`, and `x ∈ range thetaE ↔ π x = 1` on `Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a Representation

section CoindKer

variable {k G' : Type} [CommRing k] [Group G'] (U : Subgroup G') (σH : Representation k U k) (hσ : ∀ h, σH h = 1)

include hσ in
theorem coind_triv_eq_one (x : G') (hx : ∀ y : G', y * x * y⁻¹ ∈ U) : coind U.subtype σH x = 1 := by
  ext f y
  show (f : G' → k) (y * x) = (f : G' → k) y
  have h1 := (Representation.mem_coindV _ _ _).1 f.2 ⟨y * x * y⁻¹, hx y⟩ y
  rw [hσ, Module.End.one_apply] at h1
  rw [← h1]
  simp

include hσ in
theorem isOpen_ker_coind_triv [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
    (hU : IsOpen (U : Set G')) : IsOpen ((coind U.subtype σH).ker : Set G') := by
  have := Subgroup.quotient_finite_of_isOpen U hU
  have := Subgroup.finiteIndex_of_finite_quotient (H := U)
  have hc : IsOpen (U.normalCore : Set G') :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (Subgroup.isClosed_of_isOpen U hU))
  refine Subgroup.isOpen_mono (fun x hx => ?_) hc
  exact coind_triv_eq_one U σH hσ x fun y => hx y

end CoindKer

/-- `ℤ/l^n` is a local ring. -/
theorem isLocalRing_zmod_pow (l n : ℕ) (hl : l.Prime) (hn : 0 < n) : IsLocalRing (ZMod (l ^ n)) := by
  have : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rw [← ZMod.natCast_zmod_val a]
  by_cases h : l ∣ a.val
  · right
    apply IsNilpotent.isUnit_one_sub
    refine ⟨n, ?_⟩
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow_of_dvd h n
  · left
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hl hn).2 h

/-- A fixed block gives the factorisation `ψ^m = c0 g`. -/
theorem exists_block_c0 {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) {a γ : Gf} {ψm : G}
    (hfix : π ψm * a * γ * a⁻¹ ∈ Γ.map π) :
    ∃ c0 ∈ Γ, ψm = c0 * (c0⁻¹ * ψm) ∧ π (c0⁻¹ * ψm) = a * γ⁻¹ * a⁻¹ := by
  obtain ⟨c0, hc0, hπc0⟩ := hfix
  refine ⟨c0, hc0, by group, ?_⟩
  rw [map_mul, map_inv, hπc0]
  group

section BlockCover

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end BlockCover

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Euler =====
section

/-!
# S4-Lefschetz L1: Euler characteristic of traces for a three-term complex

Over a local ring, for a complex `K⁰ → K¹ → K²` of free finite modules with injective `d⁰` and free finite
cohomology `H¹ = ker d¹ / im d⁰`, `H² = coker d¹`, an endomorphism `(f⁰, f¹, f²)` of the complex satisfies
`Tr f⁰ - Tr f¹ + Tr f² = Tr(f | H²) - Tr(f | H¹)` (`euler3`). The tools: traces along a split short exact sequence
(`trace_split`), the splitting of `0 → Q → P → P ⧸ Q → 0` when `P ⧸ Q` is free (`trace_eq_restrict_add_quot`), and
freeness of such `Q` over a local ring (`sub_free_finite`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Lefschetz

open LinearMap (trace)

noncomputable section

section Intw

variable {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Traces agree along a linear equivalence intertwining two endomorphisms. -/
theorem trace_intw (e : V ≃ₗ[R] W) {f : V →ₗ[R] V} {g : W →ₗ[R] W} (hfg : ∀ v, e (f v) = g (e v)) :
    trace R V f = trace R W g := by
  have hg : g = e.conj f := LinearMap.ext fun w => by
    rw [LinearEquiv.conj_apply_apply, hfg, LinearEquiv.apply_symm_apply]
  rw [hg, LinearMap.trace_conj']

end Intw

section Split

variable {R : Type*} [CommRing R] {P' P P'' : Type*} [AddCommGroup P'] [Module R P'] [AddCommGroup P] [Module R P]
  [AddCommGroup P''] [Module R P'']

/-- Additivity of traces along a split short exact sequence of free finite modules. -/
theorem trace_split [Module.Free R P'] [Module.Finite R P'] [Module.Free R P] [Module.Finite R P]
    [Module.Free R P''] [Module.Finite R P''] {i : P' →ₗ[R] P} {r : P →ₗ[R] P'} {π : P →ₗ[R] P''}
    {s : P'' →ₗ[R] P} (hri : r ∘ₗ i = LinearMap.id) (hπs : π ∘ₗ s = LinearMap.id)
    (hsum : i ∘ₗ r + s ∘ₗ π = LinearMap.id) {φ' : P' →ₗ[R] P'} {φ : P →ₗ[R] P} {φ'' : P'' →ₗ[R] P''}
    (h1 : φ ∘ₗ i = i ∘ₗ φ') (h2 : π ∘ₗ φ = φ'' ∘ₗ π) :
    trace R P φ = trace R P' φ' + trace R P'' φ'' := by
  have e : φ = (φ ∘ₗ i) ∘ₗ r + (φ ∘ₗ s) ∘ₗ π := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_add, hsum, LinearMap.comp_id]
  have t1 : trace R P ((φ ∘ₗ i) ∘ₗ r) = trace R P' φ' := by
    rw [LinearMap.trace_comp_comm', h1, ← LinearMap.comp_assoc, hri, LinearMap.id_comp]
  have t2 : trace R P ((φ ∘ₗ s) ∘ₗ π) = trace R P'' φ'' := by
    rw [LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, h2, LinearMap.comp_assoc, hπs, LinearMap.comp_id]
  rw [e, map_add, t1, t2]

end Split

section Quot

variable {R : Type*} [CommRing R] {P : Type*} [AddCommGroup P] [Module R P] (Q : Submodule R P)

theorem mem_of_sec {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) (x : P) : x - s (Q.mkQ x) ∈ Q := by
  rw [← Submodule.Quotient.mk_eq_zero Q, Submodule.Quotient.mk_sub]
  have := LinearMap.congr_fun hs (Q.mkQ x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply] at this ⊢
  rw [this, sub_self]

/-- The retraction `P → Q`, `x ↦ x - s (x mod Q)`, attached to a section `s` of `P → P ⧸ Q`. -/
def retr {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) : P →ₗ[R] Q :=
  LinearMap.codRestrict Q (LinearMap.id - s ∘ₗ Q.mkQ) fun x => mem_of_sec Q hs x

theorem retr_subtype {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) :
    retr Q hs ∘ₗ Q.subtype = LinearMap.id :=
  LinearMap.ext fun q => Subtype.ext (by
    simp [retr, (Submodule.Quotient.mk_eq_zero Q).2 q.2])

theorem subtype_retr_add {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) :
    Q.subtype ∘ₗ retr Q hs + s ∘ₗ Q.mkQ = LinearMap.id :=
  LinearMap.ext fun x => by simp [retr]

variable [Module.Free R (P ⧸ Q)]

theorem exists_sec : ∃ s : (P ⧸ Q) →ₗ[R] P, Q.mkQ ∘ₗ s = LinearMap.id :=
  Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective

/-- Over a local ring, a submodule of a free finite module with free quotient is free and finite. -/
theorem sub_free_finite [IsLocalRing R] [Module.Free R P] [Module.Finite R P] :
    Module.Free R Q ∧ Module.Finite R Q := by
  obtain ⟨s, hs⟩ := exists_sec Q
  have hri := retr_subtype Q hs
  have : Module.Projective R Q := Module.Projective.of_split Q.subtype (retr Q hs) hri
  have : Module.Finite R Q :=
    Module.Finite.of_surjective (retr Q hs) (fun v => ⟨Q.subtype v, LinearMap.congr_fun hri v⟩)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

/-- `Tr φ = Tr(φ | Q) + Tr(φ | P ⧸ Q)` for `Q` stable under `φ`, `P` free finite and `P ⧸ Q` free finite over a local
ring. -/
theorem trace_eq_restrict_add_quot [IsLocalRing R] [Module.Free R P] [Module.Finite R P] [Module.Finite R (P ⧸ Q)]
    (φ : P →ₗ[R] P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    trace R P φ = trace R Q (φ.restrict hQ) + trace R (P ⧸ Q) (Q.mapQ Q φ fun x hx => hQ x hx) := by
  obtain ⟨s, hs⟩ := exists_sec Q
  obtain ⟨_, _⟩ := sub_free_finite Q
  exact trace_split (retr_subtype Q hs) hs (subtype_retr_add Q hs) (LinearMap.ext fun q => rfl)
    (LinearMap.ext fun x => rfl)

end Quot

section Euler

variable {R : Type*} [CommRing R] {K0 K1 K2 : Type*} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup K2] [Module R K2] (d0 : K0 →ₗ[R] K1) (d1 : K1 →ₗ[R] K2) (hd : ∀ x, d1 (d0 x) = 0)

/-- `d⁰` with values in the cocycles `ker d¹`. -/
def d0Z : K0 →ₗ[R] LinearMap.ker d1 :=
  LinearMap.codRestrict _ d0 fun x => LinearMap.mem_ker.2 (hd x)

/-- `H¹ = ker d¹ / im d⁰`. -/
abbrev Hc1 : Type _ := LinearMap.ker d1 ⧸ LinearMap.range (d0Z d0 d1 hd)

variable {d0 d1} {f0 : K0 →ₗ[R] K0} {f1 : K1 →ₗ[R] K1} {f2 : K2 →ₗ[R] K2}

theorem mem_ker_f1 (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : ∀ x ∈ LinearMap.ker d1, f1 x ∈ LinearMap.ker d1 :=
  fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← h1, hx, map_zero]

/-- `f¹` on the cocycles. -/
def fZ (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : LinearMap.ker d1 →ₗ[R] LinearMap.ker d1 :=
  f1.restrict (mem_ker_f1 h1)

theorem mem_range_d0Z (h0 : ∀ x, f1 (d0 x) = d0 (f0 x)) (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) :
    ∀ z ∈ LinearMap.range (d0Z d0 d1 hd), fZ h1 z ∈ LinearMap.range (d0Z d0 d1 hd) := by
  rintro z ⟨x, rfl⟩
  exact ⟨f0 x, Subtype.ext (h0 x).symm⟩

theorem mem_range_d1 (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : ∀ y ∈ LinearMap.range d1, f2 y ∈ LinearMap.range d1 := by
  rintro y ⟨x, rfl⟩
  exact ⟨f1 x, (h1 x).symm⟩

/-- The endomorphism of `H¹`. -/
def mapH1 (h0 : ∀ x, f1 (d0 x) = d0 (f0 x)) (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : Hc1 d0 d1 hd →ₗ[R] Hc1 d0 d1 hd :=
  Submodule.mapQ _ _ (fZ h1) fun z hz => mem_range_d0Z hd h0 h1 z hz

/-- The endomorphism of `H² = coker d¹`. -/
def mapH2 (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : K2 ⧸ LinearMap.range d1 →ₗ[R] K2 ⧸ LinearMap.range d1 :=
  Submodule.mapQ _ _ f2 fun y hy => mem_range_d1 h1 y hy

/-- **Euler characteristic of traces** for a three-term complex of free finite modules over a local ring with
injective `d⁰` and free finite `H¹`, `H²`: `Tr f⁰ - Tr f¹ + Tr f² = Tr(f | H²) - Tr(f | H¹)`. -/
theorem euler3 [IsLocalRing R] [Module.Free R K0] [Module.Finite R K0] [Module.Free R K1] [Module.Finite R K1]
    [Module.Free R K2] [Module.Finite R K2] (hinj : Function.Injective d0)
    [Module.Free R (Hc1 d0 d1 hd)] [Module.Finite R (Hc1 d0 d1 hd)]
    [Module.Free R (K2 ⧸ LinearMap.range d1)] [Module.Finite R (K2 ⧸ LinearMap.range d1)]
    (h0 : ∀ x, f1 (d0 x) = d0 (f0 x)) (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) :
    trace R K0 f0 - trace R K1 f1 + trace R K2 f2 = trace R _ (mapH2 h1) - trace R _ (mapH1 hd h0 h1) := by
  -- `B = im d¹ ⊆ K²` with quotient `H²`
  obtain ⟨_, _⟩ := sub_free_finite (LinearMap.range d1)
  have T2 : trace R K2 f2 = trace R _ (f2.restrict (mem_range_d1 h1)) + trace R _ (mapH2 h1) :=
    trace_eq_restrict_add_quot _ f2 (mem_range_d1 h1)
  -- `K¹ ⧸ ker d¹ ≃ B`
  have : Module.Free R (K1 ⧸ LinearMap.ker d1) := Module.Free.of_equiv d1.quotKerEquivRange.symm
  have : Module.Finite R (K1 ⧸ LinearMap.ker d1) := Module.Finite.equiv d1.quotKerEquivRange.symm
  obtain ⟨_, _⟩ := sub_free_finite (LinearMap.ker d1)
  have T1 : trace R K1 f1 = trace R _ (fZ h1) +
      trace R _ (Submodule.mapQ _ _ f1 fun x hx => mem_ker_f1 h1 x hx) :=
    trace_eq_restrict_add_quot _ f1 (mem_ker_f1 h1)
  have TB : trace R (K1 ⧸ LinearMap.ker d1) (Submodule.mapQ _ _ f1 fun x hx => mem_ker_f1 h1 x hx) =
      trace R _ (f2.restrict (mem_range_d1 h1)) := by
    refine trace_intw d1.quotKerEquivRange fun v => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    apply Subtype.ext
    simp [h1]
  -- `im d⁰ ⊆ ker d¹` with quotient `H¹`, and `K⁰ ≃ im d⁰`
  have hinjZ : Function.Injective (d0Z d0 d1 hd) := fun a b h => hinj (congrArg Subtype.val h)
  have TZ : trace R _ (fZ h1) = trace R _ ((fZ h1).restrict (mem_range_d0Z hd h0 h1)) +
      trace R _ (mapH1 hd h0 h1) :=
    trace_eq_restrict_add_quot _ (fZ h1) (mem_range_d0Z hd h0 h1)
  have T0 : trace R K0 f0 = trace R _ ((fZ h1).restrict (mem_range_d0Z hd h0 h1)) :=
    trace_intw (LinearEquiv.ofInjective (d0Z d0 d1 hd) hinjZ) fun v => Subtype.ext (Subtype.ext (h0 v).symm)
  linear_combination T0 - T1 + T2 - TB - TZ

end Euler

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockLef =====
section

/-!
# S4-Lefschetz, L3f1: the Euler characteristic of one fixed block

For a block `ω = [a]` of `Gf` fixed by `π(ψ^m) · γ` with `ψ^m = c0 g` (`c0 ∈ Γ`, `g ∈ H`, `π g = a γ⁻¹ a⁻¹`):
the alternating trace of `P_ω ∘ ρPC γ⁻¹ ∘ frobPC^m` on the total perfect complex equals `c^m - Tr(F | H¹_c)` of the
`G'`-cone with coefficients `coind_{H ∩ G'}^{G'} σH` (`block_euler`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh MonoidAlgebra Representation

section BlockEuler

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S] (I : S → Subgroup G) [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] {H G' : Subgroup G} (σH : Representation Λ (H.subgroupOf G') Λ) (hπ : IsOpen (π.ker : Set G)) (hΓ : Γ ≤ G') (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H) (hσ : ∀ h, σH h = 1) (a : Gf)

/-- The fixed-block condition from the block data. -/
theorem hfix_of_block {γ : Gf} {ψm c0 g : G} (hc0 : c0 ∈ Γ) (hψ : ψm = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹) :
    π ψm * a * γ * a⁻¹ ∈ Γ.map π := by
  rw [hψ, map_mul, hπg]
  exact ⟨c0, hc0, by group⟩

end BlockEuler

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Cancel =====
section

/-!
# S4-Lefschetz (L2): cancelling a non-unit factor by lifting the coefficient level

The Hattori-Stallings centraliser formula only gives `|Z(γ)| * τ_[γ] = |Z(γ)| * N_γ` in `ℤ/lᵐ`, and `|Z(γ)|` need not
be a unit. The cure: compute at the higher level `ℤ/l^(n+k)` with `|Z(γ)| ∣ l^k`-part absorbed, then reduce to `ℤ/lⁿ`.
* `cast_eq_of_mul_eq`: if `a * x = a * y` in `ZMod (l ^ (n + k))` and `a ∣ l ^ k`, then `x` and `y` have the same image
  in `ZMod (l ^ n)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.Lefschetz

/-- The level divisibility `l ^ n ∣ l ^ (n + k)`. -/
theorem lvl_dvd (l n k : ℕ) : l ^ n ∣ l ^ (n + k) := pow_dvd_pow l (Nat.le_add_right n k)

/-- **Cancellation by lifting the level.** If `a * x = a * y` in `ℤ/l^(n+k)` and `a ∣ l^k`, then `x ≡ y` in `ℤ/lⁿ`. -/
theorem cast_eq_of_mul_eq {l : ℕ} (hl : 0 < l) (n k a : ℕ) (ha : a ∣ l ^ k)
    (x y : ZMod (l ^ (n + k))) (h : (a : ZMod (l ^ (n + k))) * x = a * y) :
    ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) x = ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) y := by
  have : NeZero (l ^ (n + k)) := ⟨pow_ne_zero _ hl.ne'⟩
  rw [← sub_eq_zero, ← map_sub]
  have h0 : (a : ZMod (l ^ (n + k))) * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  rw [← ZMod.natCast_zmod_val (x - y), ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨b, hb⟩ := ha
  have hapos : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb
    exact pow_ne_zero _ hl.ne' hb
  have hdvd : l ^ n ∣ (x - y).val := by
    have h1 : a * (l ^ n * b) ∣ a * (x - y).val := by
      have he : a * (l ^ n * b) = l ^ (n + k) := by rw [pow_add, hb]; ring
      rw [he]
      exact h0
    exact dvd_trans (dvd_mul_right _ b) ((mul_dvd_mul_iff_left hapos).1 h1)
  rw [← ZMod.natCast_zmod_val (x - y), map_natCast, ZMod.natCast_eq_zero_iff]
  exact hdvd

end RamanujanPetersson.Lefschetz


end

-- ===== S4.Def_RP_Lefschetz_Pow =====
section

/-!
# S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius

`lefschetz_frob` (S4-PD) is the twisted trace formula for the Frobenius `F` itself. Here it is extended to every power
`F^m`: equivariance is stable under powers (`isEquivariant_pow`), intertwinings iterate (`intertwine_pow`), the map
induced on coinvariants by `φ^m ⊗ id` is the `m`-th power of the map induced by `φ ⊗ id` (`coinvMap_tensor_pow`), so
`Tr(F^m | M) - Tr(F^m | K¹(M)) + Tr(F^m | K²(M)) = Σ_c L(frobPC^m)[c] · Tr(τ(c)⁻¹ | M)` (`lefschetz_frob_pow`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open CurveCoh MonoidAlgebra Representation TensorProduct

noncomputable section

section Gen

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] {P : Type*} [AddCommGroup P] [Module R P]

/-- An intertwining `e ∘ f = g ∘ e` iterates: `e ∘ f^m = g^m ∘ e`. -/
theorem intertwine_pow {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (e : V → W)
    {f : V →ₗ[R] V} {g : W →ₗ[R] W} (hfg : ∀ v, e (f v) = g (e v)) : ∀ (m : ℕ) (v : V), e ((f ^ m) v) = (g ^ m) (e v)
  | 0, v => by simp only [pow_zero, Module.End.one_apply]
  | m + 1, v => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, intertwine_pow e hfg m, hfg]

variable {V : Type*} [AddCommGroup V] [Module R V]

variable {M : Type*} [AddCommGroup M] [Module R M]

end Gen

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M) {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hπ : IsOpen (π.ker : Set G))

variable (m : ℕ)

end Model

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ClassCount =====
section

/-!
# S4-Lefschetz L2b: class traces of `F^m` from twisted counts

The Lefschetz numbers of the powers of the Frobenius reduce along `Λ → Λ/(ϖ)` (`lefschetz_frob_pow_red`). Combined
with the centraliser formula `Σ (-1)^i Tr(γ⁻¹ ∘ F^m | PC^i) = |Z(γ)| · L(F^m)[γ]` (Hattori–Stallings) at the level
`ℤ/l^(n+k)` and the cancellation of the non-unit `|Z(γ)|` (`cast_eq_of_mul_eq'`), a twisted count
`Σ (-1)^i Tr(γ⁻¹ ∘ F^m | PC^i) = |Z(γ)| · N_γ` at level `n + k` gives `L(F^m)[γ] = N_γ` at level `n`
(`lefschetz_pow_eq_count`), as soon as `l^k` kills the `l`-part of `|Gf|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open CurveCoh MonoidAlgebra TensorProduct

noncomputable section

/-- Iterated intertwining across two rings. -/
theorem intertwine_pow' {R R' : Type*} [CommRing R] [CommRing R'] {V W : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R' W] (e : V → W) {f : V →ₗ[R] V} {g : W →ₗ[R'] W} (hfg : ∀ v, e (f v) = g (e v)) :
    ∀ (m : ℕ) (v : V), e ((f ^ m) v) = (g ^ m) (e v)
  | 0, v => by simp only [pow_zero, Module.End.one_apply]
  | m + 1, v => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, intertwine_pow' e hfg m, hfg]

section Red

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G) [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (m : ℕ)

end Red

section Count

variable {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) {l : ℕ} (hl : l.Prime) (n k : ℕ) (hπ : IsOpen (π.ker : Set G))

end Count

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_FrobSpec =====
section

/-!
# S4-Lefschetz, L4h part 3: Frobenius data at the boundary

For boundary data `D` (points `P s` of the pro-chart, inertia `D.inertia s`):
* `FrobSpec D ψ τ h`: `ψ⁻¹ • P s = h_s • P (τ s)` (the defining property of `trueTau`/`trueH`);
  `frobSpec_true`, `frobSpec_compat` (gives `BdryCompat`), `frobSpec_mul_geo`, `frobSpec_pow` (with `hpow`);
* `frobSpec_disj`, `frobSpec_unique` (geometric stabilisers of boundary points lie in inertia);
  `frobH1c_eq_true`: the Frobenius on `H¹_c` of any `FrobSpec` datum is the one of `trueTau`/`trueH`;
* `geoLift`, `gen_frobMatch`, `gen_bdryCompat`: for a cover (ShapGen setting of `Def_RP_Lefschetz_ShapData`), Frobenius
  data on the cover and on the base satisfy `FrobMatch` (the hypothesis of `shapiroH1c_frob`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh CP4a

noncomputable section

section Spec

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {q : ℕ} {S : Type} (D : BdryData A K q R0 S)

/-- `(ψ, τ, h)` is a Frobenius datum at the boundary: `ψ⁻¹ • P s = h_s • P (τ s)`. -/
def FrobSpec (ψ : Pi1 A K) (τ : S → S) (h : S → pi1geo A K q) : Prop :=
  ∀ s, ψ⁻¹ • D.P s = ((h s : pi1geo A K q) : Pi1 A K) • D.P (τ s)

theorem frobSpec_true (ψ : Pi1 A K) : FrobSpec D ψ (trueTau D ψ) (trueH D ψ) := trueTau_spec D ψ

theorem frobSpec_compat {ψ : Pi1 A K} {τ : S → S} {h : S → pi1geo A K q} (hS : FrobSpec D ψ τ h) :
    BdryCompat (pi1geo A K q) D.inertia ψ τ h := by
  intro s x hx
  have hx' : (x : Pi1 A K) ∈ (D.P s).inertia (Pi1 A K) := hx
  have h1 := conj_mem_inertia_smul A K R0 ψ⁻¹ hx'
  rw [inv_inv] at h1
  exact inv_conj_mem_inertia A K R0 (hS s) h1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem frobSpec_mul_geo {ψ : Pi1 A K} {τ : S → S} {h : S → pi1geo A K q} (hS : FrobSpec D ψ τ h)
    (γ0 : pi1geo A K q) : FrobSpec D (ψ * γ0) τ (fun s => γ0⁻¹ * h s) := by
  intro s
  calc (ψ * (γ0 : Pi1 A K))⁻¹ • D.P s = ((γ0 : Pi1 A K))⁻¹ • (ψ⁻¹ • D.P s) := by
        rw [mul_inv_rev]; exact mul_smul ((γ0 : Pi1 A K))⁻¹ ψ⁻¹ (D.P s)
    _ = ((γ0 : Pi1 A K))⁻¹ • ((h s : Pi1 A K) • D.P (τ s)) := by rw [hS s]
    _ = _ := (mul_smul ((γ0 : Pi1 A K))⁻¹ (h s : Pi1 A K) (D.P (τ s))).symm

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem frobSpec_pow {ψ : Pi1 A K} {τ : S → S} {h : S → pi1geo A K q} (hS : FrobSpec D ψ τ h) (m : ℕ) :
    FrobSpec D (ψ ^ m) τ^[m] (hpow (pi1geo A K q) ψ τ h m) := by
  induction m with
  | zero =>
    intro s
    show (ψ ^ 0)⁻¹ • D.P s = ((1 : pi1geo A K q) : Pi1 A K) • D.P s
    rw [pow_zero, inv_one, Subgroup.coe_one]
  | succ m ih =>
    intro s
    show (ψ ^ (m + 1))⁻¹ • D.P s = ((ψ ^ m)⁻¹ * (h s : Pi1 A K) * ψ ^ m *
      (hpow (pi1geo A K q) ψ τ h m (τ s) : Pi1 A K)) • D.P (τ^[m] (τ s))
    calc (ψ ^ (m + 1))⁻¹ • D.P s = (ψ ^ m)⁻¹ • (ψ⁻¹ • D.P s) := by
          rw [pow_succ', mul_inv_rev]; exact mul_smul (ψ ^ m)⁻¹ ψ⁻¹ (D.P s)
      _ = (ψ ^ m)⁻¹ • ((h s : Pi1 A K) • D.P (τ s)) := by rw [hS s]
      _ = ((ψ ^ m)⁻¹ * (h s : Pi1 A K) * ψ ^ m) • ((ψ ^ m)⁻¹ • D.P (τ s)) := by
          rw [smul_smul ((ψ ^ m)⁻¹ * (h s : Pi1 A K) * ψ ^ m) (ψ ^ m)⁻¹, mul_inv_cancel_right]
          exact (mul_smul (ψ ^ m)⁻¹ (h s : Pi1 A K) (D.P (τ s))).symm
      _ = _ := by
          rw [ih (τ s)]
          exact (mul_smul ((ψ ^ m)⁻¹ * (h s : Pi1 A K) * ψ ^ m)
            (hpow (pi1geo A K q) ψ τ h m (τ s) : Pi1 A K) (D.P (τ^[m] (τ s)))).symm

end Spec

section Match

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]
variable {q q' : ℕ} {S T : Type} (D : BdryData A K q R0 S) (D' : BdryData A' K' q' R0' T)
  (f : proChart A K R0 ≃+* proChart A' K' R0')
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) (hD'B : ∀ Q, D'.B Q ↔ IsBdryPrime A' K' R0' Q)
  (r : Pi1 A' K' →* Pi1 A K) (hf : ∀ σ x, f (r σ • x) = σ • f x)
  (hgeo : ∀ σ, r σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A' K' q')

include hDB in
/-- The `D`-form of the stabiliser hypothesis of `gen_dCover`. -/
theorem hstabD_of (hstab : ∀ Q, IsBdryPrime A K R0 Q → ∀ σ ∈ pi1geo A K q, σ • Q = Q → σ ∈ Q.inertia (Pi1 A K)) :
    ∀ s, ∀ σ ∈ pi1geo A K q, σ • D.P s = D.P s → σ ∈ D.inertia s :=
  fun s σ hσ hfix => hstab _ ((hDB _).1 (D.mem s)) σ hσ hfix

/-- The image `r ψ'` of a Frobenius lift of the cover, as an element of `H = range r`. -/
def rangeElt (ψ' : Pi1 A' K') : r.range := ⟨r ψ', MonoidHom.mem_range.2 ⟨ψ', rfl⟩⟩

end Match

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_H1Les =====
section

/-!
# S4-Lefschetz, L3e2d1: `H¹_c` with constant coefficients is finite free

* `free_finite_of_les`: in an exact `0 → H₀ → B → C → P → 0` with `B` finite, `B / H₀` free and `P` finite free,
  `C` is finite free (`C ≅ B / H₀ × P`: the sequence splits since `P` is projective).
* `free_H1c_triv`: `H¹_c(Γ, {I_s}; Λ)` is finite free when `H¹_par` is (`0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0`).
* `free_curveH1c`: for a curve `U/𝔽_q` with full constant field, `H¹_c(Ū, ℤ/l^n)` is finite free (CP4a's
  `free_curveH1par` with Core B discharged by `CoreB.coreBHyp_proved`, as in `CP4.lefschetz_point_count`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover CP4a

section Les

variable {R : Type*} [CommRing R]

/-- In an exact `0 → H₀ → B → C → P → 0` with `B` finite, `B / H₀` free and `P` finite free, `C` is finite free. -/
theorem free_finite_of_les {H0 B C P : Type*} [AddCommGroup H0] [Module R H0] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup P] [Module R P]
    (i : H0 →ₗ[R] B) (d : B →ₗ[R] C) (π : C →ₗ[R] P)
    (hid : Function.Exact i d) (hdπ : Function.Exact d π) (hπ : Function.Surjective π)
    (hBf : Module.Finite R B) (hQ : Module.Free R (B ⧸ LinearMap.range i))
    (hP : Module.Free R P ∧ Module.Finite R P) :
    Module.Free R C ∧ Module.Finite R C := by
  obtain ⟨_, _⟩ := hP
  have hker : LinearMap.ker d = LinearMap.range i := LinearMap.exact_iff.mp hid
  have hker' : LinearMap.ker π = LinearMap.range d := LinearMap.exact_iff.mp hdπ
  let dq : (B ⧸ LinearMap.range i) →ₗ[R] C := (LinearMap.range i).liftQ d hker.ge
  have hdq : Function.Injective dq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hker.symm
  have hex : Function.Exact dq π := by
    rw [LinearMap.exact_iff, Submodule.range_liftQ, hker']
  obtain ⟨l, hl⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let e := (hex.splitSurjectiveEquiv hdq ⟨l, hl⟩).1
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

end Les

section Pair

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

end Pair

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end Curve

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_H2Sh =====
section

/-!
# S4-Lefschetz, L4i3: `H²_c` of an induced trivial module

For `G = H·Γ` with finitely many cosets (`R : CosetReps Γ H`) and `σ` the trivial representation of `H` on `k`,
`H²_c(Γ; Ind_H^G k) = (Ind_H^G k)_Γ ≃ k` by summing over the coset representatives, and every Frobenius
`frobH2c ψ χ` acts there as `χ`.

* `indH` (the indicator of `H`), `sumMap`, `coind_decomp`, `sumMap_rho`, `mk_eq_smul`;
* `h2ShEquiv : H2c (pushRep H σ) Γ ≃ₗ[k] k`, `frobH2c_ind : frobH2c (pushRep H σ) Γ ψ χ = χ • 1`;
* **`trace_frobH2c_ind`**: `Tr(frobH2c ψ χ ^ m | H²_c(Γ; Ind_H^G k)) = χ ^ m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Representation

section H2Sh

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {Γ H : Subgroup G} (σ : Representation k H k) (hσ : ∀ h : H, σ h = 1)

open Classical in
/-- The indicator function of `H`, an element of `Ind_H^G k`. -/
def indH : coindV H.subtype σ :=
  ⟨fun x => if x ∈ H then 1 else 0, by
    rw [mem_coindV]
    intro g x
    rw [hσ]
    show (if (g : G) * x ∈ H then (1 : k) else 0) = if x ∈ H then 1 else 0
    simp only [H.mul_mem_cancel_left g.2]⟩

open Classical in
theorem indH_apply (x : G) :
    ((indH σ hσ : coindV H.subtype σ) : G → k) x = if x ∈ H then 1 else 0 := rfl

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

variable [IsTopologicalGroup G] [Γ.Normal]

end H2Sh

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtTorsor =====
section

/-!
# S4-Lefschetz, L5a: points of an unramified Galois cover form a torsor

For `B / A` with a finite group `G` acting (`A = B^G`, `Algebra.IsInvariant`) and every inertia group trivial
(unramified), and a field `Ω`:
* `hom_smul_free`: `w ∘ g = w` for a ring hom `w : B → Ω` forces `g = 1`;
* `hom_smul_trans`: two ring homs `w, w' : B → Ω` that agree on `A` differ by an element of `G`
  (`w' = w ∘ g`), provided the residue ring `B / ker w'` is finite.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtTorsor

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]

/-- **Freeness**: an unramified Galois action has no fixed ring homs. -/
theorem hom_smul_free (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) (w : B →+* Ω) {g : G}
    (h : ∀ b, w (g • b) = w b) : g = 1 := by
  have hg : g ∈ (RingHom.ker w).inertia G :=
    AddSubgroup.mem_inertia.2 fun b => (RingHom.mem_ker (f := w)).2 (by rw [map_sub, h, sub_self])
  rw [hun _ (RingHom.ker_isPrime w)] at hg
  exact hg

variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]

end PtTorsor

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtCount =====
section

/-!
# S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover

`B / A` with a finite group `G` (`A = B^G`, unramified), a subgroup `H`, an intermediate ring `C` with `C = B^H`,
an algebraically closed field `Ω` with an endomorphism `Fr`, a point `u : A → Ω` and a lift `w0 : B → Ω` of `u` with
`Fr ∘ w0 = w0 ∘ F` (`F ∈ G`). Then (`card_fixed_ptRes`)

  `#{x ∈ G | x⁻¹ F x ∈ H} = #{v : C → Ω over u | Fr ∘ v = v} * |H|`,

via the restrictions `ptRes C w0 x : c ↦ w0 (x • c)` (fibers = left cosets `x H`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtCountGen

end PtCountGen

section PtCount

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]

/-- Two translates of a ring hom `w : B → Ω` agree only for equal group elements (unramified action). -/
theorem pt_smul_eq (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) (w : B →+* Ω) {g₁ g₂ : G}
    (h : ∀ b, w (g₁ • b) = w (g₂ • b)) : g₁ = g₂ := by
  have h1 : g₂⁻¹ * g₁ = 1 := by
    refine hom_smul_free hun (w.comp (MulSemiringAction.toRingHom G B g₂)) fun b => ?_
    show w (g₂ • (g₂⁻¹ * g₁) • b) = w (g₂ • b)
    rw [← mul_smul, mul_inv_cancel_left]
    exact h b
  exact (inv_mul_eq_one.1 h1).symm

/-- The restriction `c ↦ w (x • c)` of a translate of `w : B → Ω` to `C`. -/
def ptRes (C : Type) [CommRing C] [Algebra C B] (w : B →+* Ω) (x : G) : C →+* Ω :=
  (w.comp (MulSemiringAction.toRingHom G B x)).comp (algebraMap C B)

theorem ptRes_apply (C : Type) [CommRing C] [Algebra C B] (w : B →+* Ω) (x : G) (c : C) :
    ptRes C w x c = w (x • algebraMap C B c) := rfl

variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

end PtCount

end

end Lefschetz
end RamanujanPetersson


end


