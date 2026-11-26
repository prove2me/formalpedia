-- Prove2me | Definitions.Def_RPLib_FX_GOSC_GL
-- name    : RPLib_FX_GOSC_GL
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:03:49.332052+00:00
-- url     : https://prove2.me/theorems/b31b0e2d-d805-5858-92ff-98aff6b7ddc2
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, glue lemmas
-- statement:
--   Glue lemmas of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: quotients $Z/(B\cap Z)$ of cochain modules under an ambient linear equivalence, independence of the relative cohomology $H^1_c$ from the choice of boundary representatives, the lower ramification groups at a place over infinity as the groups $\{\sigma : \sigma(b)-b\in\mathfrak Q^{u+1}\}$, the Swan conductor in Serre's lower-numbering form $\sum_{i\ge1}\frac{|G_i|}{|G_0|}(\dim M-\dim M^{G_i})$, and elementwise forms of the unramifiedness and translated-prime conditions.
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_FX_GOSC_14

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field: glue lemmas

Glue lemmas of the series `RPLib_FX_GOSC_*` between the library's cochain cohomology and Swan conductor and their
elementwise forms: quotients `Z / (B ∩ Z)` under an ambient linear equivalence (`GOSCU.finrank_quot_eq`),
independence of `H¹_c` from the choice of boundary representatives (`GOSCU.finrank_h1c_bdry`), the lower
ramification groups at a place over infinity as ideal-power inertia groups (`GOSCU.mem_lowerQ_iff_pow`), the Swan
conductor in Serre's lower-numbering form (`GOSCU.swanQ_eq_finsum`), and the unramifiedness / translated-prime
conditions in elementwise form (`GOSCU.unram_iff`, `GOSCU.mem_smul_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section P1
open scoped Pointwise

namespace RamanujanPetersson
namespace GOSCU

open CurveCoh

section Quot

variable {k : Type} [CommRing k] {V V' : Type} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- Quotients `Z / (B ∩ Z)` match under an ambient linear equivalence carrying `Z` to `Z'` and `B ∩ Z` to `B'`. -/
theorem finrank_quot_eq (T : V ≃ₗ[k] V') (Z B : Submodule k V) (Z' B' : Submodule k V')
    (hZ : ∀ v, v ∈ Z ↔ T v ∈ Z') (hB : ∀ v ∈ Z, v ∈ B ↔ T v ∈ B') :
    Module.finrank k (Z ⧸ B.comap Z.subtype) = Module.finrank k (Z' ⧸ B'.comap Z'.subtype) := by
  have hmap : Z.map (T : V →ₗ[k] V') = Z' := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hZ v).1 hv
    · intro hy
      refine ⟨T.symm y, (hZ _).2 (by simpa using hy), by simp⟩
  let f : Z ≃ₗ[k] Z' := (T.submoduleMap Z).trans (LinearEquiv.ofEq _ _ hmap)
  have hf : ∀ z : Z, ((f z : Z') : V') = T z := fun _ => rfl
  refine LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ f ?_)
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show ((f z : Z') : V') ∈ B'
    rw [hf]
    exact (hB z z.2).1 hz
  · intro hy
    refine ⟨f.symm y, ?_, by simp⟩
    show ((f.symm y : Z) : V) ∈ B
    refine (hB _ (f.symm y).2).2 ?_
    rw [← hf, LinearEquiv.apply_symm_apply]
    exact hy

end Quot

section Pair

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G)
  {S S' : Type} (I : S → Subgroup G) (I' : S' → Subgroup G) (e : S' ≃ S) (h : S' → Γ)

/-- Re-indexing the boundary trivialisations along `e` and the conjugators `h`. -/
def reidx : ((Γ → M) × (S → M)) ≃ₗ[k] ((Γ → M) × (S' → M)) where
  toFun p := (p.1, fun s' => ρ (h s') (p.2 (e s')) - p.1 (h s'))
  invFun p := (p.1, fun s => ρ ((h (e.symm s))⁻¹ : Γ) (p.2 (e.symm s) + p.1 (h (e.symm s))))
  map_add' p q := by
    refine Prod.ext rfl (funext fun s' => ?_)
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_add]
    abel
  map_smul' a p := by
    refine Prod.ext rfl (funext fun s' => ?_)
    simp [smul_sub]
  left_inv p := by
    refine Prod.ext rfl (funext fun s => ?_)
    simp only [Equiv.apply_symm_apply, sub_add_cancel]
    rw [Subgroup.coe_inv, Representation.inv_self_apply]
  right_inv p := by
    refine Prod.ext rfl (funext fun s' => ?_)
    simp only [Equiv.symm_apply_apply]
    rw [Subgroup.coe_inv, Representation.self_inv_apply, add_sub_cancel_right]

theorem reidx_fst (p : (Γ → M) × (S → M)) : (reidx ρ Γ e h p).1 = p.1 := rfl

theorem reidx_snd (p : (Γ → M) × (S → M)) (s' : S') :
    (reidx ρ Γ e h p).2 s' = ρ (h s') (p.2 (e s')) - p.1 (h s') := rfl

variable {I I' e h}

theorem reidx_mem_Z1c_iff
    (hI : ∀ (s' : S') (g : Γ), (g : G) ∈ I' s' ↔ (((h s')⁻¹ * g * h s' : Γ) : G) ∈ I (e s'))
    (p : (Γ → M) × (S → M)) : p ∈ Z1c ρ Γ I ↔ reidx ρ Γ e h p ∈ Z1c ρ Γ I' := by
  constructor
  · rintro ⟨hp1, hp2⟩
    refine ⟨hp1, fun s' g hg => ?_⟩
    have hg' := hp2 (e s') _ ((hI s' g).1 hg)
    have hc := Z1_conj ρ Γ hp1 (h s') _ _ hg'
    have he : h s' * ((h s')⁻¹ * g * h s') * (h s')⁻¹ = g := by group
    rw [he] at hc
    rw [reidx_fst, reidx_snd, hc]
  · rintro ⟨hp1', hp2⟩
    have hp1 : p.1 ∈ Z1 ρ Γ := hp1'
    refine ⟨hp1, fun s g hg => ?_⟩
    obtain ⟨s', rfl⟩ := e.surjective s
    set g' : Γ := h s' * g * (h s')⁻¹
    have hg' : (g' : G) ∈ I' s' := by
      rw [hI s' g']
      have : (h s')⁻¹ * g' * h s' = g := by simp only [g']; group
      rw [this]
      exact hg
    have h1 := hp2 s' g' hg'
    rw [reidx_fst, reidx_snd] at h1
    have hc := Z1_conj ρ Γ hp1 (h s')⁻¹ g' _ h1
    have he : (h s')⁻¹ * g' * (h s')⁻¹⁻¹ = g := by simp only [g']; group
    rw [he] at hc
    have key : ρ (((h s')⁻¹ : Γ) : G) (ρ (h s') (p.2 (e s')) - p.1 (h s')) - p.1 (h s')⁻¹ = p.2 (e s') := by
      rw [Z1_inv ρ Γ hp1, map_sub, Subgroup.coe_inv, Representation.inv_self_apply]
      abel
    rw [hc, key]

theorem reidx_mem_B1c_iff
    (hI : ∀ (s' : S') (g : Γ), (g : G) ∈ I' s' ↔ (((h s')⁻¹ * g * h s' : Γ) : G) ∈ I (e s'))
    (p : (Γ → M) × (S → M)) (hp : p ∈ Z1c ρ Γ I) : p ∈ B1c ρ Γ I ↔ reidx ρ Γ e h p ∈ B1c ρ Γ I' := by
  constructor
  · rintro ⟨-, m, hm1, hm2⟩
    refine ⟨(reidx_mem_Z1c_iff ρ Γ hI p).1 hp, m, fun g => hm1 g, fun s' => ?_⟩
    rw [reidx_snd, hm2, hm1]
    abel
  · rintro ⟨-, m, hm1, hm2⟩
    refine ⟨hp, m, fun g => hm1 g, fun s => ?_⟩
    obtain ⟨s', rfl⟩ := e.surjective s
    have h2 := hm2 s'
    rw [reidx_snd, show p.1 (h s') = ρ (h s') m - m from hm1 (h s')] at h2
    have h3 : ρ (h s') (p.2 (e s')) = ρ (h s') m := by
      rw [sub_eq_iff_eq_add.1 h2]
      abel
    have h4 := congrArg (ρ ((h s' : G))⁻¹) h3
    rwa [Representation.inv_self_apply, Representation.inv_self_apply] at h4

/-- `H¹_c` does not depend on the choice of boundary representatives (re-indexing plus conjugation). -/
theorem finrank_h1c_reidx
    (hI : ∀ (s' : S') (g : Γ), (g : G) ∈ I' s' ↔ (((h s')⁻¹ * g * h s' : Γ) : G) ∈ I (e s')) :
    Module.finrank k (H1c ρ Γ I) = Module.finrank k (H1c ρ Γ I') :=
  finrank_quot_eq (reidx ρ Γ e h) _ _ _ _ (reidx_mem_Z1c_iff ρ Γ hI)
    (fun p hp => reidx_mem_B1c_iff ρ Γ hI p hp)

end Pair

section Bdry

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ}
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

set_option synthInstance.maxHeartbeats 200000 in
/-- Two boundary data with the same boundary primes have the same `H¹_c`. -/
theorem finrank_h1c_bdry {S S' : Type} (D : BdryData A K q R0 S) (D' : BdryData A K q R0 S')
    (hB : ∀ Q, D'.B Q → D.B Q) (hB' : ∀ Q, D.B Q → D'.B Q)
    {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k (Pi1 A K) M) :
    Module.finrank k (H1c ρ (pi1geo A K q) D.inertia) =
      Module.finrank k (H1c ρ (pi1geo A K q) D'.inertia) := by
  choose e g hg he using fun s' => D.cover (D'.P s') (hB _ (D'.mem s'))
  have hinj : Function.Injective e := by
    intro s1 s2 h12
    have h2 : D'.P s2 = (g s2 * (g s1)⁻¹ : Pi1 A K) • D'.P s1 := by
      rw [he s2, he s1, h12, mul_smul (g s2) (g s1)⁻¹ (g s1 • D.P (e s2)), inv_smul_smul]
    exact D'.disj s1 s2 _ ((pi1geo A K q).mul_mem (hg s2) ((pi1geo A K q).inv_mem (hg s1))) h2
  have hsurj : Function.Surjective e := by
    intro s
    obtain ⟨s', g', hg', h'⟩ := D'.cover (D.P s) (hB' _ (D.mem s))
    refine ⟨s', D.disj (e s') s (g' * g s' : Pi1 A K) ((pi1geo A K q).mul_mem hg' (hg s')) ?_⟩
    rw [h', he s']
    exact (mul_smul g' (g s') (D.P (e s'))).symm
  let E : S' ≃ S := Equiv.ofBijective e ⟨hinj, hsurj⟩
  let h : S' → pi1geo A K q := fun s' => ⟨g s', hg s'⟩
  refine finrank_h1c_reidx ρ (pi1geo A K q) (I := D.inertia) (I' := D'.inertia) (e := E) (h := h)
    fun s' x => ?_
  show (x : Pi1 A K) ∈ (D'.P s').inertia (Pi1 A K) ↔
    (g s')⁻¹ * (x : Pi1 A K) * g s' ∈ (D.P (e s')).inertia (Pi1 A K)
  constructor
  · intro hx
    exact inv_conj_mem_inertia A K R0 (he s') hx
  · intro hx
    have := conj_mem_inertia_smul A K R0 (g s') hx
    rw [← he s'] at this
    simpa [mul_assoc] using this

end Bdry

end GOSCU
end RamanujanPetersson

end P1

noncomputable section P2
open Polynomial IsDedekindDomain Classical Module

namespace RamanujanPetersson.GOSCU
open RamanujanPetersson.Places (Rfin Rinf Oinf)
open RamanujanPetersson.GOS

section SW
variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- `σ ∈ I_Q` iff `σ b - b ∈ Q` for every `b` integral over `∞` (elementwise form). -/
theorem mem_inertia_iff' (Q : HeightOneSpectrum (Rinf Fq L)) (σ : G) :
    letI := actRinf Fq K L G
    σ ∈ Q.asIdeal.inertia G ↔ ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal, (c : L) = σ • (b : L) - b := by
  letI := actRinf Fq K L G
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, by rw [Subalgebra.coe_sub, actRinf_smul]⟩, ?_⟩
  rintro ⟨c, hc, he⟩
  have : c = σ • b - b := Subtype.ext (by rw [he, Subalgebra.coe_sub, actRinf_smul])
  rwa [← this]

/-- The lower ramification groups at `Q | ∞` are the ideal-power inertia groups:
`σ ∈ G_{Q,u} ↔ σ b - b ∈ Q^{u+1}` for every `b` integral over `∞`. -/
theorem mem_lowerQ_iff_pow (Q : HeightOneSpectrum (Rinf Fq L)) (σ : G) (u : ℕ) :
    letI := actRinf Fq K L G
    σ ∈ lowerQ Fq K L G Q u ↔ ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal ^ (u + 1), (c : L) = σ • (b : L) - b := by
  letI := actRinf Fq K L G
  by_cases hσ : σ = 1
  · subst hσ
    refine ⟨fun _ b => ⟨0, Submodule.zero_mem _, by simp⟩, fun _ => (lowerQ Fq K L G Q u).one_mem⟩
  rw [mem_lowerQ_iff Fq K L G Q hσ u]
  set D := locQ Fq K L G Q
  -- a uniformizer at `Q` inside `Rinf L`
  obtain ⟨π0, hπ0⟩ := Q.intValuation_exists_uniformizer
  have hv0 : D.v (algebraMap (Rinf Fq L) L π0) = 1 := by
    show Swan.adicAdd Q (algebraMap (Rinf Fq L) L π0) = 1
    refine Swan.withTop_eq_of_natCast_le_iff (Swan.adicAdd_algebraMap_nonneg Q π0) zero_le_one
      fun n => ?_
    rw [Swan.natCast_le_adicAdd_algebraMap_iff, ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hπ0,
      WithZero.exp_le_exp, ← WithTop.coe_natCast, ← WithTop.coe_one, WithTop.coe_le_coe]
    constructor
    · intro h; omega
    · intro h; omega
  constructor
  · rintro ⟨hI, hu⟩ b
    let σ' : Q.asIdeal.inertia G := ⟨σ, hI⟩
    have hσ' : σ' ≠ 1 := fun h => hσ (congrArg Subtype.val h)
    obtain ⟨n, -, hn⟩ := D.ramFn.exists_i_eq hσ'
    have hiQ : iQ L σ Q = n := by
      rw [← toNat_ramFn_i Fq K L G Q σ', hn, ENat.toNat_natCast]
    have hle : ((u + 1 : ℕ) : WithTop ℤ) ≤ D.v (σ' • D.ϖ - D.ϖ) := by
      have h1 : D.ramFn.i σ' = Swan.toENat (D.v (σ' • D.ϖ - D.ϖ)) := rfl
      rw [hn] at h1
      generalize D.v (σ' • D.ϖ - D.ϖ) = w at h1
      induction w with
      | top => exact le_top
      | coe m =>
        rw [Swan.toENat_coe] at h1
        have h2 : m.toNat = n := by exact_mod_cast h1.symm
        rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
        omega
    have hb := D.lb_bot D.v_ϖ σ' (x := (b : L)) (Swan.adicAdd_algebraMap_nonneg Q b)
    have e1 : (algebraMap (Rinf Fq L) L (σ • b - b)) = σ' • (b : L) - b := by
      show ((σ • b - b : Rinf Fq L) : L) = _
      rw [Subalgebra.coe_sub, actRinf_smul]
      rfl
    have hmem : ((u + 1 : ℕ) : WithTop ℤ) ≤ Swan.adicAdd Q (algebraMap (Rinf Fq L) L (σ • b - b)) := by
      rw [e1]
      exact hle.trans hb
    refine ⟨σ • b - b, (Swan.natCast_le_adicAdd_algebraMap_iff Q _ _).1 hmem, ?_⟩
    rw [Subalgebra.coe_sub, actRinf_smul]
  · intro h
    have hI : σ ∈ Q.asIdeal.inertia G := (mem_inertia_iff' Fq K L G Q σ).2 fun b => by
      obtain ⟨c, hc, he⟩ := h b
      exact ⟨c, Ideal.pow_le_self (Nat.succ_ne_zero u) hc, he⟩
    refine ⟨hI, ?_⟩
    let σ' : Q.asIdeal.inertia G := ⟨σ, hI⟩
    have hσ' : σ' ≠ 1 := fun h => hσ (congrArg Subtype.val h)
    obtain ⟨n, -, hn⟩ := D.ramFn.exists_i_eq hσ'
    have hiQ : iQ L σ Q = n := by
      rw [← toNat_ramFn_i Fq K L G Q σ', hn, ENat.toNat_natCast]
    rw [hiQ]
    have h1 := D.ramFn_i_of_unif hv0 σ'
    rw [hn] at h1
    obtain ⟨c, hc, he⟩ := h π0
    have h2 : ((u + 1 : ℕ) : WithTop ℤ) ≤ D.v (σ' • algebraMap (Rinf Fq L) L π0 - algebraMap (Rinf Fq L) L π0) := by
      have := (Swan.natCast_le_adicAdd_algebraMap_iff (L := L) Q c (u + 1)).2 hc
      show ((u + 1 : ℕ) : WithTop ℤ) ≤ Swan.adicAdd Q (σ • (π0 : L) - π0)
      rw [← he]
      exact this
    have h3 := Swan.toENat_mono h2
    rw [← h1] at h3
    have h4 : Swan.toENat ((u + 1 : ℕ) : WithTop ℤ) = ((u + 1 : ℕ) : ℕ∞) := by
      rw [← WithTop.coe_natCast, Swan.toENat_coe]
      simp
    rw [h4] at h3
    exact_mod_cast h3

section Sw2
variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M] {Gf : Type*} [Group Gf] [Fintype Gf]
  (ι : G →* Gf) (τ : Representation k Gf M)

omit [Fintype Gf] in
theorem invariants_map_eq_iInf (H : Subgroup G) (P : G → Prop) (hP : ∀ σ, σ ∈ H ↔ P σ) :
    Representation.invariants (τ.comp (H.map ι).subtype) =
      ⨅ (σ : G) (_ : P σ), LinearMap.ker (τ (ι σ) - 1) := by
  ext m
  simp only [Representation.mem_invariants, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h σ hσ
    exact h ⟨ι σ, σ, (hP σ).2 hσ, rfl⟩
  · rintro h ⟨_, σ, hσ, rfl⟩
    exact h σ ((hP σ).1 hσ)

/-- **The Swan conductor at `Q | ∞` in Serre's lower-numbering form**, with `G_u` the ideal-power inertia
groups: `Sw_Q = Σ_{i ≥ 0} |G_{i+1}|/|G_0| (dim M - dim M^{G_{i+1}})`. -/
theorem swanQ_eq_finsum [FiniteDimensional k M] (Q : HeightOneSpectrum (Rinf Fq L)) :
    swanQ Fq K L G ι τ Q = ∑ᶠ i : ℕ,
      (Nat.card {σ : G // ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal ^ (i + 2), (c : L) = σ • (b : L) - b} : ℚ) /
        (Nat.card {σ : G // ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal, (c : L) = σ • (b : L) - b} : ℚ) *
      ((finrank k M : ℚ) - finrank k ↥(⨅ (σ : G)
        (_ : ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal ^ (i + 2), (c : L) = σ • (b : L) - b),
        LinearMap.ker (τ (ι σ) - 1))) := by
  letI := actRinf Fq K L G
  set R := (locQ Fq K L G Q).ramFn
  set ρ := (τ.comp ι).comp (Q.asIdeal.inertia G).subtype
  have hterm : ∀ i : ℕ, (Nat.card (R.lower (i + 1)) : ℚ) / Nat.card (Q.asIdeal.inertia G) *
      (Swan.cod ρ (R.lower (i + 1)) : ℚ) =
      (Nat.card {σ : G // ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal ^ (i + 2), (c : L) = σ • (b : L) - b} : ℚ) /
        (Nat.card {σ : G // ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal, (c : L) = σ • (b : L) - b} : ℚ) *
      ((finrank k M : ℚ) - finrank k ↥(⨅ (σ : G)
        (_ : ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal ^ (i + 2), (c : L) = σ • (b : L) - b),
        LinearMap.ker (τ (ι σ) - 1))) := by
    intro i
    have h1 : Nat.card (R.lower (i + 1)) =
        Nat.card {σ : G // ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal ^ (i + 2), (c : L) = σ • (b : L) - b} := by
      rw [← Subgroup.card_map_of_injective (Q.asIdeal.inertia G).subtype_injective]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_lowerQ_iff_pow Fq K L G Q σ (i + 1))
    have h2 : Nat.card (Q.asIdeal.inertia G) =
        Nat.card {σ : G // ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal, (c : L) = σ • (b : L) - b} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_inertia_iff' Fq K L G Q σ)
    have h3 : (Swan.cod ρ (R.lower (i + 1)) : ℚ) = (finrank k M : ℚ) - finrank k ↥(⨅ (σ : G)
        (_ : ∀ b : Rinf Fq L, ∃ c ∈ Q.asIdeal ^ (i + 2), (c : L) = σ • (b : L) - b),
        LinearMap.ker (τ (ι σ) - 1)) := by
      rw [Swan.cod, Nat.cast_sub (Submodule.finrank_le _), finrank_fixd_lowerQ Fq K L G ι τ Q i,
        invariants_map_eq_iInf G ι τ _ _ (fun σ => mem_lowerQ_iff_pow Fq K L G Q σ (i + 1))]
    rw [h1, h2, h3]
  show R.swan ρ = _
  rw [Swan.RamFn.swan, finsum_eq_sum_of_support_subset _ (s := Finset.range R.top) ?_]
  · exact Finset.sum_congr rfl fun i _ => hterm i
  · intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hi
    rw [← hterm i, R.lower_eq_bot (not_lt.1 hlt), Swan.cod_bot]
    simp

end Sw2

end SW

end RamanujanPetersson.GOSCU

end P2

section Main
open scoped Pointwise

namespace RamanujanPetersson.GOSCU

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

theorem mem_smul_iff {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0]
    [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
    (g : Pi1 A K) (Q : Ideal (CurveCoh.proChart A K R0)) (b : CurveCoh.proChart A K R0) :
    b ∈ g • Q ↔ ∃ c ∈ Q, (b : maxUnram A K) = g (c : maxUnram A K) := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hb
    refine ⟨_, hb, ?_⟩
    show (b : maxUnram A K) = g (g⁻¹ • (b : maxUnram A K))
    rw [← AlgEquiv.smul_def, smul_inv_smul]
  · rintro ⟨c, hc, he⟩
    have : g⁻¹ • b = c := Subtype.ext (by
      show g⁻¹ • (b : maxUnram A K) = c
      rw [he, ← AlgEquiv.smul_def, inv_smul_smul])
    rwa [this]

end RamanujanPetersson.GOSCU

end Main


