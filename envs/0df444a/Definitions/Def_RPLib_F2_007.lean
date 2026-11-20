-- Prove2me | Definitions.Def_RPLib_F2_007
-- name    : RPLib_F2_007
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T07:24:59.839258+00:00
-- url     : https://prove2.me/theorems/725fed95-03eb-4245-ab20-b46ea8eaca2a
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 007 of 70
-- statement:
--   File 007 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CurveCoh_Pair`: S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)
--   * `S4.Def_RP_CurveCoh_Const`: S4-CurveCoh, part 1b: consequences of the exact sequence, and constant coefficients
--   * `S4.Def_RP_CurveCoh_Curve`: S4-CurveCoh, part 7: the curve instance
--   * `S4.Def_RP_Kummer_H1`: S4-Kummer, part 2: `H¹(Γ, ZMod N)` is the Kummer group, with the Frobenius action
--   * `S4.Def_RP_Kummer_Const`: S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory
--   * `S4.Def_RP_CP4a_Res`: S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants
--   * `S4.Def_RP_CP4a_Trans`: S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues
--   * `S4.Def_RP_CP4a_Bres`: S4-CP4a, part e3a: the constant residue map of a boundary prime
--   * `S4.Def_RP_CP4a_Bdry`: S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)
--   * `S4.Def_RP_CP4a_Newton`: S4-CP4a, part b: Newton's identity for matrices over any commutative ring
--   * `S4.Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
--   * `S4.Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
--   * `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
--   * `S4.Def_RP_Lefschetz_BlockAlg`: S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`
--   * `S4.Def_RP_CP4a_TrExact`: S4-CP4a, part d1: traces are additive along short exact sequences of free modules
--   * `S4.Def_RP_CP4a_Les`: S4-CP4a, part d2: traces along `0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0` (constant coefficients)
--   * `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
--   * `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
--   * `S4.Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
--   * `S4.Def_RP_JacAlg_Res`: Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)
--   * `S4.Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_006

/-!
# Ramanujan-Petersson curve library (flat edition), file 007 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CurveCoh_Pair`: S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)
* `S4.Def_RP_CurveCoh_Const`: S4-CurveCoh, part 1b: consequences of the exact sequence, and constant coefficients
* `S4.Def_RP_CurveCoh_Curve`: S4-CurveCoh, part 7: the curve instance
* `S4.Def_RP_Kummer_H1`: S4-Kummer, part 2: `H¹(Γ, ZMod N)` is the Kummer group, with the Frobenius action
* `S4.Def_RP_Kummer_Const`: S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory
* `S4.Def_RP_CP4a_Res`: S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants
* `S4.Def_RP_CP4a_Trans`: S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues
* `S4.Def_RP_CP4a_Bres`: S4-CP4a, part e3a: the constant residue map of a boundary prime
* `S4.Def_RP_CP4a_Bdry`: S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)
* `S4.Def_RP_CP4a_Newton`: S4-CP4a, part b: Newton's identity for matrices over any commutative ring
* `S4.Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
* `S4.Def_RP_Kummer_Frob`: S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`
* `S4.Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
* `S4.Def_RP_Lefschetz_BlockAlg`: S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`
* `S4.Def_RP_CP4a_TrExact`: S4-CP4a, part d1: traces are additive along short exact sequences of free modules
* `S4.Def_RP_CP4a_Les`: S4-CP4a, part d2: traces along `0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0` (constant coefficients)
* `S4.Def_RP_CP4a_Lef`: S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)
* `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
* `S4.Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
* `S4.Def_RP_JacAlg_Res`: Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)
* `S4.Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CurveCoh_Pair =====
section

/-!
# S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)

Setting (S4_DESIGN section 3, reviews R2/R5/R19):
* a topological group `G` (later `π₁(U)`), a normal subgroup `Γ` (later `π₁(U ⊗ F̄)`, the geometric fundamental
  group), a representation `ρ` of `G` on `M` over ANY commutative ring `k` (review END-2, decision R19), and a family
  `I : S → Subgroup G` (later the inertia groups at the geometric boundary points `s ∈ X̄ \ Ū`, review R5).

Definitions:
* `H0 = M^Γ`;
* `H1` = LOCALLY CONSTANT (continuous, `M` discrete) 1-cocycles on `Γ` modulo coboundaries; part 2 shows it is the
  colimit of the finite-level `H¹` over open normal subgroups (covers);
* `H1c` = `H¹` of the mapping cone of `C^*(Γ, M) → ⊕_s C^*(I_s ∩ Γ, M)`: pairs `(c, b)` of a cocycle `c` and boundary
  trivialisations `b_s` with `c g = g • b_s - b_s` on `I_s ∩ Γ`, modulo `(d m, (m)_s)`;
* `H2c` = the coinvariants `M_Γ` (definition kept by review R2; the Tate twist `(-1)` enters the Frobenius as a scalar);
* the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0`, `H¹_par = ker (H¹ → ⊕_s H¹(I_s ∩ Γ))`;
* the operators `T_ψ` (`ψ ∈ G`): `(T_ψ c)(g) = ρ(ψ) c(ψ⁻¹ g ψ)`. The GEOMETRIC Frobenius is `F = T_{φ⁻¹}` for an
  arithmetic Frobenius lift `φ`; on `H2c` it is `q • ρ(φ⁻¹)` (geometric Frobenius acts on `ℤ/lⁿ(-1)` by `q`).
  All operators commute with the maps of the exact sequence.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G)

/-! ## Degree 0 and degree 1 -/

/-- `H⁰ := M^Γ`, the invariants of the geometric group. -/
def H0 : Submodule k M := Representation.invariants (ρ.comp Γ.subtype)

theorem mem_H0 (m : M) : m ∈ H0 ρ Γ ↔ ∀ g : Γ, ρ g m = m := Iff.rfl

/-! ## The cone: compactly supported `H¹` -/

variable {S : Type} (I : S → Subgroup G)

/-! ## The maps of the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0` -/

/-- `H⁰ → ⊕_s M^{I_s}`, the diagonal. -/
def h0ToBdry : H0 ρ Γ →ₗ[k] bdryInv ρ Γ I where
  toFun m := ⟨fun _ => m, fun _ g _ => (mem_H0 ρ Γ _).1 m.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forget the boundary data. -/
def z1cToZ1 : Z1c ρ Γ I →ₗ[k] Z1 ρ Γ where
  toFun p := ⟨p.1.1, p.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `H¹_c → H¹`. -/
noncomputable def h1cToH1 : H1c ρ Γ I →ₗ[k] H1 ρ Γ :=
  Submodule.mapQ _ _ (z1cToZ1 ρ Γ I) (by
    rintro p ⟨_, m, hm, _⟩
    exact ⟨p.2.1, m, hm⟩)

theorem h1cToH1_mk (p : Z1c ρ Γ I) : h1cToH1 ρ Γ I (H1c.mk ρ Γ I p) = H1.mk ρ Γ (z1cToZ1 ρ Γ I p) := rfl

theorem bdryToH1c_apply (b : bdryInv ρ Γ I) :
    bdryToH1c ρ Γ I b = H1c.mk ρ Γ I ⟨(0, b), zero_bdry_mem ρ Γ I b⟩ := rfl

theorem h0ToBdry_injective [Nonempty S] : Function.Injective (h0ToBdry ρ Γ I) := by
  intro m m' h
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  exact Subtype.ext (congrFun (congrArg Subtype.val h) s)

/-- Exactness at `⊕_s M^{I_s}`. -/
theorem exact_h0ToBdry_bdryToH1c : Function.Exact (h0ToBdry ρ Γ I) (bdryToH1c ρ Γ I) := by
  intro b
  rw [bdryToH1c_apply, H1c.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  constructor
  · rintro ⟨_, m, hm, hm'⟩
    have hm0 : m ∈ H0 ρ Γ := fun g => by
      have h0 : (0 : M) = ρ g m - m := hm g
      exact (sub_eq_zero.mp h0.symm)
    exact ⟨⟨m, hm0⟩, Subtype.ext (funext fun s => (hm' s).symm)⟩
  · rintro ⟨m, rfl⟩
    refine ⟨zero_bdry_mem ρ Γ I _, m, fun g => ?_, fun s => rfl⟩
    simp [(mem_H0 ρ Γ _).1 m.2 g]

/-- Exactness at `H¹_c`. -/
theorem exact_bdryToH1c_h1cToH1 : Function.Exact (bdryToH1c ρ Γ I) (h1cToH1 ρ Γ I) := by
  intro x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
    change h1cToH1 ρ Γ I (H1c.mk ρ Γ I p) = 0 at hx
    rw [h1cToH1_mk, H1.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
    obtain ⟨_, m, hm⟩ := hx
    have hm' : ∀ g : Γ, (p : (Γ → M) × (S → M)).1 g = ρ g m - m := hm
    have hmem : (fun s => (p : (Γ → M) × (S → M)).2 s - m) ∈ bdryInv ρ Γ I := by
      intro s g hg
      have h1 := p.2.2 s g hg
      rw [hm' g] at h1
      show ρ g ((p : (Γ → M) × (S → M)).2 s - m) = (p : (Γ → M) × (S → M)).2 s - m
      rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
      exact h1.symm
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [bdryToH1c_apply]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    refine ⟨(Z1c ρ Γ I).sub_mem (zero_bdry_mem ρ Γ I _) p.2, -m, fun g => ?_, fun s => ?_⟩
    · show (0 : Γ → M) g - (p : (Γ → M) × (S → M)).1 g = ρ g (-m) - -m
      rw [hm' g, map_neg]
      simp only [Pi.zero_apply]
      abel
    · show ((p : (Γ → M) × (S → M)).2 s - m) - (p : (Γ → M) × (S → M)).2 s = -m
      abel
  · rintro ⟨b, rfl⟩
    rw [bdryToH1c_apply, h1cToH1_mk, H1.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    exact ⟨(Z1 ρ Γ).zero_mem, 0, fun g => by simp [z1cToZ1]⟩

/-- Exactness at the right end: the image of `H¹_c → H¹` is `H¹_par`. -/
theorem range_h1cToH1 : LinearMap.range (h1cToH1 ρ Γ I) = H1par ρ Γ I := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ y
    refine ⟨z1cToZ1 ρ Γ I p, ⟨p.2.1, fun s => ⟨p.1.2 s, fun g hg => p.2.2 s g hg⟩⟩, rfl⟩
  · rintro ⟨c, ⟨hcZ, hc⟩, rfl⟩
    choose b hb using hc
    refine ⟨H1c.mk ρ Γ I ⟨((c : Γ → M), b), hcZ, fun s g hg => hb s g hg⟩, rfl⟩

/-! ## Frobenius operators -/

section Frob

variable [IsTopologicalGroup G] [hΓ : Γ.Normal]

/-- Frobenius on `H⁰`: `m ↦ ρ(ψ) m`. -/
def frobH0 (ψ : G) : H0 ρ Γ →ₗ[k] H0 ρ Γ :=
  (ρ ψ).restrict (fun m hm => fun g => by
    show ρ g (ρ ψ m) = ρ ψ m
    rw [← rho_conj ρ Γ ψ g, (mem_H0 ρ Γ m).1 hm])

variable {S : Type} (I : S → Subgroup G)

theorem frobBdry_mem (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h)
    {b : S → M} (hb : b ∈ bdryInv ρ Γ I) :
    (fun s => ρ ψ (ρ (h s) (b (τ s)))) ∈ bdryInv ρ Γ I := by
  intro s g hg
  have h1 := hb (τ s) _ (bdryCompat_mem Γ I hI s g hg)
  show ρ g (ρ ψ (ρ (h s) (b (τ s)))) = ρ ψ (ρ (h s) (b (τ s)))
  rw [← rho_conj ρ Γ ψ g]
  congr 1
  calc ρ (conjΓ Γ ψ g) (ρ (h s) (b (τ s)))
      = ρ (h s) (ρ (((h s)⁻¹ * conjΓ Γ ψ g * h s : Γ) : G) (b (τ s))) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply,
          Representation.self_inv_apply]
    _ = ρ (h s) (b (τ s)) := by rw [h1]

/-- Frobenius on `⊕_s M^{I_s}`: `b ↦ (s ↦ ρ(ψ) ρ(h_s) b_{τ s})`. -/
def frobBdry (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) :
    bdryInv ρ Γ I →ₗ[k] bdryInv ρ Γ I where
  toFun b := ⟨fun s => ρ ψ (ρ (h s) (b.1 (τ s))), frobBdry_mem ρ Γ I ψ τ h hI b.2⟩
  map_add' b b' := by
    ext s
    simp
  map_smul' a b := by
    ext s
    simp

/-! ### Frobenius commutes with the exact sequence -/

theorem frobBdry_h0ToBdry (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (m : H0 ρ Γ) :
    frobBdry ρ Γ I ψ τ h hI (h0ToBdry ρ Γ I m) = h0ToBdry ρ Γ I (frobH0 ρ Γ ψ m) := by
  ext s
  show ρ ψ (ρ (h s) m.1) = ρ ψ m.1
  rw [(mem_H0 ρ Γ _).1 m.2]

theorem frobH1c_bdryToH1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (b : bdryInv ρ Γ I) :
    frobH1c ρ Γ I ψ τ h hI (bdryToH1c ρ Γ I b) = bdryToH1c ρ Γ I (frobBdry ρ Γ I ψ τ h hI b) := by
  rw [bdryToH1c_apply, bdryToH1c_apply]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  refine Prod.ext (funext fun g => ?_) (funext fun s => ?_)
  · show ρ ψ ((0 : Γ → M) (conjΓ Γ ψ g)) = 0
    simp
  · show ρ ψ (ρ (h s) (b.1 (τ s)) - (0 : Γ → M) (h s)) = ρ ψ (ρ (h s) (b.1 (τ s)))
    simp

theorem h1cToH1_frobH1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (x : H1c ρ Γ I) :
    h1cToH1 ρ Γ I (frobH1c ρ Γ I ψ τ h hI x) = frobH1 ρ Γ ψ (h1cToH1 ρ Γ I x) := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

end Frob

/-! ## Sanity: constant coefficients -/

section Constant

variable (I : S → Subgroup G)

/-- `H⁰` of a representation on which `Γ` acts trivially is everything. -/
theorem H0_eq_top_of_trivial (h : ∀ g : Γ, ρ g = 1) : H0 ρ Γ = ⊤ :=
  eq_top_iff.2 fun m _ => fun g => by
    show ρ g m = m
    rw [h g]; rfl

/-- For constant coefficients every boundary vector is invariant. -/
theorem bdryInv_eq_top_of_trivial (h : ∀ g : Γ, ρ g = 1) : bdryInv ρ Γ I = ⊤ :=
  eq_top_iff.2 fun b _ => fun s g _ => by
    show ρ g (b s) = b s
    rw [h g]; rfl

end Constant

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_CurveCoh_Const =====
section

/-!
# S4-CurveCoh, part 1b: consequences of the exact sequence, and constant coefficients

* `(⊕_s M^{I_s}) / H⁰ ↪ H¹_c` (exactness), and it is an isomorphism when `H¹_par = 0`;
* constant coefficients (`Γ` acts trivially, e.g. the constant sheaf `Λ = ℤ/lⁿ` or `O/λⁿ` on `U_j`):
  `H⁰ = M`, `H²_c = M` (before the Tate twist), `M^{S ∖ {s₀}} ↪ H¹_c`, and `H¹_c ≅ M^{S ∖ {s₀}}` when `H¹_par = 0`
  (for `U ⊆ ℙ¹`, `H¹_par = H¹(ℙ¹) = 0` is supplied by S4-Kummer); for `M = Λ` this is free of rank `#S - 1`.
Everything is over an arbitrary commutative ring `k` (review END-2, decision R19).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

set_option linter.unusedSectionVars false

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G)
  {S : Type} (I : S → Subgroup G)

theorem ker_bdryToH1c : LinearMap.ker (bdryToH1c ρ Γ I) = LinearMap.range (h0ToBdry ρ Γ I) :=
  LinearMap.exact_iff.mp (exact_h0ToBdry_bdryToH1c ρ Γ I)

/-- `(⊕_s M^{I_s}) / H⁰ → H¹_c`. -/
noncomputable def bdryQuotToH1c : (bdryInv ρ Γ I ⧸ LinearMap.range (h0ToBdry ρ Γ I)) →ₗ[k] H1c ρ Γ I :=
  (LinearMap.range (h0ToBdry ρ Γ I)).liftQ (bdryToH1c ρ Γ I) (ker_bdryToH1c ρ Γ I).ge

theorem bdryQuotToH1c_mk (b : bdryInv ρ Γ I) :
    bdryQuotToH1c ρ Γ I (Submodule.Quotient.mk b) = bdryToH1c ρ Γ I b := rfl

theorem bdryQuotToH1c_injective : Function.Injective (bdryQuotToH1c ρ Γ I) := by
  rw [← LinearMap.ker_eq_bot, bdryQuotToH1c, Submodule.ker_liftQ, ker_bdryToH1c, Submodule.mkQ_map_self]

theorem bdryToH1c_surjective (hpar : H1par ρ Γ I = ⊥) : Function.Surjective (bdryToH1c ρ Γ I) := by
  intro x
  have hx : h1cToH1 ρ Γ I x = 0 := by
    have h : h1cToH1 ρ Γ I x ∈ H1par ρ Γ I := range_h1cToH1 ρ Γ I ▸ LinearMap.mem_range_self _ x
    rw [hpar] at h
    exact (Submodule.mem_bot k).1 h
  exact (exact_bdryToH1c_h1cToH1 ρ Γ I x).1 hx

/-- If `H¹_par = 0` then `H¹_c ≅ (⊕_s M^{I_s}) / H⁰`. -/
noncomputable def bdryQuotEquivH1c (hpar : H1par ρ Γ I = ⊥) :
    (bdryInv ρ Γ I ⧸ LinearMap.range (h0ToBdry ρ Γ I)) ≃ₗ[k] H1c ρ Γ I :=
  LinearEquiv.ofBijective (bdryQuotToH1c ρ Γ I)
    ⟨bdryQuotToH1c_injective ρ Γ I, by
      intro x
      obtain ⟨b, rfl⟩ := bdryToH1c_surjective ρ Γ I hpar x
      exact ⟨Submodule.Quotient.mk b, rfl⟩⟩

/-! ## Constant coefficients -/

section Constant

/-- Constant coefficients: `H⁰ = M`. -/
noncomputable def h0ConstEquiv (htriv : ∀ g : Γ, ρ g = 1) : H0 ρ Γ ≃ₗ[k] M :=
  (LinearEquiv.ofEq _ _ (H0_eq_top_of_trivial ρ Γ htriv)).trans (LinearEquiv.ofTop ⊤ rfl)

theorem coinvariantsKer_eq_bot (htriv : ∀ g : Γ, ρ g = 1) :
    Representation.Coinvariants.ker (ρ.comp Γ.subtype) = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, x⟩, rfl⟩
  show ρ (g : G) x - x = 0
  rw [htriv g, Module.End.one_apply, sub_self]

/-- Constant coefficients: `H²_c = M_Γ = M` (the Tate twist `(-1)` lives in the Frobenius, see `frobH2c`). -/
noncomputable def h2cConstEquiv (htriv : ∀ g : Γ, ρ g = 1) : H2c ρ Γ ≃ₗ[k] M :=
  Submodule.quotEquivOfEqBot _ (coinvariantsKer_eq_bot ρ Γ htriv)

variable (s0 : S)

/-- `b ↦ (b_s - b_{s₀})_{s ≠ s₀}`. -/
def bdryDiff : bdryInv ρ Γ I →ₗ[k] ({s // s ≠ s0} → M) where
  toFun b s := (b : S → M) s - (b : S → M) s0
  map_add' b b' := by
    funext s
    simp only [Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' a b := by
    funext s
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_sub, RingHom.id_apply]

theorem bdryDiff_apply (b : bdryInv ρ Γ I) (s : {s // s ≠ s0}) :
    bdryDiff ρ Γ I s0 b s = (b : S → M) s - (b : S → M) s0 := rfl

theorem ker_bdryDiff (htriv : ∀ g : Γ, ρ g = 1) :
    LinearMap.ker (bdryDiff ρ Γ I s0) = LinearMap.range (h0ToBdry ρ Γ I) := by
  ext b
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hb
    refine ⟨⟨(b : S → M) s0, by rw [H0_eq_top_of_trivial ρ Γ htriv]; trivial⟩, ?_⟩
    apply Subtype.ext
    funext s
    by_cases hs : s = s0
    · subst hs
      rfl
    · have h := congrFun hb ⟨s, hs⟩
      rw [bdryDiff_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h.symm
  · rintro ⟨m, rfl⟩
    funext s
    exact sub_self _

theorem bdryDiff_surjective (htriv : ∀ g : Γ, ρ g = 1) : Function.Surjective (bdryDiff ρ Γ I s0) := by
  classical
  intro f
  refine ⟨⟨fun s => if h : s = s0 then 0 else f ⟨s, h⟩, by
    rw [bdryInv_eq_top_of_trivial ρ Γ I htriv]; trivial⟩, ?_⟩
  funext s
  rw [bdryDiff_apply]
  simp [s.2]

/-- Constant coefficients: `M^{S ∖ {s₀}} ≅ (⊕_s M) / M`. -/
noncomputable def constQuotEquiv (htriv : ∀ g : Γ, ρ g = 1) :
    (bdryInv ρ Γ I ⧸ LinearMap.range (h0ToBdry ρ Γ I)) ≃ₗ[k] ({s // s ≠ s0} → M) :=
  (Submodule.quotEquivOfEq _ _ (ker_bdryDiff ρ Γ I s0 htriv).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (bdryDiff_surjective ρ Γ I s0 htriv))

end Constant

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_CurveCoh_Curve =====
section

/-!
# S4-CurveCoh, part 7: the curve instance

`U = Spec A` with function field `K` (for the project's curves `K = 𝔽_q(X)`), `π₁(U) = Gal(K_U/K)`
(`Pi1 A K`, S4-GalCover, Krull topology, compact).

* Constants: `IsConst q x` (`x ∈ 𝔽_{qⁿ}` for some `n ≥ 1`); the geometric fundamental group
  `pi1geo A K q = π₁(U ⊗ 𝔽̄_q)`, the automorphisms fixing every constant: closed (`pi1geo_isClosed`), normal,
  compact (`pi1geo_compactSpace`, used by the colimit description `curveH1_exists_finite_level`).
* Frobenius lifts `IsFrobLift A K q φ` (`φ x = x^q` on constants): two lifts differ by `π₁^geo`
  (`IsFrobLift.inv_mul_mem`). The EXISTENCE of a lift (the constant-field extensions are unramified, so lie in `K_U`)
  is not proved here: every statement takes the lift `φ` as an argument (supplied by S4-Kummer / CP4a).
* Boundary: for a chart ring `R0` with fraction field `K` (for `∞`: `R0 = O_∞`, S3-Places `Places.Oinf`), the
  pro-chart `proChart A K R0 = integralClosure R0 K_U` with its `π₁(U)`-action; `BdryData` chooses representatives
  `P s` of the `π₁^geo`-orbits of the boundary points (a `π₁(U)`-stable predicate `B`, for `∞` the nonzero primes);
  `I s = BdryData.inertia s` is the inertia group (review R5). `conj_mem_inertia_smul`: inertia is transported by
  conjugation, so every `ψ` permutes the boundary (`BdryData.exists_compat`, giving the data of `frobH1c`).
  Two boundary families (e.g. `∞` and finite removed points) combine with `bdryCompat_sum`.
* Curve cohomology (any commutative coefficient ring `Λ`, review R19): `curveH0/H1/H1c/H1par/H2c` and the
  GEOMETRIC Frobenius `geomFrobH0/H1/H1c/Bdry/H2c` (`F = T_{φ⁻¹}`, `q` on `H²_c`), the exact sequence `curve_les`,
  Frobenius compatibility `geomFrob_les`.
* Lisse coefficients `IsLisse ρ` (open kernel): they factor through a finite Galois etale cover
  (`IsLisse.exists_cover`, via S4-GalCover `exists_cover_of_isOpen`).
* Sanity: `curveH0_trivialEquiv` (`H⁰(Λ) = Λ`, e.g. `Λ = ℤ/lⁿ`), `curveH2c_trivialEquiv` with
  `geomFrobH2c_trivial` (`F = q` on `H²_c(Λ) = Λ(-1)`), `finrank_curveH1c_trivial` (rank of `H¹_c(Λ)` is
  `#boundary - 1` when `H¹_par = 0`, e.g. on `U_j` where S4-Kummer gives `Pic(Ū_j) = 0`).
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

/-! ## Constants and the geometric fundamental group -/

section Geo

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (q : ℕ)

instance pi1geo_compactSpace : CompactSpace (pi1geo A K q) :=
  isCompact_iff_compactSpace.mp (pi1geo_isClosed A K q).isCompact

/-! ## Boundary points and their inertia -/

section Boundary

variable (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)]

variable {A K q R0} {S : Type} (D : BdryData A K q R0 S)

/-- Every `ψ ∈ π₁(U)` permutes the geometric boundary points compatibly with inertia. -/
theorem BdryData.exists_compat (ψ : Pi1 A K) :
    ∃ (τ : S → S) (h : S → pi1geo A K q), BdryCompat (pi1geo A K q) D.inertia ψ τ h := by
  have key : ∀ s, ∃ t, ∃ g ∈ pi1geo A K q, ψ⁻¹ • D.P s = g • D.P t := fun s =>
    D.cover _ (D.B_smul ψ⁻¹ _ (D.mem s))
  choose τ g hg hτ using key
  refine ⟨τ, fun s => ⟨g s, hg s⟩, fun s x hx => ?_⟩
  have hx' : (x : Pi1 A K) ∈ (D.P s).inertia (Pi1 A K) := hx
  have h1 := conj_mem_inertia_smul A K R0 ψ⁻¹ hx'
  rw [inv_inv] at h1
  exact inv_conj_mem_inertia A K R0 (hτ s) h1

/-- A chosen boundary permutation for `ψ`. -/
def BdryData.frobTau (ψ : Pi1 A K) : S → S := (D.exists_compat ψ).choose

/-- The chosen correcting elements `h_s ∈ π₁^geo` for `ψ`. -/
def BdryData.frobH (ψ : Pi1 A K) : S → pi1geo A K q := (D.exists_compat ψ).choose_spec.choose

theorem BdryData.frob_compat (ψ : Pi1 A K) :
    BdryCompat (pi1geo A K q) D.inertia ψ (D.frobTau ψ) (D.frobH ψ) :=
  (D.exists_compat ψ).choose_spec.choose_spec

end Boundary

/-! ## Curve cohomology and the geometric Frobenius -/

section Cohomology

variable {A K} {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)] {S : Type}
  {Λ : Type} [CommRing Λ] {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)

/-- `H⁰(U ⊗ 𝔽̄_q, M)`. -/
abbrev curveH0 : Submodule Λ M := H0 ρ (pi1geo A K q)

/-- `H¹_c(U ⊗ 𝔽̄_q, M)`: the cone over the boundary inertia groups of `D`. -/
abbrev curveH1c (D : BdryData A K q R0 S) : Type := H1c ρ (pi1geo A K q) D.inertia

/-- `H²_c(U ⊗ 𝔽̄_q, M) := M_{π₁^geo}` (review R2; the twist `(-1)` is carried by the Frobenius). -/
abbrev curveH2c : Type := H2c ρ (pi1geo A K q)

/-- GEOMETRIC Frobenius on `H⁰`: `F = T_{φ⁻¹}` for an arithmetic Frobenius lift `φ`. -/
def geomFrobH0 (φ : Pi1 A K) : curveH0 q ρ →ₗ[Λ] curveH0 q ρ := frobH0 ρ (pi1geo A K q) φ⁻¹

/-- GEOMETRIC Frobenius on `H¹`. -/
def geomFrobH1 (φ : Pi1 A K) : curveH1 q ρ →ₗ[Λ] curveH1 q ρ := frobH1 ρ (pi1geo A K q) φ⁻¹

/-- GEOMETRIC Frobenius on `⊕_s M^{I_s}`. -/
def geomFrobBdry (D : BdryData A K q R0 S) (φ : Pi1 A K) :
    bdryInv ρ (pi1geo A K q) D.inertia →ₗ[Λ] bdryInv ρ (pi1geo A K q) D.inertia :=
  frobBdry ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹) (D.frob_compat φ⁻¹)

/-- GEOMETRIC Frobenius on `H¹_c`. -/
def geomFrobH1c (D : BdryData A K q R0 S) (φ : Pi1 A K) : curveH1c q ρ D →ₗ[Λ] curveH1c q ρ D :=
  frobH1c ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹) (D.frob_compat φ⁻¹)

/-- GEOMETRIC Frobenius on `H²_c = M_{π₁^geo}(-1)`: `q • ρ(φ⁻¹)`. -/
def geomFrobH2c (φ : Pi1 A K) : curveH2c q ρ →ₗ[Λ] curveH2c q ρ := frobH2c ρ (pi1geo A K q) φ⁻¹ (q : Λ)

/-! ## Lisse coefficients -/

end Cohomology

/-! ## Sanity checks for the constant sheaf -/

section Sanity

variable {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)] {S : Type} (Λ : Type) [CommRing Λ]

end Sanity

end Geo

/-! ## The boundary at infinity (S3-Places) -/

section Infinity

variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] (A : Type) [CommRing A] [Algebra A (RatFunc Fq)]

end Infinity

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_H1 =====
section

/-!
# S4-Kummer, part 2: `H¹(Γ, ZMod N)` is the Kummer group, with the Frobenius action

Setting of part 1 (`Def_RP_Kummer_Gal`): fields `K ⊆ E` with `E/K` integral, `Γ ≤ Gal(E/K)`, a primitive `N`-th root
of unity `ζ` fixed by `Γ`. Cohomology is the locally constant cohomology of `Def_RP_CurveCoh_Pair` with TRIVIAL
coefficients `ZMod N` (`triv K E N`).

* `B1_triv_eq_bot`, `H1mk_triv_injective`: with trivial coefficients there are no coboundaries;
* `kclass hζ hζΓ hα : H1 (triv K E N) Γ`: the class of the Kummer character of a radical `α`;
* `kummerEquiv`: **Kummer theory**, `rad Γ N / (Γ-fixed units) ≃* H¹(Γ, ZMod N)`;
* `frobH1_kclass`: for `ψ` with `ψ ζ = ζ ^ w'` (and `Γ` normal), `T_ψ [kchar α] = w • [kchar (ψ α)]` when `w w' = 1`;
* `geomFrob_kclass`: for an ARITHMETIC Frobenius `φ ζ = ζ ^ q`, the GEOMETRIC Frobenius `F = T_{φ⁻¹}` acts by
  `F [kchar α] = q • [kchar (φ⁻¹ α)]`: on `H¹(Γ, ZMod N) = (Kummer group) ⊗ μ_N^{⊗ -1}` the twist is the scalar `q`
  (review R4: eigenvalues `q / ω_i`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh

noncomputable section

section Triv

variable (K E : Type) [Field K] [Field E] [Algebra K E] (N : ℕ)

variable {K E} (Γ : Subgroup (E ≃ₐ[K] E))

end Triv

section Classes

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
  {Γ : Subgroup (E ≃ₐ[K] E)} {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)

include hζ hζΓ

end Classes

section Frob

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
  {Γ : Subgroup (E ≃ₐ[K] E)} [hΓ : Γ.Normal] {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)

theorem conj_mem_of_normal (ψ : E ≃ₐ[K] E) : ∀ σ ∈ Γ, ψ⁻¹ * σ * ψ ∈ Γ := fun σ hσ => by
  simpa using hΓ.conj_mem σ hσ ψ⁻¹

/-- Radicals are stable under any automorphism normalising `Γ`. -/
theorem rad_map (ψ : E ≃ₐ[K] E) {α : Eˣ} (hα : α ∈ rad Γ N) : Units.map (ψ : E →* E) α ∈ rad Γ N := by
  intro σ hσ
  have h := hα _ (conj_mem_of_normal ψ σ hσ)
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← map_pow]
  calc σ (ψ ((α : E) ^ N)) = ψ ((ψ⁻¹ * σ * ψ) ((α : E) ^ N)) := by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    _ = ψ ((α : E) ^ N) := by rw [h]

theorem frobH1_mk (ψ : E ≃ₐ[K] E) (c : Z1 (triv K E N) Γ) :
    frobH1 (triv K E N) Γ ψ (H1.mk (triv K E N) Γ c) =
      H1.mk (triv K E N) Γ ⟨twist (triv K E N) Γ ψ c, twist_mem_Z1 _ Γ ψ c.2⟩ :=
  rfl

/-- Frobenius on Kummer classes: if `ψ ζ = ζ ^ w'` and `w w' = 1` then `T_ψ [kchar α] = w • [kchar (ψ α)]`. -/
theorem frobH1_kclass (ψ : E ≃ₐ[K] E) {w w' : ZMod N} (hψ : ψ ζ = epow ζ w') (hww : w * w' = 1)
    {α : Eˣ} (hα : α ∈ rad Γ N) :
    frobH1 (triv K E N) Γ ψ (kclass hζ hζΓ hα) = w • kclass hζ hζΓ (rad_map ψ hα) := by
  rw [kclass, kclass, frobH1_mk, ← map_smul]
  congr 1
  apply Subtype.ext
  funext σ
  show (triv K E N) ψ (kchar hζ α (conjΓ Γ ψ σ)) = w * kchar hζ (Units.map (ψ : E →* E) α) σ
  rw [Representation.trivial_apply, kchar_conj hζ ψ (conj_mem_of_normal ψ) hψ hα (rad_map ψ hα) σ, ← mul_assoc,
    hww, one_mul]
  rfl

include hζ in
/-- If `φ ζ = ζ ^ w` and `w w' = 1` then `φ⁻¹ ζ = ζ ^ w'`. -/
theorem inv_apply_zeta (φ : E ≃ₐ[K] E) {w w' : ZMod N} (hφ : φ ζ = epow ζ w) (hww : w * w' = 1) :
    φ⁻¹ ζ = epow ζ w' := by
  have h1 : φ (epow ζ w') = ζ := by
    calc φ (epow ζ w') = (φ ζ) ^ w'.val := map_pow φ ζ w'.val
      _ = epow ζ (w * w') := by rw [hφ, epow_pow hζ]
      _ = ζ := by rw [hww, epow, ZMod.val_one_eq_one_mod, pow_mod_N hζ, pow_one]
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
  exact h1.symm

/-- **Geometric Frobenius on Kummer classes** (review R4). For an arithmetic Frobenius `φ` (`φ ζ = ζ ^ q`, `q`
invertible mod `N`), the geometric Frobenius `F = T_{φ⁻¹}` acts by `F [kchar α] = q • [kchar (φ⁻¹ α)]`. -/
theorem geomFrob_kclass (φ : E ≃ₐ[K] E) {q : ℕ} {q' : ZMod N} (hφ : φ ζ = epow ζ (q : ZMod N))
    (hq : (q : ZMod N) * q' = 1) {α : Eˣ} (hα : α ∈ rad Γ N) :
    frobH1 (triv K E N) Γ φ⁻¹ (kclass hζ hζΓ hα) = (q : ZMod N) • kclass hζ hζΓ (rad_map φ⁻¹ hα) :=
  frobH1_kclass hζ hζΓ φ⁻¹ (inv_apply_zeta hζ φ hφ hq) hq hα

end Frob

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Const =====
section

/-!
# S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory

`K` of characteristic `p`, `q = p ^ e` (`e > 0`), `A` any ring with `K = Frac`-like algebra `A → K` (no hypothesis on
`A` is needed: constant extensions are unramified over every `A`).

* `constLevel K p k = K(roots of X^(p^k) - X)` is a finite Galois subextension of `K̄/K` with trivial inertia at every
  prime of the integral closure of `A` (`constLevel_mem_unramSet`): an inertia element `σ` moves a root `s` to a root,
  `σ s - s` is again a root (Frobenius is additive), hence `0` or a unit, and it lies in the prime;
* `mem_maxUnram_of_isConst`: every constant of `K̄` lies in `K_U = maxUnram A K`;
* `exists_zeta`: for `N` prime to `p` there is a primitive `N`-th root of unity `ζ ∈ K_U` which is a constant;
  `zeta_fixed`: `π₁^geo` fixes it; `frobLift_zeta`: an arithmetic Frobenius lift sends `ζ ↦ ζ ^ q`;
* `curveKummerEquiv`: `H¹(U ⊗ 𝔽̄, ZMod N) ≃ rad / (π₁^geo-fixed units)`, and `geomFrobH1_kclass`:
  `F [kchar α] = q • [kchar (φ⁻¹ α)]` for the GEOMETRIC Frobenius of `Def_RP_CurveCoh_Curve` (review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh Polynomial

noncomputable section

section Level

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

variable {K p}

end Level

section Zeta

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  {e : ℕ} (he : 0 < e) (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

variable {A K p N}

end Zeta

section Curve

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q N : ℕ} [NeZero N] {ζ : maxUnram A K}
  (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ pi1geo A K q, σ ζ = ζ)

/-- **Geometric Frobenius on Kummer classes over the curve** (review R4): for an arithmetic Frobenius lift `φ`,
`F [kchar α] = q • [kchar (φ⁻¹ α)]`. -/
theorem geomFrobH1_kclass {φ : Pi1 A K} (hφ : φ ζ = epow ζ (q : ZMod N)) {q' : ZMod N}
    (hq : (q : ZMod N) * q' = 1) {α : (maxUnram A K)ˣ} (hα : α ∈ rad (pi1geo A K q) N) :
    geomFrobH1 q (triv K (maxUnram A K) N) φ (kclass hζ hζΓ hα) =
      (q : ZMod N) • kclass hζ hζΓ (rad_map φ⁻¹ hα) :=
  geomFrob_kclass hζ hζΓ φ hφ hq hα

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_Res =====
section

/-!
# S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants

For a nonzero prime `Q` of the pro-chart `B = proChart A K R0` with finite residue ring `R0 ⧸ (Q ∩ R0)` of order a
power of `q = p^e`, and assuming `K_U` contains primitive `(q^a - 1)`-th roots of unity for every `a ≥ 1`:

* `constSub`: the constants of `K_U` that lie in `B` form a subring;
* `const_eq_of_sub_mem`: two constants congruent mod a proper ideal are equal;
* `exists_const_sub_mem`: every element of `B` is congruent mod `Q` to a constant;
* `resEquiv`: so `constSub ≃+* B ⧸ Q`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

section Field

variable {L : Type} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p] (e : ℕ)

end Field

section Res

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  (p e : ℕ) [hp : Fact p.Prime] [CharP K p]

variable {A K R0 p e}

variable (A K R0 p e)

theorem resEquiv_apply (he : 0 < e) (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    (Q : Ideal (proChart A K R0)) [Q.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) (c : constSub A K R0 p e) :
    resEquiv A K R0 p e he hζ Q hcard c = Ideal.Quotient.mk Q (c : proChart A K R0) := rfl

end Res

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Trans =====
section

/-!
# S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues

* `isInvariant_proChart`: `(proChart A K R0)^{π₁(U)} = R0` (`R0` integrally closed with fraction field `K`).
* `exists_smul_of_under_eq'`: `π₁(U)` is transitive on the primes of the pro-chart over a prime of `R0` (profinite).
* `exists_stab_of_algEquiv`: the stabilizer of `Q` surjects onto `Aut((B ⧸ Q)/(R0 ⧸ Q ∩ R0))`.
* `exists_pi1geo_smul`: two primes `Q, Q'` (finite residue rings of `q`-power order) on which every `r ∈ R0` has the
  same constant residue are conjugate under `π₁^geo`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

section Trans

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

theorem isInvariant_proChart [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K] :
    Algebra.IsInvariant R0 (proChart A K R0) (Pi1 A K) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Pi1 A K, σ (b : maxUnram A K) = b := fun σ => congrArg Subtype.val (hb σ)
  obtain ⟨k, hk⟩ := (InfiniteGalois.mem_bot_iff_fixed (k := K) (K := maxUnram A K) (b : maxUnram A K)).2 hfix
  have hint : IsIntegral R0 k := by
    have hb' : IsIntegral R0 (b : maxUnram A K) := b.2
    rw [← hk] at hb'
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R0 K (maxUnram A K))
      (algebraMap K (maxUnram A K)).injective).1 hb'
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨a, Subtype.ext ?_⟩
  show algebraMap R0 (maxUnram A K) a = b
  rw [IsScalarTower.algebraMap_apply R0 K (maxUnram A K), ha]
  exact hk

theorem exists_smul_of_under_eq' [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
    (P Q : Ideal (proChart A K R0)) [P.IsPrime] [Q.IsPrime] (h : P.under R0 = Q.under R0) :
    ∃ g : Pi1 A K, Q = g • P := by
  letI : TopologicalSpace (proChart A K R0) := ⊥
  haveI : DiscreteTopology (proChart A K R0) := ⟨rfl⟩
  haveI : ContinuousSMul (Pi1 A K) (proChart A K R0) := by
    refine (continuousSMul_iff_stabilizer_isOpen).2 fun x => ?_
    refine Subgroup.isOpen_mono (H₁ := fixElt A K (x : maxUnram A K)) (fun σ hσ => ?_) (fixElt_isOpen A K _)
    exact Subtype.ext hσ
  haveI := isInvariant_proChart (A := A) (K := K) (R0 := R0)
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite P Q h

theorem exists_stab_of_algEquiv [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
    (Q : Ideal (proChart A K R0)) [Q.IsPrime]
    (σ' : (proChart A K R0 ⧸ Q) ≃ₐ[R0 ⧸ Q.under R0] (proChart A K R0 ⧸ Q)) :
    ∃ δ : Pi1 A K, δ • Q = Q ∧ ∀ b, Ideal.Quotient.mk Q (δ • b) = σ' (Ideal.Quotient.mk Q b) := by
  letI : TopologicalSpace (proChart A K R0) := ⊥
  haveI : DiscreteTopology (proChart A K R0) := ⟨rfl⟩
  haveI : ContinuousSMul (Pi1 A K) (proChart A K R0) := by
    refine (continuousSMul_iff_stabilizer_isOpen).2 fun x => ?_
    refine Subgroup.isOpen_mono (H₁ := fixElt A K (x : maxUnram A K)) (fun σ hσ => ?_) (fixElt_isOpen A K _)
    exact Subtype.ext hσ
  haveI := isInvariant_proChart (A := A) (K := K) (R0 := R0)
  obtain ⟨⟨δ, hδ⟩, hδσ⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Pi1 A K) (Q.under R0) Q σ'
  refine ⟨δ, hδ, fun b => ?_⟩
  rw [← hδσ]
  rfl

variable {p e : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 200000 in
/-- **Geometric transitivity**: boundary-type primes with the same constant residues on `R0` are `π₁^geo`-conjugate. -/
theorem exists_pi1geo_smul [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K] (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    {Q Q' : Ideal (proChart A K R0)} [Q.IsPrime] [Q'.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
    (hres : ∀ r : R0, ∀ c ∈ constSub A K R0 p e,
      algebraMap R0 (proChart A K R0) r - c ∈ Q → algebraMap R0 (proChart A K R0) r - c ∈ Q') :
    ∃ g ∈ pi1geo A K (p ^ e), Q' = g • Q := by
  have hres' : ∀ r : R0, ∀ c ∈ constSub A K R0 p e,
      algebraMap R0 (proChart A K R0) r - c ∈ Q' → algebraMap R0 (proChart A K R0) r - c ∈ Q := by
    intro r c hc h'
    obtain ⟨c0, hc0, h0⟩ := exists_const_sub_mem he hζ hcard (algebraMap R0 (proChart A K R0) r)
    have h0' := hres r c0 hc0 h0
    have hcc : c0 = c := const_eq_of_sub_mem he (Ideal.IsPrime.ne_top ‹_›) hc0 hc (by
      have h2 := Q'.sub_mem h' h0'
      rwa [sub_sub_sub_cancel_left] at h2)
    rw [← hcc]
    exact h0
  have hunder : Q.under R0 = Q'.under R0 := by
    ext r
    simp only [Ideal.under, Ideal.mem_comap]
    constructor
    · intro h
      simpa using hres r 0 (zero_mem _) (by simpa using h)
    · intro h
      simpa using hres' r 0 (zero_mem _) (by simpa using h)
  obtain ⟨σ, hσ⟩ := exists_smul_of_under_eq' Q Q' hunder
  have hσc : ∀ r : R0, ∀ c ∈ constSub A K R0 p e, algebraMap R0 (proChart A K R0) r - c ∈ Q →
      algebraMap R0 (proChart A K R0) r - σ • c ∈ Q := by
    intro r c hc h
    have h1 : algebraMap R0 (proChart A K R0) r - σ • c ∈ Q' := by
      rw [hσ]
      have h2 := Ideal.smul_mem_pointwise_smul σ _ Q h
      rwa [smul_sub, smul_algebraMap] at h2
    exact hres' r _ ((constSmul R0 p e σ ⟨c, hc⟩).2) h1
  let e0 := resEquiv A K R0 p e he hζ Q hcard
  let eR : (proChart A K R0 ⧸ Q) ≃+* (proChart A K R0 ⧸ Q) := e0.symm.trans ((constSmul R0 p e σ).trans e0)
  have heR : ∀ c : constSub A K R0 p e, eR (Ideal.Quotient.mk Q (c : proChart A K R0)) =
      Ideal.Quotient.mk Q (σ • (c : proChart A K R0)) := by
    intro c
    show e0 (constSmul R0 p e σ (e0.symm (e0 c))) = _
    rw [e0.symm_apply_apply]
    rfl
  have hcomm : ∀ y : R0 ⧸ Q.under R0, eR (algebraMap _ _ y) = algebraMap _ _ y := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc, hrc⟩ := exists_const_sub_mem he hζ hcard (algebraMap R0 (proChart A K R0) r)
    change eR (Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r)) =
      Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r)
    rw [Ideal.Quotient.eq.2 hrc, heR ⟨c, hc⟩]
    exact (Ideal.Quotient.eq.2 ((Ideal.Quotient.eq.1 (Ideal.Quotient.eq.2 (hσc r c hc hrc))))).symm.trans
      (Ideal.Quotient.eq.2 hrc)
  obtain ⟨δ, hδQ, hδ⟩ := exists_stab_of_algEquiv Q (AlgEquiv.ofRingEquiv (f := eR) hcomm)
  have hδc : ∀ c ∈ constSub A K R0 p e, δ • c = σ • c := by
    intro c hc
    have h1 : Ideal.Quotient.mk Q (δ • c) = Ideal.Quotient.mk Q (σ • c) := by
      rw [hδ]
      exact heR ⟨c, hc⟩
    exact const_eq_of_sub_mem he (Ideal.IsPrime.ne_top ‹_›) ((mem_constSub.1 hc).map δ)
      ((mem_constSub.1 hc).map σ) (Ideal.Quotient.eq.1 h1)
  refine ⟨σ * δ⁻¹, ?_, ?_⟩
  · rw [mem_pi1geo]
    intro y hy
    have h := hδc (mkConst he (σ⁻¹ • y) (hy.map σ⁻¹)) (mkConst_mem he _ _)
    have hv : δ • (σ⁻¹ • y) = y := (congrArg Subtype.val h).trans (smul_inv_smul σ y)
    show (σ * δ⁻¹) • y = y
    rw [mul_smul, inv_smul_eq_iff.2 hv.symm, smul_inv_smul]
  · exact hσ.trans (mul_inv_smul_of_smul_eq hδQ).symm

end Trans

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Bres =====
section

/-!
# S4-CP4a, part e3a: the constant residue map of a boundary prime

* `exists_frob_pow_of_finite`: two embeddings of a finite field `k ⊇ k0` into a field that agree on `k0`
  differ by a power of the `#k0`-Frobenius.
* `bres Q hQ : R0 →+* K_U`: `r ↦` the constant congruent to `r` modulo the boundary prime `Q` (via `resEquiv`),
  with `bres_spec`, `bres_eq`, `bres_isConst`, `bres_ker`, `bres_const`.
* Transport: `bres_smul` (`bres (σ Q) = σ ∘ bres Q`), `bres_geo` (`π₁^geo` does not change it), `bres_frob_pow`
  (`bres (φ^j Q) = Frob_q^j ∘ bres Q` for a Frobenius lift `φ`).
* `bres_conj`: equal residue maps force `π₁^geo`-conjugate primes (`exists_pi1geo_smul`).
* `exists_bres_eq`: every `k0`-compatible `χ : R0 →+* K_U` with nonzero kernel is `bres Q` of a boundary prime
  (lying over, `exists_frob_pow_of_finite`, then `φ^j`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

open scoped Pointwise

noncomputable section

section FinFrob

end FinFrob

section Bres

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
  {p e : ℕ} [hp : Fact p.Prime] [CharP K p] (he : 0 < e)
  (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
  (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
    Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)

/-- The constant residue map at a boundary prime `Q`: `r ↦` the constant congruent to `r` mod `Q`. -/
def bres (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) : R0 →+* maxUnram A K :=
  haveI := hQ.1
  haveI := (hgood Q hQ).1
  ((integralClosure R0 (maxUnram A K)).val.toRingHom.comp (constSub A K R0 p e).subtype).comp
    ((resEquiv A K R0 p e he hζ Q (hgood Q hQ).2).symm.toRingHom.comp
      ((Ideal.Quotient.mk Q).comp (algebraMap R0 (proChart A K R0))))

theorem bres_spec (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    ∃ c ∈ constSub A K R0 p e, ((c : proChart A K R0) : maxUnram A K) = bres he hζ hgood Q hQ r ∧
      algebraMap R0 (proChart A K R0) r - c ∈ Q := by
  haveI := hQ.1
  haveI := (hgood Q hQ).1
  refine ⟨((resEquiv A K R0 p e he hζ Q (hgood Q hQ).2).symm
    (Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r)) : proChart A K R0), Subtype.prop _, rfl, ?_⟩
  have h := (resEquiv A K R0 p e he hζ Q (hgood Q hQ).2).apply_symm_apply
    (Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r))
  rw [resEquiv_apply] at h
  exact Ideal.Quotient.eq.1 h.symm

theorem bres_eq (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) {r : R0} {c : proChart A K R0}
    (hc : c ∈ constSub A K R0 p e) (h : algebraMap R0 (proChart A K R0) r - c ∈ Q) :
    bres he hζ hgood Q hQ r = (c : maxUnram A K) := by
  obtain ⟨c0, hc0, h0, h0Q⟩ := bres_spec he hζ hgood Q hQ r
  rw [← h0]
  have h1 : c0 - c ∈ Q := by
    have h2 := Q.sub_mem h h0Q
    rwa [sub_sub_sub_cancel_left] at h2
  rw [const_eq_of_sub_mem he hQ.1.ne_top hc0 hc h1]

theorem bres_congr {Q Q' : Ideal (proChart A K R0)} (hQQ : Q = Q') (hQ : IsBdryPrime A K R0 Q)
    (hQ' : IsBdryPrime A K R0 Q') : bres he hζ hgood Q hQ = bres he hζ hgood Q' hQ' := by
  subst hQQ
  rfl

theorem bres_isConst (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    IsConst (p ^ e) (bres he hζ hgood Q hQ r) := by
  obtain ⟨c, hc, hcr, -⟩ := bres_spec he hζ hgood Q hQ r
  rw [← hcr]
  exact hc

theorem bres_ker (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    bres he hζ hgood Q hQ r = 0 ↔ r ∈ Q.under R0 := by
  constructor
  · intro h
    obtain ⟨c, -, hcr, hcQ⟩ := bres_spec he hζ hgood Q hQ r
    have hc0 : c = 0 := Subtype.ext (hcr.trans h)
    rw [hc0, sub_zero] at hcQ
    exact hcQ
  · intro h
    have h2 := bres_eq he hζ hgood Q hQ (zero_mem (constSub A K R0 p e)) (r := r) (by rw [sub_zero]; exact h)
    rw [h2]
    rfl

theorem bres_const (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) {r : R0}
    (hr : IsConst (p ^ e) (algebraMap R0 (maxUnram A K) r)) :
    bres he hζ hgood Q hQ r = algebraMap R0 (maxUnram A K) r := by
  have h2 := bres_eq he hζ hgood Q hQ (c := algebraMap R0 (proChart A K R0) r) hr (by rw [sub_self]; exact zero_mem _)
  rw [h2]
  rfl

theorem bres_smul (σ : Pi1 A K) (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    bres he hζ hgood (σ • Q) (isBdryPrime_smul A K R0 σ hQ) r = σ (bres he hζ hgood Q hQ r) := by
  obtain ⟨c, hc, hcr, hcQ⟩ := bres_spec he hζ hgood Q hQ r
  rw [← hcr]
  have h2 := Ideal.smul_mem_pointwise_smul σ _ Q hcQ
  rw [smul_sub, smul_algebraMap] at h2
  exact bres_eq he hζ hgood (σ • Q) _ ((mem_constSub.1 hc).map σ) h2

theorem bres_geo {g : Pi1 A K} (hg : g ∈ pi1geo A K (p ^ e)) (Q : Ideal (proChart A K R0))
    (hQ : IsBdryPrime A K R0 Q) :
    bres he hζ hgood (g • Q) (isBdryPrime_smul A K R0 g hQ) = bres he hζ hgood Q hQ :=
  RingHom.ext fun r => (bres_smul he hζ hgood g Q hQ r).trans
    ((mem_pi1geo A K _ g).1 hg _ (bres_isConst he hζ hgood Q hQ r))

theorem bres_frob {φ : Pi1 A K} (hφ : IsFrobLift A K (p ^ e) φ) (Q : Ideal (proChart A K R0))
    (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    bres he hζ hgood (φ • Q) (isBdryPrime_smul A K R0 φ hQ) r = bres he hζ hgood Q hQ r ^ (p ^ e) :=
  (bres_smul he hζ hgood φ Q hQ r).trans (hφ _ (bres_isConst he hζ hgood Q hQ r))

set_option synthInstance.maxHeartbeats 200000 in
theorem bres_frob_pow {φ : Pi1 A K} (hφ : IsFrobLift A K (p ^ e) φ) (Q : Ideal (proChart A K R0))
    (hQ : IsBdryPrime A K R0 Q) (j : ℕ) (r : R0) :
    bres he hζ hgood (φ ^ j • Q) (isBdryPrime_smul A K R0 _ hQ) r = bres he hζ hgood Q hQ r ^ ((p ^ e) ^ j) := by
  induction j with
  | zero =>
    rw [bres_congr he hζ hgood ((congrArg (fun g : Pi1 A K => g • Q) (pow_zero φ)).trans (one_smul (Pi1 A K) Q)) _ hQ, pow_zero, pow_one]
  | succ j ih =>
    rw [bres_congr he hζ hgood ((congrArg (fun g : Pi1 A K => g • Q) (pow_succ' φ j)).trans (mul_smul φ (φ ^ j) Q)) _
      (isBdryPrime_smul A K R0 φ (isBdryPrime_smul A K R0 _ hQ)),
      bres_frob he hζ hgood hφ (φ ^ j • Q) (isBdryPrime_smul A K R0 _ hQ), ih, ← pow_mul,
      pow_succ]

set_option synthInstance.maxHeartbeats 200000 in
theorem bres_conj (Q Q' : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (hQ' : IsBdryPrime A K R0 Q')
    (h : bres he hζ hgood Q hQ = bres he hζ hgood Q' hQ') : ∃ g ∈ pi1geo A K (p ^ e), Q' = g • Q := by
  haveI := hQ.1
  haveI := hQ'.1
  haveI := (hgood Q hQ).1
  refine exists_pi1geo_smul he hζ (hgood Q hQ).2 fun r c hc hrc => ?_
  obtain ⟨c', -, hc'r, hc'Q⟩ := bres_spec he hζ hgood Q' hQ' r
  have hcc : c' = c := Subtype.ext (hc'r.trans ((RingHom.congr_fun h r).symm.trans
    (bres_eq he hζ hgood Q hQ hc hrc)))
  rw [← hcc]
  exact hc'Q

set_option synthInstance.maxHeartbeats 200000 in
/-- **Surjectivity**: a `k0`-compatible `χ : R0 →+* K_U` with nonzero kernel is the residue map of a boundary
prime. -/
theorem exists_bres_eq {φ : Pi1 A K} (hφ : IsFrobLift A K (p ^ e) φ) {k0 : Type} [Field k0] [Fintype k0]
    [Algebra k0 R0] (hq0 : Fintype.card k0 = p ^ e) (χ : R0 →+* maxUnram A K)
    (hχ : ∀ a : k0, χ (algebraMap k0 R0 a) = algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a))
    (hker : RingHom.ker χ ≠ ⊥) :
    ∃ (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q), bres he hζ hgood Q hQ = χ := by
  have hinj := algebraMap_proChart_injective (A := A) (K := K) (R0 := R0)
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨Q, -, hQp, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ)
    (⊥ : Ideal (proChart A K R0)) (fun x hx => by
      have h0 : algebraMap R0 (proChart A K R0) x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
      rw [hinj (h0.trans (map_zero _).symm)]
      exact zero_mem _)
  have hQ : IsBdryPrime A K R0 Q := ⟨hQp, fun h0 => hker (by
    rw [← hQP, h0]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩)⟩
  haveI := hQp
  haveI := (hgood Q hQ).1
  have hunder : Q.under R0 = RingHom.ker χ := hQP
  haveI : (Q.under R0).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R0 ⧸ Q.under R0))
  letI := Ideal.Quotient.field (Q.under R0)
  have hconst : ∀ a : k0, IsConst (p ^ e) (algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a)) := fun a =>
    ⟨1, one_pos, by rw [pow_one, ← map_pow, ← map_pow, ← hq0, FiniteField.pow_card]⟩
  have H1 : ∀ a ∈ Q.under R0, bres he hζ hgood Q hQ a = 0 := fun a ha => (bres_ker he hζ hgood Q hQ a).2 ha
  have H2 : ∀ a ∈ Q.under R0, χ a = 0 := fun a ha => (RingHom.mem_ker).1 (hunder ▸ ha)
  have hfg : ∀ a : k0, Ideal.Quotient.lift (Q.under R0) (bres he hζ hgood Q hQ) H1
      (algebraMap k0 (R0 ⧸ Q.under R0) a) = Ideal.Quotient.lift (Q.under R0) χ H2 (algebraMap k0 (R0 ⧸ Q.under R0) a) := by
    intro a
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, hχ,
      bres_const he hζ hgood Q hQ (hconst a)]
  obtain ⟨j, hj⟩ := exists_frob_pow_of_finite _ _ hfg
  refine ⟨φ ^ j • Q, isBdryPrime_smul A K R0 _ hQ, RingHom.ext fun r => ?_⟩
  rw [bres_frob_pow he hζ hgood hφ Q hQ j r]
  have h3 := hj (Ideal.Quotient.mk _ r)
  rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, hq0] at h3
  exact h3.symm

end Bres

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Bdry =====
section

/-!
# S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)

* `trueTau D ψ`, `trueH D ψ`, `trueTau_spec` (`ψ⁻¹ • P s = h_s • P (τ s)`), `trueCompat`: the boundary permutation of
  `ψ` WITH its defining property (`BdryData.frobTau` is a bare choice without it).
* `sres D s := bres (P s)`: injective (`sres_injective`); `sres (τ s) = (sres s)^q` for `ψ = φ⁻¹` (`sres_trueTau`).
* `iterate_trueTau_eq_iff`: `τ^m s = s ↔ sres s` has values in `𝔽_{q^m}`.
* `levelField k0 M m` (`x^{q^m} = x`), `card_levelField`, `finrank_levelField` (`= m`).
* `card_fix_eq`: `#{s | τ^m s = s} = #Hom_{k0}(R0, 𝔽_{q^m})`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

open scoped Pointwise

noncomputable section

section True

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ}
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {S : Type} (D : BdryData A K q R0 S)

end True

section Level

variable (k0 M : Type) [Field k0] [Fintype k0] [Field M] [Algebra k0 M]

variable {k0 M}

theorem finrank_levelField {m : ℕ} (hm : 0 < m) {ζ : M} (hζ : IsPrimitiveRoot ζ (Fintype.card k0 ^ m - 1)) :
    Module.finrank k0 (levelField k0 M m) = m := by
  have hc := card_levelField hm hζ
  have : Finite (levelField k0 M m) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  let _ : Fintype (levelField k0 M m) := Fintype.ofFinite _
  have h2 := Module.card_eq_pow_finrank (K := k0) (V := levelField k0 M m)
  rw [← Nat.card_eq_fintype_card, hc] at h2
  exact (Nat.pow_right_injective (Fintype.one_lt_card (α := k0)) h2).symm

/-- A `k0`-compatible ring hom with values in `𝔽_{q^m}`, as a `k0`-algebra hom. -/
def toLevelHom {R0 : Type} [CommRing R0] [Algebra k0 R0] {m : ℕ} (χ : R0 →+* M)
    (hmem : ∀ r, χ r ∈ levelField k0 M m) (hχ : ∀ a, χ (algebraMap k0 R0 a) = algebraMap k0 M a) :
    R0 →ₐ[k0] levelField k0 M m :=
  { χ.codRestrict (levelField k0 M m) hmem with commutes' := fun a => Subtype.ext (hχ a) }

end Level

section Sres

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
  {p e : ℕ} [Fact p.Prime] [CharP K p] (he : 0 < e)
  (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
  (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
    Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
  {q : ℕ} {S : Type} (D : BdryData A K q R0 S) (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q)

/-- The residue map at the boundary point `s`. -/
def sres (s : S) : R0 →+* maxUnram A K :=
  bres he hζ hgood (D.P s) ((hDB _).1 (D.mem s))

set_option synthInstance.maxHeartbeats 200000 in
theorem sres_injective (hq : q = p ^ e) : Function.Injective (sres he hζ hgood D hDB) := by
  subst hq
  intro s t hst
  obtain ⟨g, hg, hgt⟩ := bres_conj he hζ hgood _ _ ((hDB _).1 (D.mem s)) ((hDB _).1 (D.mem t)) hst
  exact D.disj s t g hg hgt

set_option synthInstance.maxHeartbeats 200000 in
/-- `sres (τ s) = Frob_q ∘ sres s` for the true boundary permutation of `φ⁻¹`. -/
theorem sres_trueTau (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) (s : S) (r : R0) :
    sres he hζ hgood D hDB (trueTau D φ⁻¹ s) r = sres he hζ hgood D hDB s r ^ q := by
  subst hq
  have hs := (hDB _).1 (D.mem s)
  have ht := (hDB _).1 (D.mem (trueTau D φ⁻¹ s))
  have h1 := bres_geo he hζ hgood (trueH D φ⁻¹ s).2 (D.P (trueTau D φ⁻¹ s)) ht
  have h2 : ((trueH D φ⁻¹ s : pi1geo A K (p ^ e)) : Pi1 A K) • D.P (trueTau D φ⁻¹ s) = φ • D.P s :=
    (trueTau_spec D φ⁻¹ s).symm.trans (congrArg (fun g : Pi1 A K => g • D.P s) (inv_inv φ))
  have h3 := bres_congr he hζ hgood h2 (isBdryPrime_smul A K R0 _ ht) (isBdryPrime_smul A K R0 φ hs)
  show bres he hζ hgood (D.P (trueTau D φ⁻¹ s)) ht r = bres he hζ hgood (D.P s) hs r ^ (p ^ e)
  rw [← h1, h3, bres_frob he hζ hgood hφ (D.P s) hs]

theorem sres_iterate (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) (m : ℕ) (s : S) (r : R0) :
    sres he hζ hgood D hDB ((trueTau D φ⁻¹)^[m] s) r = sres he hζ hgood D hDB s r ^ (q ^ m) := by
  induction m with
  | zero => rw [Function.iterate_zero_apply, pow_zero, pow_one]
  | succ m ih =>
    rw [Function.iterate_succ_apply', sres_trueTau he hζ hgood D hDB hq hφ, ih, ← pow_mul, pow_succ]

/-- `τ^m s = s` iff the residue map at `s` has values in `𝔽_{q^m}`. -/
theorem iterate_trueTau_eq_iff (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) (m : ℕ) (s : S) :
    (trueTau D φ⁻¹)^[m] s = s ↔
      ∀ r, sres he hζ hgood D hDB s r ^ (q ^ m) = sres he hζ hgood D hDB s r := by
  constructor
  · intro h r
    rw [← sres_iterate he hζ hgood D hDB hq hφ m s r, h]
  · intro h
    apply sres_injective he hζ hgood D hDB hq
    ext r
    rw [sres_iterate he hζ hgood D hDB hq hφ m s r, h r]

include he hζ hgood hDB in
set_option synthInstance.maxHeartbeats 200000 in
/-- **`#{s | τ^m s = s} = #Hom_{k0}(R0, 𝔽_{q^m})`** for the true boundary permutation of `φ⁻¹`. -/
theorem card_fix_eq (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) {k0 : Type} [Field k0]
    [Fintype k0] [Algebra k0 R0] [Algebra k0 (maxUnram A K)] (hq0 : Fintype.card k0 = q)
    (hcomp : ∀ a : k0, algebraMap k0 (maxUnram A K) a = algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a))
    (r0 : R0) (hr0 : ∀ N : ℕ, 2 ≤ N → r0 ^ N ≠ r0) [Fintype S] [DecidableEq S] (m : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun s => (trueTau D φ⁻¹)^[m] s = s).card =
      Nat.card (R0 →ₐ[k0] levelField k0 (maxUnram A K) m) := by
  have hmem : ∀ s, (trueTau D φ⁻¹)^[m] s = s → ∀ r,
      sres he hζ hgood D hDB s r ∈ levelField k0 (maxUnram A K) m := fun s hs r =>
    mem_levelField.2 (by rw [hq0]; exact (iterate_trueTau_eq_iff he hζ hgood D hDB hq hφ m s).1 hs r)
  have hconstR : ∀ a : k0, IsConst (p ^ e) (algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a)) := by
    intro a
    rw [← hcomp]
    exact ⟨1, one_pos, by rw [pow_one, ← hq, ← hq0, ← map_pow, FiniteField.pow_card]⟩
  have hconst : ∀ s a, sres he hζ hgood D hDB s (algebraMap k0 R0 a) = algebraMap k0 (maxUnram A K) a := by
    intro s a
    show bres he hζ hgood (D.P s) ((hDB _).1 (D.mem s)) (algebraMap k0 R0 a) = _
    rw [bres_const he hζ hgood (D.P s) ((hDB _).1 (D.mem s)) (hconstR a), hcomp]
  let Φ : {s // (trueTau D φ⁻¹)^[m] s = s} → (R0 →ₐ[k0] levelField k0 (maxUnram A K) m) :=
    fun s => toLevelHom (sres he hζ hgood D hDB s.1) (hmem s.1 s.2) (hconst s.1)
  have hinj : Function.Injective Φ := by
    intro s t hst
    apply Subtype.ext
    apply sres_injective he hζ hgood D hDB hq
    apply RingHom.ext
    intro r
    exact congrArg (fun f : R0 →ₐ[k0] levelField k0 (maxUnram A K) m =>
      ((f r : levelField k0 (maxUnram A K) m) : maxUnram A K)) hst
  have hsurj : Function.Surjective Φ := by
    intro ψ
    let χ : R0 →+* maxUnram A K := ((levelField k0 (maxUnram A K) m).val.comp ψ).toRingHom
    have hχ : ∀ a : k0, χ (algebraMap k0 R0 a) = algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a) := by
      intro a
      rw [← hcomp]
      exact ((levelField k0 (maxUnram A K) m).val.comp ψ).commutes a
    have hχmem : ∀ r, χ r ∈ levelField k0 (maxUnram A K) m := fun r => (ψ r).2
    have hker : RingHom.ker χ ≠ ⊥ := by
      intro h0
      have hinjχ : Function.Injective χ := (RingHom.injective_iff_ker_eq_bot χ).2 h0
      have h1q : 1 < q := by rw [← hq0]; exact Fintype.one_lt_card
      have hq1 : 2 ≤ q ^ m :=
        calc 2 ≤ q := h1q
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) hm
      apply hr0 (q ^ m) hq1
      apply hinjχ
      rw [map_pow]
      have h := mem_levelField.1 (hχmem r0)
      rwa [hq0] at h
    have hφ' : IsFrobLift A K (p ^ e) φ := by rw [← hq]; exact hφ
    obtain ⟨Q, hQ, hQχ⟩ := exists_bres_eq he hζ hgood hφ' (hq0.trans hq) χ hχ hker
    obtain ⟨s, g, hg, hQs⟩ := D.cover Q ((hDB Q).2 hQ)
    have hg' : g ∈ pi1geo A K (p ^ e) := by rw [← hq]; exact hg
    have hs := (hDB _).1 (D.mem s)
    have hsχ : sres he hζ hgood D hDB s = χ :=
      ((bres_geo he hζ hgood hg' (D.P s) hs).symm.trans
        (bres_congr he hζ hgood hQs hQ (isBdryPrime_smul A K R0 g hs)).symm).trans hQχ
    have hfix : (trueTau D φ⁻¹)^[m] s = s := by
      rw [iterate_trueTau_eq_iff he hζ hgood D hDB hq hφ m s]
      intro r
      rw [hsχ, ← hq0]
      exact mem_levelField.1 (hχmem r)
    refine ⟨⟨s, hfix⟩, ?_⟩
    apply AlgHom.ext
    intro r
    apply Subtype.ext
    show sres he hζ hgood D hDB s r = ((ψ r : levelField k0 (maxUnram A K) m) : maxUnram A K)
    exact (RingHom.congr_fun hsχ r).trans rfl
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Sres

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Newton =====
section

/-!
# S4-CP4a, part b: Newton's identity for matrices over any commutative ring

For a square matrix `A` over a commutative ring `R`, with `C = charpolyRev A = det (1 - X A)`:
* `coe_derivative_charpolyRev`: `C' = - C · Σ_k tr(A^(k+1)) X^k` in `R⟦X⟧` (log-derivative / Jacobi at all points;
  proof: `det (1 - (t + X) A) = det (1 - t A) det (1 + X M')` over `R⟦t⟧[X]`, `M' = -(1 - t A)⁻¹ A`).
* `coe_derivative_prod_one_sub`: the same for `Π_i (1 - c_i X)` and the power sums `Σ_i c_i^(k+1)`.
* `trace_pow_eq_of_charpolyRev_eq`: equal `charpolyRev` gives equal traces of all positive powers.
* `exists_trace_pow_eq_sum_pow`: if `charpolyRev A = L` and `Π (1 - c_i X) = L` for one integer polynomial `L`,
  then `tr(A^(k+1))` and `Σ c_i^(k+1)` are the images of one integer `s k`.
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The geometric series `Σ_k X^k A^k` as a matrix of power series. -/
noncomputable def geomMat (A : Matrix n n R) : Matrix n n (PowerSeries R) :=
  fun i j => PowerSeries.mk fun k => (A ^ k) i j

theorem mapC_mul_geomMat (A : Matrix n n R) :
    A.map PowerSeries.C * geomMat A = fun i j => PowerSeries.mk fun k => (A ^ (k + 1)) i j := by
  ext i j k
  simp [Matrix.mul_apply, geomMat, map_sum, PowerSeries.coeff_C_mul, pow_succ', Matrix.mul_apply]

theorem geomMat_mul_mapC (A : Matrix n n R) :
    geomMat A * A.map PowerSeries.C = fun i j => PowerSeries.mk fun k => (A ^ (k + 1)) i j := by
  ext i j k
  simp [Matrix.mul_apply, geomMat, map_sum, PowerSeries.coeff_mul_C, pow_succ, Matrix.mul_apply]

theorem one_sub_X_smul_mul_geomMat (A : Matrix n n R) :
    (1 - (PowerSeries.X : PowerSeries R) • A.map PowerSeries.C) * geomMat A = 1 := by
  have hW : ∀ i j, (A.map PowerSeries.C * geomMat A) i j = PowerSeries.mk fun k => (A ^ (k + 1)) i j :=
    fun i j => by rw [mapC_mul_geomMat]
  rw [sub_mul, one_mul, smul_mul_assoc]
  ext i j k
  rw [Matrix.sub_apply, Matrix.smul_apply, hW, smul_eq_mul]
  rcases k with _ | k
  · by_cases h : i = j <;> simp [geomMat, Matrix.one_apply, h]
  · by_cases h : i = j <;> simp [geomMat, Matrix.one_apply, h, PowerSeries.coeff_succ_X_mul]

theorem coe_charpolyRev (A : Matrix n n R) :
    ((A.charpolyRev : R[X]) : PowerSeries R) =
      det (1 - (PowerSeries.X : PowerSeries R) • A.map PowerSeries.C) := by
  rw [charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h] <;> ring

theorem trace_geomMat_mul (A : Matrix n n R) :
    trace (geomMat A * A.map PowerSeries.C) = PowerSeries.mk fun k => trace (A ^ (k + 1)) := by
  rw [geomMat_mul_mapC]
  refine PowerSeries.ext fun k => ?_
  simp [Matrix.trace, Matrix.diag, map_sum]

/-- **Matrix Newton identity** (log-derivative form): `C' = -C · Σ_k tr(A^(k+1)) X^k`, `C = charpolyRev A`. -/
theorem coe_derivative_charpolyRev (A : Matrix n n R) :
    ((derivative A.charpolyRev : R[X]) : PowerSeries R) =
      -(A.charpolyRev : PowerSeries R) * PowerSeries.mk fun k => trace (A ^ (k + 1)) := by
  set t : PowerSeries R := PowerSeries.X
  set AS : Matrix n n (PowerSeries R) := A.map PowerSeries.C
  set U : Matrix n n (PowerSeries R) := 1 - t • AS with hU
  set V : Matrix n n (PowerSeries R) := geomMat A
  have hUV : U * V = 1 := one_sub_X_smul_mul_geomMat A
  set M' : Matrix n n (PowerSeries R) := -(V * AS)
  have hUM : U * M' = -AS := by
    simp only [M', Matrix.mul_neg, ← Matrix.mul_assoc, hUV, Matrix.one_mul]
  let φ : R[X] →+* (PowerSeries R)[X] :=
    Polynomial.eval₂RingHom (Polynomial.C.comp PowerSeries.C) (X + Polynomial.C t)
  have hφ : ∀ p : R[X], φ p = taylor t (p.map PowerSeries.C) := by
    intro p
    simp [φ, taylor_apply, Polynomial.comp, Polynomial.eval₂_map]
  have h1 : φ A.charpolyRev =
      det (1 - (X + Polynomial.C t) • AS.map Polynomial.C) := by
    rw [charpolyRev, RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [φ, AS, h] <;> ring
  have h2 : (1 : Matrix n n (PowerSeries R)[X]) - (X + Polynomial.C t) • AS.map Polynomial.C =
      U.map Polynomial.C * (1 + (X : (PowerSeries R)[X]) • M'.map Polynomial.C) := by
    have e1 : U.map Polynomial.C * M'.map Polynomial.C = -AS.map Polynomial.C := by
      rw [← Matrix.map_mul, hUM]
      ext i j
      simp
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, e1]
    ext i j
    by_cases h : i = j <;> simp [U, AS, h] <;> ring
  have h3 : (φ A.charpolyRev).coeff 1 = det U * trace M' := by
    rw [h1, h2, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Polynomial.coeff_C_mul,
      coeff_det_one_add_X_smul_one]
  have h4 : (φ A.charpolyRev).coeff 1 = ((derivative A.charpolyRev : R[X]) : PowerSeries R) := by
    rw [hφ, taylor_coeff_one, Polynomial.derivative_map, Polynomial.eval_map,
      Polynomial.eval₂_C_X_eq_coe]
  rw [← h4, h3, coe_charpolyRev, Matrix.trace_neg, trace_geomMat_mul]
  ring

/-- The same for a product `Π_i (1 - c_i X)`: `P' = -P · Σ_k (Σ_i c_i^(k+1)) X^k`. -/
theorem coe_derivative_prod_one_sub (c : Multiset R) :
    ((derivative (c.map fun r => 1 - Polynomial.C r * X).prod : R[X]) : PowerSeries R) =
      -(((c.map fun r => 1 - Polynomial.C r * X).prod : R[X]) : PowerSeries R) *
        PowerSeries.mk fun k => (c.map (· ^ (k + 1))).sum := by
  induction c using Multiset.induction_on with
  | empty =>
    have : (PowerSeries.mk fun _ => (0 : R)) = 0 := by ext; simp
    simp [this]
  | cons a c ih =>
    have key : (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ (k + 1)) =
        PowerSeries.C a := by
      refine PowerSeries.ext fun k => ?_
      rcases k with _ | k
      · simp
      · rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
        simp [pow_succ]
        ring
    have hmk : (PowerSeries.mk fun k => ((a ::ₘ c).map (· ^ (k + 1))).sum) =
        PowerSeries.mk (fun k => a ^ (k + 1)) + PowerSeries.mk fun k => (c.map (· ^ (k + 1))).sum := by
      ext k; simp
    rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_mul, ih, hmk]
    simp only [derivative_sub, derivative_one, derivative_C_mul_X, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, zero_sub, Polynomial.coe_neg] at *
    linear_combination (((c.map fun r => 1 - Polynomial.C r * X).prod : R[X]) : PowerSeries R) * key

/-- Log-derivative cancellation: if `P(0) = 1`, the series `S` with `P' = -P S` is unique. -/
theorem logDeriv_unique {P : R[X]} (hP : P.coeff 0 = 1) {S₁ S₂ : PowerSeries R}
    (h₁ : ((derivative P : R[X]) : PowerSeries R) = -(P : PowerSeries R) * S₁)
    (h₂ : ((derivative P : R[X]) : PowerSeries R) = -(P : PowerSeries R) * S₂) : S₁ = S₂ := by
  have hu : IsUnit (P : PowerSeries R) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe, hP]
    exact isUnit_one
  have h := h₁.symm.trans h₂
  rw [neg_mul, neg_mul, neg_inj] at h
  exact hu.mul_left_cancel h

end Mat

section Transfer

/-- An integer polynomial with constant term `1` has integer "power sums" `s` with `L' = -L · Σ s_k X^k`. -/
theorem exists_powerSums (L : ℤ[X]) (hL : L.coeff 0 = 1) :
    ∃ s : ℕ → ℤ, ((derivative L : ℤ[X]) : PowerSeries ℤ) = -(L : PowerSeries ℤ) * PowerSeries.mk s := by
  have hu : IsUnit (L : PowerSeries ℤ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe, hL]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun k => PowerSeries.coeff k (-((↑(u⁻¹) : PowerSeries ℤ) * ((derivative L : ℤ[X]) : PowerSeries ℤ))), ?_⟩
  have : (PowerSeries.mk fun k => PowerSeries.coeff k (-((↑(u⁻¹) : PowerSeries ℤ) * ((derivative L : ℤ[X]) : PowerSeries ℤ)))) =
      -((↑(u⁻¹) : PowerSeries ℤ) * ((derivative L : ℤ[X]) : PowerSeries ℤ)) := by ext; simp
  rw [this, ← hu, mul_neg, neg_mul, neg_neg, ← mul_assoc, Units.mul_inv, one_mul]

theorem map_powerSums {R : Type*} [CommRing R] (L : ℤ[X]) (s : ℕ → ℤ)
    (hs : ((derivative L : ℤ[X]) : PowerSeries ℤ) = -(L : PowerSeries ℤ) * PowerSeries.mk s) :
    ((derivative (L.map (Int.castRingHom R)) : R[X]) : PowerSeries R) =
      -((L.map (Int.castRingHom R) : R[X]) : PowerSeries R) * PowerSeries.mk fun k => (s k : R) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom R)) hs
  rw [map_mul, map_neg, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe,
    ← Polynomial.derivative_map] at h
  rw [h]
  congr 2

/-- **Newton transfer.** If `charpolyRev A` and `Π (1 - c_i X)` are images of one integer polynomial `L`, then for
every `k` there is one integer `s k` with `tr(A^(k+1)) = s k` and `Σ_i c_i^(k+1) = s k`. -/
theorem exists_trace_pow_eq_sum_pow {R K : Type*} [CommRing R] [CommRing K] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n R) (L : ℤ[X]) (c : Multiset K)
    (hL : L.coeff 0 = 1) (hA : A.charpolyRev = L.map (Int.castRingHom R))
    (hc : L.map (Int.castRingHom K) = (c.map fun r => 1 - Polynomial.C r * X).prod) :
    ∃ s : ℕ → ℤ, ∀ k : ℕ, trace (A ^ (k + 1)) = (s k : R) ∧ (c.map (· ^ (k + 1))).sum = (s k : K) := by
  have hL0 : (L.map (Int.castRingHom R)).coeff 0 = 1 := by
    rw [← hA, Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev]
  have hLK0 : (L.map (Int.castRingHom K)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hL, map_one]
  obtain ⟨s, hs⟩ := exists_powerSums L hL
  refine ⟨s, fun k => ⟨?_, ?_⟩⟩
  · have h1 := logDeriv_unique (S₁ := PowerSeries.mk fun k => trace (A ^ (k + 1))) hL0
      (by rw [← hA]; exact coe_derivative_charpolyRev A) (map_powerSums L s hs)
    simpa using congrArg (PowerSeries.coeff k) h1
  · have h2 := logDeriv_unique (S₁ := PowerSeries.mk fun k => (c.map (· ^ (k + 1))).sum) hLK0
      (by rw [hc]; exact coe_derivative_prod_one_sub c) (map_powerSums L s hs)
    simpa using congrArg (PowerSeries.coeff k) h2

end Transfer

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_FE =====
section

/-!
# S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius

* `zeta_RH_FE` (function fields with full constant field): the inverse zeta roots `c` (S3-ZetaSB `zeta_shape`)
  satisfy `#c = 2g`, `‖c_i‖ = √q` (RH equality, from `Π c_i = q^g` of CoreA `card_eq_two_genus`), `0 ∉ c`,
  `conj c = c`, the functional equation `{q / c_i} = {c_i}`, and `Π (X - c_i)` is the image of a monic `P0 ∈ ℤ[X]`.
* `det_mul_charpolyRev_of_mul_eq`: `G M = q` gives `det M · det(1 - X G) = (-1)^d · χ_M(q X)`.
* `exists_trace_pow_frob` (review R4): if `χ_M = P0`, `P0 = Π (X - c_i)` over `ℂ`, `{q / c_i} = {c_i}` and
  `G M = q` with `q` a unit, then `tr(M^(k+1))`, `tr(G^(k+1))` and `Σ c_i^(k+1)` are one integer `s k`.
  (`M` = arithmetic Frobenius `π` on `T_l`, `G = q π⁻¹` = geometric Frobenius on `H^1`.)
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

section Alg

variable {K : Type*} [Field K]

/-- Functional equation as a polynomial identity: if `{q / c_i} = {c_i}` and `0 ∉ c`, then
`Π (q X - c_i) = (Π (-c_i)) · Π (1 - c_i X)`. -/
theorem comp_prod_X_sub_C (c : Multiset K) (q : K) (h0 : (0 : K) ∉ c) :
    (c.map fun r => X - Polynomial.C r).prod.comp (Polynomial.C q * X) =
      Polynomial.C (c.map fun r => -r).prod *
        ((c.map fun x => q / x).map fun r => 1 - Polynomial.C r * X).prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := fun h => h0 (h ▸ Multiset.mem_cons_self a s)
    have hs : (0 : K) ∉ s := fun h => h0 (Multiset.mem_cons_of_mem h)
    have key : (Polynomial.C q * X - Polynomial.C a : K[X]) =
        Polynomial.C (-a) * (1 - Polynomial.C (q / a) * X) := by
      rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul]
      have : -a * (q / a) = -q := by field_simp
      rw [this, Polynomial.C_neg, Polynomial.C_neg]
      ring
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, sub_comp, X_comp, C_comp]
    rw [ih hs, key, Polynomial.C_mul]
    ring

theorem fe_comp (c : Multiset K) (q : K) (h0 : (0 : K) ∉ c) (hfe : c.map (fun x => q / x) = c) :
    (c.map fun r => X - Polynomial.C r).prod.comp (Polynomial.C q * X) =
      Polynomial.C ((c.map fun r => X - Polynomial.C r).prod.coeff 0) *
        (c.map fun r => 1 - Polynomial.C r * X).prod := by
  rw [comp_prod_X_sub_C c q h0, hfe, coeff_zero_eq_eval_zero, eval_multiset_prod]
  simp [Multiset.map_map, Function.comp_def]

end Alg

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- `G M = q` gives `det M · det(1 - X G) = (-1)^d χ_M(q X)`. -/
theorem det_mul_charpolyRev_of_mul_eq (M G : Matrix n n R) (q : R) (hGM : G * M = q • 1) :
    Polynomial.C M.det * G.charpolyRev =
      (-1) ^ Fintype.card n * M.charpoly.comp (Polynomial.C q * X) := by
  have e1 : (1 - (X : R[X]) • G.map Polynomial.C) * M.map Polynomial.C =
      -((Polynomial.C q * X) • (1 : Matrix n n R[X]) - M.map Polynomial.C) := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hGM]
    ext i j : 1
    by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring
  have e2 : M.charpoly.comp (Polynomial.C q * X) =
      det ((Polynomial.C q * X) • (1 : Matrix n n R[X]) - M.map Polynomial.C) := by
    change Polynomial.compRingHom (Polynomial.C q * X) (det (charmatrix M)) = _
    rw [RingHom.map_det]
    congr 1
    ext i j : 1
    by_cases h : i = j <;> simp [h, charmatrix_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [e2, ← det_neg, ← e1, det_mul, charpolyRev, mul_comm, ← RingHom.mapMatrix_apply, RingHom.map_det]
  rfl

/-- **Trace of geometric Frobenius (R4).** Let `χ_M = P0` with `P0 ∈ ℤ[X]` monic, `P0 = Π (X - c_i)` over `ℂ`,
`0 ∉ c`, `{q / c_i} = {c_i}`, and `G M = q` with `q` a unit. Then `d = #c` and `tr(M^(k+1))`, `tr(G^(k+1))`,
`Σ c_i^(k+1)` are the images of one integer `s k`. -/
theorem exists_trace_pow_frob [Nontrivial R] (M G : Matrix n n R) (q0 : ℕ) (hGM : G * M = (q0 : R) • 1)
    (hq : IsUnit (q0 : R)) (P0 : ℤ[X]) (hP0 : P0.Monic) (c : Multiset ℂ)
    (hc : P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod)
    (hM : M.charpoly = P0.map (Int.castRingHom R)) (h0 : (0 : ℂ) ∉ c)
    (hfe : c.map (fun x => (q0 : ℂ) / x) = c) :
    Fintype.card n = Multiset.card c ∧ ∃ s : ℕ → ℤ, ∀ k : ℕ, trace (M ^ (k + 1)) = (s k : R) ∧
      trace (G ^ (k + 1)) = (s k : R) ∧ (c.map (· ^ (k + 1))).sum = (s k : ℂ) := by
  classical
  have hdeg : P0.natDegree = Multiset.card c := by
    have := congrArg Polynomial.natDegree hc
    rwa [hP0.natDegree_map, natDegree_multiset_prod_X_sub_C_eq_card] at this
  have hn : Fintype.card n = Multiset.card c := by
    rw [← charpoly_natDegree_eq_dim M, hM, hP0.natDegree_map, hdeg]
  have hL0 : (P0.reflect (Multiset.card c)).coeff 0 = 1 := by
    rw [coeff_reflect, revAt_zero, ← hdeg]
    exact hP0
  have hLM : M.charpolyRev = (P0.reflect (Multiset.card c)).map (Int.castRingHom R) := by
    rw [← reverse_charpoly, hM, Polynomial.reverse, hP0.natDegree_map, hdeg, reflect_map]
  have hLc : (P0.reflect (Multiset.card c)).map (Int.castRingHom ℂ) =
      (c.map fun r => 1 - Polynomial.C r * X).prod := by
    rw [← reflect_map, hc, reflect_prod_X_sub_C]
  have hdetM : IsUnit M.det := by
    have h := congrArg Matrix.det hGM
    rw [det_mul, det_smul, det_one, mul_one] at h
    exact isUnit_of_mul_isUnit_right (h ▸ hq.pow _)
  have hdet : M.det = (-1) ^ Fintype.card n * ((P0.coeff 0 : ℤ) : R) := by
    rw [det_eq_sign_charpoly_coeff, hM, coeff_map, eq_intCast]
  have hFEint : P0.comp (Polynomial.C (q0 : ℤ) * X) =
      Polynomial.C (P0.coeff 0) * P0.reflect (Multiset.card c) := by
    apply Polynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    have h1 : ((P0.coeff 0 : ℤ) : ℂ) = ((c.map fun r => X - Polynomial.C r).prod).coeff 0 := by
      rw [← hc, coeff_map, eq_intCast]
    rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X, hLc, hc]
    simp only [eq_intCast, Int.cast_natCast]
    rw [h1]
    exact fe_comp c (q0 : ℂ) h0 hfe
  have hcomp : M.charpoly.comp (Polynomial.C (q0 : R) * X) =
      Polynomial.C ((P0.coeff 0 : ℤ) : R) * (P0.reflect (Multiset.card c)).map (Int.castRingHom R) := by
    have h := congrArg (Polynomial.map (Int.castRingHom R)) hFEint
    rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X] at h
    simp only [eq_intCast, Int.cast_natCast] at h
    rw [hM, h]
  have hLG : G.charpolyRev = (P0.reflect (Multiset.card c)).map (Int.castRingHom R) := by
    apply (Polynomial.isUnit_C.mpr hdetM).mul_left_cancel
    rw [det_mul_charpolyRev_of_mul_eq M G _ hGM, hcomp, hdet, Polynomial.C_mul, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]
    ring
  obtain ⟨s, hs⟩ := exists_trace_pow_eq_sum_pow M _ c hL0 hLM hLc
  obtain ⟨s', hs'⟩ := exists_trace_pow_eq_sum_pow G _ c hL0 hLG hLc
  have hss : s = s' := funext fun k => by
    have := (hs k).2.symm.trans (hs' k).2
    exact_mod_cast this
  subst hss
  exact ⟨hn, s, fun k => ⟨(hs k).1, (hs' k).1, (hs k).2⟩⟩

end Mat

section Concrete

open Places RR ZetaSB

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

end Concrete

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_Kummer_Frob =====
section

/-!
# S4-Kummer K5e: Frobenius equivariance of `H¹_par(π₁^geo, Z/N) ≃ Pic⁰(X̄)[N]`

* `geomFrobH1_mem_curveH1par`: the geometric Frobenius preserves `H¹_par`.
* `piBar_toBar`, `divN_frobF`, `psiAt_frobF`: the arithmetic Frobenius `π` on `Pic(X̄)` and `[div(a)/N]`.
* `frobLift_Fc`: an arithmetic Frobenius lift `φ ∈ π₁(U)` restricts to `frobF` on every constant level `F_m`.
* `Psi_frob`: `Ψ(φ α) = π Ψ(α)`.
* `exists_kummerPicEquiv_frob` (**K5e**): `Φ : H¹_par ≃+ Pic⁰(X̄)[N]` with `Φ[kchar α] = Ψ α` and
  `π (Φ (F x)) = q • Φ x` for the geometric Frobenius `F` (the `μ_N⁻¹` twist, review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial PicDescent Places

noncomputable section

section Generic

theorem units_map_aut_inv {K E : Type} [Field K] [Field E] [Algebra K E] (φ : E ≃ₐ[K] E) (α : Eˣ) :
    Units.map (φ : E →* E) (Units.map ((φ⁻¹ : E ≃ₐ[K] E) : E →* E) α) = α :=
  Units.ext (φ.apply_symm_apply (α : E))

theorem exists_inv_of_coprime {r N : ℕ} (hcop : Nat.Coprime r N) : ∃ q' : ZMod N, (r : ZMod N) * q' = 1 :=
  ⟨((ZMod.unitOfCoprime _ hcop)⁻¹ : (ZMod N)ˣ), by rw [← ZMod.coe_unitOfCoprime _ hcop, Units.mul_inv]⟩

end Generic

section ParFrob

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ} {R0 : Type} [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)] {S : Type}
  {Λ : Type} [CommRing Λ] {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)
  (D : BdryData A K q R0 S)

/-- The geometric Frobenius preserves `H¹_par`. -/
theorem geomFrobH1_mem_curveH1par (φ : Pi1 A K) {x : curveH1 q ρ} (hx : x ∈ curveH1par q ρ D) :
    geomFrobH1 q ρ φ x ∈ curveH1par q ρ D := by
  have hx' : x ∈ LinearMap.range (h1cToH1 ρ (pi1geo A K q) D.inertia) := by
    rw [range_h1cToH1]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  show _ ∈ H1par ρ (pi1geo A K q) D.inertia
  rw [← range_h1cToH1]
  exact ⟨geomFrobH1c q ρ D φ y, h1cToH1_frobH1c ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹)
    (D.frob_compat φ⁻¹) y⟩

end ParFrob

section DivFrob

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

/-- `div(π f) / N = π (div(f) / N)`. -/
theorem divN_frobF (N : ℕ) (f : F') : divN L N (frobF h f) = actD h (frobL Fq L) (divN L N f) := by
  ext P
  have h1 : (Places.div (frobF h f) : Divisor L F') P = actD h (frobL Fq L) (Places.div f) P := by
    rw [div_frobF]
  rw [actD_apply] at h1
  rw [actD_apply, divN_apply, divN_apply, ← Places.div_apply, ← Places.div_apply, h1]

end DivFrob

section FrobPic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

/-- `π` on `Pic(X̄)` restricts to `frobN m` on `Pic(F_m)`. -/
theorem piBar_toBar (m : ℕ) [NeZero m] (x : Pic (Lc Fq Ω m) (Fc Fq F Ω m)) :
    piBar Ω hk (toBar Ω hk m x) = toBar Ω hk m (frobN Ω hk m x) := by
  have : Fact (m ∣ lev m) := ⟨dvd_lev (NeZero.pos m) le_rfl⟩
  rw [toBar_apply hk m x, toBar_apply hk m (frobN Ω hk m x), piBar_of, frobN_conNN]

/-- `[div(π a)/N] = π [div(a)/N]`. -/
theorem psiAt_frobF (N m : ℕ) [NeZero m] (a : Fc Fq F Ω m) :
    psiAt Ω hk N m (frobF (isConstExt_Fc Fq F Ω hk m) a) = piBar Ω hk (psiAt Ω hk N m a) := by
  unfold psiAt
  rw [piBar_toBar, divN_frobF, ← frobN_mk]

end FrobPic

section Curve

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
/-- An arithmetic Frobenius lift restricts to `frobF = π ⊗ id` on `F_m`. -/
theorem frobLift_Fc {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) (m : ℕ)
    [NeZero m] (a : Fc Fq F (AlgebraicClosure F) m) :
    ((φ ⟨(a : AlgebraicClosure F), Fc_le_maxUnram hq he m a.2⟩ : maxUnram (Rfin Fq F) F) : AlgebraicClosure F) =
      ((frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) a : Fc Fq F (AlgebraicClosure F) m) :
        AlgebraicClosure F) := by
  have hle : Fc Fq F (AlgebraicClosure F) m ≤ maxUnram (Rfin Fq F) F := Fc_le_maxUnram hq he m
  let f : Fc Fq F (AlgebraicClosure F) m →ₐ[F] AlgebraicClosure F :=
    (maxUnram (Rfin Fq F) F).val.comp (φ.toAlgHom.comp (IntermediateField.inclusion hle))
  let g : Fc Fq F (AlgebraicClosure F) m →ₐ[F] AlgebraicClosure F :=
    (Fc Fq F (AlgebraicClosure F) m).val.comp (frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m)).toAlgHom
  have hfg : f.toLinearMap = g.toLinearMap := by
    refine LinearMap.ext_on_range (eq_top_iff.2 (isConstExt_Fc Fq F (AlgebraicClosure F) hk m).span) fun j => ?_
    have hc : IsConst (Fintype.card Fq) (IntermediateField.inclusion hle (algebraMap (Lc Fq (AlgebraicClosure F) m)
        (Fc Fq F (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j))) :=
      ⟨m, NeZero.pos m, Subtype.ext (by
        rw [SubmonoidClass.coe_pow]; exact mem_Lc.1 ((pbL Fq (AlgebraicClosure F) m).basis j).2)⟩
    show ((φ (IntermediateField.inclusion hle (algebraMap (Lc Fq (AlgebraicClosure F) m)
        (Fc Fq F (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j))) : maxUnram (Rfin Fq F) F) :
          AlgebraicClosure F) =
      ((frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) (algebraMap (Lc Fq (AlgebraicClosure F) m)
        (Fc Fq F (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j)) :
          Fc Fq F (AlgebraicClosure F) m) : AlgebraicClosure F)
    rw [hφ _ hc, frobF_algebraMap_L, SubmonoidClass.coe_pow]
    show (((pbL Fq (AlgebraicClosure F) m).basis j : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) ^
        Fintype.card Fq =
      ((frobL Fq (Lc Fq (AlgebraicClosure F) m) ((pbL Fq (AlgebraicClosure F) m).basis j) :
        Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F)
    rw [frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    exact (SubmonoidClass.coe_pow _ _).symm
  exact LinearMap.congr_fun hfg a

section PsiFrob

variable {N : ℕ} [NeZero N]

include hq in
/-- An arithmetic Frobenius lift acts on a primitive `N`-th root of unity (`p ∤ N`) by `ζ ↦ ζ ^ q`. -/
theorem frobLift_zeta_card (hNF : (N : F) ≠ 0) {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
    {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ) :
    φ ζ = epow ζ ((Fintype.card Fq : ℕ) : ZMod N) := by
  have hcop : Nat.Coprime (p ^ e) N := coprime_q F p N hNF
  have hcζ : IsConst (p ^ e) ζ := by
    rw [← hq]
    exact isConst_of_pow_eq Fintype.one_lt_card one_pos (by rw [hq]; exact hcop) (one_pow _) one_ne_zero
      hζ.pow_eq_one
  have hφ' : IsFrobLift (Rfin Fq F) F (p ^ e) φ := by rw [← hq]; exact hφ
  rw [hq]
  exact frobLift_zeta hζ hcζ hφ'

variable (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

/-- `kchar (φ⁻¹ α)` is parabolic when `kchar α` is (`F [kchar α] = q • [kchar (φ⁻¹ α)]`, `q` invertible). -/
theorem kclass_rad_map_mem_par {φ : Pi1 (Rfin Fq F) F} (hφζ : φ ζ = epow ζ ((Fintype.card Fq : ℕ) : ZMod N))
    {q' : ZMod N} (hq' : ((Fintype.card Fq : ℕ) : ZMod N) * q' = 1) {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) (hx : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    kclass hζ hζΓ (rad_map φ⁻¹ hα) ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D := by
  have hF := geomFrobH1_kclass hζ hζΓ hφζ hq' hα
  have h2 := Submodule.smul_mem _ q' (geomFrobH1_mem_curveH1par (triv F (maxUnram (Rfin Fq F) F) N) D φ hx)
  rw [hF, smul_smul, mul_comm, hq', one_smul] at h2
  exact h2

theorem geomFrob_kclass_par {φ : Pi1 (Rfin Fq F) F} (hφζ : φ ζ = epow ζ ((Fintype.card Fq : ℕ) : ZMod N))
    {q' : ZMod N} (hq' : ((Fintype.card Fq : ℕ) : ZMod N) * q' = 1) {α : (maxUnram (Rfin Fq F) F)ˣ}
    (hα : α ∈ rad (pi1geo (Rfin Fq F) F (Fintype.card Fq)) N) (hx : kclass hζ hζΓ hα ∈ curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :
    (⟨geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ (kclass hζ hζΓ hα),
        geomFrobH1_mem_curveH1par _ D φ hx⟩ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) =
      Fintype.card Fq • (⟨kclass hζ hζΓ (rad_map φ⁻¹ hα), kclass_rad_map_mem_par hζ hζΓ D hφζ hq' hα hx⟩ : curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_nsmul]
  show geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ (kclass hζ hζΓ hα) =
    Fintype.card Fq • kclass hζ hζΓ (rad_map φ⁻¹ hα)
  rw [geomFrobH1_kclass hζ hζΓ hφζ hq' hα, Nat.cast_smul_eq_nsmul]

end PsiFrob

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_Bridge =====
section

/-!
# S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)

* `tatePicN`: the CoreA Tate coordinates at level `n` as a map `(ℤ/l^n)^s → Pic⁰(X̄)[l^n]`; bijective when
  `A = Pic(X̄)[l^∞]` is divisible (CB1), and `π` acts by `M mod l^n` (`tatePic_frob`).
* `CoreBHyp`: Core B (CB1 + CB2) as an explicit `Prop`: `A` is `l`-divisible, and every CoreA Tate matrix of `π`
  has characteristic polynomial `Π (X - ω_i) ∈ ℤ[X]` for the zeta roots `ω`.
* `trace_of_picEquiv`: for any `ZMod (l^n)`-module `H` with an additive `Φ : H ≃ Pic⁰(X̄)[l^n]` such that
  `π (Φ (f x)) = q Φ x`, `Tr(f^m | H) = 1 + q^m - N_m` (via `exists_tateEquivN`, `coords_key`, `trace_pow_of_coords`).
* `trace_frobPar` (review R4): with the F-equivariant Kummer isomorphism `H¹_par ≃ Pic⁰(X̄)[l^n]` (S4-Kummer),
  `Tr(F^m | H¹_par(Ū, ℤ/l^n)) = 1 + q^m - N_m` for the geometric Frobenius `F`, all `m ≥ 1`.
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer

section LinAlg

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

theorem conj_pow' (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) (m : ℕ) : e.conj (f ^ m) = e.conj f ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]; rfl
  | succ m ih => rw [pow_succ, Module.End.mul_eq_comp, LinearEquiv.conj_comp, ih, pow_succ, Module.End.mul_eq_comp]

theorem toLin'_pow' {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n R) (m : ℕ) :
    Matrix.toLin' (G ^ m) = Matrix.toLin' G ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
  | succ m ih => rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ, Module.End.mul_eq_comp]

end LinAlg

section Abstract

variable {H : Type*} [AddCommGroup H] {L : ℕ} [Module (ZMod L) H] {s : ℕ}

/-- **Trace from coordinates.** If `Ψ : H ≃ (ℤ/L)^s` and `Mn (Ψ (f x)) = q Ψ x` (so `f` is `q Mn⁻¹` in
coordinates), `χ_Mn = P0 = Π (X - c_i)`, `0 ∉ c`, `{q / c_i} = {c_i}`, then `Tr(f^(k+1))` and `Σ c_i^(k+1)`
are one integer. -/
theorem trace_pow_of_coords [Fact (1 < L)] (Ψ : H ≃+ (Fin s → ZMod L)) (f : Module.End (ZMod L) H)
    (Mn : Matrix (Fin s) (Fin s) (ZMod L)) (q0 : ℕ) (hq : IsUnit (q0 : ZMod L))
    (hkey : ∀ x, Mn *ᵥ Ψ (f x) = (q0 : ZMod L) • Ψ x) (P0 : ℤ[X]) (hP0 : P0.Monic) (c : Multiset ℂ)
    (hc : P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod)
    (hM : Mn.charpoly = P0.map (Int.castRingHom (ZMod L))) (h0 : (0 : ℂ) ∉ c)
    (hfe : c.map (fun x => (q0 : ℂ) / x) = c) :
    ∃ sk : ℕ → ℤ, ∀ k : ℕ, LinearMap.trace (ZMod L) H (f ^ (k + 1)) = (sk k : ZMod L) ∧
      (c.map (· ^ (k + 1))).sum = (sk k : ℂ) := by
  classical
  let ΨL : H ≃ₗ[ZMod L] (Fin s → ZMod L) := Ψ.toLinearEquiv (ZMod.map_smul Ψ)
  have : Module.Free (ZMod L) H := Module.Free.of_equiv ΨL.symm
  have : Module.Finite (ZMod L) H := Module.Finite.equiv ΨL.symm
  obtain ⟨G, hG⟩ : ∃ G, G = LinearMap.toMatrix' (ΨL.conj f) := ⟨_, rfl⟩
  have hGv : ∀ v, G *ᵥ v = Ψ (f (Ψ.symm v)) := fun v => by
    rw [← Matrix.toLin'_apply, hG, Matrix.toLin'_toMatrix', LinearEquiv.conj_apply_apply]
    rfl
  have hMG : Mn * G = (q0 : ZMod L) • 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hGv, hkey, AddEquiv.apply_symm_apply,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨u, hu⟩ := hq
  have hGM : G * Mn = (q0 : ZMod L) • 1 := by
    have h1 : Mn * (((u⁻¹ : (ZMod L)ˣ) : ZMod L) • G) = 1 := by
      rw [Matrix.mul_smul, hMG, ← hu, smul_smul, Units.inv_mul, one_smul]
    have h2 := (mul_eq_one_comm (a := Mn)).mp h1
    have h3 := congrArg (fun X => (u : ZMod L) • X) h2
    simp only [Matrix.smul_mul, smul_smul, Units.mul_inv, one_smul] at h3
    rw [h3, hu]
  obtain ⟨-, sk, hs⟩ := exists_trace_pow_frob Mn G q0 hGM ⟨u, hu⟩ P0 hP0 c hc hM h0 hfe
  refine ⟨sk, fun k => ⟨?_, (hs k).2.2⟩⟩
  rw [← LinearMap.trace_conj' _ ΨL, conj_pow', ← Matrix.toLin'_toMatrix' (ΨL.conj f), ← hG, ← toLin'_pow',
    Matrix.trace_toLin'_eq, (hs k).2.1]

/-- Transport of `π (Φ (f x)) = q Φ x` and `π (E v) = E (Mn v)` to coordinates: `Mn (Ψ (f x)) = q Ψ x`. -/
theorem coords_key {X G : Type*} [AddCommGroup X] [AddCommGroup G] {P : AddSubgroup G}
    (Φ : X ≃+ P) (E : (Fin s → ZMod L) ≃+ P) (f : X → X) (π : G →+ G) (Mn : Matrix (Fin s) (Fin s) (ZMod L))
    (q : ℕ) (hΦ : ∀ x, π (Φ (f x) : G) = q • (Φ x : G)) (hE : ∀ v, π (E v : G) = (E (Mn *ᵥ v) : G)) (x : X) :
    Mn *ᵥ (Φ.trans E.symm) (f x) = (q : ZMod L) • (Φ.trans E.symm) x := by
  rw [Nat.cast_smul_eq_nsmul]
  apply E.injective
  apply Subtype.ext
  rw [← hE, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, map_nsmul, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, AddSubgroup.coe_nsmul]
  exact hΦ x

end Abstract

section Tate

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)
variable {l : ℕ} [Fact l.Prime] {k0 : ℕ}
  (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y) {s : ℕ}
  (b1 : Fin s → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)

/-- `π` acts on the level-`n` coordinates by `M mod l^n`. -/
theorem tatePic_frob {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (hM : IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M) (n : ℕ) (cb : Fin s → ZMod (l ^ n)) :
    piBar Ω hk (tatePic hk hdiv b1 hb1 n cb) = tatePic hk hdiv b1 hb1 n (M.map (PadicInt.toZModPow n) *ᵥ cb) := by
  have h := congrArg (fun y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range => ((y : Aℓ Ω hk l) : PicBar Ω hk)) (hM n cb)
  exact h

/-- With `A` divisible: an additive `(ℤ/l^n)^s ≃ Pic⁰(X̄)[l^n]` on which `π` acts by `M mod l^n`. -/
theorem exists_tateEquiv (hinj : ∀ N, Function.Injective (tateMap hdiv b1 hb1 N))
    (hsurj : ∀ N (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range), l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x)
    (htop : (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (hM : IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M) (n : ℕ) :
    ∃ E : (Fin s → ZMod (l ^ n)) ≃+ PicBar0N Ω hk (l ^ n), ∀ v,
      piBar Ω hk (E v : PicBar Ω hk) = (E (M.map (PadicInt.toZModPow n) *ᵥ v) : PicBar Ω hk) :=
  ⟨AddEquiv.ofBijective _ (tatePicN_bijective hk hdiv b1 hb1 hinj hsurj htop n),
    fun v => tatePic_frob hk hdiv b1 hb1 hM n v⟩

/-- `exists_tateEquiv` at a level `N = l ^ n`, with the reduced matrix's characteristic polynomial. -/
theorem exists_tateEquivN (hinj : ∀ N, Function.Injective (tateMap hdiv b1 hb1 N))
    (hsurj : ∀ N (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range), l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x)
    (htop : (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (hM : IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M) (n N : ℕ) (hN : N = l ^ n) (P0 : ℤ[X])
    (hMP : M.charpoly = P0.map (Int.castRingHom ℤ_[l])) :
    ∃ (E : (Fin s → ZMod N) ≃+ PicBar0N Ω hk N) (Mn : Matrix (Fin s) (Fin s) (ZMod N)),
      Mn.charpoly = P0.map (Int.castRingHom (ZMod N)) ∧
      ∀ v, piBar Ω hk (E v : PicBar Ω hk) = (E (Mn *ᵥ v) : PicBar Ω hk) := by
  subst hN
  obtain ⟨E, hE⟩ := exists_tateEquiv hk hdiv b1 hb1 hinj hsurj htop hM n
  refine ⟨E, M.map (PadicInt.toZModPow n), ?_, hE⟩
  rw [Matrix.charpoly_map, hMP, Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

end Tate

section Frob

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

/-- **Core B as an explicit hypothesis** (CB1 + CB2 of `S4_COREB_ROUTE.md`): `A = Pic(X̄)[l^∞]` is `l`-divisible,
and for every CoreA Tate basis (injective at every level) the matrix `M` of the arithmetic Frobenius `π` has
`χ_M = Π (X - ω_i)` with integer coefficients, where `ω` are the zeta roots (`N_m = 1 + q^m - Σ ω_i^m`,
`#ω ≤ 2g`, which pins `ω` down). -/
def CoreBHyp (l : ℕ) [Fact l.Prime] : Prop :=
  (∀ y : Aℓ (AlgebraicClosure F) hk l, ∃ z, l • z = y) ∧
  ∀ (k0 : ℕ) (hdiv : ∀ y : (smulHom (Aℓ (AlgebraicClosure F) hk l) (l ^ k0)).range, ∃ z, l • z = y)
    (b1 : Fin (2 * genusF Fq F) → (smulHom (Aℓ (AlgebraicClosure F) hk l) (l ^ k0)).range)
    (hb1 : ∀ i, l • b1 i = 0) (M : Matrix (Fin (2 * genusF Fq F)) (Fin (2 * genusF Fq F)) ℤ_[l]),
    (∀ N, Function.Injective (tateMap hdiv b1 hb1 N)) →
    IsTateMat hdiv b1 hb1 (endD (piA (AlgebraicClosure F) hk l) (l ^ k0)) M →
    ∀ c : Multiset ℂ, Multiset.card c ≤ 2 * genusF Fq F →
      (∀ m : ℕ, 1 ≤ m → (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) →
      ∃ P0 : ℤ[X], P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod ∧
        M.charpoly = P0.map (Int.castRingHom ℤ_[l])

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

/-- The geometric Frobenius `F` on `H¹_par(Ū, ℤ/N) = H¹(X̄, ℤ/N)`. -/
noncomputable def frobPar (φ : Pi1 (Rfin Fq F) F) :
    Module.End (ZMod N) (curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :=
  (geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ).restrict
    (fun _ hx => geomFrobH1_mem_curveH1par _ D φ hx)

end Frob

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_Lefschetz_BlockAlg =====
section

/-!
# S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`

Pure algebra. For a subgroup `P` of a group `Gf`, the blocks are the right cosets `P x`
(`Blk P`, the quotient by `QuotientGroup.rightRel P`), and `eB P ω` is the coefficient projection of
`Λ[Gf]` onto the block `ω`.
* `sum_eB`, `eB_mul`: the `eB P ω` are orthogonal idempotents summing to `1`;
* `eB_left`: left multiplication by `single p 1`, `p ∈ P`, commutes with every `eB P ω`;
* `blkShift`, `eB_shift`: for `u` normalizing `P`, `F ↦ single u 1 * F * single v 1` maps block `ω`
  to block `blkShift P u v hu ω` (the block of `u x v`);
* `blkShift_fixed_iff`: the block of `a` is fixed iff `u * a * v * a⁻¹ ∈ P`.
-/

set_option autoImplicit false

universe u

namespace RamanujanPetersson
namespace Lefschetz

open MonoidAlgebra

section BlockAlg

variable {Λ : Type*} [CommRing Λ] {Gf : Type u} [Group Gf] (P : Subgroup Gf)

/-- The blocks: the right cosets `P x` of `P` in `Gf`. -/
def Blk : Type u := Quotient (QuotientGroup.rightRel P)

end BlockAlg

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_TrExact =====
section

/-!
# S4-CP4a, part d1: traces are additive along short exact sequences of free modules

`trace_eq_add_of_exact`: for `0 → P → M → Q → 0` exact (`P`, `Q` finite free over a commutative ring) and
compatible endomorphisms `fP, f, fQ`, `Tr f = Tr fP + Tr fQ` (the sequence splits since `Q` is projective; in the
split coordinates `f` is block upper triangular, and the off-diagonal block has trace `0`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.CP4a

variable {R : Type*} [CommRing R] {P M Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]

/-- A short exact sequence `0 → P → M → Q → 0` with `Q` projective splits: `P × Q ≃ M`. -/
theorem exists_split_of_exact [Module.Projective R Q] (i : P →ₗ[R] M) (π : M →ₗ[R] Q)
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : LinearMap.range i = LinearMap.ker π) :
    ∃ e : (P × Q) ≃ₗ[R] M, (∀ p, e (p, 0) = i p) ∧ ∀ x, π x = (e.symm x).2 := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ q, π (s q) = q := fun q => LinearMap.congr_fun hs q
  have hπi : ∀ p, π (i p) = 0 := fun p => LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self i p)
  have he0 : Function.Bijective (i.coprod s) := by
    constructor
    · refine (injective_iff_map_eq_zero _).mpr ?_
      rintro ⟨p, q⟩ h
      rw [LinearMap.coprod_apply] at h
      have hq : q = 0 := by
        have h1 := congrArg π h
        rwa [map_add, hπi, hs', zero_add, map_zero] at h1
      subst hq
      rw [map_zero, add_zero] at h
      rw [(injective_iff_map_eq_zero i).mp hi p h]
      rfl
    · intro x
      have hx : x - s (π x) ∈ LinearMap.range i := by
        rw [hex, LinearMap.mem_ker, map_sub, hs', sub_self]
      obtain ⟨p, hp⟩ := hx
      exact ⟨(p, π x), by rw [LinearMap.coprod_apply, hp, sub_add_cancel]⟩
  refine ⟨LinearEquiv.ofBijective _ he0, fun p => ?_, fun x => ?_⟩
  · rw [LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_zero, add_zero]
  · obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ he0).surjective x
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.ofBijective_apply, LinearMap.coprod_apply, map_add, hπi, hs',
      zero_add]

/-- **Trace additivity** along `0 → P → M → Q → 0` (finite free `P`, `Q`). -/
theorem trace_eq_add_of_exact [Module.Free R P] [Module.Finite R P] [Module.Free R Q] [Module.Finite R Q]
    (i : P →ₗ[R] M) (π : M →ₗ[R] Q) (hi : Function.Injective i) (hπ : Function.Surjective π)
    (hex : LinearMap.range i = LinearMap.ker π) (f : Module.End R M) (fP : Module.End R P) (fQ : Module.End R Q)
    (hP : ∀ p, f (i p) = i (fP p)) (hQ : ∀ x, π (f x) = fQ (π x)) :
    LinearMap.trace R M f = LinearMap.trace R P fP + LinearMap.trace R Q fQ := by
  obtain ⟨e, he1, he2⟩ := exists_split_of_exact i π hi hπ hex
  have : Module.Free R M := Module.Free.of_equiv e
  have : Module.Finite R M := Module.Finite.equiv e
  rw [← LinearMap.trace_conj' f e.symm]
  set g := e.symm.conj f with hgdef
  have hg1 : ∀ p, g (p, 0) = (fP p, 0) := fun p => by
    rw [hgdef, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, he1, hP, ← he1, LinearEquiv.symm_apply_apply]
  have hg2 : ∀ q, (g (0, q)).2 = fQ q := fun q => by
    rw [hgdef, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, ← he2, hQ, he2, LinearEquiv.symm_apply_apply]
  set h := LinearMap.fst R P Q ∘ₗ g ∘ₗ LinearMap.inr R P Q with hh
  have hsplit : g = LinearMap.prodMap fP fQ + LinearMap.inl R P Q ∘ₗ (h ∘ₗ LinearMap.snd R P Q) := by
    refine LinearMap.prod_ext (LinearMap.ext fun p => ?_) (LinearMap.ext fun q => ?_)
    · simp [hg1]
    · refine Prod.ext ?_ ?_
      · simp [hh]
      · simp [hg2]
  rw [hsplit, map_add, LinearMap.trace_prodMap', LinearMap.trace_comp_comm', LinearMap.comp_assoc,
    LinearMap.snd_comp_inl, LinearMap.comp_zero, map_zero, add_zero]

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Les =====
section

/-!
# S4-CP4a, part d2: traces along `0 → H⁰ → ⊕_s Λ → H¹_c → H¹_par → 0` (constant coefficients)

* `trace_les` / `trace_les_pow`: for an exact `0 → H₀ → B → C → P → 0` with compatible endomorphisms
  (`H₀`, `B / H₀`, `P` finite free), `Tr(f_C^m) = Tr(f_B^m) - Tr(f_{H₀}^m) + Tr(f_P^m)`.
* `trace_funLeft`: the trace of `b ↦ b ∘ σ` on `S → R` is `#{s | σ s = s}`.
* Constant coefficients (`Representation.trivial k G k`, generic profinite-style `G`, `Γ`, boundary `I`):
  `trace_frobH0_triv` (`= 1`), `trace_frobBdry_triv` (`= #Fix(τ^m)`), `trace_frobH2c_triv` (`= χ^m`),
  `trace_frobH1c_triv`: `Tr(F^m | H¹_c) = #Fix(τ^m) - 1 + Tr(F^m | H¹_par)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CP4a

open CurveCoh

section Abstract

variable {R : Type*} [CommRing R]

theorem pow_apply_comm {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (g : M₁ →ₗ[R] M₂) (f₁ : Module.End R M₁) (f₂ : Module.End R M₂) (h : ∀ x, f₂ (g x) = g (f₁ x))
    (m : ℕ) (x : M₁) : (f₂ ^ m) (g x) = g ((f₁ ^ m) x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [pow_succ, Module.End.mul_apply, h, ih, pow_succ, Module.End.mul_apply]

theorem conj_pow_les {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) (m : ℕ) : e.conj (f ^ m) = e.conj f ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]; rfl
  | succ m ih => rw [pow_succ, Module.End.mul_eq_comp, LinearEquiv.conj_comp, ih, pow_succ, Module.End.mul_eq_comp]

theorem exact_codRestrict {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : Submodule R M₃)
    (hp : ∀ x, g x ∈ p) (h : Function.Exact f g) : Function.Exact f (LinearMap.codRestrict p g hp) := fun y => by
  rw [← h y, Subtype.ext_iff]
  exact Iff.rfl

theorem surjective_codRestrict {M₂ M₃ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (g : M₂ →ₗ[R] M₃) (p : Submodule R M₃) (hp : ∀ x, g x ∈ p) (h : LinearMap.range g = p) :
    Function.Surjective (LinearMap.codRestrict p g hp) := by
  rintro ⟨y, hy⟩
  rw [← h] at hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  exact ⟨x, rfl⟩

/-- **Trace along a four-term exact sequence** `0 → H₀ → B → C → P → 0`. -/
theorem trace_les {H0 B C P : Type*} [AddCommGroup H0] [Module R H0] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup P] [Module R P]
    (i : H0 →ₗ[R] B) (d : B →ₗ[R] C) (π : C →ₗ[R] P) (hi : Function.Injective i)
    (hid : Function.Exact i d) (hdπ : Function.Exact d π) (hπ : Function.Surjective π)
    (hH0 : Module.Free R H0 ∧ Module.Finite R H0) (hBf : Module.Finite R B)
    (hQ : Module.Free R (B ⧸ LinearMap.range i)) (hP : Module.Free R P ∧ Module.Finite R P)
    (f0 : Module.End R H0) (fB : Module.End R B) (fC : Module.End R C) (fP : Module.End R P)
    (h0 : ∀ x, fB (i x) = i (f0 x)) (h1 : ∀ b, fC (d b) = d (fB b)) (h2 : ∀ c, π (fC c) = fP (π c)) :
    LinearMap.trace R C fC = LinearMap.trace R B fB - LinearMap.trace R H0 f0 + LinearMap.trace R P fP := by
  obtain ⟨_, _⟩ := hH0
  obtain ⟨_, _⟩ := hP
  have hle : LinearMap.range i ≤ (LinearMap.range i).comap fB := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f0 x, (h0 x).symm⟩
  have hker : LinearMap.ker d = LinearMap.range i := LinearMap.exact_iff.mp hid
  have hker' : LinearMap.ker π = LinearMap.range d := LinearMap.exact_iff.mp hdπ
  let fQ : Module.End R (B ⧸ LinearMap.range i) := (LinearMap.range i).mapQ (LinearMap.range i) fB hle
  let dq : (B ⧸ LinearMap.range i) →ₗ[R] C := (LinearMap.range i).liftQ d hker.ge
  have hB := trace_eq_add_of_exact i (LinearMap.range i).mkQ hi (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm fB f0 fQ h0 (fun _ => rfl)
  have hdq : Function.Injective dq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hker.symm
  have hC := trace_eq_add_of_exact dq π hdq hπ (by rw [Submodule.range_liftQ, hker']) fC fQ fP
    (fun x => by
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
      exact h1 b) h2
  rw [hC, hB]
  ring

/-- `trace_les` for powers, with the three known traces as hypotheses (for term-mode use on heavy types). -/
theorem trace_les_pow {H0 B C P : Type*} [AddCommGroup H0] [Module R H0] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup P] [Module R P]
    (i : H0 →ₗ[R] B) (d : B →ₗ[R] C) (π : C →ₗ[R] P) (hi : Function.Injective i)
    (hid : Function.Exact i d) (hdπ : Function.Exact d π) (hπ : Function.Surjective π)
    (hH0 : Module.Free R H0 ∧ Module.Finite R H0) (hBf : Module.Finite R B)
    (hQ : Module.Free R (B ⧸ LinearMap.range i)) (hP : Module.Free R P ∧ Module.Finite R P)
    (f0 : Module.End R H0) (fB : Module.End R B) (fC : Module.End R C) (fP : Module.End R P)
    (h0 : ∀ x, fB (i x) = i (f0 x)) (h1 : ∀ b, fC (d b) = d (fB b)) (h2 : ∀ c, π (fC c) = fP (π c))
    (m : ℕ) {t0 tB tP : R} (ht0 : LinearMap.trace R H0 (f0 ^ m) = t0)
    (htB : LinearMap.trace R B (fB ^ m) = tB) (htP : LinearMap.trace R P (fP ^ m) = tP) :
    LinearMap.trace R C (fC ^ m) = tB - t0 + tP := by
  rw [← ht0, ← htB, ← htP]
  exact trace_les i d π hi hid hdπ hπ hH0 hBf hQ hP _ _ _ _ (pow_apply_comm i f0 fB h0 m)
    (pow_apply_comm d fB fC h1 m) (fun c => (pow_apply_comm π fC fP (fun c => (h2 c).symm) m c).symm)

theorem funLeft_pow {S : Type*} (σ : S → S) (m : ℕ) :
    LinearMap.funLeft R R σ ^ m = LinearMap.funLeft R R σ^[m] := by
  induction m with
  | zero => exact LinearMap.ext fun _ => rfl
  | succ m ih =>
    rw [pow_succ', ih, Function.iterate_succ, LinearMap.funLeft_comp]
    rfl

/-- **Permutation trace**: `Tr(b ↦ b ∘ σ | S → R) = #{s | σ s = s}`. -/
theorem trace_funLeft {S : Type*} [Fintype S] [DecidableEq S] (σ : S → S) :
    LinearMap.trace R (S → R) (LinearMap.funLeft R R σ) =
      ((Finset.univ.filter fun s => σ s = s).card : R) := by
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R S), LinearMap.toMatrix_eq_toMatrix', Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix'_apply, LinearMap.funLeft_apply, Pi.single_apply]
  rw [Finset.sum_boole]

theorem trace_one_of_equiv {M₁ : Type*} [AddCommGroup M₁] [Module R M₁] (e : M₁ ≃ₗ[R] R) :
    LinearMap.trace R M₁ 1 = 1 := by
  have := Module.Free.of_equiv e.symm
  have := Module.Finite.equiv e.symm
  rw [LinearMap.trace_one, e.finrank_eq]
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · rw [Module.finrank_self, Nat.cast_one]

/-- Arithmetic of the Lefschetz combination `Tr(H²_c) - Tr(H¹_c)`. -/
theorem lefschetz_combine (q Nm fix m : ℕ) {t2 t1 : R} (h2 : t2 = (q : R) ^ m)
    (h1 : t1 = (fix : R) - 1 + (((1 + (q : ℤ) ^ m - (Nm : ℤ)) : ℤ) : R)) : t2 - t1 = (Nm : R) - (fix : R) := by
  rw [h2, h1]
  push_cast
  ring

end Abstract

section Pair

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

theorem frobH0_triv (ψ : G) : frobH0 (Representation.trivial k G k) Γ ψ = 1 :=
  LinearMap.ext fun _ => rfl

theorem trace_frobH0_triv (ψ : G) (m : ℕ) :
    LinearMap.trace k (H0 (Representation.trivial k G k) Γ) (frobH0 (Representation.trivial k G k) Γ ψ ^ m) = 1 := by
  rw [frobH0_triv, one_pow]
  exact trace_one_of_equiv (h0ConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl))

/-- Constant coefficients: `⊕_s M^{I_s} = (S → k)`. -/
noncomputable def bdryTrivEquiv : bdryInv (Representation.trivial k G k) Γ I ≃ₗ[k] (S → k) :=
  (LinearEquiv.ofEq _ _ (bdryInv_eq_top_of_trivial _ Γ I (fun _ => rfl))).trans (LinearEquiv.ofTop ⊤ rfl)

theorem trace_frobBdry_triv [Fintype S] [DecidableEq S] (ψ : G) (τ : S → S) (h : S → Γ)
    (hI : BdryCompat Γ I ψ τ h) (m : ℕ) :
    LinearMap.trace k (bdryInv (Representation.trivial k G k) Γ I)
        (frobBdry (Representation.trivial k G k) Γ I ψ τ h hI ^ m) =
      ((Finset.univ.filter fun s => τ^[m] s = s).card : k) := by
  have he : (bdryTrivEquiv Γ I).conj (frobBdry (Representation.trivial k G k) Γ I ψ τ h hI) =
      LinearMap.funLeft k k τ := LinearMap.ext fun _ => rfl
  rw [← LinearMap.trace_conj' _ (bdryTrivEquiv Γ I), conj_pow_les, he, funLeft_pow, trace_funLeft]

theorem trace_frobH2c_triv (ψ : G) (χ : k) (m : ℕ) :
    LinearMap.trace k (H2c (Representation.trivial k G k) Γ)
      (frobH2c (Representation.trivial k G k) Γ ψ χ ^ m) = χ ^ m := by
  have hf : frobH2c (Representation.trivial k G k) Γ ψ χ = χ • 1 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    exact frobH2c_mk _ _ _ _ _
  rw [hf, smul_pow, one_pow, map_smul,
    trace_one_of_equiv (h2cConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl)), smul_eq_mul, mul_one]

/-- `H¹_c → H¹_par` (the corestriction of `h1cToH1` to its range). -/
noncomputable def h1cToH1par : H1c (Representation.trivial k G k) Γ I →ₗ[k] H1par (Representation.trivial k G k) Γ I :=
  LinearMap.codRestrict _ (h1cToH1 (Representation.trivial k G k) Γ I) fun c => by
    rw [← range_h1cToH1]
    exact LinearMap.mem_range_self _ c

/-- **Constant coefficients**: `Tr(F^m | H¹_c) = #Fix(τ^m) - 1 + Tr(F^m | H¹_par)` (`F = T_ψ`, any `fP` on
`H¹_par` compatible with `h1cToH1`, `H¹_par` finite free). -/
theorem trace_frobH1c_triv [Fintype S] [DecidableEq S] [Nonempty S] (ψ : G) (τ : S → S) (h : S → Γ)
    (hI : BdryCompat Γ I ψ τ h) (fP : Module.End k (H1par (Representation.trivial k G k) Γ I))
    (hfP : ∀ c, h1cToH1 (Representation.trivial k G k) Γ I (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI c) =
      (fP (h1cToH1par (k := k) Γ I c) : H1 (Representation.trivial k G k) Γ))
    (hP : Module.Free k (H1par (Representation.trivial k G k) Γ I) ∧
      Module.Finite k (H1par (Representation.trivial k G k) Γ I))
    (m : ℕ) {tP : k} (htP : LinearMap.trace k _ (fP ^ m) = tP) :
    LinearMap.trace k (H1c (Representation.trivial k G k) Γ I)
        (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI ^ m) =
      ((Finset.univ.filter fun s => τ^[m] s = s).card : k) - 1 + tP :=
  by
  refine trace_les_pow (h0ToBdry _ Γ I) (bdryToH1c _ Γ I) (h1cToH1par (k := k) Γ I) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hP
    (frobH0 _ Γ ψ) (frobBdry _ Γ I ψ τ h hI) _ fP ?_ ?_ ?_ m ?_ ?_ htP
  · exact h0ToBdry_injective _ Γ I
  · exact exact_h0ToBdry_bdryToH1c _ Γ I
  · exact exact_codRestrict _ _ _ _ (exact_bdryToH1c_h1cToH1 _ Γ I)
  · exact surjective_codRestrict _ _ _ (range_h1cToH1 _ Γ I)
  · exact ⟨Module.Free.of_equiv (h0ConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl)).symm,
      Module.Finite.equiv (h0ConstEquiv (Representation.trivial k G k) Γ (fun _ => rfl)).symm⟩
  · exact Module.Finite.equiv (bdryTrivEquiv Γ I).symm
  · exact Module.Free.of_equiv (constQuotEquiv (Representation.trivial k G k) Γ I (Classical.arbitrary S)
      (fun _ => rfl)).symm
  · exact frobBdry_h0ToBdry _ Γ I ψ τ h hI
  · exact frobH1c_bdryToH1c _ Γ I ψ τ h hI
  · exact fun c => Subtype.ext (hfP c)
  · exact trace_frobH0_triv Γ ψ m
  · exact trace_frobBdry_triv Γ I ψ τ h hI m

end Pair

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Lef =====
section

/-!
# S4-CP4a, part d2 (curve): the Lefschetz identity mod `l^n` for constant coefficients (Core B as a hypothesis)

* `free_of_picEquiv`, `free_curveH1par`: `H¹_par(Ū, ℤ/l^n) ≅ Pic⁰(X̄)[l^n]` is finite free over `ℤ/l^n`.
* `trace_frobH1c_curve`: `Tr(F^m | H¹_c(Ū, ℤ/l^n)) = #Fix(τ^m) - 1 + (1 + q^m - N_m)`, where `τ` is the
  permutation of the boundary `S` in any boundary-compatible geometric Frobenius `T_{φ⁻¹, τ, h}` (from the exact sequence `0 → H⁰ → ⊕_S Λ → H¹_c → H¹_par → 0`).
* `trace_geomFrobH2c_triv`: `Tr(F^m | H²_c(Ū, ℤ/l^n)) = q^m`.
* `lefschetz_triv`: `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = N_m - #Fix(τ^m)` in `ℤ/l^n`, every `m ≥ 1`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer

section Lef

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

/-- **`Tr(F^m | H²_c(Ū, ℤ/N)) = q^m`**. -/
theorem trace_geomFrobH2c_triv (φ : Pi1 (Rfin Fq F) F) (m : ℕ) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) =
      ((Fintype.card Fq : ℕ) : ZMod N) ^ m :=
  trace_frobH2c_triv (pi1geo (Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ _ m

end Lef

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_BdryInf =====
section

/-!
# S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`

For the chart `Rinf` at infinity of a function field `F/𝔽_q`, with `𝔽_{q^m} ⊆ K_U` for all `m` (`hζc`):
* `good_inf`: residue rings of boundary primes are finite of `q`-power order.
* `card_fix_inf`: `#{s | τ^m s = s} = #Hom_{𝔽_q}(Rinf, 𝔽_{q^m})` for the true boundary permutation `τ` of `φ⁻¹`.
* `numPoints_eq_add_fix`: `N_m = #U(𝔽_{q^m}) + #{s | τ^m s = s}`, `#U(L) := #Hom_{𝔽_q}(Rfin, L)`, `[L : 𝔽_q] = m`.
* `lefschetz_count`: `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n` (Core B as a hypothesis).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section BdryInf

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

omit [Fintype Fq] [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] in
theorem algebraMap_Fq_maxUnram (a : Fq) : algebraMap Fq (maxUnram (Rfin Fq F) F) a =
    algebraMap (Rinf Fq F) (maxUnram (Rfin Fq F) F) (algebraMap Fq (Rinf Fq F) a) := by
  rw [IsScalarTower.algebraMap_apply (Rinf Fq F) F (maxUnram (Rfin Fq F) F),
    IsScalarTower.algebraMap_apply Fq F (maxUnram (Rfin Fq F) F),
    ← IsScalarTower.algebraMap_apply Fq (Rinf Fq F) F]

/-- `#Hom_{𝔽_q}(Rfin, L)` depends only on `[L : 𝔽_q]`. -/
theorem card_algHom_Rfin_congr (L L' : Type) [Field L] [Algebra Fq L] [Finite L] [Field L'] [Algebra Fq L']
    [Finite L'] (h : Module.finrank Fq L = Module.finrank Fq L') :
    Nat.card (Rfin Fq F →ₐ[Fq] L) = Nat.card (Rfin Fq F →ₐ[Fq] L') := by
  have key : ∀ (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0), n = n' →
      ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN) hn).toFinset, deg Fq P =
        ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN) hn').toFinset, deg Fq P := by
    rintro n _ hn hn' rfl
    rfl
  have : Module.Finite Fq L := Module.Finite.of_finite
  have : Module.Finite Fq L' := Module.Finite.of_finite
  rw [card_algHom_Rfin Fq F L, card_algHom_Rfin Fq F L']
  exact key _ _ (Module.finrank_pos (R := Fq) (M := L)).ne' (Module.finrank_pos (R := Fq) (M := L')).ne' h

variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq hζc in
theorem exists_prim_level (m : ℕ) (hm : 0 < m) :
    ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z (Fintype.card Fq ^ m - 1) := by
  rw [hq]
  exact hζc m hm

include hq he hζc hDB in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Fixed boundary points over `∞`**: `#{s | τ^m s = s} = #Hom_{𝔽_q}(Rinf, 𝔽_{q^m})`. -/
theorem card_fix_inf {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    [Fintype S] [DecidableEq S] (m : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun s => (trueTau D φ⁻¹)^[m] s = s).card =
      Nat.card (Rinf Fq F →ₐ[Fq] levelField Fq (maxUnram (Rfin Fq F) F) m) :=
  card_fix_eq he hζc (good_inf hq) D hDB hq hφ rfl algebraMap_Fq_maxUnram
    (algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)) (fun _ hN => piInf_pow_ne_self Fq F hN) m hm

end BdryInf

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_FrobLift =====
section

/-!
# S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist

For a function field `F/𝔽_q` (`q = p ^ e`) with `constField = 𝔽_q`:
* `cast_ne_zero_of_not_dvd`, `isUnit_cast_Rfin`, `isUnit_cast_Rinf`: `N = l ^ n` with `l ∤ q` is a unit;
* `exists_zeta_geo`: a primitive `N`-th root of unity `ζ ∈ K_U` fixed by `π₁^geo`;
* `exists_zeta_level`: primitive `(q ^ a - 1)`-th roots of unity in `K_U`;
* `exists_frobLift`: there is `φ ∈ π₁(U)` with `φ x = x ^ q` on all constants (a compactness argument over the
  closed sets `T_m = {σ | σ x = x ^ q whenever x ^ (q ^ m) = x}`, each nonempty by lifting `frobF` on `F_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places PicDescent CurveCoh Kummer GalCover

noncomputable section

section FrobSet

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

end FrobSet

section Exist

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
theorem cast_ne_zero_of_not_dvd {l : ℕ} [hl : Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) (n : ℕ) :
    ((l ^ n : ℕ) : F) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff F p] at h
  have hpl : p ∣ l := (Fact.out : p.Prime).dvd_of_dvd_pow h
  have hpl' : p = l := (Nat.prime_dvd_prime_iff_eq Fact.out hl.out).1 hpl
  apply hlq
  rw [hq, ← hpl']
  exact dvd_pow_self p he.ne'

end Exist

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_JacAlg_Res =====
section

/-!
# Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)

* R1 `det_aeval_eq_resultant`: for a square matrix `A` over a domain, `det F(A) = Res(χ_A, F)` (degree
  parameters `card n`, `natDegree F`); `linearMap_det_aeval_eq_resultant`: the same for an endomorphism of a
  free finite module (parameters `finrank`, `natDegree F`).
* R2 `eq_of_norm_resultant_eq`: over an ultrametric nontrivially normed field, monic `P, Q` with
  `‖Res(P, G)‖ = ‖Res(Q, G)‖` for all `G` are equal. For a monic irreducible `φ` with `P = φ^d P₁`, `φ ∤ P₁`,
  `‖Res(P, φ + c)‖ = ‖c‖^(d deg φ) · ‖Res(P₁, φ)‖` for small `c` (`exists_norm_resultant_add_C`) reads off `d`;
  equal multiplicities give equal normalized factors. Milne's Lemma 10.21 without a Galois closure.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial UniqueFactorizationMonoid

section Det

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma det_sub_algebraMap {K : Type*} [CommRing K] (A : Matrix n n K) (r : K) :
    (A - algebraMap K (Matrix n n K) r).det = (-1) ^ Fintype.card n * A.charpoly.eval r := by
  rw [Matrix.eval_charpoly, ← Matrix.det_neg, neg_sub]
  congr 2

theorem det_aeval_eq_resultant_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (A : Matrix n n K) (F : K[X]) :
    (aeval A F).det = resultant A.charpoly F (Fintype.card n) F.natDegree := by
  have hF : F.Splits := IsAlgClosed.splits F
  have hcard : Multiset.card F.roots = F.natDegree := hF.natDegree_eq_card_roots.symm
  rw [resultant_comm, resultant_eq_prod_eval F A.charpoly _ (Matrix.charpoly_natDegree_eq_dim A).le hF]
  let ψ : K[X] →* K := Matrix.detMonoidHom.comp (aeval A).toRingHom.toMonoidHom
  have hψ : ∀ G : K[X], ψ G = (aeval A G).det := fun G => rfl
  rw [← hψ]
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  rw [map_mul, map_multiset_prod, Multiset.map_map, hψ, aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.det_smul, Matrix.det_one, mul_one]
  have h1 : ∀ a : K, (⇑ψ ∘ fun a => X - C a) a =
      (-1) ^ Fintype.card n * A.charpoly.eval a := by
    intro a
    show (aeval A (X - C a)).det = _
    rw [map_sub, aeval_X, aeval_C, det_sub_algebraMap]
  rw [Multiset.map_congr rfl (fun a _ => h1 a), Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate, hcard, ← pow_mul]
  ring

theorem det_aeval_eq_resultant {R : Type*} [CommRing R] [IsDomain R] (A : Matrix n n R) (F : R[X]) :
    (aeval A F).det = resultant A.charpoly F (Fintype.card n) F.natDegree := by
  let L := AlgebraicClosure (FractionRing R)
  let φ : R →+* L := (algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))
  have hφ : Function.Injective φ :=
    (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R (FractionRing R))
  apply hφ
  have hmap : φ.mapMatrix (aeval A F) = aeval (φ.mapMatrix A) (F.map φ) := by
    refine map_aeval_eq_aeval_map ?_ F A
    ext r i j
    simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  rw [RingHom.map_det, hmap, det_aeval_eq_resultant_of_isAlgClosed, ← resultant_map_map,
    RingHom.mapMatrix_apply, Matrix.charpoly_map, natDegree_map_eq_of_injective hφ]

end Det

section Field

variable {K : Type*} [Field K]

end Field

section Ultra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

end Ultra

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_JacAlg_Charpoly =====
section

/-!
# Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)

* C1 `norm_resultant_eq_of_int`, `norm_resultant_eq_of_int_rat`: for monic `P, Q` over `ℤ_l`, equal norms
  `‖Res(P, F)‖ = ‖Res(Q, F)‖` for all integer `F` with `p ∤ F(0)` (`p ≠ l` prime) extend to all `G` over `ℤ_l`
  (approximation mod `l^K`) and then over `ℚ_l` (clearing denominators; the degrees agree via `F = l`).
* C2 `charpoly_eq_of_norm_det`: if `‖Res(P₀, F)‖_l = ‖det F(M)‖_l` for those `F`, then `charpoly M = P₀`.
  `DegreeData.deg_eq_resultant`: `deg F = Res(P₀, F)` when `P_π = P₀` (Milne 10.22).
  `DegreeData.charpoly_eq`: `‖deg F‖_l = ‖det F(M)‖_l` for `p ∤ F(0)` gives `charpoly(M) = P_π` (Milne 10.20),
  and `DegreeData.finrank_eq`: the rank is `2g`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

variable {l : ℕ} [hl : Fact l.Prime]

lemma norm_sub_le_of_toZModPow_eq {x y : ℤ_[l]} {K : ℕ}
    (h : PadicInt.toZModPow K x = PadicInt.toZModPow K y) : ‖x - y‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h,
    sub_self]

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ}

end DegreeData

end RamanujanPetersson.JacAlg


end


