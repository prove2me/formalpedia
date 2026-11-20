-- Prove2me | Definitions.Def_RPLib_F2_070
-- name    : RPLib_F2_070
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T23:29:16.295416+00:00
-- url     : https://prove2.me/theorems/0c61119c-421c-4251-b119-aa4bd5cf8d39
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 070 of 70
-- statement:
--   File 070 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_PtSum`: S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count
--   * `S4.Def_RP_Lefschetz_TwistCount`: S4-Lefschetz, L6a: the Lefschetz trace formula mod `l^n` on the cone complex, as a sum over points
--   * `S4.Def_RP_Lefschetz_Pkg`: S4-Lefschetz, L6c: the perfect-complex package of `lefschetz_twist`, discharged
--   * `S4.Def_RP_Lefschetz_Pkg2`: S4-Lefschetz, L6c': the package with the cocycle finiteness discharged
--   * `S4.Def_RP_Lefschetz_Main`: S4-Lefschetz, L6e: the trace formula mod `l^n`, with `Pic` divisibility discharged
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_069

/-!
# Ramanujan-Petersson curve library (flat edition), file 070 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_PtSum`: S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count
* `S4.Def_RP_Lefschetz_TwistCount`: S4-Lefschetz, L6a: the Lefschetz trace formula mod `l^n` on the cone complex, as a sum over points
* `S4.Def_RP_Lefschetz_Pkg`: S4-Lefschetz, L6c: the perfect-complex package of `lefschetz_twist`, discharged
* `S4.Def_RP_Lefschetz_Pkg2`: S4-Lefschetz, L6c': the package with the cocycle finiteness discharged
* `S4.Def_RP_Lefschetz_Main`: S4-Lefschetz, L6e: the trace formula mod `l^n`, with `Pic` divisibility discharged
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_PtSum =====
section

/-!
# S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count

* `ptCount S f γ`: the number of `u ∈ S` with `f u` conjugate to `γ`;
* group counting: `card_conj_fiber`, `card_conj_fiber_zero`, `sum_card_conj_eq`, `card_coset_conj`,
  `sum_fixed_blk_card`;
* `pi_mem_geo_of_fix`: an element of `π₁` fixing a primitive `(q^N0 - 1)`-th root of unity (`|Gf| ∣ N0`) maps into
  `π(π₁^geo)`;
* `euler_eq_count`: `Σ_i (-1)^i Tr(ρPC γ⁻¹ ∘ frobPC^m | PC^i) = |Z(γ)| · #{u ∈ S | π(F_u) ~ γ}` (the `hcount`
  hypothesis of `lefschetz_pow_eq_count`), `S` the `F_{q^m}`-points of `U` and `F_u` normalized Frobenius elements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation

section Count

variable {G : Type} [Group G]

end Count

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **L5c5: the twisted count (`hcount` of `lefschetz_pow_eq_count`).** The alternating trace of `γ⁻¹ ∘ F^m` on the
perfect complex is `|Z(γ)| · #{u ∈ S | π(F_u) ~ γ}`, for `S` the `Fr`-fixed points `u : R_fin → Ω` normalized by `ιS`
on `𝔽_q` (`Fr = (·)^(q^m)`) and normalized Frobenius elements `F_u`. -/
def euler_eq_count (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    [∀ i, Module.Free (ZMod N) (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Finite (ZMod N) (PC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    (Hr : ResHyp (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia)
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hTW : ∀ s (e : Z1 (regRep (ZMod N) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓
        (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s))),
      (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
          MonoidAlgebra (ZMod N) Gf)
        (conjSub (φ⁻¹ * (trueH (bdryInf Fq K) φ⁻¹ s : Pi1 (Rfin Fq K) K))
          (bdry_mem _ _ _ _ _ (trueCompat (bdryInf Fq K) φ⁻¹) s) (Hr.sg s)) =
        (Fintype.card Fq : ZMod N) •
          (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
            MonoidAlgebra (ZMod N) Gf) (Hr.sg (trueTau (bdryInf Fq K) φ⁻¹ s)))
    (γ : Gf) {m : ℕ} (hm : 0 < m) {r : ℕ} (hmr : m * Fintype.card Gf ∣ r) (hQ : 1 < p ^ (e * r))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq r →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x) :
    ∑ i ∈ Finset.range (2 + 1), (-1 : ZMod N) ^ i *
        LinearMap.trace (ZMod N) _
          (ρPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i γ⁻¹ ∘ₗ
            frobPC (ZMod N) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
              (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) i ^ m) =
      (Nat.card {z : Gf // z⁻¹ * γ * z = γ} : ZMod N) * (ptCount S (fun u => π (Fu u)) γ : ZMod N) := by
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hN0 : 0 < m * Fintype.card Gf := Nat.mul_pos hm Fintype.card_pos
  have hQ1 : 1 ≤ Fintype.card Fq ^ (m * Fintype.card Gf) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨ζ, hζ⟩ := exists_zeta_level (Fq := Fq) (F := K) he (m * Fintype.card Gf) hN0
  rw [← hq] at hζ
  have hcst : IsConst (Fintype.card Fq) ζ := ⟨m * Fintype.card Gf, hN0, prim_pow_fix hQ1 hζ⟩
  have hζn : ζ ∈ kStar (Rfin Fq K) K hq r := by
    rw [mem_kStar]
    obtain ⟨t, ht⟩ := hmr
    rw [ht, pow_mul]
    exact pow_pow_fix (prim_pow_fix hQ1 hζ) t
  have hdeg : ∀ u ∈ S, π (φ⁻¹ ^ m) * π (Fu u) ∈ (pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π := by
    intro u hu
    obtain ⟨w, -, hwF, hwι⟩ := hFu u hu
    have hFζ : (Fu u) ζ = ζ ^ (Fintype.card Fq ^ m) :=
      frob_apply_kStar Fq hq hQ Fr hFr ιS w (Fu u) hwF hwι ζ hζn
    have hy : (φ⁻¹ ^ m * Fu u) ζ = ζ := by
      rw [AlgEquiv.mul_apply, hFζ, ← frob_pow_apply hφ hcst m, ← AlgEquiv.mul_apply, inv_pow, inv_mul_cancel,
        AlgEquiv.one_apply]
    rw [← map_mul]
    exact pi_mem_geo_of_fix Fq K hφ π hπ hN0 (dvd_mul_left _ _) hζ _ hy
  obtain ⟨cnt, hcnt, hsum⟩ := euler_eq_sum_cover Fq K hq he l n hn hN hlq π hπ Hr hφ hTW γ hm
  refine hsum.trans ?_
  have hω : ∀ ω ∈ Finset.univ.filter (fun ω => blkShift ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)
      (π (φ⁻¹ ^ m)) γ (map_mem_normalizer π (φ⁻¹ ^ m)) ω = ω),
      cnt ω = ∑ u ∈ S, Nat.card {b : Gf // blk ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π) b = ω ∧
        b⁻¹ * π (Fu u) * b = γ} := by
    intro ω hωf
    have hfix := (Finset.mem_filter.1 hωf).2
    obtain ⟨a, c0, E, hE, hfd, hsep, σ, hblkA, hc0, hπg, hcard, -, -, ⟨Nζ, hNZ, ζ', hζ', hNζ, hrange⟩, hc⟩ :=
      hcnt ω hfix
    subst hNζ
    subst hblkA
    rw [hc]
    refine (card_rfin_eq_sum Fq hq E hE π hπ hφ hc0 hm hζ' hrange hcard hmr hQ hπg Fr hFr ιS S hS Fu
      hFu).trans (Finset.sum_congr rfl fun u _ => ?_)
    exact card_coset_conj _ a (π (Fu u)) γ
  have hnat : ∑ ω ∈ Finset.univ.filter (fun ω => blkShift ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)
      (π (φ⁻¹ ^ m)) γ (map_mem_normalizer π (φ⁻¹ ^ m)) ω = ω), cnt ω =
        Nat.card {z : Gf // z⁻¹ * γ * z = γ} * ptCount S (fun u => π (Fu u)) γ := by
    rw [Finset.sum_congr rfl hω, Finset.sum_comm]
    refine (Finset.sum_congr rfl fun u hu => ?_).trans (sum_card_conj_eq S (fun u => π (Fu u)) γ)
    exact sum_fixed_blk_card _ (π (φ⁻¹ ^ m)) γ (π (Fu u)) (map_mem_normalizer π (φ⁻¹ ^ m)) (hdeg u hu)
  rw [← Nat.cast_mul, ← hnat, Nat.cast_sum]

end Main

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_TwistCount =====
section

/-!
# S4-Lefschetz, L6a: the Lefschetz trace formula mod `l^n` on the cone complex, as a sum over points

* `ptCount_eq_card`, `sum_class_ptCount`: `Σ_c L(c) χ(c) = Σ_{u ∈ S} χ([g u])` when `L([γ]) = #{u ∈ S | g u ~ γ}`;
* **`lefschetz_twist`**: for a lisse `τ : Gf → GL(M)` over `ℤ/l^n` (through `π : π₁(U) → Gf`),
  `Tr(F^m | M) - Tr(F^m | K¹(M)) + Tr(F^m | K²(M)) = Σ_{u ∈ U(F_{q^m})} Tr(τ(π F_u)⁻¹ | M)`, with `F` the geometric
  Frobenius `φ⁻¹` on the cone complex `K(M)` and `F_u` (arithmetic) Frobenius elements at the `F_{q^m}`-points `u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings

section Gen

end Gen

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **L6a: the Lefschetz trace formula mod `l^n` on the cone complex.** For a representation `τ` of `Gf` on a finite
free `ℤ/l^n`-module `M` (a lisse sheaf trivialized by `π`), the alternating trace of the geometric Frobenius `F^m` on
the cone complex `K(M)` is `Σ_{u ∈ S} Tr(τ(π F_u)⁻¹ | M)`, `S` the `F_{q^m}`-points of `U` and `F_u` Frobenius elements.
Hypotheses: the perfect-complex package at the levels `l^(n+k)` and `l^n` (`l^k` kills the `l`-part of `|Gf|`). -/
def lefschetz_twist (l n k : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Gf : Type} [Group Gf] [Fintype Gf] [Fintype (ConjClasses Gf)] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    [∀ i, Module.Free (ZMod (l ^ (n + k)))
      (PC (ZMod (l ^ (n + k))) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Finite (ZMod (l ^ (n + k)))
      (PC (ZMod (l ^ (n + k))) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Free (ZMod (l ^ n)) (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    [∀ i, Module.Finite (ZMod (l ^ n))
      (PC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i)]
    (Hr : ResHyp (ZMod (l ^ (n + k))) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia)
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hTW : ∀ s (e : Z1 (regRep (ZMod (l ^ (n + k))) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓
        (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s))),
      (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
          MonoidAlgebra (ZMod (l ^ (n + k))) Gf)
        (conjSub (φ⁻¹ * (trueH (bdryInf Fq K) φ⁻¹ s : Pi1 (Rfin Fq K) K))
          (bdry_mem _ _ _ _ _ (trueCompat (bdryInf Fq K) φ⁻¹) s) (Hr.sg s)) =
        (Fintype.card Fq : ZMod (l ^ (n + k))) •
          (e : ↥(pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia (trueTau (bdryInf Fq K) φ⁻¹ s)) →
            MonoidAlgebra (ZMod (l ^ (n + k))) Gf) (Hr.sg (trueTau (bdryInf Fq K) φ⁻¹ s)))
    (hall : H2All (ZMod (l ^ (n + k))) (Pi1 (Rfin Fq K) K) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) l (n + k))
    (hallI : ∀ s, H2All (ZMod (l ^ (n + k))) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l (n + k))
    (hall' : H2All (ZMod (l ^ n)) (Pi1 (Rfin Fq K) K) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) l n)
    (hallI' : ∀ s, H2All (ZMod (l ^ n)) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l n)
    (hkv : (Fintype.card Gf).factorization l ≤ k)
    (hρ : ∀ i, IsProj (ρPC (ZMod (l ^ (n + k))) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i))
    (hρ' : ∀ i, IsProj (ρPC (ZMod (l ^ n)) π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia i))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    {m : ℕ} (hm : 0 < m) {r : ℕ} (hmr : m * Fintype.card Gf ∣ r) (hQ : 1 < p ^ (e * r))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq r →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x) :
    LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
        LinearMap.trace (ZMod (l ^ n)) _ (frob1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹
          (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) ^ m) +
        LinearMap.trace (ZMod (l ^ n)) _ (frob2 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))
          (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
          (trueCompat (bdryInf Fq K) φ⁻¹) ^ m) =
      ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ (n + k)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : IsLocalRing (ZMod (l ^ n)) := isLocalRing_zmod_pow l n hl hn
  have hΛ : ((l ^ n : ℕ) : ZMod (l ^ n)) = 0 := ZMod.natCast_self _
  have H := lefschetz_frob_pow π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
    (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) τ hΛ hall' hallI' hπ m hρ'
  refine H.trans ((sum_class_ptCount S (fun u => π (Fu u)) _ (fun γ => ?_) _).trans
    (Finset.sum_congr rfl fun u _ => ?_))
  · exact lefschetz_pow_eq_count π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia φ⁻¹
      (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) (trueCompat (bdryInf Fq K) φ⁻¹) hl n k hall hallI hπ
      hkv hρ m (fun γ => ptCount S (fun u => π (Fu u)) γ) γ
      (euler_eq_count Fq K hq he l (n + k) (by omega) rfl hlq π hπ Hr hφ hTW γ hm hmr hQ Fr hFr ιS S hS Fu hFu)
  · rw [twChar_mk (isEquivariant_id (ρ := τ)), LinearMap.comp_id]

end Main

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Pkg =====
section

/-!
# S4-Lefschetz, L6c: the perfect-complex package of `lefschetz_twist`, discharged

* `zmod_maximalIdeal_eq`, `zmod_l_pow_eq_zero`, `zmod_l_pow_ne_zero`, `charP_residue_zmod`: `ℤ/l^N` is a local ring
  with maximal ideal `(l)`, `l` of nilpotency index exactly `N`, residue characteristic `l`.
* **`lefschetz_pkg`**: `lefschetz_twist` with the residue hypothesis and its Frobenius twist (`exists_resHyp_tw`),
  `H²`-vanishing (`h2All_geo`, `cone_h3_eq_zero`), projectivity (a Sylow subgroup) and freeness/finiteness of the
  complex (`pc_free_finite`) all discharged. Remaining hypotheses: `PicDivU` (level `l`), `PicDivX` (level
  `l^(n+k)`), `π` cut out by a finite unramified `M`, and finiteness of `Z¹(Γ, Λ[Gf])` (`Γ = π₁^geo`, `π₁^geo ⊓ I_s`)
  at the two levels (L6z).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue

section ZModPow

variable (l N : ℕ) [Fact l.Prime]

end ZModPow

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **L6c: the trace formula mod `l^n` on the cone complex, package discharged.** `lefschetz_twist` with all
perfect-complex hypotheses proved, given `Pic(V̄)/l = 0` (`hPicU`), the level-`l^(n+k)` divisibility `hPic`, `π` cut out
by a finite unramified `M`, and finiteness of the cocycle modules `Z¹(Γ, Λ[Gf])` at the levels `l^(n+k)` and `l^n`. -/
def lefschetz_pkg (l n k : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    (hPicU : CdOne.PicDivU (Rfin Fq K) K p l) (hPic : PicDivX (Rfin Fq K) K (Rinf Fq K) p (l ^ (n + k)))
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] [Fintype (ConjClasses Gf)] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    [Module.Finite (ZMod (l ^ (n + k))) (Z1 (regRep (ZMod (l ^ (n + k))) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)))]
    [∀ s, Module.Finite (ZMod (l ^ (n + k)))
      (Z1 (regRep (ZMod (l ^ (n + k))) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s))]
    [Module.Finite (ZMod (l ^ n)) (Z1 (regRep (ZMod (l ^ n)) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)))]
    [∀ s, Module.Finite (ZMod (l ^ n))
      (Z1 (regRep (ZMod (l ^ n)) π) (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s))]
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hkv : (Fintype.card Gf).factorization l ≤ k)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    {m : ℕ} (hm : 0 < m) {r : ℕ} (hmr : m * Fintype.card Gf ∣ r) (hQ : 1 < p ^ (e * r))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq r →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x) :
    LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
        LinearMap.trace (ZMod (l ^ n)) _ (frob1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹
          (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) ^ m) +
        LinearMap.trace (ZMod (l ^ n)) _ (frob2 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))
          (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
          (trueCompat (bdryInf Fq K) φ⁻¹) ^ m) =
      ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹) := by
  classical
  have hl : l.Prime := Fact.out
  have hnk : 0 < n + k := by omega
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ (n + k)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : IsLocalRing (ZMod (l ^ n)) := isLocalRing_zmod_pow l n hl hn
  haveI : IsLocalRing (ZMod (l ^ (n + k))) := isLocalRing_zmod_pow l (n + k) hl hnk
  haveI : CharP (IsLocalRing.ResidueField (ZMod (l ^ n))) l := charP_residue_zmod l n hn
  haveI : CharP (IsLocalRing.ResidueField (ZMod (l ^ (n + k)))) l := charP_residue_zmod l (n + k) hnk
  haveI := nonempty_bdryS (Fq := Fq) (F := K)
  have hl0 : (l : K) ≠ 0 := by
    have h1 := cast_ne_zero_of_not_dvd (F := K) hq he hlq 1
    rwa [pow_one] at h1
  have hΛk : ((l ^ (n + k) : ℕ) : ZMod (l ^ (n + k))) = 0 := ZMod.natCast_self _
  have hΛn : ((l ^ n : ℕ) : ZMod (l ^ n)) = 0 := ZMod.natCast_self _
  obtain ⟨Hr, hTW⟩ := exists_resHyp_tw hq he hl0 (n + k) hPic hM hMU π hπM hπ (bdryInf Fq K)
    (bdryData_B _ _ _ _) hΛk
  have hall := CdOne.h2All_geo (Rfin Fq K) Fq he hq (Kummer.perfect_Rfin Fq K) l (isUnit_cast_Rfin hl0) hPicU
    (ZMod (l ^ (n + k))) (n + k)
  have hallI : ∀ s, H2All (ZMod (l ^ (n + k))) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l (n + k) :=
    fun s => cone_h3_eq_zero hq he hl0 hPicU (bdryInf Fq K) s (ZMod (l ^ (n + k))) (n + k)
  have hall' := CdOne.h2All_geo (Rfin Fq K) Fq he hq (Kummer.perfect_Rfin Fq K) l (isUnit_cast_Rfin hl0) hPicU
    (ZMod (l ^ n)) n
  have hallI' : ∀ s, H2All (ZMod (l ^ n)) (Pi1 (Rfin Fq K) K)
      (pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s) l n :=
    fun s => cone_h3_eq_zero hq he hl0 hPicU (bdryInf Fq K) s (ZMod (l ^ n)) n
  obtain ⟨P⟩ : Nonempty (Sylow l Gf) := inferInstance
  letI : Fintype (P : Subgroup Gf) := Fintype.ofFinite _
  have hρ := isProj_ρPC_of_sylow π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
    (zmod_maximalIdeal_eq l (n + k) hnk) (zmod_l_pow_eq_zero l (n + k)) (fun _ h => zmod_l_pow_ne_zero l (n + k) h)
    hΛk hall hallI hπ (P : Subgroup Gf) P.isPGroup' P.not_dvd_index
  have hρ' := isProj_ρPC_of_sylow π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
    (zmod_maximalIdeal_eq l n hn) (zmod_l_pow_eq_zero l n) (fun _ h => zmod_l_pow_ne_zero l n h)
    hΛn hall' hallI' hπ (P : Subgroup Gf) P.isPGroup' P.not_dvd_index
  have hPCk := pc_free_finite π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
    (zmod_maximalIdeal_eq l (n + k) hnk) (zmod_l_pow_eq_zero l (n + k)) (fun _ h => zmod_l_pow_ne_zero l (n + k) h)
    hΛk hall hallI hπ
  have hPCn := pc_free_finite π (pi1geo (Rfin Fq K) K (Fintype.card Fq)) (bdryInf Fq K).inertia
    (zmod_maximalIdeal_eq l n hn) (zmod_l_pow_eq_zero l n) (fun _ h => zmod_l_pow_ne_zero l n h)
    hΛn hall' hallI' hπ
  haveI := hPCk.1
  haveI := hPCk.2
  haveI := hPCn.1
  haveI := hPCn.2
  exact lefschetz_twist Fq K hq he l n k hn hlq π hπ Hr hφ (hTW φ hφ) hall hallI hall' hallI' hkv hρ hρ' τ hm hmr
    hQ Fr hFr ιS S hS Fu hFu

end Main

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Pkg2 =====
section

/-!
# S4-Lefschetz, L6c': the package with the cocycle finiteness discharged

* **`lefschetz_pkg2`**: `lefschetz_pkg` without the four `Module.Finite (Z¹(Γ, Λ[Gf]))` instance hypotheses
  (`Γ = π₁^geo`, `π₁^geo ⊓ I_s`, levels `l^(n+k)` and `l^n`), supplied by `finite_Z1_regRep_geo` and
  `finite_Z1_regRep_inertia` (L6z). Remaining hypotheses: `PicDivU` (level `l`), `PicDivX` (level `l^(n+k)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **L6c': the trace formula mod `l^n` on the cone complex**, given only `PicDivU` (level `l`) and `PicDivX` (level
`l^(n+k)`) besides the geometric data: `lefschetz_pkg` with the cocycle finiteness of L6z. -/
def lefschetz_pkg2 (l n k : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    (hPicU : CdOne.PicDivU (Rfin Fq K) K p l) (hPic : PicDivX (Rfin Fq K) K (Rinf Fq K) p (l ^ (n + k)))
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] [Fintype (ConjClasses Gf)] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hkv : (Fintype.card Gf).factorization l ≤ k)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    {m : ℕ} (hm : 0 < m) {r : ℕ} (hmr : m * Fintype.card Gf ∣ r) (hQ : 1 < p ^ (e * r))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq r →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x) :
    LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
        LinearMap.trace (ZMod (l ^ n)) _ (frob1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹
          (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) ^ m) +
        LinearMap.trace (ZMod (l ^ n)) _ (frob2 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))
          (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
          (trueCompat (bdryInf Fq K) φ⁻¹) ^ m) =
      ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ (n + k)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI := finite_Z1_regRep_geo Fq K hq he l (n + k) rfl hlq hM hMU π hπM
  haveI := fun s => finite_Z1_regRep_inertia Fq K hq he l (n + k) rfl hlq hM hMU π hπM s
  haveI := finite_Z1_regRep_geo Fq K hq he l n rfl hlq hM hMU π hπM
  haveI := fun s => finite_Z1_regRep_inertia Fq K hq he l n rfl hlq hM hMU π hπM s
  exact lefschetz_pkg Fq K hq he l n k hn hlq hPicU hPic hM hMU π hπM hπ hφ hkv τ hm hmr hQ Fr hFr ιS S hS Fu hFu

end Main

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Main =====
section

/-!
# S4-Lefschetz, L6e: the trace formula mod `l^n`, with `Pic` divisibility discharged

* **`lefschetz_main`**: `lefschetz_pkg2` with `hPicU := picDivU` (L6e4) and `hPic := picDivX` (L6e5): for a function
  field `K / 𝔽_q` with full constant field, `l ∤ q`, a finite quotient `π : π₁ → Gf` cut out by `Mf ⊆ K_U` and a free
  `ℤ/l^n`-representation `τ` of `Gf`, the Lefschetz identity of the cone complex holds with no further hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a PerfectCx Representation HattoriStallings Residue

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **L6e: the trace formula mod `l^n` on the cone complex**, unconditional on `Pic`: `lefschetz_pkg2` with the
divisibility hypotheses discharged by `picDivU` and `picDivX` (`l ∤ q`). -/
theorem lefschetz_main (l n k : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    [Fintype (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    [DecidableEq (BdryS (Rfin Fq K) K (Fintype.card Fq) (Rinf Fq K))]
    {Mf : IntermediateField K (AlgebraicClosure K)} (hM : Mf ∈ unramSet (Rfin Fq K) K)
    (hMU : Mf ≤ maxUnram (Rfin Fq K) K)
    {Gf : Type} [Group Gf] [Fintype Gf] [Fintype (ConjClasses Gf)] (π : Pi1 (Rfin Fq K) K →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Rfin Fq K) K)))
    [Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Rfin Fq K) K (Fintype.card Fq) ⊓ (bdryInf Fq K).inertia s).map π)]
    {φ : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
    (hkv : (Fintype.card Gf).factorization l ≤ k)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    {m : ℕ} (hm : 0 < m) {r : ℕ} (hmr : m * Fintype.card Gf ∣ r) (hQ : 1 < p ^ (e * r))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (ιS : kStar (Rfin Fq K) K hq r →+* Ω) (S : Finset (Rfin Fq K →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (u.comp (algebraMap Fq (Rfin Fq K)) = ιS.comp (algebraMap Fq (kStar (Rfin Fq K) K hq r)) ∧
      Fr.comp u = u))
    (Fu : (Rfin Fq K →+* Ω) → Pi1 (Rfin Fq K) K)
    (hFu : ∀ u ∈ S, ∃ w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω,
      w.comp (algebraMap (Rfin Fq K) _) = u ∧ (∀ b, w (Fu u • b) = Fr (w b)) ∧
        ∀ x, w (incStar (Rfin Fq K) K hq r hQ x) = ιS x) :
    LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
        LinearMap.trace (ZMod (l ^ n)) _ (frob1 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq)) φ⁻¹
          (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹) ^ m) +
        LinearMap.trace (ZMod (l ^ n)) _ (frob2 (τ.comp π) (pi1geo (Rfin Fq K) K (Fintype.card Fq))
          (bdryInf Fq K).inertia φ⁻¹ (trueTau (bdryInf Fq K) φ⁻¹) (trueH (bdryInf Fq K) φ⁻¹)
          (trueCompat (bdryInf Fq K) φ⁻¹) ^ m) =
      ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹) :=
  lefschetz_pkg2 Fq K hq he l n k hn hlq (picDivU Fq K l hlq) (picDivX Fq K l hlq (n + k)) hM hMU π hπM hπ hφ hkv τ hm
    hmr hQ Fr hFr ιS S hS Fu hFu

end Main

end

end Lefschetz
end RamanujanPetersson


end


