-- Prove2me | Definitions.Def_RPLib_F2_041
-- name    : RPLib_F2_041
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T14:13:30.195338+00:00
-- url     : https://prove2.me/theorems/587abe7a-de74-4928-b2ee-49f71d6e939d
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 041 of 70
-- statement:
--   File 041 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_ClassCount`: S4-Lefschetz L2b: class traces of `F^m` from twisted counts
--   * `S4.Def_RP_Lefschetz_PtTorsor`: S4-Lefschetz, L5a: points of an unramified Galois cover form a torsor
--   * `S4.Def_RP_Lefschetz_PtExt`: S4-Lefschetz, L5b (part 1): points extend along integral extensions
--   * `S4.Def_RP_Lefschetz_PtCount`: S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover
--   * `S4.Def_RP_Lefschetz_PtFix`: S4-Lefschetz, L5c1: generic point-count bookkeeping
--   * `S4.Def_RP_Lefschetz_PtBlk`: S4-Lefschetz, L5c2: the block point count (generic)
--   * `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
--   * `S4.Def_RP_Lefschetz_PtCov`: S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points
--   * `S4.Def_RP_Lefschetz_PtLift`: S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers
--   * `S4.Def_RP_Lefschetz_PtE`: S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count
--   * `S4.Def_RP_Lefschetz_PtAsm`: S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`
--   * `S4.Def_RP_Lefschetz_PtSum`: S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_039

/-!
# Ramanujan-Petersson curve library (flat edition), file 041 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_ClassCount`: S4-Lefschetz L2b: class traces of `F^m` from twisted counts
* `S4.Def_RP_Lefschetz_PtTorsor`: S4-Lefschetz, L5a: points of an unramified Galois cover form a torsor
* `S4.Def_RP_Lefschetz_PtExt`: S4-Lefschetz, L5b (part 1): points extend along integral extensions
* `S4.Def_RP_Lefschetz_PtCount`: S4-Lefschetz, L5b: counting Frobenius-fixed points of an intermediate cover
* `S4.Def_RP_Lefschetz_PtFix`: S4-Lefschetz, L5c1: generic point-count bookkeeping
* `S4.Def_RP_Lefschetz_PtBlk`: S4-Lefschetz, L5c2: the block point count (generic)
* `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
* `S4.Def_RP_Lefschetz_PtCov`: S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points
* `S4.Def_RP_Lefschetz_PtLift`: S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers
* `S4.Def_RP_Lefschetz_PtE`: S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count
* `S4.Def_RP_Lefschetz_PtAsm`: S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`
* `S4.Def_RP_Lefschetz_PtSum`: S4-Lefschetz, L5c5: the alternating trace of `γ⁻¹ ∘ F^m` is `|Z(γ)|` times a point count
-/

set_option autoImplicit false

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

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct PerfectCx

noncomputable section

section Red

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ'))
  (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ}
  (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G)) [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (m : ℕ)

include hsurj ht hk in
theorem hs_red0p [Module.Free Λ (MonoidAlgebra Λ Gf)] [Module.Finite Λ (MonoidAlgebra Λ Gf)]
    [Module.Free Λ' (MonoidAlgebra Λ' Gf)] [Module.Finite Λ' (MonoidAlgebra Λ' Gf)] (hρ : IsProj (rRep Λ Gf))
    (c : ConjClasses Gf) :
    hs (rRep Λ' Gf) (regRep Λ' π ψ ^ m) c = algebraMap Λ Λ' (hs (rRep Λ Gf) (regRep Λ π ψ ^ m) c) :=
  hs_red_of ϖ hsurj ht hρ
    (isEquivariant_pow (show IsEquivariant (rRep Λ Gf) (rRep Λ Gf) (regRep Λ π ψ) from
      fun x => LinearMap.ext fun a => (mulRight_regRep π (single x⁻¹ 1) ψ a).symm) m)
    _ (redA Λ Λ' Gf) (redA_surjective hsurj) (redA_ker hk) (fun x a => redA_rRep x a)
    (intertwine_pow' _ (fun a => redA_regRep π ψ a) m) c

include hsurj ht hk hΛ hall hπ in
theorem hs_red1p [Module.Free Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))]
    [Module.Finite Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))]
    [Module.Free Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf))]
    [Module.Finite Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf))] (hρ : IsProj (rho1 Λ π Γ S))
    (c : ConjClasses Gf) :
    hs (rho1 Λ' π Γ S) (frob1 (regRep Λ' π) Γ ψ t h ^ m) c =
      algebraMap Λ Λ' (hs (rho1 Λ π Γ S) (frob1 (regRep Λ π) Γ ψ t h ^ m) c) :=
  hs_red_of ϖ hsurj ht hρ (isEquivariant_pow (frob1_equiv (Λ := Λ) (π := π) (Γ := Γ) (ψ := ψ) (t := t) (h := h)) m) _
    (red1 Λ Λ' π Γ) (red1_surjective π Γ hsurj hΛ hall hπ) (red1_ker π Γ hk hΛ hall hπ) (red1_rho1 π Γ)
    (intertwine_pow' _ (red1_frob π Γ ψ t h) m) c

include hsurj ht hk hΛ hallI hπ in
theorem hs_red2p [Module.Free Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))]
    [Module.Finite Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))]
    [Module.Free Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s))]
    [Module.Finite Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s))] (hρ : IsProj (rho2 Λ π Γ I))
    (c : ConjClasses Gf) :
    hs (rho2 Λ' π Γ I) (frob2 (regRep Λ' π) Γ I ψ t h hI ^ m) c =
      algebraMap Λ Λ' (hs (rho2 Λ π Γ I) (frob2 (regRep Λ π) Γ I ψ t h hI ^ m) c) :=
  hs_red_of ϖ hsurj ht hρ
    (isEquivariant_pow (frob2_equiv (Λ := Λ) (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) hI) m) _
    (red2 Λ Λ' π Γ I) (red2_surjective π Γ I hsurj hΛ hallI hπ) (red2_ker π Γ I hk hΛ hallI hπ)
    (red2_rho2 π Γ I) (intertwine_pow' _ (red2_frob π Γ I ψ t h hI) m) c

include hsurj ht hk hΛ hall hallI hπ in
/-- **Mod `ϖ` compatibility of the Lefschetz numbers of the powers of the Frobenius.** -/
theorem lefschetz_frob_pow_red [hF : ∀ i, Module.Free Λ (PC Λ π Γ I i)] [hT : ∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    [hF' : ∀ i, Module.Free Λ' (PC Λ' π Γ I i)] [hT' : ∀ i, Module.Finite Λ' (PC Λ' π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC Λ π Γ I i)) (c : ConjClasses Gf) :
    lefschetz (ρPC Λ' π Γ I) 2 (fun i => frobPC Λ' π Γ I ψ t h hI i ^ m) c =
      algebraMap Λ Λ' (lefschetz (ρPC Λ π Γ I) 2 (fun i => frobPC Λ π Γ I ψ t h hI i ^ m) c) := by
  have key : ∀ i ∈ Finset.range (2 + 1), hs (ρPC Λ' π Γ I i) (frobPC Λ' π Γ I ψ t h hI i ^ m) c =
      algebraMap Λ Λ' (hs (ρPC Λ π Γ I i) (frobPC Λ π Γ I ψ t h hI i ^ m) c) := by
    intro i hi
    match i, hi with
    | 0, _ =>
      have : Module.Free Λ (MonoidAlgebra Λ Gf) := hF 0
      have : Module.Finite Λ (MonoidAlgebra Λ Gf) := hT 0
      have : Module.Free Λ' (MonoidAlgebra Λ' Gf) := hF' 0
      have : Module.Finite Λ' (MonoidAlgebra Λ' Gf) := hT' 0
      exact hs_red0p π hsurj ht hk ψ m (hρ 0) c
    | 1, _ =>
      have : Module.Free Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) := hF 1
      have : Module.Finite Λ (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) := hT 1
      have : Module.Free Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) := hF' 1
      have : Module.Finite Λ' (Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf)) := hT' 1
      exact hs_red1p π Γ hsurj ht hk hΛ hall hπ ψ t h m (hρ 1) c
    | 2, _ =>
      have : Module.Free Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) := hF 2
      have : Module.Finite Λ ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) := hT 2
      have : Module.Free Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) := hF' 2
      have : Module.Finite Λ' ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) := hT' 2
      exact hs_red2p π Γ I hsurj ht hk hΛ hallI hπ ψ t h hI m (hρ 2) c
    | k + 3, hk3 => exact absurd (Finset.mem_range.1 hk3) (by omega)
  simp only [lefschetz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_pow, map_neg,
    map_one]
  exact Finset.sum_congr rfl fun i hi => by rw [key i hi]

end Red

section Count

variable {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ)
  (hI : BdryCompat Γ I ψ t h) {l : ℕ} (hl : l.Prime) (n k : ℕ)
  (hall : H2All (ZMod (l ^ (n + k))) G Γ l (n + k)) (hallI : ∀ s, H2All (ZMod (l ^ (n + k))) G (Γ ⊓ I s) l (n + k))
  (hπ : IsOpen (π.ker : Set G))

include hl hall hallI hπ in
/-- **Class traces of `F^m` from twisted counts.** If at level `l^(n+k)`, with `l^k` killing the `l`-part of `|Gf|`,
`Σ (-1)^i Tr(γ⁻¹ ∘ F^m | PC^i) = |Z(γ)| · N_γ`, then `L(F^m)[γ] = N_γ` at level `l^n`. -/
theorem lefschetz_pow_eq_count (hkv : (Fintype.card Gf).factorization l ≤ k)
    [∀ i, Module.Free (ZMod (l ^ (n + k))) (PC (ZMod (l ^ (n + k))) π Γ I i)]
    [∀ i, Module.Finite (ZMod (l ^ (n + k))) (PC (ZMod (l ^ (n + k))) π Γ I i)]
    [∀ i, Module.Free (ZMod (l ^ n)) (PC (ZMod (l ^ n)) π Γ I i)]
    [∀ i, Module.Finite (ZMod (l ^ n)) (PC (ZMod (l ^ n)) π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC (ZMod (l ^ (n + k))) π Γ I i)) (m : ℕ) (Nc : Gf → ℕ) (γ : Gf)
    (hcount : ∑ i ∈ Finset.range (2 + 1), (-1 : ZMod (l ^ (n + k))) ^ i *
        LinearMap.trace _ _ (ρPC (ZMod (l ^ (n + k))) π Γ I i γ⁻¹ ∘ₗ
          frobPC (ZMod (l ^ (n + k))) π Γ I ψ t h hI i ^ m) =
      (Nat.card {z : Gf // z⁻¹ * γ * z = γ} : ZMod (l ^ (n + k))) * Nc γ) :
    lefschetz (ρPC (ZMod (l ^ n)) π Γ I) 2 (fun i => frobPC (ZMod (l ^ n)) π Γ I ψ t h hI i ^ m)
      (ConjClasses.mk γ) = Nc γ := by
  have : NeZero (l ^ (n + k)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  let _ : Algebra (ZMod (l ^ (n + k))) (ZMod (l ^ n)) := ZMod.algebra' (ZMod (l ^ n)) (l ^ n) (lvl_dvd l n k)
  have hsurj : Function.Surjective (algebraMap (ZMod (l ^ (n + k))) (ZMod (l ^ n))) := ZMod.ringHom_surjective _
  have ht : algebraMap (ZMod (l ^ (n + k))) (ZMod (l ^ n)) ((l ^ n : ℕ) : ZMod (l ^ (n + k))) = 0 := by
    rw [map_natCast, ZMod.natCast_self]
  have hk : ∀ r, algebraMap (ZMod (l ^ (n + k))) (ZMod (l ^ n)) r = 0 →
      ∃ s, r = ((l ^ n : ℕ) : ZMod (l ^ (n + k))) * s := by
    intro r hr
    rw [← ZMod.natCast_zmod_val r, map_natCast, ZMod.natCast_eq_zero_iff] at hr
    obtain ⟨b, hb⟩ := hr
    exact ⟨b, by rw [← Nat.cast_mul, ← hb, ZMod.natCast_zmod_val]⟩
  have hΛ : ((l ^ (n + k) : ℕ) : ZMod (l ^ (n + k))) = 0 := ZMod.natCast_self _
  have hred := lefschetz_frob_pow_red π Γ I hsurj ht hk hΛ hall hallI hπ ψ t h hI m hρ (ConjClasses.mk γ)
  have H := lefschetz_trace_inv_comp hρ (fun i => isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI i) m) 2 γ
  have H2 := hcount.symm.trans H
  have hZ0 : Nat.card {z : Gf // z⁻¹ * γ * z = γ} ≠ 0 := Nat.card_ne_zero.2 ⟨⟨⟨1, by simp⟩⟩, inferInstance⟩
  have hZv : (Nat.card {z : Gf // z⁻¹ * γ * z = γ}).factorization l ≤ k :=
    le_trans ((Nat.factorization_le_iff_dvd hZ0 Fintype.card_ne_zero).2 (card_centralizer_dvd γ) l) hkv
  have hc := cast_eq_of_mul_eq' hl n k _ hZ0 hZv _ _ H2
  exact hred.trans (hc.symm.trans (map_natCast _ _))

end Count

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

/-- In a finite field `κ`, every image `ι' x` of a ring hom `ι' : κ → Ω` lies in the image of any other ring hom
`ι : κ → Ω`. -/
theorem mem_range_of_finite {κ : Type} [Field κ] [Fintype κ] (ι ι' : κ →+* Ω) (x : κ) :
    ∃ z, ι z = ι' x := by
  classical
  have hmon : (X ^ Fintype.card κ - X : κ[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast Fintype.one_lt_card)
  have hroots := FiniteField.roots_X_pow_card_sub_X κ
  have hdeg : (X ^ Fintype.card κ - X : κ[X]).natDegree = Fintype.card κ :=
    FiniteField.X_pow_card_sub_X_natDegree_eq κ Fintype.one_lt_card
  have hprod : (Finset.univ.val.map fun a : κ => X - C a).prod = (X ^ Fintype.card κ - X : κ[X]) := by
    rw [← hroots]
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by rw [hroots, hdeg]; rfl)
  have hprod' : ∏ a : κ, (X - C a) = (X ^ Fintype.card κ - X : κ[X]) := hprod
  have hev := congrArg (fun f => eval (ι' x) (f.map ι)) hprod'
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_prod, eval_sub,
    eval_pow, eval_X, eval_C] at hev
  have hx : ι' x ^ Fintype.card κ - ι' x = 0 := by rw [← map_pow, FiniteField.pow_card, sub_self]
  rw [hx, Finset.prod_eq_zero_iff] at hev
  obtain ⟨z, -, hz⟩ := hev
  exact ⟨z, (sub_eq_zero.1 hz).symm⟩

variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]

/-- **Transitivity**: two ring homs `B → Ω` agreeing on `A` differ by an element of `G` (finite residue ring). -/
theorem hom_smul_trans (w w' : B →+* Ω) (hww : w.comp (algebraMap A B) = w'.comp (algebraMap A B))
    [Finite (B ⧸ RingHom.ker w')] : ∃ g : G, ∀ b, w' b = w (g • b) := by
  classical
  have hQ : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
  have hQ' : (RingHom.ker w').IsPrime := RingHom.ker_isPrime w'
  have hww' : ∀ a : A, w (algebraMap A B a) = w' (algebraMap A B a) := fun a => RingHom.congr_fun hww a
  have hund : (RingHom.ker w).under A = (RingHom.ker w').under A := by
    ext a
    show w (algebraMap A B a) = 0 ↔ w' (algebraMap A B a) = 0
    rw [hww']
  obtain ⟨g0, hg0⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G (RingHom.ker w) (RingHom.ker w') hund
  -- `w'' = w ∘ g0⁻¹` has kernel `ker w'`
  let w'' : B →+* Ω := w.comp (MulSemiringAction.toRingHom G B g0⁻¹)
  have hw'' : ∀ b, w'' b = w (g0⁻¹ • b) := fun b => rfl
  have hker : ∀ b, b ∈ RingHom.ker w' → w'' b = 0 := by
    intro b hb
    rw [hg0, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
    rw [hw'']
    exact hb
  -- the residue field `κ = B ⧸ ker w'` and the two embeddings
  let P : Ideal A := (RingHom.ker w').under A
  have : (RingHom.ker w').LiesOver P := ⟨rfl⟩
  have : IsDomain (B ⧸ RingHom.ker w') := Ideal.Quotient.isDomain _
  letI : Field (B ⧸ RingHom.ker w') := (Finite.isField_of_domain (B ⧸ RingHom.ker w')).toField
  letI : Fintype (B ⧸ RingHom.ker w') := Fintype.ofFinite _
  let ι' : B ⧸ RingHom.ker w' →+* Ω := Ideal.Quotient.lift (RingHom.ker w') w' fun b hb => RingHom.mem_ker.1 hb
  let ι'' : B ⧸ RingHom.ker w' →+* Ω := Ideal.Quotient.lift (RingHom.ker w') w'' hker
  have hι'' : Function.Injective ι'' := ι''.injective
  have hι' : Function.Injective ι' := ι'.injective
  choose τ0 hτ0 using mem_range_of_finite ι'' ι'
  let τr : (B ⧸ RingHom.ker w') →+* (B ⧸ RingHom.ker w') :=
    { toFun := τ0
      map_one' := hι'' (by rw [hτ0, map_one, map_one])
      map_mul' := fun x y => hι'' (by rw [hτ0, map_mul, map_mul, hτ0, hτ0])
      map_zero' := hι'' (by rw [hτ0, map_zero, map_zero])
      map_add' := fun x y => hι'' (by rw [hτ0, map_add, map_add, hτ0, hτ0]) }
  have hτr : ∀ x, ι'' (τr x) = ι' x := hτ0
  let τa : (B ⧸ RingHom.ker w') →ₐ[A ⧸ P] (B ⧸ RingHom.ker w') :=
    { τr with
      commutes' := by
        intro r
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        refine hι'' ?_
        show ι'' (τr (Ideal.Quotient.mk _ (algebraMap A B a))) = ι'' (Ideal.Quotient.mk _ (algebraMap A B a))
        rw [hτr]
        show w' (algebraMap A B a) = w (g0⁻¹ • algebraMap A B a)
        rw [smul_algebraMap, hww'] }
  have hτinj : Function.Injective τa := fun x y hxy =>
    hι' (by rw [← hτr, ← hτr]; exact congrArg ι'' hxy)
  let τ : (B ⧸ RingHom.ker w') ≃ₐ[A ⧸ P] (B ⧸ RingHom.ker w') :=
    AlgEquiv.ofBijective τa ⟨hτinj, Finite.injective_iff_surjective.1 hτinj⟩
  obtain ⟨⟨g1, hg1⟩, hτ⟩ := Ideal.Quotient.stabilizerHom_surjective G P (RingHom.ker w') τ
  refine ⟨g0⁻¹ * g1, fun b => ?_⟩
  have h1 : τ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (g1 • b) := by
    rw [← hτ]
    rfl
  have h2 : ι' (Ideal.Quotient.mk _ b) = ι'' (τa (Ideal.Quotient.mk _ b)) := (hτr _).symm
  calc w' b = ι' (Ideal.Quotient.mk _ b) := rfl
    _ = ι'' (τ (Ideal.Quotient.mk _ b)) := h2
    _ = ι'' (Ideal.Quotient.mk _ (g1 • b)) := by rw [h1]
    _ = w ((g0⁻¹ * g1) • b) := by rw [mul_smul]; rfl

end PtTorsor

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtExt =====
section

/-!
# S4-Lefschetz, L5b (part 1): points extend along integral extensions

`exists_hom_extend`: for an injective integral `C → B` and an algebraically closed field `Ω`, every ring hom
`v : C → Ω` extends to `w : B → Ω` (lying over + `IsAlgClosed.lift` on the residue rings).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtExt

/-- **Extension of points** along an injective integral extension, into an algebraically closed field. -/
theorem exists_hom_extend {C B Ω : Type} [CommRing C] [CommRing B] [Algebra C B] [Algebra.IsIntegral C B]
    [FaithfulSMul C B] [Field Ω] [IsAlgClosed Ω] (v : C →+* Ω) :
    ∃ w : B →+* Ω, w.comp (algebraMap C B) = v := by
  classical
  have hP : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker v) (⊥ : Ideal B)
    (Ideal.comap_bot_le_of_injective _ (FaithfulSMul.algebraMap_injective C B))
  have : Q.LiesOver (RingHom.ker v) := ⟨hQP.symm⟩
  have : IsDomain (C ⧸ RingHom.ker v) := Ideal.Quotient.isDomain _
  have : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  let vb : C ⧸ RingHom.ker v →+* Ω := Ideal.Quotient.lift _ v fun c hc => RingHom.mem_ker.1 hc
  have hvb : Function.Injective vb := by
    refine (injective_iff_map_eq_zero vb).2 fun x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 hx)
  letI : Algebra (C ⧸ RingHom.ker v) Ω := vb.toAlgebra
  have : Module.IsTorsionFree (C ⧸ RingHom.ker v) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hvb
  have hinj : Function.Injective (algebraMap (C ⧸ RingHom.ker v) (B ⧸ Q)) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk Q (algebraMap C B c) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [← hQP]
    exact hx
  have : Module.IsTorsionFree (C ⧸ RingHom.ker v) (B ⧸ Q) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have : Algebra.IsIntegral (C ⧸ RingHom.ker v) (B ⧸ Q) := inferInstance
  have : Algebra.IsAlgebraic (C ⧸ RingHom.ker v) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (B ⧸ Q) →ₐ[C ⧸ RingHom.ker v] Ω := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun c => ?_⟩
  show ψ (algebraMap (C ⧸ RingHom.ker v) (B ⧸ Q) (Ideal.Quotient.mk _ c)) = v c
  rw [ψ.commutes]
  rfl

end PtExt

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

/-- **Counting by fibers**: if `f` maps `{x | P x}` onto `{t | Q t}` with fibers the right cosets `x H`, then
`#{x | P x} = #{t | Q t} * |H|`. -/
theorem pt_card_eq_mul {G X : Type} [Group G] (H : Subgroup G) (P : G → Prop) (Q : X → Prop) (f : G → X)
    (hfib : ∀ x0 x, P x0 → (f x = f x0 ↔ x0⁻¹ * x ∈ H)) (hPH : ∀ x h, P x → h ∈ H → P (x * h))
    (hsurj : ∀ t, Q t → ∃ x, P x ∧ f x = t) (hPQ : ∀ x, P x → Q (f x)) :
    Nat.card {x : G // P x} = Nat.card {t : X // Q t} * Nat.card H := by
  classical
  have hsurj' : ∀ t, ∃ x, Q t → P x ∧ f x = t := by
    intro t
    by_cases hq : Q t
    · obtain ⟨x, hx⟩ := hsurj t hq
      exact ⟨x, fun _ => hx⟩
    · exact ⟨1, fun h => absurd h hq⟩
  choose sec hsec using hsurj'
  let e : {x : G // P x} ≃ {t : X // Q t} × H :=
    { toFun := fun x => (⟨f x.1, hPQ x.1 x.2⟩,
        ⟨(sec (f x.1))⁻¹ * x.1, (hfib _ x.1 (hsec _ (hPQ x.1 x.2)).1).1 (hsec _ (hPQ x.1 x.2)).2.symm⟩)
      invFun := fun p => ⟨sec p.1.1 * p.2, hPH _ _ (hsec _ p.1.2).1 p.2.2⟩
      left_inv := fun x => Subtype.ext (by
        show sec (f x.1) * ((sec (f x.1))⁻¹ * x.1) = x.1
        exact mul_inv_cancel_left _ _)
      right_inv := fun p => by
        have hf : f (sec p.1.1 * p.2) = p.1.1 :=
          ((hfib _ _ (hsec _ p.1.2).1).2 (by rw [inv_mul_cancel_left]; exact p.2.2)).trans (hsec _ p.1.2).2
        refine Prod.ext (Subtype.ext hf) (Subtype.ext ?_)
        show (sec (f (sec p.1.1 * p.2)))⁻¹ * (sec p.1.1 * p.2) = p.2
        rw [hf, inv_mul_cancel_left] }
  rw [Nat.card_congr e, Nat.card_prod]

end PtCountGen

section PtCount

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]

variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

/-- **Fibers of restriction** are the cosets `x0 H`. -/
theorem ptRes_eq_iff (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) (u : A →+* Ω)
    (hfin : ∀ w : B →+* Ω, w.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w))
    (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u) (x x0 : G) :
    ptRes C w0 x = ptRes C w0 x0 ↔ x0⁻¹ * x ∈ H := by
  constructor
  · intro hxx
    have hover : (w0.comp (MulSemiringAction.toRingHom G B x)).comp (algebraMap A B) = u := by
      refine RingHom.ext fun a => ?_
      show w0 (x • algebraMap A B a) = u a
      rw [smul_algebraMap]
      exact RingHom.congr_fun hw0 a
    haveI := hfin _ hover
    obtain ⟨h, hh⟩ := hom_smul_trans (A := C) (G := H) (w0.comp (MulSemiringAction.toRingHom G B x0))
      (w0.comp (MulSemiringAction.toRingHom G B x)) hxx.symm
    have hx : x = x0 * h := pt_smul_eq hun w0 fun b => by
      rw [mul_smul]
      exact hh b
    rw [hx, inv_mul_cancel_left]
    exact h.2
  · intro hmem
    refine RingHom.ext fun c => ?_
    show w0 (x • algebraMap C B c) = w0 (x0 • algebraMap C B c)
    have hfix : (x0⁻¹ * x) • algebraMap C B c = algebraMap C B c := smul_algebraMap (⟨x0⁻¹ * x, hmem⟩ : H) c
    calc w0 (x • algebraMap C B c) = w0 (x0 • (x0⁻¹ * x) • algebraMap C B c) := by
          rw [← mul_smul, mul_inv_cancel_left]
      _ = w0 (x0 • algebraMap C B c) := by rw [hfix]

end PtCount

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtFix =====
section

/-!
# S4-Lefschetz, L5c1: generic point-count bookkeeping

* `card_algHom_eq_fixed`: `k`-points of a `k`-algebra `R` (`k` finite, `|k| = Q`) are the `Ω`-points `v` of `R`
  with `v ∘ (k → R) = ι` and `v ^ Q = v`.
* `card_fixed_ptRes_pred`: `card_fixed_ptRes` with an extra condition `Rp` on the points (constant on fibers),
  and `finite_fixed_ptRes_pred` (the counted points form a finite set).
* `card_eq_sum_fiber`: counting a set of points by their restrictions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtFixGen

/-- Every `z` with `z ^ |k| = z` lies in the image of a ring hom `ι : k → Ω` (`k` finite). -/
theorem mem_range_of_pow_card_pt {k Ω : Type} [Field k] [Fintype k] [Field Ω] (ι : k →+* Ω) {z : Ω}
    (hz : z ^ Fintype.card k = z) : ∃ c, ι c = z := by
  classical
  have hmon : (X ^ Fintype.card k - X : k[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast Fintype.one_lt_card)
  have hroots := FiniteField.roots_X_pow_card_sub_X k
  have hdeg : (X ^ Fintype.card k - X : k[X]).natDegree = Fintype.card k :=
    FiniteField.X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card
  have hprod : (Finset.univ.val.map fun a : k => X - C a).prod = (X ^ Fintype.card k - X : k[X]) := by
    rw [← hroots]
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by rw [hroots, hdeg]; rfl)
  have hprod' : ∏ a : k, (X - C a) = (X ^ Fintype.card k - X : k[X]) := hprod
  have hev := congrArg (fun f => eval z (f.map ι)) hprod'
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_prod, eval_sub,
    eval_pow, eval_X, eval_C] at hev
  have hx : z ^ Fintype.card k - z = 0 := by rw [hz, sub_self]
  rw [hx, Finset.prod_eq_zero_iff] at hev
  obtain ⟨c, -, hc⟩ := hev
  exact ⟨c, (sub_eq_zero.1 hc).symm⟩

/-- **`k`-points as `Fr_Q`-fixed `Ω`-points.** -/
theorem card_algHom_eq_fixed {k R Ω : Type} [Field k] [Fintype k] [CommRing R] [Algebra k R] [Field Ω]
    (ι : k →+* Ω) :
    Nat.card (R →ₐ[k] k) =
      Nat.card {v : R →+* Ω // v.comp (algebraMap k R) = ι ∧ ∀ r, v r ^ Fintype.card k = v r} := by
  classical
  have hι : Function.Injective ι := ι.injective
  let Φ : (R →ₐ[k] k) →
      {v : R →+* Ω // v.comp (algebraMap k R) = ι ∧ ∀ r, v r ^ Fintype.card k = v r} :=
    fun f => ⟨ι.comp f.toRingHom,
      RingHom.ext fun a => by
        show ι (f (algebraMap k R a)) = ι a
        exact congrArg ι (f.commutes a),
      fun r => by
        show ι (f r) ^ Fintype.card k = ι (f r)
        rw [← map_pow, FiniteField.pow_card]⟩
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨fun f f' h => ?_, fun v => ?_⟩)
  · ext r
    exact hι (RingHom.congr_fun (congrArg Subtype.val h) r)
  · choose c hc using fun r => mem_range_of_pow_card_pt ι (v.2.2 r)
    refine ⟨{ toFun := c
              map_one' := hι (by rw [hc, map_one, map_one])
              map_mul' := fun x y => hι (by rw [hc, map_mul, map_mul, hc, hc])
              map_zero' := hι (by rw [hc, map_zero, map_zero])
              map_add' := fun x y => hι (by rw [hc, map_add, map_add, hc, hc])
              commutes' := fun a => hι (by rw [hc]; exact RingHom.congr_fun v.2.1 a) }, ?_⟩
    exact Subtype.ext (RingHom.ext fun r => hc r)

/-- **Counting by restrictions.** -/
theorem card_eq_sum_fiber {V U : Type} (res : V → U) (P : V → Prop) (s : Finset U)
    (hs : ∀ v, P v → res v ∈ s) [∀ u, Finite {v // res v = u ∧ P v}] :
    Nat.card {v // P v} = ∑ u ∈ s, Nat.card {v // res v = u ∧ P v} := by
  classical
  let e : {v // P v} ≃ Σ u : s, {v // res v = u ∧ P v} :=
    { toFun := fun v => ⟨⟨res v.1, hs v.1 v.2⟩, ⟨v.1, rfl, v.2⟩⟩
      invFun := fun p => ⟨p.2.1, p.2.2.2⟩
      left_inv := fun v => rfl
      right_inv := by
        rintro ⟨⟨u, hu⟩, ⟨v, hvu, hv⟩⟩
        have e : res v = u := hvu
        subst e
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_coe_sort s (fun u => Nat.card {v // res v = u ∧ P v})

end PtFixGen

section PtFix

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]
variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

/-- Restrictions of translates by `x` with `x⁻¹ F x ∈ H` are `Fr`-fixed points over `u`. -/
theorem ptRes_mem (Fr : Ω →+* Ω) (u : A →+* Ω) (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u) (F : G)
    (hF : ∀ b, Fr (w0 b) = w0 (F • b)) {x : G} (hx : x⁻¹ * F * x ∈ H) :
    (ptRes C w0 x).comp (algebraMap A C) = u ∧ Fr.comp (ptRes C w0 x) = ptRes C w0 x := by
  refine ⟨?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    show w0 (x • algebraMap C B (algebraMap A C a)) = u a
    rw [← IsScalarTower.algebraMap_apply, smul_algebraMap]
    exact RingHom.congr_fun hw0 a
  · refine RingHom.ext fun c => ?_
    show Fr (w0 (x • algebraMap C B c)) = w0 (x • algebraMap C B c)
    have hfix : (x⁻¹ * F * x) • algebraMap C B c = algebraMap C B c :=
      smul_algebraMap (⟨x⁻¹ * F * x, hx⟩ : H) c
    have hFx : F * x = x * (x⁻¹ * F * x) := by group
    rw [hF, ← mul_smul, hFx, mul_smul, hfix]

/-- Every `Fr`-fixed point of `C` over `u` is the restriction of a translate `w0 ∘ x` with `x⁻¹ F x ∈ H`. -/
theorem ptRes_surj (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) [IsAlgClosed Ω] [FaithfulSMul C B]
    (Fr : Ω →+* Ω) (u : A →+* Ω)
    (hfin : ∀ w : B →+* Ω, w.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w))
    (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u) (F : G) (hF : ∀ b, Fr (w0 b) = w0 (F • b))
    (v : C →+* Ω) (hvu : v.comp (algebraMap A C) = u) (hvF : Fr.comp v = v) :
    ∃ x : G, x⁻¹ * F * x ∈ H ∧ ptRes C w0 x = v := by
  have : Algebra.IsIntegral C B := Algebra.IsInvariant.isIntegral C B H
  obtain ⟨w, hw⟩ := exists_hom_extend (B := B) v
  have hwu : w.comp (algebraMap A B) = u := by
    rw [IsScalarTower.algebraMap_eq A C B, ← RingHom.comp_assoc, hw, hvu]
  have := hfin w hwu
  obtain ⟨x, hx⟩ := hom_smul_trans (A := A) (G := G) w0 w (hw0.trans hwu.symm)
  have hFu : (Fr.comp w).comp (algebraMap A B) = u := by
    rw [RingHom.comp_assoc, hwu, ← hvu, ← RingHom.comp_assoc, hvF]
  have := hfin (Fr.comp w) hFu
  have hwC : w.comp (algebraMap C B) = (Fr.comp w).comp (algebraMap C B) := by
    rw [RingHom.comp_assoc, hw, hvF]
  obtain ⟨h, hh⟩ := hom_smul_trans (A := C) (G := H) w (Fr.comp w) hwC
  have hFx : F * x = x * h := pt_smul_eq hun w0 fun b => by
    rw [mul_smul, mul_smul, ← hF, ← hx, ← hx]
    exact hh b
  refine ⟨x, ?_, ?_⟩
  · have e : x⁻¹ * F * x = h := by rw [mul_assoc, hFx, inv_mul_cancel_left]
    rw [e]
    exact h.2
  · refine RingHom.ext fun c => ?_
    show w0 (x • algebraMap C B c) = v c
    rw [← hx]
    exact RingHom.congr_fun hw c

include H in
/-- The `Fr`-fixed points over `u` (with a condition `Rp`) form a finite set. -/
theorem finite_fixed_ptRes_pred (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) [IsAlgClosed Ω]
    [FaithfulSMul C B] (Fr : Ω →+* Ω) (u : A →+* Ω)
    (hfin : ∀ w : B →+* Ω, w.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w))
    (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u) (F : G) (hF : ∀ b, Fr (w0 b) = w0 (F • b))
    (Rp : (C →+* Ω) → Prop) :
    Finite {v : C →+* Ω // (v.comp (algebraMap A C) = u ∧ Fr.comp v = v) ∧ Rp v} := by
  refine Finite.of_surjective
    (fun x : {x : G // x⁻¹ * F * x ∈ H ∧ Rp (ptRes C w0 x)} =>
      (⟨ptRes C w0 x.1, ptRes_mem H Fr u w0 hw0 F hF x.2.1, x.2.2⟩ :
        {v : C →+* Ω // (v.comp (algebraMap A C) = u ∧ Fr.comp v = v) ∧ Rp v})) ?_
  rintro ⟨v, ⟨hvu, hvF⟩, hR⟩
  obtain ⟨x, hx, hxv⟩ := ptRes_surj H hun Fr u hfin w0 hw0 F hF v hvu hvF
  refine ⟨⟨x, hx, ?_⟩, Subtype.ext hxv⟩
  show Rp (ptRes C w0 x)
  rw [hxv]
  exact hR

end PtFix

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtBlk =====
section

/-!
# S4-Lefschetz, L5c2: the block point count (generic)

`card_fixed_blk`: let `Γ ≤ G` be a subgroup whose translates of `w0` satisfy the normalization `Rp`, and such that
every normalized translate comes from `Γ H`. If `π : G →* Gf` has `Γ ∩ H = Γ ∩ ker π` and, on `Γ`, the condition
`y⁻¹ F y ∈ H` reads `(π y a)⁻¹ π(F) (π y a) = γ`, then the normalized `Fr`-fixed points of `C` over `u` are counted
by `#{p ∈ π(Γ) | (p a)⁻¹ π(F) (p a) = γ}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtBlk

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]
variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

/-- Counting `y ∈ Γ` with `y⁻¹ F y ∈ H` through the normalized fixed points. -/
theorem card_blk_pts (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) [IsAlgClosed Ω]
    [FaithfulSMul C B] (Fr : Ω →+* Ω) (u : A →+* Ω)
    (hfin : ∀ w : B →+* Ω, w.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w))
    (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u) (F : G) (hF : ∀ b, Fr (w0 b) = w0 (F • b))
    (Rp : (C →+* Ω) → Prop) (Γ : Subgroup G) (hRpΓ : ∀ y ∈ Γ, Rp (ptRes C w0 y))
    (hRpD : ∀ x : G, Rp (ptRes C w0 x) → ∃ y ∈ Γ, ∃ h ∈ H, x = y * h) :
    Nat.card {y : Γ // (y : G)⁻¹ * F * y ∈ H} =
      Nat.card {v : C →+* Ω // (v.comp (algebraMap A C) = u ∧ Fr.comp v = v) ∧ Rp v} *
        Nat.card (H.subgroupOf Γ) := by
  refine pt_card_eq_mul (H.subgroupOf Γ) (fun y : Γ => (y : G)⁻¹ * F * y ∈ H)
    (fun v : C →+* Ω => (v.comp (algebraMap A C) = u ∧ Fr.comp v = v) ∧ Rp v)
    (fun y : Γ => ptRes C w0 (y : G)) ?_ ?_ ?_ ?_
  · intro y0 y _
    show ptRes C w0 (y : G) = ptRes C w0 (y0 : G) ↔ _
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact ptRes_eq_iff H hun u hfin w0 hw0 (y : G) (y0 : G)
  · intro y h hy hh
    rw [Subgroup.mem_subgroupOf] at hh
    have hy' : (y : G)⁻¹ * F * y ∈ H := hy
    show ((y * h : Γ) : G)⁻¹ * F * ((y * h : Γ) : G) ∈ H
    rw [Subgroup.coe_mul]
    have e : ((y : G) * h)⁻¹ * F * ((y : G) * h) = (h : G)⁻¹ * ((y : G)⁻¹ * F * y) * h := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hy') hh
  · rintro v ⟨⟨hvu, hvF⟩, hRv⟩
    obtain ⟨x, hx, hxv⟩ := ptRes_surj H hun Fr u hfin w0 hw0 F hF v hvu hvF
    have hRx : Rp (ptRes C w0 x) := by rw [hxv]; exact hRv
    obtain ⟨y, hyΓ, h, hh, rfl⟩ := hRpD x hRx
    refine ⟨⟨y, hyΓ⟩, ?_, ?_⟩
    · show y⁻¹ * F * y ∈ H
      have e : y⁻¹ * F * y = h * ((y * h)⁻¹ * F * (y * h)) * h⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    · show ptRes C w0 y = v
      rw [← hxv]
      have e : (y * h)⁻¹ * y = h⁻¹ := by group
      refine (ptRes_eq_iff H hun u hfin w0 hw0 y (y * h)).2 ?_
      rw [e]
      exact H.inv_mem hh
  · intro y hy
    exact ⟨ptRes_mem H Fr u w0 hw0 F hF hy, hRpΓ y y.2⟩

/-- Counting `y ∈ Γ` with `(π y a)⁻¹ π(F) (π y a) = γ` through `p = π y`. -/
theorem card_blk_grp {G Gf : Type} [Group G] [Group Gf] [Finite G] (H Γ : Subgroup G) (π : G →* Gf)
    (hΓH : ∀ y ∈ Γ, y ∈ H ↔ π y = 1) (F : G) (a γ : Gf) :
    Nat.card {y : Γ // (π y * a)⁻¹ * π F * (π y * a) = γ} =
      Nat.card {p : Gf // p ∈ Γ.map π ∧ (p * a)⁻¹ * π F * (p * a) = γ} * Nat.card (H.subgroupOf Γ) := by
  refine pt_card_eq_mul (H.subgroupOf Γ) (fun y : Γ => (π (y : G) * a)⁻¹ * π F * (π (y : G) * a) = γ)
    (fun p : Gf => p ∈ Γ.map π ∧ (p * a)⁻¹ * π F * (p * a) = γ) (fun y : Γ => π (y : G)) ?_ ?_ ?_ ?_
  · intro y0 y _
    show π (y : G) = π (y0 : G) ↔ _
    rw [Subgroup.mem_subgroupOf, hΓH _ (y0⁻¹ * y).2, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      inv_mul_eq_one, eq_comm]
  · intro y h hy hh
    rw [Subgroup.mem_subgroupOf, hΓH _ h.2] at hh
    show (π ((y * h : Γ) : G) * a)⁻¹ * π F * (π ((y * h : Γ) : G) * a) = γ
    rw [Subgroup.coe_mul, map_mul, hh, mul_one]
    exact hy
  · rintro p ⟨⟨y, hy, rfl⟩, hp⟩
    exact ⟨⟨y, hy⟩, hp, rfl⟩
  · intro y hy
    exact ⟨⟨y, y.2, rfl⟩, hy⟩

/-- **L5c2: the block point count.** -/
theorem card_fixed_blk (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) [IsAlgClosed Ω]
    [FaithfulSMul C B] (Fr : Ω →+* Ω) (u : A →+* Ω)
    (hfin : ∀ w : B →+* Ω, w.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w))
    (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u) (F : G) (hF : ∀ b, Fr (w0 b) = w0 (F • b))
    (Rp : (C →+* Ω) → Prop) (Γ : Subgroup G) (hRpΓ : ∀ y ∈ Γ, Rp (ptRes C w0 y))
    (hRpD : ∀ x : G, Rp (ptRes C w0 x) → ∃ y ∈ Γ, ∃ h ∈ H, x = y * h)
    {Gf : Type} [Group Gf] (π : G →* Gf) (hΓH : ∀ y ∈ Γ, y ∈ H ↔ π y = 1) (a γ : Gf)
    (hcond : ∀ y ∈ Γ, y⁻¹ * F * y ∈ H ↔ (π y * a)⁻¹ * π F * (π y * a) = γ) :
    Nat.card {v : C →+* Ω // (v.comp (algebraMap A C) = u ∧ Fr.comp v = v) ∧ Rp v} =
      Nat.card {p : Gf // p ∈ Γ.map π ∧ (p * a)⁻¹ * π F * (p * a) = γ} := by
  have hpos : 0 < Nat.card (H.subgroupOf Γ) := Nat.card_pos
  have h1 := card_blk_pts H hun Fr u hfin w0 hw0 F hF Rp Γ hRpΓ hRpD
  have h2 := card_blk_grp H Γ π hΓH F a γ
  have e12 : Nat.card {y : Γ // (y : G)⁻¹ * F * y ∈ H} =
      Nat.card {y : Γ // (π y * a)⁻¹ * π F * (π y * a) = γ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => hcond y y.2)
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans (e12.trans h2))

end PtBlk

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtPro =====
section

/-!
# S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)

* `finite_setOf_pow_eq`, `finite_quot_ker`: points with values in a finite set have finite residue rings.
* `resPt`, `jPt`: restriction `π₁(U) → Gal(L/K)` and the inclusion `O_L → O_{K_U}` (the pro-chart over `A`) for a
  finite unramified Galois level `L`, with `resPt_surjective`, `jPt_smul`.
* `exists_frob_pro`: for a point `w` of the pro-chart with `Fr ∘ w = w` on `A` (finite image), some `F ∈ π₁(U)` has
  `w ∘ F = Fr ∘ w` (finite levels by `hom_smul_trans`, then compactness of `π₁(U)`).
* `IsFrobPt Fr u F` and `exists_isFrobPt`: every point `u` of `A` has a Frobenius element.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section PtProGen

/-- The solutions of `z ^ Q = z` in a field form a finite set. -/
theorem finite_setOf_pow_eq {F : Type} [Field F] {Q : ℕ} (hQ : 1 < Q) : {z : F | z ^ Q = z}.Finite := by
  classical
  have hne : (X ^ Q - X : F[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hQ
  refine (((X ^ Q - X : F[X]).roots.toFinset : Set F).toFinite).subset fun z hz => ?_
  have hz' : z ^ Q = z := hz
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X, hz', sub_self]

/-- A point of a finite `A`-algebra whose restriction to `A` has finite image has a finite residue ring. -/
theorem finite_quot_ker {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Field Ω]
    (w : B →+* Ω) (hu : (Set.range (w.comp (algebraMap A B))).Finite) : Finite (B ⧸ RingHom.ker w) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  have : Finite (Set.range (w.comp (algebraMap A B))) := hu.to_subtype
  let f : (s → Set.range (w.comp (algebraMap A B))) → Ω := fun c => ∑ i : s, (c i : Ω) * w i
  have hsub : Set.range w ⊆ Set.range f := by
    rintro _ ⟨b, rfl⟩
    have hb : b ∈ Submodule.span A (s : Set B) := by rw [hs]; exact Submodule.mem_top
    obtain ⟨g, hg⟩ := Submodule.mem_span_finset'.1 hb
    refine ⟨fun i => ⟨w (algebraMap A B (g i)), g i, rfl⟩, ?_⟩
    show ∑ i : s, w (algebraMap A B (g i)) * w i = w b
    rw [← hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hfin : (Set.range w).Finite := (Set.finite_range f).subset hsub
  have : Finite w.range := by
    rw [← SetLike.coe_sort_coe, RingHom.coe_range]
    exact hfin.to_subtype
  exact Finite.of_equiv _ (RingHom.quotientKerEquivRange w).symm.toEquiv

end PtProGen

section PtPro

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- Restriction `π₁(U) → Gal(L/K)` to a normal finite level `L ≤ K_U`. -/
def resPt {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L] :
    Pi1 A K →* (L ≃ₐ[K] L) :=
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  AlgEquiv.restrictNormalHom L

theorem resPt_apply {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    (σ : Pi1 A K) (y : L) : ((resPt A K hLU σ y : L) : AlgebraicClosure K) =
      ((σ (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K) := by
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ L y)

theorem resPt_surjective {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L] :
    Function.Surjective (resPt A K hLU) := by
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  exact AlgEquiv.restrictNormalHom_surjective (maxUnram A K)

/-- The inclusion of the integral closure of `A` in `L ≤ K_U` into the pro-chart over `A`. -/
def jPt {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) :
    integralClosure A L →+* proChart A K A :=
  (((IntermediateField.inclusion hLU).restrictScalars A).mapIntegralClosure).toRingHom

theorem jPt_val {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) (b : integralClosure A L) :
    (((jPt A K hLU b : maxUnram A K)) : AlgebraicClosure K) = ((b : L) : AlgebraicClosure K) := rfl

theorem jPt_algebraMap {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) (a : A) :
    jPt A K hLU (algebraMap A _ a) = algebraMap A _ a :=
  AlgHom.commutes (((IntermediateField.inclusion hLU).restrictScalars A).mapIntegralClosure) a

theorem jPt_smul {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    (σ : Pi1 A K) (b : integralClosure A L) : jPt A K hLU (resPt A K hLU σ • b) = σ • jPt A K hLU b := by
  refine Subtype.ext (Subtype.ext ?_)
  show (((resPt A K hLU σ (b : L)) : L) : AlgebraicClosure K) =
    ((σ (IntermediateField.inclusion hLU (b : L)) : maxUnram A K) : AlgebraicClosure K)
  exact resPt_apply A K hLU σ (b : L)

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end PtPro

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtCov =====
section

/-!
# S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points

* `exists_unramSet_fix`: a finite unramified Galois level `L` containing a finite set of `K_U`, whose fixer in
  `π₁(U)` lies in a given open subgroup; `fix_of_resPt_eq_one`, `pi_eq_of_resPt_eq`, `piBar` (`π` through
  `Gal(L/K)`), `piBar_resPt`.
* `isConj_of_isFrobPt`: two Frobenius elements at the same point are conjugate modulo an open normal subgroup.
* `kStar hq n`: the constants `x ∈ K_U` with `x ^ (q ^ n) = x` (a finite field with an `Fq`-algebra structure),
  `incStar` into the pro-chart.
* `exists_normFrob`: at every point `u` (with `Fr ∘ u = u`, finite image) there are a point `w` of the pro-chart over
  `u` and a Frobenius element `F` (`w ∘ F = Fr ∘ w`) with `w = ιS` on `kStar` (normalization by `φ ^ j`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section PtCovLevel

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- One unramified finite Galois level containing a finite set `s ⊆ K_U` whose fixer lies in an open subgroup. -/
theorem exists_unramSet_fix (N : Subgroup (Pi1 A K)) (hN : IsOpen (N : Set (Pi1 A K)))
    (s : Finset (AlgebraicClosure K)) (hs : ∀ x ∈ s, x ∈ maxUnram A K) :
    ∃ L ∈ unramSet A K, IntermediateField.adjoin K (s : Set (AlgebraicClosure K)) ≤ L ∧
      ∀ σ : Pi1 A K, (∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ L → σ y = y) → σ ∈ N := by
  classical
  obtain ⟨E, hE, hEN⟩ :=
    (krullTopology_mem_nhds_one_iff K (maxUnram A K) N).mp (hN.mem_nhds N.one_mem)
  have hfg : E.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    exact (Submodule.fg_iff_finiteDimensional _).mpr hE
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.mp hfg
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K
    (s ∪ htfin.toFinset.image (fun x : maxUnram A K => (x : AlgebraicClosure K))) (by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact hs x hx
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
        exact y.2)
  refine ⟨L, hL, le_trans (IntermediateField.adjoin.mono K _ _ ?_) hle, fun σ hσ => ?_⟩
  · intro x hx
    exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx))
  apply hEN
  have hgen : ∀ x ∈ t, σ x = x := by
    intro x hx
    apply hσ
    apply hle
    apply IntermediateField.subset_adjoin
    exact Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, htfin.mem_toFinset.mpr hx, rfl⟩))
  have hEfix : E ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [← hadj, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hgen x hx, ih (Subgroup.zpow_mem_zpowers σ _)]
    | pred n ih =>
      have hinv : σ⁻¹ x = x := by
        conv_lhs => rw [← hgen x hx]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih (Subgroup.zpow_mem_zpowers σ _)]
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hEfix hx) σ (Subgroup.mem_zpowers σ)

variable {A K}

theorem fix_of_resPt_eq_one {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    {σ : Pi1 A K} (hσ : resPt A K hLU σ = 1) (y : maxUnram A K) (hy : (y : AlgebraicClosure K) ∈ L) :
    σ y = y := by
  have h1 := resPt_apply A K hLU σ ⟨(y : AlgebraicClosure K), hy⟩
  rw [hσ, AlgEquiv.one_apply] at h1
  have h2 : IntermediateField.inclusion hLU ⟨(y : AlgebraicClosure K), hy⟩ = y := Subtype.ext rfl
  rw [h2] at h1
  exact Subtype.ext h1.symm

theorem pi_eq_of_resPt_eq {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (hker : ∀ σ, resPt A K hLU σ = 1 → π σ = 1) {x y : Pi1 A K}
    (h : resPt A K hLU x = resPt A K hLU y) : π x = π y := by
  have h1 := hker (x⁻¹ * y) (by rw [map_mul, map_inv, h, inv_mul_cancel])
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

/-- `π` through `Gal(L/K)`, when `ker resPt ≤ ker π`. -/
def piBar {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (hker : ∀ σ, resPt A K hLU σ = 1 → π σ = 1) :
    (L ≃ₐ[K] L) →* Gf where
  toFun g := π (resPt_surjective A K hLU g).choose
  map_one' := hker _ (resPt_surjective A K hLU 1).choose_spec
  map_mul' g h := by
    rw [← map_mul]
    apply pi_eq_of_resPt_eq hLU π hker
    rw [map_mul, (resPt_surjective A K hLU _).choose_spec, (resPt_surjective A K hLU g).choose_spec,
      (resPt_surjective A K hLU h).choose_spec]

theorem le_maxUnram_of_mem {L : IntermediateField K (AlgebraicClosure K)} (hL : L ∈ unramSet A K) :
    L ≤ maxUnram A K := by
  unfold maxUnram
  exact le_iSup (f := fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K))) ⟨L, hL⟩

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end PtCovLevel

section KStar

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
variable {k0 : Type} [Field k0] [Fintype k0] [Algebra k0 K] {p e : ℕ} [Fact p.Prime] [CharP K p]

/-- The constants `x ∈ K_U` with `x ^ (p ^ (e * n)) = x` (`= x ^ (q ^ n)` for `q = #k0 = p ^ e`). -/
def kStar (_hq : Fintype.card k0 = p ^ e) (n : ℕ) : Subfield (maxUnram A K) :=
  (iterateFrobenius (maxUnram A K) p (e * n)).eqLocusField (RingHom.id _)

theorem mem_kStar (hq : Fintype.card k0 = p ^ e) (n : ℕ) (x : maxUnram A K) :
    x ∈ kStar A K hq n ↔ x ^ (Fintype.card k0 ^ n) = x := by
  rw [hq, ← pow_mul]
  exact Iff.rfl

/-- `k0 → kStar`. -/
def kStarMap (hq : Fintype.card k0 = p ^ e) (n : ℕ) : k0 →+* kStar A K hq n :=
  ((algebraMap K (maxUnram A K)).comp (algebraMap k0 K)).codRestrict (kStar A K hq n) fun c => by
    rw [mem_kStar, RingHom.comp_apply, ← map_pow, ← map_pow, FiniteField.pow_card_pow]

instance kStarAlgebra (hq : Fintype.card k0 = p ^ e) (n : ℕ) : Algebra k0 (kStar A K hq n) :=
  (kStarMap A K hq n).toAlgebra

theorem kStar_algebraMap_val (hq : Fintype.card k0 = p ^ e) (n : ℕ) (c : k0) :
    ((algebraMap k0 (kStar A K hq n) c : kStar A K hq n) : maxUnram A K) =
      algebraMap K (maxUnram A K) (algebraMap k0 K c) := rfl

theorem isIntegral_of_pow_eq {Q : ℕ} (hQ : 1 < Q) {x : maxUnram A K} (hx : x ^ Q = x) : IsIntegral A x := by
  refine ⟨X ^ Q - X, monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by exact_mod_cast hQ)), ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_X, hx, sub_self]

/-- `kStar → O_{K_U}` (the pro-chart over `A`). -/
def incStar (hq : Fintype.card k0 = p ^ e) (n : ℕ) (hQ : 1 < p ^ (e * n)) : kStar A K hq n →+* proChart A K A :=
  (kStar A K hq n).subtype.codRestrict (integralClosure A (maxUnram A K)) fun x =>
    isIntegral_of_pow_eq A K hQ (x := (x : maxUnram A K)) x.2

theorem incStar_val (hq : Fintype.card k0 = p ^ e) (n : ℕ) (hQ : 1 < p ^ (e * n)) (x : kStar A K hq n) :
    ((incStar A K hq n hQ x : proChart A K A) : maxUnram A K) = x := rfl

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end KStar

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtLift =====
section

/-!
# S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers

* `liftHom r hr π hker : G →* Gf` (`π` through a surjection `r` with `ker r ≤ ker π`), `liftHom_apply`;
* `card_fixed_blk_lift`: `card_fixed_blk` with `Γ`, `F`, `π` given upstairs (in `P`, e.g. `π₁(U)`), through
  `r : P →* G`: the count is `#{p ∈ π(Γ) | (p a)⁻¹ π(F) (p a) = γ}`;
* `mem_blkH_of_fix_iff` (`x ζ = ζ`: `x ∈ H_ω ↔ π x = 1`), `mem_blkH_of_ginv_iff` (`x ζ = g⁻¹ ζ`:
  `x ∈ H_ω ↔ π x = π g⁻¹`);
* `mem_fixRestrict_iff`, `isOpen_fixRestrict`, `resPt_eq_one_of_fix`: the fixer of a finite level `L ≤ K_U` is open
  and is `ker resPt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section LiftHom

variable {P G Gf : Type} [Group P] [Group G] [Group Gf]

/-- `π` through a surjection `r` with `ker r ≤ ker π`. -/
def liftHom (r : P →* G) (hr : Function.Surjective r) (π : P →* Gf) (hker : ∀ σ, r σ = 1 → π σ = 1) :
    G →* Gf where
  toFun g := π (hr g).choose
  map_one' := hker _ (hr 1).choose_spec
  map_mul' g h := by
    rw [← map_mul]
    apply eq_of_lift_eq r π hker
    rw [map_mul, (hr _).choose_spec, (hr g).choose_spec, (hr h).choose_spec]

theorem liftHom_apply (r : P →* G) (hr : Function.Surjective r) (π : P →* Gf) (hker : ∀ σ, r σ = 1 → π σ = 1)
    (σ : P) : liftHom r hr π hker (r σ) = π σ :=
  eq_of_lift_eq r π hker (hr (r σ)).choose_spec

end LiftHom

section PtLift

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]
variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

/-- **The block count, upstairs**: `card_fixed_blk` with `Γ`, `F` and `π` living on `P` (e.g. `π₁(U)`). -/
theorem card_fixed_blk_lift (hun : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥) [IsAlgClosed Ω]
    [FaithfulSMul C B] (Fr : Ω →+* Ω) (u : A →+* Ω)
    (hfin : ∀ w : B →+* Ω, w.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w))
    (w0 : B →+* Ω) (hw0 : w0.comp (algebraMap A B) = u)
    {P Gf : Type} [Group P] [Group Gf] (r : P →* G) (hr : Function.Surjective r) (π : P →* Gf)
    (hker : ∀ σ, r σ = 1 → π σ = 1) (F : P) (hF : ∀ b, Fr (w0 b) = w0 (r F • b))
    (Rp : (C →+* Ω) → Prop) (Γ : Subgroup P) (hRpΓ : ∀ y ∈ Γ, Rp (ptRes C w0 (r y)))
    (hRpD : ∀ x : G, Rp (ptRes C w0 x) → ∃ y ∈ Γ, ∃ h ∈ H, x = r y * h)
    (hΓH : ∀ y ∈ Γ, r y ∈ H ↔ π y = 1) (a γ : Gf)
    (hcond : ∀ y ∈ Γ, (r y)⁻¹ * r F * r y ∈ H ↔ (π y * a)⁻¹ * π F * (π y * a) = γ) :
    Nat.card {v : C →+* Ω // (v.comp (algebraMap A C) = u ∧ Fr.comp v = v) ∧ Rp v} =
      Nat.card {p : Gf // p ∈ Γ.map π ∧ (p * a)⁻¹ * π F * (p * a) = γ} := by
  have hπb := liftHom_apply r hr π hker
  have h := card_fixed_blk H hun Fr u hfin w0 hw0 (r F) hF Rp (Γ.map r)
    (by rintro _ ⟨y, hy, rfl⟩; exact hRpΓ y hy)
    (fun x hx => by
      obtain ⟨y, hy, h, hh, rfl⟩ := hRpD x hx
      exact ⟨r y, ⟨y, hy, rfl⟩, h, hh, rfl⟩)
    (liftHom r hr π hker) (by rintro _ ⟨y, hy, rfl⟩; rw [hπb]; exact hΓH y hy) a γ
    (by rintro _ ⟨y, hy, rfl⟩; rw [hπb, hπb]; exact hcond y hy)
  rw [h, Subgroup.map_map, show (liftHom r hr π hker).comp r = π from MonoidHom.ext hπb, hπb]

end PtLift

section BlkFix

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 A K →* Gf) (g : Pi1 A K) (ζ : maxUnram A K)

/-- `x ζ = ζ` (not only `x ∈ π₁^geo`): `x ∈ H_ω ↔ π x = 1`. -/
theorem mem_blkH_of_fix_iff {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ (q ^ m))
    [NeZero ((q ^ m) ^ Fintype.card Gf - 1)] (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1))
    {x : Pi1 A K} (hxζ : x ζ = ζ) : x ∈ blkH π g ζ hζ ↔ π x = 1 := by
  have hr : 0 < Fintype.card Gf := Fintype.card_pos
  have hζc : IsConst q ζ := isConst_zeta (Gf := Gf) hq2 hm hζ
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

/-- `x ζ = g⁻¹ ζ`: `x ∈ H_ω ↔ π x = π g⁻¹`. -/
theorem mem_blkH_of_ginv_iff {q m : ℕ} (hq2 : 2 ≤ q) (hm : 0 < m)
    (hg : ∀ x : maxUnram A K, IsConst q x → g⁻¹ x = x ^ (q ^ m))
    [NeZero ((q ^ m) ^ Fintype.card Gf - 1)] (hζ : IsPrimitiveRoot ζ ((q ^ m) ^ Fintype.card Gf - 1))
    {x : Pi1 A K} (hxζ : x ζ = g⁻¹ ζ) : x ∈ blkH π g ζ hζ ↔ π x = π g⁻¹ := by
  have hgx : (g * x) ζ = ζ := by
    rw [AlgEquiv.mul_apply, hxζ, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rw [← (blkH π g ζ hζ).mul_mem_cancel_left (g_mem_blkH π g ζ hζ),
    mem_blkH_of_fix_iff π g ζ hq2 hm hg hζ hgx, map_mul, map_inv, mul_eq_one_iff_inv_eq, eq_comm]

end BlkFix

section FixRestrict

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)

theorem mem_fixRestrict_iff (σ : Pi1 A K) : σ ∈ (IntermediateField.restrict hLU).fixingSubgroup ↔
    ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ L → σ y = y := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    exact h y ((IntermediateField.mem_restrict hLU y).2 hy)
  · intro h y hy
    exact h y ((IntermediateField.mem_restrict hLU y).1 hy)

end FixRestrict

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtE =====
section

/-!
# S4-Lefschetz, L5c4b: a block cover `E` inside a finite level `L`, and the per-point block count

* `mem_range_thetaE_iff_fix`: `range thetaE` = the automorphisms of `K_U` fixing `E` pointwise;
* `resPt_mem_fix_iff`: `resPt x ∈ Gal(L/E) ↔ x` fixes `E`;
* `rfixE`: the `Gal(L/E)`-invariants of the integral closure of `R_fin` in `L`; `rfixEquiv : R_E ≃+* rfixE`;
* `kcInc`, `toStar`, `kappaE`: the constants of `E` in `K_U`, in `kStar`, in `rfixE`;
* `frob_apply_kStar`: a normalized Frobenius acts on `kStar` as `x ↦ x^Q`;
* `hGH_ptE`, `hcond_ptE`, `hRpG_ptE`, `hRpD_ptE`: the hypotheses of `card_fixed_blk_lift`;
* `card_pt_blk`: the `k_E`-points of `R_E` over a point `u` of `U` = `#{p ∈ π(Γ) | (p a)⁻¹ π(F_u) (p a) = γ}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

theorem conj_eq_iff_ptE {G : Type} [Group G] (X a γ : G) : a⁻¹ * X * a = γ ↔ X = a * γ * a⁻¹ := by
  constructor
  · rintro rfl
    group
  · rintro rfl
    group

theorem isConst_pow_ptE {L : Type} [Field L] {q : ℕ} {x : L} (k : ℕ) (hx : IsConst q x) : IsConst q (x ^ k) := by
  obtain ⟨n, hn, h⟩ := hx
  exact ⟨n, hn, by rw [← pow_mul, mul_comm, pow_mul, h]⟩

section PtE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

theorem le_maxUnram_rfin_ptE {E : IntermediateField K (AlgebraicClosure K)} (hE : E ≤ maxUnram Fq[X] K) :
    E ≤ maxUnram (Rfin Fq K) K := fun x hx => by
  rw [maxUnram_rfin Fq K]
  exact hE hx

/-- `range thetaE` = the automorphisms of `K_U` fixing `E` pointwise. -/
theorem mem_range_thetaE_iff_fix (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (hE : E ≤ maxUnram Fq[X] K) (τ : Pi1 (Rfin Fq K) K) :
    τ ∈ (thetaE Fq K E hE).range ↔
      ∀ y : maxUnram (Rfin Fq K) K, (y : AlgebraicClosure K) ∈ E → τ y = y := by
  have he : pi1Congr (maxUnram_rfin Fq K).symm ((pi1Congr (maxUnram_rfin Fq K).symm).symm τ) = τ :=
    ContinuousMulEquiv.apply_symm_apply _ τ
  rw [mem_range_thetaE_iff, mem_range_theta]
  constructor
  · intro h y hy
    have h2 := pi1Congr_fix Fq K E hE _ h y hy
    rw [he] at h2
    exact h2
  · intro h x hx
    apply Subtype.ext
    have hx' : x ∈ maxUnram (Rfin Fq K) K := le_maxUnram_rfin_ptE Fq K hE hx
    have hv := pi1Congr_val (maxUnram_rfin Fq K).symm ((pi1Congr (maxUnram_rfin Fq K).symm).symm τ)
      ⟨x, hE hx⟩ ⟨x, hx'⟩ rfl
    rw [he, h ⟨x, hx'⟩ hx] at hv
    exact hv.symm

variable {K}

/-- `Gal(L/E)` inside `Gal(L/K)`. -/
abbrev galLE {E L : IntermediateField K (AlgebraicClosure K)} (hEL : E ≤ L) : Subgroup (L ≃ₐ[K] L) :=
  (IntermediateField.restrict hEL).fixingSubgroup

theorem resPt_mem_fix_iff {E L : IntermediateField K (AlgebraicClosure K)} (hEL : E ≤ L)
    (hLU : L ≤ maxUnram (Rfin Fq K) K) [Normal K L] (x : Pi1 (Rfin Fq K) K) :
    resPt (Rfin Fq K) K hLU x ∈ galLE hEL ↔
      ∀ y : maxUnram (Rfin Fq K) K, (y : AlgebraicClosure K) ∈ E → x y = y := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have h1 := h ⟨(y : AlgebraicClosure K), hEL hy⟩ ((IntermediateField.mem_restrict hEL _).2 hy)
    have h2 := resPt_apply (Rfin Fq K) K hLU x ⟨(y : AlgebraicClosure K), hEL hy⟩
    rw [h1] at h2
    have h3 : IntermediateField.inclusion hLU ⟨(y : AlgebraicClosure K), hEL hy⟩ = y := Subtype.ext rfl
    rw [h3] at h2
    exact Subtype.ext h2.symm
  · intro h z hz
    apply Subtype.ext
    rw [resPt_apply]
    exact congrArg Subtype.val
      (h (IntermediateField.inclusion hLU z) ((IntermediateField.mem_restrict hEL z).1 hz))

/-- `FixedPoints.subalgebra`, elaborated over `CommRing`s. -/
abbrev fixSubG (R B : Type) [CommRing R] [CommRing B] [Algebra R B] {G : Type} [Group G] [MulSemiringAction G B]
    [SMulCommClass G R B] (H : Subgroup G) : Subalgebra R B :=
  FixedPoints.subalgebra R B H

/-- The finiteness hypothesis `hfin` of the point counts, from a finite image of `u`. -/
theorem hfin_gen {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Field Ω]
    (u : A →+* Ω) (hfinu : (Set.range u).Finite) :
    ∀ w' : B →+* Ω, w'.comp (algebraMap A B) = u → Finite (B ⧸ RingHom.ker w') := fun w' hw' =>
  finite_quot_ker w' (by rw [hw']; exact hfinu)

section RFix

variable {E L : IntermediateField K (AlgebraicClosure K)} (hEL : E ≤ L)

/-- The `Gal(L/E)`-invariants of the integral closure of `R_fin` in `L`. Built through `fixSubG` so that its
type carries the instance paths of `CommRing`s (then `CommRing`, quotients and `IsGaloisGroup` are found). -/
abbrev rfixE := fixSubG (Rfin Fq K) (integralClosure (Rfin Fq K) L) (galLE hEL)

/-- (Instance search does not find it through `Subalgebra.toCommRing`: the ambient instances need unfolding.) -/
instance commRing_rfixE : CommRing (rfixE Fq hEL) :=
  @Subalgebra.toCommRing (Rfin Fq K) (integralClosure (Rfin Fq K) L) _ _ _ (rfixE Fq hEL)

theorem mem_rfixE_iff (b : integralClosure (Rfin Fq K) L) : b ∈ rfixE Fq hEL ↔ ∀ h : galLE hEL, h • b = b :=
  Iff.rfl

theorem rfixE_ext {c c' : rfixE Fq hEL}
    (h : (((c : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K) =
      (((c' : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K)) : c = c' :=
  Subtype.ext (Subtype.ext (Subtype.ext h))

theorem isIntegral_incl_ptE (x : Rfin Fq E) :
    IsIntegral (Rfin Fq K) (IntermediateField.inclusion hEL (x : E)) := by
  have h1 : IsIntegral Fq[X] (((IntermediateField.inclusion hEL).restrictScalars Fq[X]) (x : E)) :=
    IsIntegral.map ((IntermediateField.inclusion hEL).restrictScalars Fq[X]) x.2
  exact h1.tower_top

theorem incl_mem_rfixE (x : Rfin Fq E) :
    (⟨IntermediateField.inclusion hEL (x : E), isIntegral_incl_ptE Fq hEL x⟩ :
      integralClosure (Rfin Fq K) L) ∈ rfixE Fq hEL := by
  rw [mem_rfixE_iff]
  intro h
  apply Subtype.ext
  have hh := h.2
  rw [IntermediateField.mem_fixingSubgroup_iff] at hh
  exact hh _ ((IntermediateField.mem_restrict hEL _).2 (x : E).2)

/-- `R_fin(E) → rfixE`. -/
def rfixMap : Rfin Fq E →+* rfixE Fq hEL where
  toFun x := ⟨⟨IntermediateField.inclusion hEL (x : E), isIntegral_incl_ptE Fq hEL x⟩, incl_mem_rfixE Fq hEL x⟩
  map_one' := rfixE_ext Fq hEL rfl
  map_mul' _ _ := rfixE_ext Fq hEL rfl
  map_zero' := rfixE_ext Fq hEL rfl
  map_add' _ _ := rfixE_ext Fq hEL rfl

theorem rfixMap_injective : Function.Injective (rfixMap Fq hEL) := fun x y h =>
  Subtype.ext (Subtype.ext (congrArg (fun c : rfixE Fq hEL =>
    (((c : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K)) h))

theorem rfixMap_surjective [FiniteDimensional K L] [IsGalois K L] : Function.Surjective (rfixMap Fq hEL) := by
  intro c
  have hfix : ((c : integralClosure (Rfin Fq K) L) : L) ∈
      IntermediateField.fixedField (IntermediateField.restrict hEL).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 := (mem_rfixE_iff Fq hEL _).1 c.2 ⟨f, hf⟩
    exact congrArg Subtype.val h1
  rw [IsGalois.fixedField_fixingSubgroup] at hfix
  have hyE : (((c : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K) ∈ E :=
    (IntermediateField.mem_restrict hEL _).1 hfix
  have hintL : IsIntegral Fq[X] ((c : integralClosure (Rfin Fq K) L) : L) :=
    isIntegral_trans (R := Fq[X]) (A := Rfin Fq K) _ (c : integralClosure (Rfin Fq K) L).2
  have h2 : ((IntermediateField.inclusion hEL).restrictScalars Fq[X])
      (⟨(((c : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K), hyE⟩ : E) =
        ((c : integralClosure (Rfin Fq K) L) : L) := Subtype.ext rfl
  have hintE : IsIntegral Fq[X]
      (⟨(((c : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K), hyE⟩ : E) := by
    refine (isIntegral_algHom_iff ((IntermediateField.inclusion hEL).restrictScalars Fq[X])
      (IntermediateField.inclusion hEL).toRingHom.injective).1 ?_
    rw [h2]
    exact hintL
  exact ⟨⟨⟨(((c : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K), hyE⟩, hintE⟩, rfixE_ext Fq hEL rfl⟩

/-- **`R_E ≃ (R_L)^{Gal(L/E)}`**. -/
def rfixEquiv [FiniteDimensional K E] [Algebra.IsSeparable K E] [FiniteDimensional K L] [IsGalois K L] :
    Rfin (Kc Fq E) E ≃+* rfixE Fq hEL :=
  (rfinKcEquiv Fq E).trans
    (RingEquiv.ofBijective (rfixMap Fq hEL) ⟨rfixMap_injective Fq hEL, rfixMap_surjective Fq hEL⟩)

theorem rfixEquiv_val [FiniteDimensional K E] [Algebra.IsSeparable K E] [FiniteDimensional K L] [IsGalois K L]
    (x : Rfin (Kc Fq E) E) :
    (((rfixEquiv Fq hEL x : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K) =
      ((x : E) : AlgebraicClosure K) := rfl

theorem isGaloisGroup_ptE [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisGroup (L ≃ₐ[K] L) (Rfin Fq K) (integralClosure (Rfin Fq K) L) := by
  haveI : IsFractionRing (integralClosure (Rfin Fq K) L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := Rfin Fq K) K L
  exact IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (Rfin Fq K) (integralClosure (Rfin Fq K) L) K L

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem isGaloisGroup_rfixE [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisGroup (galLE hEL) (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) := by
  have hG := isGaloisGroup_ptE Fq (L := L)
  exact { faithful := by
            have := hG.faithful
            infer_instance
          commutes := inferInstance
          isInvariant := ⟨fun x h => ⟨⟨x, h⟩, rfl⟩⟩ }

theorem faithfulSMul_rfixE : FaithfulSMul (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 fun _ _ h => Subtype.ext h

end RFix

section Hyp

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)
variable {E L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- The constants `k_E` in `K_U`. -/
def kcInc (hEU : E ≤ maxUnram (Rfin Fq K) K) : Kc Fq E →+* maxUnram (Rfin Fq K) K :=
  (IntermediateField.inclusion hEU).toRingHom.comp (algebraMap (Kc Fq E) E)

theorem kcInc_val (hEU : E ≤ maxUnram (Rfin Fq K) K) (c : Kc Fq E) :
    ((kcInc Fq hEU c : maxUnram (Rfin Fq K) K) : AlgebraicClosure K) = ((c : E) : AlgebraicClosure K) := rfl

theorem kcInc_pow (hEU : E ≤ maxUnram (Rfin Fq K) K) {m : ℕ}
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (c : Kc Fq E) :
    kcInc Fq hEU c ^ (Fintype.card Fq ^ m) = kcInc Fq hEU c := by
  rw [← map_pow, ← hcard, FiniteField.pow_card]

theorem isConst_kcInc (hEU : E ≤ maxUnram (Rfin Fq K) K) {m : ℕ} (hm : 0 < m)
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (c : Kc Fq E) :
    IsConst (Fintype.card Fq) (kcInc Fq hEU c) :=
  ⟨m, hm, kcInc_pow Fq hEU hcard c⟩

/-- The constants `k_E` in `kStar` (level `n`, `m ∣ n`). -/
def toStar (hEU : E ≤ maxUnram (Rfin Fq K) K) {m n : ℕ} (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m)
    (hmn : m ∣ n) : Kc Fq E →+* kStar (Rfin Fq K) K hq n :=
  (kcInc Fq hEU).codRestrict (kStar (Rfin Fq K) K hq n) fun c => by
    obtain ⟨k, hk⟩ := hmn
    rw [mem_kStar, hk, pow_mul, ← hcard, ← map_pow, FiniteField.pow_card_pow]

theorem toStar_val (hEU : E ≤ maxUnram (Rfin Fq K) K) {m n : ℕ}
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (hmn : m ∣ n) (c : Kc Fq E) :
    ((toStar Fq hq hEU hcard hmn c : kStar (Rfin Fq K) K hq n) : maxUnram (Rfin Fq K) K) = kcInc Fq hEU c := rfl

/-- A normalized Frobenius acts on `kStar` as `x ↦ x ^ Q`. -/
theorem frob_apply_kStar {n : ℕ} (hQ : 1 < p ^ (e * n)) {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) {Q : ℕ}
    (hFr : ∀ z, Fr z = z ^ Q) (ιS : kStar (Rfin Fq K) K hq n →+* Ω)
    (w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω) (F : Pi1 (Rfin Fq K) K) (hwF : ∀ b, w (F • b) = Fr (w b))
    (hwι : ∀ x, w (incStar (Rfin Fq K) K hq n hQ x) = ιS x) (x : maxUnram (Rfin Fq K) K)
    (hx : x ∈ kStar (Rfin Fq K) K hq n) : F x = x ^ Q := by
  have hFx : F x ∈ kStar (Rfin Fq K) K hq n := by
    rw [mem_kStar, ← map_pow, (mem_kStar _ _ hq n x).1 hx]
  have hsm : F • incStar (Rfin Fq K) K hq n hQ ⟨x, hx⟩ = incStar (Rfin Fq K) K hq n hQ ⟨F x, hFx⟩ :=
    Subtype.ext rfl
  have h1 : ιS ⟨F x, hFx⟩ = ιS (⟨x, hx⟩ ^ Q) := by
    calc ιS ⟨F x, hFx⟩ = w (incStar (Rfin Fq K) K hq n hQ ⟨F x, hFx⟩) := (hwι _).symm
      _ = w (F • incStar (Rfin Fq K) K hq n hQ ⟨x, hx⟩) := by rw [hsm]
      _ = Fr (ιS ⟨x, hx⟩) := (hwF _).trans (congrArg Fr (hwι _))
      _ = ιS (⟨x, hx⟩ ^ Q) := by rw [hFr, map_pow]
  have h2 := congrArg Subtype.val (ιS.injective h1)
  rw [SubmonoidClass.coe_pow] at h2
  exact h2

variable (hEL : E ≤ L) [FiniteDimensional K L] [IsGalois K L]

/-- `ptRes` for `B = O_L` and `C = rfixE` (its instance arguments are fixed here, before `w` is supplied). -/
abbrev ptResE (Ω : Type) [Field Ω] :=
  ptRes (B := integralClosure (Rfin Fq K) L) (G := L ≃ₐ[K] L) (Ω := Ω) (rfixE Fq hEL)

/-- The constants `k_E` in `rfixE`. -/
def kappaE : Kc Fq E →+* rfixE Fq hEL :=
  (rfixEquiv Fq hEL).toRingHom.comp (algebraMap (Kc Fq E) (Rfin (Kc Fq E) E))

theorem kappaE_val (c : Kc Fq E) :
    (((kappaE Fq hEL c : integralClosure (Rfin Fq K) L) : L) : AlgebraicClosure K) =
      ((c : E) : AlgebraicClosure K) := rfl

theorem jPt_kappaE (hLU : L ≤ maxUnram (Rfin Fq K) K) {m n : ℕ}
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (hmn : m ∣ n) (hQ : 1 < p ^ (e * n)) (c : Kc Fq E) :
    jPt (Rfin Fq K) K hLU (algebraMap (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (kappaE Fq hEL c)) =
      incStar (Rfin Fq K) K hq n hQ (toStar Fq hq (hEL.trans hLU) hcard hmn c) :=
  Subtype.ext (Subtype.ext rfl)

variable (hE : E ≤ maxUnram Fq[X] K) (hLU : L ≤ maxUnram (Rfin Fq K) K)
variable {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Rfin Fq K) K →* Gf)
variable {φ c0 : Pi1 (Rfin Fq K) K} (hφ : IsFrobLift (Rfin Fq K) K (Fintype.card Fq) φ)
  (hc0 : c0 ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) {m : ℕ} (hm : 0 < m)
  [NeZero ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1)] {ζ : maxUnram (Rfin Fq K) K}
  (hζ : IsPrimitiveRoot ζ ((Fintype.card Fq ^ m) ^ Fintype.card Gf - 1))
  (hblk : ∀ τ, τ ∈ (thetaE Fq K E hE).range ↔ τ ∈ blkH π (c0⁻¹ * φ⁻¹ ^ m) ζ hζ)

include hφ hc0 hm hblk in
/-- `hΓH`: for geometric `y`, `resPt y ∈ Gal(L/E) ↔ π y = 1`. -/
theorem hGH_ptE (y : Pi1 (Rfin Fq K) K) (hy : y ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) :
    resPt (Rfin Fq K) K hLU y ∈ galLE hEL ↔ π y = 1 := by
  rw [resPt_mem_fix_iff Fq hEL hLU, ← mem_range_thetaE_iff_fix Fq K E hE y, hblk]
  exact mem_blkH_geo_iff π _ ζ Fintype.one_lt_card hm (fun x hx => ginv_apply hφ hc0 m x hx) hζ hy

include hφ hc0 hm hblk in
/-- `hcond`: for geometric `y` and `F ζ = ζ^(q^m)`, the conjugate `y⁻¹ F y` lies in `Gal(L/E)` (after `resPt`) iff
`(π y a)⁻¹ π F (π y a) = γ`. -/
theorem hcond_ptE {a γ : Gf} (hπg : π (c0⁻¹ * φ⁻¹ ^ m) = a * γ⁻¹ * a⁻¹) (F : Pi1 (Rfin Fq K) K)
    (hFζ : F ζ = ζ ^ (Fintype.card Fq ^ m)) (y : Pi1 (Rfin Fq K) K)
    (hy : y ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) :
    (resPt (Rfin Fq K) K hLU y)⁻¹ * resPt (Rfin Fq K) K hLU F * resPt (Rfin Fq K) K hLU y ∈ galLE hEL ↔
      (π y * a)⁻¹ * π F * (π y * a) = γ := by
  have hq2 : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hg : ∀ x : maxUnram (Rfin Fq K) K, IsConst (Fintype.card Fq) x →
      (c0⁻¹ * φ⁻¹ ^ m)⁻¹ x = x ^ (Fintype.card Fq ^ m) := fun x hx => ginv_apply hφ hc0 m x hx
  have hζc : IsConst (Fintype.card Fq) ζ := isConst_zeta (Gf := Gf) hq2 hm hζ
  have hζc' : IsConst (Fintype.card Fq) (ζ ^ (Fintype.card Fq ^ m)) := isConst_pow_ptE _ hζc
  have hxζ : (y⁻¹ * F * y) ζ = (c0⁻¹ * φ⁻¹ ^ m)⁻¹ ζ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, (mem_pi1geo _ _ _ y).1 hy ζ hζc, hFζ,
      (mem_pi1geo _ _ _ y⁻¹).1 (inv_mem hy) _ hζc', hg ζ hζc]
  rw [← map_inv, ← map_mul, ← map_mul, resPt_mem_fix_iff Fq hEL hLU,
    ← mem_range_thetaE_iff_fix Fq K E hE (y⁻¹ * F * y), hblk,
    mem_blkH_of_ginv_iff π _ ζ hq2 hm hg hζ hxζ, map_mul, map_mul, map_inv, map_inv, hπg,
    show (π y * a)⁻¹ * π F * (π y * a) = a⁻¹ * ((π y)⁻¹ * π F * π y) * a by group,
    conj_eq_iff_ptE ((π y)⁻¹ * π F * π y) a γ, show (a * γ⁻¹ * a⁻¹)⁻¹ = a * γ * a⁻¹ by group]

include hm in
/-- `hRpΓ`: geometric `y` satisfy the normalization `Rp`. -/
theorem hRpG_ptE {n : ℕ} (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (hmn : m ∣ n)
    (hQ : 1 < p ^ (e * n)) {Ω : Type} [Field Ω] (ιS : kStar (Rfin Fq K) K hq n →+* Ω)
    (w : proChart (Rfin Fq K) K (Rfin Fq K) →+* Ω) (hwι : ∀ x, w (incStar (Rfin Fq K) K hq n hQ x) = ιS x)
    (y : Pi1 (Rfin Fq K) K) (hy : y ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) (c : Kc Fq E) :
    ptResE Fq hEL Ω (w.comp (jPt (Rfin Fq K) K hLU)) (resPt (Rfin Fq K) K hLU y) (kappaE Fq hEL c) =
      ιS (toStar Fq hq (hEL.trans hLU) hcard hmn c) := by
  show w (jPt (Rfin Fq K) K hLU (resPt (Rfin Fq K) K hLU y •
      algebraMap (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (kappaE Fq hEL c))) = _
  have hv : resPt (Rfin Fq K) K hLU y •
      algebraMap (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (kappaE Fq hEL c) =
        algebraMap (rfixE Fq hEL) (integralClosure (Rfin Fq K) L) (kappaE Fq hEL c) := by
    apply Subtype.ext
    apply Subtype.ext
    show ((resPt (Rfin Fq K) K hLU y (((kappaE Fq hEL c : integralClosure (Rfin Fq K) L) : L)) : L) :
      AlgebraicClosure K) = ((c : E) : AlgebraicClosure K)
    have h1 : IntermediateField.inclusion hLU (((kappaE Fq hEL c : integralClosure (Rfin Fq K) L) : L)) =
        kcInc Fq (hEL.trans hLU) c := Subtype.ext rfl
    rw [resPt_apply, h1, (mem_pi1geo _ _ _ y).1 hy _ (isConst_kcInc Fq (hEL.trans hLU) hm hcard c), kcInc_val]
  rw [hv, jPt_kappaE Fq hq hEL hLU hcard hmn hQ c, hwι]

end Hyp

end PtE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtAsm =====
section

/-!
# S4-Lefschetz, L5c4c: the `k_E`-points of a block cover `E`, summed over the points of `U`

* `pow_pow_fix`, `coe_algebraMap_kc`, `toStar_algebraMap_ptA`, `algebraMap_rfixE_fq`: compatibilities;
* `rfixHomEquiv`, `card_fixed_rfin_eq`: `k_E`-points of `R_E` = normalized `Fr`-fixed points of `rfixE`;
* `card_rfin_eq_sum`: `#R_E(k_E) = Σ_{u ∈ S} #{p ∈ π(Γ) | (p a)⁻¹ π(F_u) (p a) = γ}` for the `F_{q^m}`-points `S` of `U`
  (normalized by `ιS` on `𝔽_q`) and normalized Frobenius elements `F_u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

theorem pow_pow_fix {M : Type} [Monoid M] {x : M} {Q : ℕ} (h : x ^ Q = x) (t : ℕ) : x ^ (Q ^ t) = x := by
  induction t with
  | zero => rw [pow_zero, pow_one]
  | succ t ih => rw [pow_succ, pow_mul, ih, h]

section PtAsm

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {K : Type} [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

theorem coe_algebraMap_kc (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] (c : Fq) :
    (((algebraMap Fq (Kc Fq E) c : Kc Fq E) : E) : AlgebraicClosure K) =
      algebraMap K (AlgebraicClosure K) (algebraMap Fq K c) := by
  have h1 : ((algebraMap Fq (Kc Fq E) c : Kc Fq E) : E) = algebraMap K E (algebraMap Fq K c) := by
    rw [← IsScalarTower.algebraMap_apply Fq K E]
    rfl
  rw [h1]
  rfl

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)
variable {E L : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E] [Algebra.IsSeparable K E]

theorem toStar_algebraMap_ptA (hEU : E ≤ maxUnram (Rfin Fq K) K) {m n : ℕ}
    (hcard : Fintype.card (Kc Fq E) = Fintype.card Fq ^ m) (hmn : m ∣ n) (c : Fq) :
    toStar Fq hq hEU hcard hmn (algebraMap Fq (Kc Fq E) c) = algebraMap Fq (kStar (Rfin Fq K) K hq n) c := by
  apply Subtype.ext
  apply Subtype.ext
  show (((algebraMap Fq (Kc Fq E) c : Kc Fq E) : E) : AlgebraicClosure K) =
    algebraMap K (AlgebraicClosure K) (algebraMap Fq K c)
  exact coe_algebraMap_kc Fq E c

variable (hEL : E ≤ L) [FiniteDimensional K L] [IsGalois K L]

theorem algebraMap_rfixE_fq (c : Fq) :
    algebraMap (Rfin Fq K) (rfixE Fq hEL) (algebraMap Fq (Rfin Fq K) c) =
      kappaE Fq hEL (algebraMap Fq (Kc Fq E) c) := by
  apply rfixE_ext Fq hEL
  rw [kappaE_val, coe_algebraMap_kc]
  rfl

variable (Ω : Type) [Field Ω]

end PtAsm

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {K : Type} [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)

end Main

end

end Lefschetz
end RamanujanPetersson


end

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

/-- The number of `u ∈ S` with `f u` conjugate to `γ`. -/
def ptCount {X G : Type} [Group G] (S : Finset X) (f : X → G) (γ : G) : ℕ := by
  classical
  exact (S.filter fun u => IsConj (f u) γ).card

section Count

variable {G : Type} [Group G]

end Count

section Main

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end Main

end

end Lefschetz
end RamanujanPetersson


end


