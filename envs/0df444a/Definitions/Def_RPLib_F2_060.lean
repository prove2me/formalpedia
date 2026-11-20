-- Prove2me | Definitions.Def_RPLib_F2_060
-- name    : RPLib_F2_060
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T21:38:00.59075+00:00
-- url     : https://prove2.me/theorems/d77e0818-6528-46e0-9ea4-2bea289d22ac
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 060 of 70
-- statement:
--   File 060 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
--   * `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
--   * `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
--   * `S4.Def_RP_ThetaCube_Deg`: S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor
--   * `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--   * `S4.Def_RP_ThetaCube_Surj`: S4-ThetaCube, file Surj (D-C2): a surjection from `X1^n` detects Weil divisors by lines
--   * `S4.Def_RP_ThetaCube_Ord`: S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders
--   * `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
--   * `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
--   * `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
--   * `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
--   * `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
--   * `S4.Def_RP_ThetaCube_Gen`: S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
--   * `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
--   * `S4.Def_RP_ThetaCube_NZS`: S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
--   * `S4.Def_RP_ThetaCube_Pick`: S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
--   * `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
--   * `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
--   * `S4.Def_RP_ThetaCube_TrNe`: S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
--   * `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
--   * `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--   * `S4.Def_RP_ThetaCube_GrC`: S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
--   * `S4.Def_RP_ThetaCube_Surj3`: S4-ThetaCube, file Surj3 (D-C1, part 10): `Φ3 : X1^n ⟶ J^3` is surjective and dominant
--   * `S4.Def_RP_JacFrob_PolyG`: S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_059

/-!
# Ramanujan-Petersson curve library (flat edition), file 060 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
* `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
* `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
* `S4.Def_RP_ThetaCube_Deg`: S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor
* `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
* `S4.Def_RP_ThetaCube_Surj`: S4-ThetaCube, file Surj (D-C2): a surjection from `X1^n` detects Weil divisors by lines
* `S4.Def_RP_ThetaCube_Ord`: S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders
* `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
* `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `S4.Def_RP_ThetaCube_Gen`: S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
* `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `S4.Def_RP_ThetaCube_NZS`: S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
* `S4.Def_RP_ThetaCube_Pick`: S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
* `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `S4.Def_RP_ThetaCube_TrNe`: S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
* `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
* `S4.Def_RP_ThetaCube_GrC`: S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
* `S4.Def_RP_ThetaCube_Surj3`: S4-ThetaCube, file Surj3 (D-C1, part 10): `Φ3 : X1^n ⟶ J^3` is surjective and dominant
* `S4.Def_RP_JacFrob_PolyG`: S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Sep =====
section

/-!
# Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)

* **`eq_one_of_stab`**: a `K`-point `c` of `J` with `W(K) · c ⊆ W` is `1` (Riemann's theorem `mem_W_iff` and the
  divisor form `mem_PrincK_of_stab`);
* `hsep_W`: translates of `W` separate `K`-points: for `b ≠ b'` some `a` has `b a ∈ W`, `b' a ∉ W`;
* `support_effI_Theta`: the support of the ideal sheaf `effI Θ` is `W`; `support_effI_Theta_ne_top`;
* **`hsep_Theta`**: the `hsep` hypothesis of `inum_pos` for `D = Θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors
open RamanujanPetersson.IntersectC

universe u

section Sep

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem support_effI_Theta_ne_top (hg : 0 < genusFK K F) : (effI (Theta P0)).support ≠ ⊤ := by
  have : IsLocallyNoetherian (Jac K F).left := LocallyOfFiniteType.isLocallyNoetherian (Jac K F).hom
  exact support_effI_ne_top (Theta P0) (theta_mem_weilDivisors P0 hg) (finite_support_Theta P0)

end Sep

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_ThetaX0 =====
section

/-!
# Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`

* `pullback_openImm`: the pull-back of a Weil divisor along an open immersion is its restriction;
* `tauX d`, an open immersion, dominant; `pullback_tauX_apply`: `τ_d^* Θ` is the indicator of `τ_d⁻¹ (zTheta)`;
* `exists_eta`: if `τ_d y ∈ W`, then `zTheta = τ_d η'` for some `η' ⤳ y`;
* `exists_sep`: finitely many `K`-points of `Rfin` off a finite set `S` are common zeros of an `s` that has no zero on `S`;
* `normS_mem_eta` (the upper-bound input of the plus-curve trick): if `φ(t) = 0` and some chart point `A` contains `φ`
  but no other zero of `t`, then `Nm(t)` vanishes at the point `η'` with `τ_{c_φ⁻¹} η' = zTheta`. Proof: a minimal prime
  `q ⊆ m_A` of `(Nm t)` has height `≤ 1` (Krull); every closed point of `V(Nm t)` contains a zero of `t`, so it lies on
  `τ⁻¹ W` (if that zero is `φ`, `mem_transl_W`) or on `V(Nm s)` (`s` vanishing at the other zeros, none on `A`); by
  Jacobson `q ∈ τ⁻¹ W`, and `coheight zTheta = 1` forces `τ q = zTheta`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section General

open CategoryTheory AlgebraicGeometry

variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  [∀ y : C, UniqueFactorizationMonoid (C.presheaf.stalk y)] (ι : U ⟶ C) [IsOpenImmersion ι] [IsDominant ι]

end General

section ThetaX0

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- `τ_d^* Θ` is the indicator of the point over `zTheta`. -/
theorem pullback_tauX_apply (hg : 0 < genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (z : X0 K F) :
    JacDivisors.pullback (tauX d) (Theta P0) z = if tauX d z = zTheta P0 then 1 else 0 := by
  rw [pullback_openImm (tauX d) (theta_mem_weilDivisors P0 hg) z, Theta_apply]

set_option maxHeartbeats 1000000 in
/-- **Upper-bound input**: `Nm(t)` vanishes at the point `η'` over `zTheta` of the chart translated by `c_φ⁻¹`, as soon
as one chart point `A` contains `φ` and no other zero of `t`. -/
theorem normS_mem_eta (hg : 0 < genusFK K F) (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
    (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
      clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (φ : Rfin K F →ₐ[K] K) {t : Rfin K F} (ht0 : t ≠ 0) (ht : φ t = 0)
    (yA : LawRing K F →ₐ[K] K) (hφA : φ ∈ ptSet (yA.comp (awayι (K := K) (lawPre K F).u0)))
    (hA : ∀ ψ ∈ ptSet (yA.comp (awayι (K := K) (lawPre K F).u0)), ψ t = 0 → ψ = φ)
    {z : X0 K F} (hz : tauX (c φ)⁻¹ z = zTheta P0) :
    awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t) ∈
      PrimeSpectrum.asIdeal (R := LawRing K F) z := by
  obtain ⟨s, hsT, hsA⟩ := exists_sep (ptSet (yA.comp (awayι (K := K) (lawPre K F).u0)))
    ((finite_zeros ht0).toFinset.erase φ) (by
      rw [Finset.disjoint_right]
      intro e he heA
      have h1 := Finset.mem_erase.1 he
      exact h1.1 (hA e heA ((finite_zeros ht0).mem_toFinset.1 h1.2)))
  set N : LawRing K F := awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t) with hN_def
  set M : LawRing K F := awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) s) with hM_def
  have hN : ∀ yR : LawRing K F →ₐ[K] K, yR N = 0 →
      ∃ ψ ∈ ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)), ψ t = 0 := by
    intro yR h
    rw [hN_def, eval_normS] at h
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 h
    exact ⟨_, (mem_ptSet _ _).2 ⟨l, rfl⟩, hl⟩
  have hyAN : yA N = 0 := by
    obtain ⟨l, hl⟩ := (mem_ptSet _ _).1 hφA
    rw [hN_def, eval_normS]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [hl]; exact ht)
  have hyAM : yA M ≠ 0 := by
    rw [hM_def, eval_normS]
    exact Finset.prod_ne_zero_iff.2 fun l _ => hsA _ ((mem_ptSet _ _).2 ⟨l, rfl⟩)
  -- the minimal prime `q ⊆ m_A` of `(N)` (Krull: height `≤ 1`)
  have hNk : Ideal.span {N} ≤ RingHom.ker (yA : LawRing K F →+* K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 hyAN
  haveI : (RingHom.ker (yA : LawRing K F →+* K)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqmin, hqk⟩ := Ideal.exists_minimalPrimes_le hNk
  have hq1 : q.height ≤ 1 := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := ({N} : Finset (LawRing K F))) (p := q)
      (by rw [Finset.coe_singleton]; exact hqmin)
    rwa [Finset.card_singleton, Nat.cast_one] at h1
  let xq : X0 K F := ((⟨q, hqmin.1.1⟩ : PrimeSpectrum (LawRing K F)) : X0 K F)
  have hMq : M ∉ q := fun h => hyAM (RingHom.mem_ker.1 (hqk h))
  -- `V(N) ⊆ τ⁻¹ W ∪ V(M)` (closed points, then Jacobson)
  let Sset : Set (X0 K F) :=
    tauX (c φ)⁻¹ ⁻¹' W P0 ∪ (PrimeSpectrum.zeroLocus ({M} : Set (LawRing K F)) : Set (X0 K F))
  have hS : IsClosed Sset :=
    ((isClosed_W P0).preimage (tauX (c φ)⁻¹).continuous).union (PrimeSpectrum.isClosed_zeroLocus _)
  haveI hJ : JacobsonSpace (X0 K F) := LocallyOfFiniteType.jacobsonSpace (jX0 K F ≫ (Jac K F).hom)
  haveI : JacobsonSpace (PrimeSpectrum ↑(CommRingCat.of (LawRing K F))) := hJ
  have hV : IsClosed (PrimeSpectrum.zeroLocus ({N} : Set (LawRing K F)) : Set (X0 K F)) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hsub : (PrimeSpectrum.zeroLocus ({N} : Set (LawRing K F)) : Set (X0 K F)) ⊆ Sset := by
    rw [← closure_inter_closedPoints hV]
    refine closure_minimal ?_ hS
    rintro p ⟨hpN, hpc⟩
    obtain ⟨yR, rfl⟩ := JacLaw.exists_kpt (K := K) (A := LawRing K F) p hpc
    have hyN : yR N = 0 := by
      have h1 : N ∈ PrimeSpectrum.asIdeal (R := LawRing K F) (kpt yR) :=
        (PrimeSpectrum.mem_zeroLocus _ _).1 hpN (Set.mem_singleton N)
      rwa [kpt_asIdeal, RingHom.mem_ker] at h1
    obtain ⟨ψ, hψ, hψt⟩ := hN yR hyN
    by_cases hψφ : ψ = φ
    · refine Or.inl ?_
      show tauX (c φ)⁻¹ (kpt yR) ∈ W P0
      rw [tauX_apply]
      rw [hψφ] at hψ
      exact mem_transl_W P0 c hc yR φ hψ
    · refine Or.inr ((PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.2 ?_))
      show M ∈ PrimeSpectrum.asIdeal (R := LawRing K F) (kpt yR)
      rw [kpt_asIdeal, RingHom.mem_ker]
      obtain ⟨l, hl⟩ := (mem_ptSet _ _).1 hψ
      rw [hM_def, eval_normS]
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by
        rw [hl]
        exact hsT ψ (Finset.mem_erase.2 ⟨hψφ, (finite_zeros ht0).mem_toFinset.2 hψt⟩))
  have hxq : xq ∈ Sset := hsub ((PrimeSpectrum.mem_zeroLocus _ _).2
    (Set.singleton_subset_iff.2 (hqmin.1.2 (Ideal.subset_span rfl))))
  have hxqW : tauX (c φ)⁻¹ xq ∈ W P0 := by
    rcases (Set.mem_union _ _ _).1 hxq with h | h
    · exact h
    · exact absurd ((PrimeSpectrum.mem_zeroLocus _ _).1 h (Set.mem_singleton M)) hMq
  -- coheight: `τ xq = zTheta`
  have hspec : tauX (c φ)⁻¹ xq ≤ zTheta P0 :=
    specializes_iff_mem_closure.2 (by rw [closure_zTheta P0]; exact hxqW)
  have hco : Order.coheight (tauX (c φ)⁻¹ xq) ≤ 1 := by
    rw [(tauX (c φ)⁻¹).isOpenEmbedding.coheight_eq, ← idealHeight_eq_coheight (.of (LawRing K F)) xq]
    exact hq1
  have heq : tauX (c φ)⁻¹ xq = zTheta P0 := by
    by_contra hne
    have hlt := Order.coheight_strictAnti (lt_of_le_not_ge hspec fun h =>
      hne (Specializes.antisymm (show tauX (c φ)⁻¹ xq ⤳ zTheta P0 from h)
        (show zTheta P0 ⤳ tauX (c φ)⁻¹ xq from hspec)).eq)
      (by rw [coheight_zTheta P0 hg]; exact ENat.one_lt_top)
    rw [coheight_zTheta P0 hg] at hlt
    exact absurd (lt_of_lt_of_le hlt hco) (lt_irrefl _)
  have hzq : z = xq := (tauX (c φ)⁻¹).isOpenEmbedding.injective (hz.trans heq.symm)
  rw [hzq]
  exact hqmin.1.2 (Ideal.subset_span rfl)

end ThetaX0

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Mult2 =====
section

/-!
# Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)

* `avoid_Theta`: a map to `J` with one point off `W` avoids `Θ`;
* `kappa`: the plus-curve chart map `κ = Spec (lawMapPlus) : Spec R2 → X0`, `jMap_transl`, `kappa_kpt`;
* `lawMapPlus_normS`: `κ^* (Nm t) = t · ∏_{i ≠ i0} a_i(t)`;
* `fpull_kappa`, `ord_fpull_kappa`: `κ^* (Nm t)` has order one at a `K`-point `x` when `t` is a uniformizer at
  `ptR2 x` with no zero at the other points `a_i`;
* **`cpull_kappa_eq_one`**: `(τ ∘ κ)^* Θ` has multiplicity exactly one at every `K`-point `x` of the plus-curve
  (`τ = τ_{c_φ⁻¹}`, `φ = ptR2 x`): lower bound by `exists_eta` + `cpull_pos`, upper bound by `cpull_le_ord` with the
  norm `Nm t` (`normS_mem_eta`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Mult2

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

variable (hg : 0 < genusFK K F) (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

include hg hc in
/-- Lower bound: `κ (kpt x)` lies on the translate of `W`. -/
theorem one_le_cpull_kappa [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K)
    (hA' : Avoid (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0))) :
    1 ≤ cpull (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0)) (kpt x) := by
  have hy : tauX (c (ptR2 c0 a i0 x))⁻¹ (kappa c0 a i0 (kpt x)) ∈ W P0 := by
    rw [kappa_kpt, tauX_apply]
    exact mem_transl_W P0 c hc _ _ (mem_ptSet_plus c0 a i0 x)
  obtain ⟨z₀, hz₀, hsp⟩ := exists_eta P0 _ hy
  have hpos := cpull_pos (kappa c0 a i0) (pullback_mem_weilDivisors _ (Theta P0)) hA'
    (coheight_kpt_R2 c0 a i0 x)
    (fun z _ _ => by rw [pullback_tauX_apply P0 hg]; split_ifs <;> norm_num) hsp
    (by rw [pullback_tauX_apply P0 hg, if_pos hz₀]; norm_num)
  omega

end Mult2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_Deg =====
section

/-!
# S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor

* `polyEnd_one`: `1(π) = 𝟙`.
* `exists_avoid`, `cTh P0 hg φ := (φ ≫ τ_b)^* Θ` for a translate `b` whose image avoids `Θ`.
* `iform_cTh`: `(cTh φ)^g = deg φ · (Θ^g)`.
* `formTh g hdim`: the intersection form as a multilinear map (`DegPoly.formOfAdd` of `iform`).
* `hD_Th`, `hproj_Th`: the hypotheses `hD` and `hproj` of `DegPoly.degreeDataOfQuad` for
  `c G := cTh (polyEnd π G)` and `deg G := degree (polyEnd π G).left`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

end Poly

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (K F) in
/-- The intersection form on cycles of `J`, as a multilinear map. -/
noncomputable def formTh (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g) :
    MultilinearMap ℤ (fun _ : Fin g => AlgebraicCycle (Jac K F).left ℤ) ℤ :=
  DegPoly.formOfAdd (iform (Jac K F) g hdim) (iform_update_add (Jac K F) g hdim)

theorem formTh_apply (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g)
    (w : Fin g → AlgebraicCycle (Jac K F).left ℤ) : formTh K F g hdim w = iform (Jac K F) g hdim w :=
  rfl

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Sym =====
section

/-!
# S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`

* `algebraMap_generic`, **`cpull_eq_pullback`**: for a dominant map, `cpull` is `JacDivisors.pullback`;
* `negJ = (𝟙 J)⁻¹` (the inverse map), `comp_negJ : φ ≫ negJ = φ⁻¹`;
* `DTh P0 x0 := τ_{x0}^* Θ + (negJ ≫ τ_{x0})^* Θ`: Weil (`DTh_mem`), effective (`DTh_nonneg`);
* `avoid_DTh`: every homomorphism avoids `DTh P0 x0` when `x0 ∉ W`;
* **`cpull_DTh`**: `φ^* D' = (φ ≫ τ_{x0})^* Θ + (φ⁻¹ ≫ τ_{x0})^* Θ`;
* **`cpull_inv_DTh`**: `(φ⁻¹)^* D' = φ^* D'` (exact symmetry).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (φ : C ⟶ Y) [IsDominant φ]

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

lemma avoid_one_transl (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hx0 : pt (Jac K F) x0 ∉ W P0) :
    Avoid (transl (Jac K F) x0).left (Theta P0) := by
  have h := avoid_of_one_comp P0 x0 hx0 (𝟙 _) (Category.comp_id _)
  rw [Category.id_comp] at h
  exact h

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Surj =====
section

/-!
# S4-ThetaCube, file Surj (D-C2): a surjection from `X1^n` detects Weil divisors by lines

Let `Φ : X1^n ⟶ Y` be surjective (`Y` integral, locally Noetherian, factorial stalks) and `E` a Weil divisor on `Y`
such that for every `K`-point `p` of `X1^n` and every direction `i`, the composite `line i p ≫ Φ`, whenever it avoids
`E`, pulls `E` back to `0` at the parameter of `p`. Then `E = 0`.
Proof: if `E y > 0` (`y` of codimension one), `exists_open_test` gives an open `U ∋ y` on which (a) every avoiding
test curve through `closure {y} ∩ U` has positive pull-back and (b) every curve through `U` whose generic point
leaves `closure {y}` avoids `E`. Take a component `T'` of `Φ⁻¹ (closure {y})` maximal among those meeting the fibre
over `y`; its generic point lies over `y`. Off the other components, every line through a point of `T' ∩ Φ⁻¹ U`
stays in `T'` (else (b) and (a) contradict the hypothesis), so `T' = X1^n` by `reach`, and `y` would be generic.
* `exists_open_test` (general curves and schemes);
* **`eq_zero_of_surj`** (line hypothesis), **`eq_zero_of_cpull_surj`** (`Φ` dominant, `cpull Φ E = 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Test

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

end Test

section Surj

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]
variable {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

lemma false_of_surj_pos (Φ : (PP K F n).left ⟶ Y) (hsurj : Function.Surjective Φ)
    {E : AlgebraicCycle Y ℤ} (hE : E ∈ weilDivisors Y)
    (htest : ∀ i (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n), Avoid ((line K F n i p).left ≫ Φ) E →
      cpull ((line K F n i p).left ≫ Φ) E ((p ≫ prj K F n i).left (IsLocalRing.closedPoint K)) = 0)
    {y : Y} (hy : Order.coheight y = 1) (hpos : 0 < E y) : False := by
  haveI : CompactSpace (PP K F n).left := QuasiCompact.compactSpace_of_compactSpace (PP K F n).hom
  haveI : IsNoetherian (PP K F n).left := {}
  obtain ⟨U, hUo, hyU, ha, hb⟩ := exists_open_test (C := (X1O K F).left) hE hy hpos
  have hTc : IsClosed (Φ ⁻¹' closure {y}) := isClosed_closure.preimage Φ.continuous
  obtain ⟨S, hS, hST⟩ := NoetherianSpace.exists_finset_irreducible
    (⟨Φ ⁻¹' closure {y}, hTc⟩ : Closeds (PP K F n).left)
  have hCT : ∀ C ∈ S, (C : Set (PP K F n).left) ⊆ Φ ⁻¹' closure {y} := fun C hCS x hx => by
    have h : C ≤ S.sup id := Finset.le_sup (f := id) hCS
    rw [← hST] at h
    exact SetLike.coe_subset_coe.mpr h hx
  have hTS : ∀ z ∈ Φ ⁻¹' closure {y}, ∃ C ∈ S, z ∈ (C : Set (PP K F n).left) := fun z hz => by
    have hzT : z ∈ ((S.sup id : Closeds (PP K F n).left) : Set (PP K F n).left) := by rw [← hST]; exact hz
    rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hzT
    obtain ⟨C, hCS, hzC⟩ := hzT
    exact ⟨C, hCS, hzC⟩
  obtain ⟨a, ha'⟩ := hsurj y
  have haT : a ∈ Φ ⁻¹' closure {y} := by
    show Φ a ∈ closure {y}
    rw [ha']
    exact subset_closure rfl
  set M : Set (Closeds (PP K F n).left) := {C | C ∈ S ∧ y ∈ Φ '' (C : Set (PP K F n).left)} with hM
  have hMfin : M.Finite := S.finite_toSet.subset fun C hC => hC.1
  have hMne : M.Nonempty := by
    obtain ⟨C, hCS, haC⟩ := hTS a haT
    exact ⟨C, hCS, a, haC, ha'⟩
  obtain ⟨C0, hC0⟩ := hMfin.exists_maximal hMne
  obtain ⟨t, hgen⟩ : ∃ t, IsGenericPoint t (C0 : Set (PP K F n).left) :=
    ⟨_, (hS ⟨C0, hC0.1.1⟩).isGenericPoint_genericPoint C0.isClosed⟩
  have hΦt : Φ t = y := by
    obtain ⟨c, hcC, hcy⟩ := hC0.1.2
    have h1 : Φ t ⤳ y := by
      rw [← hcy]
      exact (hgen.specializes hcC).map Φ.continuous
    have h2 : y ⤳ Φ t := specializes_iff_mem_closure.mpr (hCT C0 hC0.1.1 hgen.mem)
    exact (h1.antisymm h2).eq
  set R : Set (PP K F n).left :=
    ⋃ C ∈ {C | C ∈ S ∧ ¬ (C : Set (PP K F n).left) ⊆ C0}, (C : Set (PP K F n).left) with hRdef
  have hRc : IsClosed R :=
    (S.finite_toSet.subset fun C hC => hC.1).isClosed_biUnion fun C _ => C.isClosed
  have htR : t ∉ R := by
    rw [hRdef, Set.mem_iUnion₂]
    rintro ⟨C, ⟨hCS, hCC0⟩, htC⟩
    have hsub : (C0 : Set (PP K F n).left) ⊆ C := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr htC) C.isClosed
    exact hCC0 (SetLike.coe_subset_coe.mpr (hC0.2 ⟨hCS, t, htC, hΦt⟩ (SetLike.coe_subset_coe.mp hsub)))
  have hTR : Φ ⁻¹' closure {y} ⊆ (C0 : Set (PP K F n).left) ∪ R := by
    intro z hz
    obtain ⟨C, hCS, hzC⟩ := hTS z hz
    by_cases hCC0 : (C : Set (PP K F n).left) ⊆ C0
    · exact Or.inl (hCC0 hzC)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨C, ⟨hCS, hCC0⟩, hzC⟩)
  have hU'o : IsOpen (Φ ⁻¹' U ∩ Rᶜ) := (hUo.preimage Φ.continuous).inter hRc.isOpen_compl
  have hval : ∀ i (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n),
      (line K F n i p).left ((p ≫ prj K F n i).left (IsLocalRing.closedPoint K)) =
        p.left (IsLocalRing.closedPoint K) := fun i p =>
    congrArg (fun φ => φ.left (IsLocalRing.closedPoint K)) (line_val n i p)
  have hlines : LinesIn K F n (C0 : Set (PP K F n).left) (Φ ⁻¹' U ∩ Rᶜ) := by
    rintro p ⟨hpC, hpU, hpR⟩ i
    by_cases hη : Φ ((line K F n i p).left (genericPoint (X1O K F).left)) ∈ closure {y}
    · have hηC : (line K F n i p).left (genericPoint (X1O K F).left) ∈ (C0 : Set (PP K F n).left) := by
        rcases hTR hη with h | h
        · exact h
        · refine absurd ?_ hpR
          rw [← hval i p]
          exact (xi_specializes _ _).mem_closed hRc h
      rintro _ ⟨c, rfl⟩
      exact (xi_specializes _ c).mem_closed C0.isClosed hηC
    · exfalso
      have hx1 := coheight_kpt_X1 (p ≫ prj K F n i)
      have hxU : ((line K F n i p).left ≫ Φ) ((p ≫ prj K F n i).left (IsLocalRing.closedPoint K)) ∈ U := by
        show Φ ((line K F n i p).left _) ∈ U
        rw [hval i p]
        exact hpU
      have hxy : ((line K F n i p).left ≫ Φ) ((p ≫ prj K F n i).left (IsLocalRing.closedPoint K)) ∈
          closure {y} := by
        show Φ ((line K F n i p).left _) ∈ closure {y}
        rw [hval i p]
        exact hCT C0 hC0.1.1 hpC
      have hA := hb ((line K F n i p).left ≫ Φ) _ hxU hη
      have key := ha ((line K F n i p).left ≫ Φ) _ hxU hxy hx1 hA
      rw [htest i p hA] at key
      exact lt_irrefl _ key
  have hC0U := reach (K := K) (F := F) n (C0 : Set (PP K F n).left) (Φ ⁻¹' U ∩ Rᶜ) C0.isClosed
    (hS ⟨C0, hC0.1.1⟩) hU'o ⟨t, hgen.mem, by show Φ t ∈ U ∧ t ∉ R; exact ⟨hΦt ▸ hyU, htR⟩⟩ hlines
  have hYU : closure {y} = (Set.univ : Set Y) := Set.eq_univ_iff_forall.mpr fun b => by
    obtain ⟨a', rfl⟩ := hsurj b
    refine hCT C0 hC0.1.1 ?_
    rw [hC0U]
    exact Set.mem_univ a'
  have hmax : IsMax y := fun b _ => specializes_iff_mem_closure.mpr (Set.eq_univ_iff_forall.mp hYU b)
  rw [Order.coheight_eq_zero.mpr hmax] at hy
  exact zero_ne_one hy

/-- **Surjections from `X1^n` detect Weil divisors by lines.** -/
theorem eq_zero_of_surj (Φ : (PP K F n).left ⟶ Y) (hsurj : Function.Surjective Φ)
    {E : AlgebraicCycle Y ℤ} (hE : E ∈ weilDivisors Y)
    (htest : ∀ i (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n), Avoid ((line K F n i p).left ≫ Φ) E →
      cpull ((line K F n i p).left ≫ Φ) E ((p ≫ prj K F n i).left (IsLocalRing.closedPoint K)) = 0) :
    E = 0 := by
  ext y
  rw [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  by_cases hy : Order.coheight y = 1
  · rcases lt_trichotomy (E y) 0 with h | h | h
    · exfalso
      refine false_of_surj_pos Φ hsurj ((weilDivisors Y).neg_mem hE) (fun i p hA => ?_) hy ?_
      · have hA' := avoid_neg _ hA
        rw [neg_neg] at hA'
        rw [cpull_neg _ hE hA', Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, htest i p hA', neg_zero]
      · rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply]
        omega
    · exact h
    · exact (false_of_surj_pos Φ hsurj hE htest hy h).elim
  · by_contra h
    exact hy (hE y h)

end Surj

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Ord =====
section

/-!
# S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders

* `val_chart_algebraMap`: on a singleton chart, the stalk valuation at `kpt ψ0` is `≤ 1` on the chart ring
  and `< 1` exactly on `ker ψ0`;
* `ord_chart_kpt`: `ord_{kpt ψ0} h = P.ord (psiA h)` for the center `P` of `ψ0`;
* **`ord_kpt`**: `ord_{q} g = (kPl q).ord (PsiX g)`; `ord_phiX_kpt`; `ord_genericPoint_X1 = 0`;
* `isClosed_of_coheight_X1`; **`eq_of_kpt_X1`**: Weil divisors on `X1` agree if they agree at `K`-points.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.JacLaw RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Ord

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **D-B1 (dictionary on `X1`).** The order of a rational function at a `K`-point `q` of `X1` is the order
of the corresponding element of `F` at the place `kPl q`. -/
theorem ord_kpt (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (g : (X1 K F).functionField) :
    Scheme.ord g (q.left (IsLocalRing.closedPoint K)) = (kPl q).ord (PsiX K F g) := by
  obtain ⟨c, ψ0, hcen, hq⟩ := exists_chart0 hg q
  haveI := isOpenImmersion_ιX1 (K := K) (F := F) (Ac K c)
  haveI : IsLocallyNoetherian ((symDiagram K (algebraMap K[X] F X) 1).obj (Ac K c)) :=
    (inferInstance : IsLocallyNoetherian (cht K F (Ac K c)))
  haveI : IsIntegral (colimit (symDiagram K (algebraMap K[X] F X) 1)) :=
    (inferInstance : IsIntegral (X1 K F))
  haveI : IsLocallyNoetherian (colimit (symDiagram K (algebraMap K[X] F X) 1)) :=
    (inferInstance : IsLocallyNoetherian (X1 K F))
  have h1 := ord_ffMap_openImm (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (Ac K c)) g
    (kpt (A := SymRing K (Bc F c) 1) ψ0)
  have h2 := ord_chart_kpt c ψ0 hcen
    ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (Ac K c))).hom g)
  have h3 : PsiX K F g =
      psiA K F (Ac K c) ((ffMap (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (Ac K c))).hom g) := by
    rw [← PsiA_eq_PsiX (Ac K c)]
    rfl
  rw [hq, h3]
  exact h1.symm.trans h2

theorem ord_phiX_kpt (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (f : F) :
    Scheme.ord (phiX K F f) (q.left (IsLocalRing.closedPoint K)) = (kPl q).ord f := by
  rw [ord_kpt hg, PsiX_phiX]

theorem div_kpt (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (g : (X1 K F).functionField) :
    JacDivisors.div (X1 K F) g (q.left (IsLocalRing.closedPoint K)) = (kPl q).ord (PsiX K F g) :=
  ord_kpt hg q g

end Ord

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Slice =====
section

/-!
# S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `line_prj_self`, `line_prj_ne`: a line against the projections;
* `cval q g` (the constant `g(q)` as an element of `F`), **`cval_mem`**: it lies in `K`;
* `exists_stalk_of_ord`: nonnegative place order at `q` ⇒ regular at the point `q`;
* `zPP`, `detPP` (the determinant `det_k`), `sliceRow`;
* **`slice_detPP`**: `PsiX (fpull line (detPP ..)) = det (sliceRow ..)`; **`avoid_detPP`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Slice

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- Nonnegative order at the place of `q` ⇒ regular at the point `q`. -/
theorem exists_stalk_of_ord (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (f : F)
    (hf : 0 ≤ (kPl q).ord f) {x : (X1O K F).left} (hx : x = q.left (IsLocalRing.closedPoint K)) :
    ∃ w : (X1O K F).left.presheaf.stalk x, algebraMap _ (X1O K F).left.functionField w = phiX K F f := by
  subst hx
  obtain ⟨w, hw⟩ := mem_range_algebraMap_stalk_of_ord_nonneg (q.left (IsLocalRing.closedPoint K))
    (phiX K F f) (fun z hz h1 => by
      by_cases hzq : z = q.left (IsLocalRing.closedPoint K)
      · subst hzq
        rw [ord_phiX_kpt hg]
        exact hf
      · exact absurd hz (not_specializes_of_coheight (coheight_kpt_X1 q) h1 hzq))
  exact ⟨w, hw⟩

variable (K F) in
/-- **`det_k`**: `det [ pr_{τ j}^# h_l ; h_l(m_i) ]` in the function field of `X1^n`. -/
noncomputable def detPP (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (h : Fin N ⊕ Fin r → F) : (PP K F n).left.functionField :=
  (Matrix.of fun a l => fpull (zPP K F n τ m a) (phiX K F (h l))).det

variable (K F) in
/-- The slice matrix over `F`: row `j` is `h` if `τ j = i0`, else the constants `h(p_{τ j})`; then `h(m_i)`. -/
noncomputable def sliceRow (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (h : Fin N ⊕ Fin r → F) :
    Fin N ⊕ Fin r → Fin N ⊕ Fin r → F :=
  fun a l => Sum.elim (fun j => if τ j = i0 then h l else cval K F (p ≫ prj K F n (τ j)) (phiX K F (h l)))
    (fun i => cval K F (m i) (phiX K F (h l))) a

/-- Regularity of the entries of `det_k` at the generic point of a line. -/
theorem reg_detPP (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hτ : ∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l))
    (hm : ∀ i l, 0 ≤ (kPl (m i)).ord (h l)) (a l : Fin N ⊕ Fin r) :
    ∃ w : (X1O K F).left.presheaf.stalk (((line K F n i0 p).left ≫ zPP K F n τ m a) (genericPoint _)),
      algebraMap _ (X1O K F).left.functionField w = phiX K F (h l) := by
  rcases a with j | i
  · by_cases hj : τ j = i0
    · rw [line_zPP_self n τ m i0 p j hj]
      exact ⟨phiX K F (h l), algebraMap_generic _⟩
    · rw [line_zPP_ne n τ m i0 p j hj]
      exact exists_stalk_of_ord hg _ _ (hτ j hj l) (toUnit_comp_apply _ _)
  · rw [line_zPP_inr n τ m i0 p i]
    exact exists_stalk_of_ord hg _ _ (hm i l) (toUnit_comp_apply _ _)

end Slice

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cof =====
section

/-!
# S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `det_mem_range`: a matrix with entries in `K` has its determinant in `K`;
* **`slice_mem_LFK`** (Laplace along the variable row): the slice lies in `L(D)` when every `h l` does;
* `ptRow` (the point of each row, `q` in the variable rows), `comp_line_zPP`;
* **`ord_slice_pos`**: the slice vanishes at `q` when two rows sit at `q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Cof

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Laplace along the variable row**: the slice is a `K`-combination of the `h l`. -/
theorem slice_mem_LFK (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (h : Fin N ⊕ Fin r → F) (j0 : Fin N)
    (hτ0 : τ j0 = i0) (hj0 : ∀ j, τ j = i0 → j = j0) (D : Places.Divisor K F) (hD : ∀ l, h l ∈ LFK K F D) :
    (Matrix.of (sliceRow K F n τ m i0 p h)).det ∈ LFK K F D := by
  rw [Matrix.det_eq_sum_mul_adjugate_row _ (Sum.inl j0)]
  refine Submodule.sum_mem _ fun l _ => ?_
  have e : Matrix.of (sliceRow K F n τ m i0 p h) (Sum.inl j0) l = h l := by
    simp only [Matrix.of_apply, sliceRow, Sum.elim_inl, if_pos hτ0]
  obtain ⟨c, hc⟩ := det_mem_range (K := K)
    ((Matrix.of (sliceRow K F n τ m i0 p h)).updateRow (Sum.inl j0) (Pi.single l 1)) (by
      intro a l'
      rw [Matrix.updateRow_apply]
      split_ifs with ha
      · rw [Pi.single_apply]
        split_ifs
        exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
      · rcases a with j | i
        · have hj : τ j ≠ i0 := fun h' => ha (by rw [hj0 j h'])
          simp only [Matrix.of_apply, sliceRow, Sum.elim_inl, if_neg hj]
          exact cval_mem _ _
        · simp only [Matrix.of_apply, sliceRow, Sum.elim_inr]
          exact cval_mem _ _)
  rw [e, Matrix.adjugate_apply, ← hc, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ c (hD l)

end Cof

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_NZ =====
section

/-!
# S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `ellFK_add_div`, `ellFK_of_clsK_eq`: `ℓ` only depends on the divisor class;
* `sliceRow_of_ne`: the constant rows of a slice are the values at `ptC`;
* **`slice_ne_zero`**: the slice with one variable row is nonzero when `ℓ(H - Zsl) ≤ 1`;
* **`slice_ne_zero_const`**: the all-constant slice is nonzero when `ℓ(H - Zall) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section NZ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

lemma sliceRow_of_ne (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (h : Fin N ⊕ Fin r → F) {a : Fin N ⊕ Fin r}
    (ha : ∀ j, a = Sum.inl j → τ j ≠ i0) (l : Fin N ⊕ Fin r) :
    sliceRow K F n τ m i0 p h a l = cval K F (ptC K F n τ m p a) (phiX K F (h l)) := by
  rcases a with j | i
  · simp only [sliceRow, ptC, Sum.elim_inl, if_neg (ha j rfl)]
  · rfl

end NZ

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Test =====
section

/-!
# S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
At `z = p_{i0}` on the `i0`-th line through `p`:
* `cpull_detPP_kpt`: the determinant side is `ord_{p_{i0}}` of the slice;
* `ord_slice_const`: an all-constant slice has order `0` everywhere;
* `ord_slice_eq`: the order of a one-variable slice is `G (p_{i0})` once `G ∼ H - Zsl`, `ℓ(G) = 1`;
* `cube_side_mem`, `cube_side_not_mem`: the `Θ` side via `line_psiS_transl`, `Dc_kpt_eq`, `cpull_const_Theta`;
* **`test_mem`**, **`test_not_mem`**: the two sides agree at `z` (both avoid);
* `Zsl_eq`, `jacPic_psiE`, `cls_good_eq`, **`cls_test`**: the class bookkeeping `[G_S] = [H - Zsl_S]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Test

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- An all-constant slice is a nonzero constant: its order is `0` at every place. -/
theorem ord_slice_const (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (hτ : ∀ j, τ j ≠ i0)
    (hne : (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0) (P : Place K F) :
    P.ord (Matrix.of (sliceRow K F n τ m i0 p h)).det = 0 := by
  choose V hVs using fun (a l : Fin N ⊕ Fin r) =>
    Set.mem_range.mp (cval_mem (ptC K F n τ m p a) (phiX K F (h l)))
  have e : (Matrix.of (sliceRow K F n τ m i0 p h)).det = algebraMap K F (Matrix.of V).det := by
    rw [RingHom.map_det]
    congr 1
    ext a l
    rw [Matrix.of_apply, sliceRow_of_ne n τ m i0 p h (fun j _ => hτ j), RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.of_apply, hVs]
  rw [e] at hne ⊢
  exact ord_algebraMap_K P fun h0 => hne (by rw [h0, map_zero])

/-- **`[G_S] = [H - Zsl_S]`** for a block enumeration `τ` and `x0` of class `[W0 + Σ m] - (2g + r - 2)[P0]`. -/
theorem cls_test {W0 G H : Places.Divisor K F} (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {N r : ℕ}
    (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (j0 : Fin N) (hτ0 : τ j0 = i0)
    (hτi : Function.Injective τ) (hτS : ∀ k, β k ∈ S ↔ ∃ j, τ j = k)
    (hx0 : ((Multiplicative.toAdd (jacPicEquiv K F x0) : Pic0K K F) : PicK K F) =
      clsK K F (W0 + ∑ i, Finsupp.single (kPl (m i)) 1) -
        (2 * (genusFK K F : ℤ) + r - 2) • clsK K F (Finsupp.single P0 1))
    (hH : clsK K F H = ((genusFK K F : ℤ) + r + ((Finset.univ.filter (fun k => β k ∈ S)).erase i0).card) •
      clsK K F (Finsupp.single P0 1))
    (hgood : IsGoodFor P0 W0 ((p ≫ psiE P0 n β S i0) * x0) G) :
    clsK K F G = clsK K F (H - Zsl K F n τ m p j0) := by
  rw [Zsl_eq n β S τ m p i0 j0 hτ0 hτi hτS]
  exact cls_good_eq P0 n β S i0 p x0 m hx0 hH hgood.cls

end Test

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Good =====
section

/-!
# S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `IsSat n i B`: `B` contains the `i`-th line through each of its `K`-points; `isSat_iUnion`, `isSat_empty`;
* `ConstAlong n i φ`: `φ` is constant along the `i`-th lines; `isSat_preimage`, closure under `≫`, `*`, `⁻¹`,
  constants, `psiE`, `epsS := psiE · x0`;
* `ne_univ_of_compl`: finitely many closed sets with nonempty complements do not cover an irreducible space;
* `exists_ne_place`: every place has a different one;
* **`bad P0 n β i x0 cK c2 A`** `= ⋃ badC`: `e_S(p) ∉ Ogood` (all `S`), `p_k = A l` (`k ≠ i`), `p_k = p_k'`
  (`k ≠ k'`, both `≠ i`), in Abel-Jacobi coordinates; **`isClosed_bad`**, **`isSat_bad`**, **`bad_ne_univ`** (when
  `x0 ∈ Ogood`), **`of_not_mem_bad`** (the three conditions at a good `K`-point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Good

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (n : ℕ) (β : Fin n → Fin 3) (i : Fin n) (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {s : ℕ}
  (A : Fin s → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))

theorem isClosed_badC (c : Finset (Fin 3) ⊕ (Fin n × Fin s) ⊕ (Fin n × Fin n)) :
    IsClosed (badC P0 n β i x0 cK c2 A c) := by
  rcases c with S | ⟨k, l⟩ | ⟨k, k'⟩
  · exact (isOpen_Ogood P0 cK c2).isClosed_compl.preimage (epsS P0 n β S i x0).left.continuous
  · rw [badC_mid]
    split_ifs
    · exact isClosed_empty
    · exact (JacChunk.GrpPt.isClosed_ev (Jac K F) (A l ≫ ajO P0)).preimage
        (prj K F n k ≫ ajO P0).left.continuous
  · rw [badC_pair]
    split_ifs
    · exact isClosed_empty
    · exact (JacChunk.GrpPt.isClosed_ev (Jac K F) 1).preimage
        ((prj K F n k ≫ ajO P0) * (prj K F n k' ≫ ajO P0)⁻¹).left.continuous

theorem isClosed_bad : IsClosed (bad P0 n β i x0 cK c2 A) :=
  isClosed_iUnion_of_finite (isClosed_badC P0 n β i x0 cK c2 A)

theorem isSat_bad : IsSat n i (bad P0 n β i x0 cK c2 A) :=
  isSat_iUnion _ (isSat_badC P0 n β i x0 cK c2 A)

theorem exists_not_mem_badC (hg : 0 < genusFK K F) (hx0 : pt (Jac K F) x0 ∈ Ogood P0 cK c2)
    (c : Finset (Fin 3) ⊕ (Fin n × Fin s) ⊕ (Fin n × Fin n)) : ∃ y, y ∉ badC P0 n β i x0 cK c2 A c := by
  obtain ⟨p0, hp0⟩ := exists_pt_coord hg P0 n (fun _ => P0)
  rcases c with S | ⟨k, l⟩ | ⟨k, k'⟩
  · refine ⟨p0.left (IsLocalRing.closedPoint K), ?_⟩
    rw [badC_inl]
    intro h
    apply h
    show (p0 ≫ epsS P0 n β S i x0).left (IsLocalRing.closedPoint K) ∈ Ogood P0 cK c2
    rw [comp_epsS, psiE_of_P0 P0 n β S i p0 hp0, _root_.one_mul]
    exact hx0
  · by_cases hk : k = i
    · exact ⟨p0.left (IsLocalRing.closedPoint K), by rw [badC_mid, if_pos hk]; simp⟩
    · obtain ⟨Q, hQ⟩ := exists_ne_place (kPl (A l))
      obtain ⟨p, hp⟩ := exists_pt_coord hg P0 n (fun _ => Q)
      refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
      rw [badC_mid, if_neg hk]
      intro h
      apply hQ
      have e : p ≫ prj K F n k ≫ ajO P0 = A l ≫ ajO P0 := JacChunk.GrpPt.ev_inj (Jac K F) h
      rw [← Category.assoc, kPl_spec P0 (p ≫ prj K F n k), kPl_spec P0 (A l), hp k] at e
      exact ajK_injective hg P0 e
  · by_cases hk : k = i ∨ k' = i ∨ k = k'
    · exact ⟨p0.left (IsLocalRing.closedPoint K), by rw [badC_pair, if_pos hk]; simp⟩
    · obtain ⟨Q, hQ⟩ := exists_ne_place P0
      obtain ⟨p, hp⟩ := exists_pt_coord hg P0 n (fun j => if j = k then Q else P0)
      refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
      rw [badC_pair, if_neg hk]
      intro h
      simp only [not_or] at hk
      have e : p ≫ ((prj K F n k ≫ ajO P0) * (prj K F n k' ≫ ajO P0)⁻¹) = 1 :=
        JacChunk.GrpPt.ev_inj (Jac K F) h
      rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one, ← Category.assoc, ← Category.assoc,
        kPl_spec P0 (p ≫ prj K F n k), kPl_spec P0 (p ≫ prj K F n k')] at e
      have e2 := ajK_injective hg P0 e
      have hk1 : kPl (p ≫ prj K F n k) = Q := by simpa using hp k
      have hk2 : kPl (p ≫ prj K F n k') = P0 := by simpa [Ne.symm hk.2.2] using hp k'
      rw [hk1, hk2] at e2
      exact hQ e2

/-- **The bad set is not everything** once `x0 ∈ Ogood`. -/
theorem bad_ne_univ (hg : 0 < genusFK K F) (hx0 : pt (Jac K F) x0 ∈ Ogood P0 cK c2) :
    bad P0 n β i x0 cK c2 A ≠ Set.univ :=
  ne_univ_of_compl _ (isClosed_badC P0 n β i x0 cK c2 A) (exists_not_mem_badC P0 n β i x0 cK c2 A hg hx0)

end Good

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Gen =====
section

/-!
# S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
* `ord_slice_gen`: `ord_q (slice) = G q - H q + Zsl q` (no condition on `q`);
* **`test_mem_gen`**: the `β i0 ∈ S` test with the correction `- H q + Zsl q` (it cancels in the cube sum);
* **`ell_zero_of_not_mem_W`**: `deg D = g - 1`, `[e] = [W0 - D] - (g-1)[P0]`, `e ∉ W` give `ℓ(D) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Off `W`, a divisor of degree `g - 1` in the matching class has no sections.** -/
theorem ell_zero_of_not_mem_W (hg : 0 < genusFK K F) {W0 D : Places.Divisor K F} (hW : IsCanonicalFK K F W0)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hd : D.deg = (genusFK K F : ℤ) - 1)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - D) - ((genusFK K F : ℤ) - 1) • clsK K F (Finsupp.single P0 1))
    (ha : e.left (IsLocalRing.closedPoint K) ∉ W P0) : ellFK K F D = 0 := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hrr := riemannRochFK' hk hW D
  rw [hd] at hrr
  have hdG : (D + Finsupp.single P0 1).deg = (genusFK K F : ℤ) := by
    rw [PlacesK.Divisor.deg_add, hd, deg_single_one (K := K) (F := F) P0]
    ring
  have heG : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - (D + Finsupp.single P0 1)) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) := by
    rw [he, sub_add_eq_sub_sub, clsK_sub (K := K) (F := F) (W0 - D)]
    module
  have h0 : ellFK K F (W0 - D) = 0 := by
    by_contra hne
    obtain ⟨E, hE, hcE⟩ := (one_le_ell_iff (W0 - D)).1 (by omega)
    have hex : ∃ E' : Places.Divisor K F, 0 ≤ E' ∧
        clsK K F E' = clsK K F (W0 - (D + Finsupp.single P0 1) + Finsupp.single P0 1) :=
      ⟨E, hE, by rw [hcE]; congr 1; abel⟩
    obtain ⟨t, ht⟩ := (exists_sum_ajCls_iff hg P0 hW hdG _ heG P0).2 hex
    rw [ajCls_self, zero_add] at ht
    exact ha ((mem_W_iff P0 e).2 ⟨t, by rw [← ht, ofAdd_toAdd]⟩)
  omega

end Gen

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Asm1 =====
section

/-!
# S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `tauS`, `j0S`: the enumeration of the block `{k | β k ∈ S}`;
* `HS`, `YS`, `Vp`, `VS`: the correction divisors; **`cancel_VS`**: their signed cube sum is `0`;
* **`test_S`**: off `bad i0`, both sides avoid and `cpull det_S = cpull Θ_S + VS_S (p_{i0})`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Asm1

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The determinant divisor of the block `S`. -/
noncomputable def dS (n : ℕ) (β : Fin n → Fin 3) {r : ℕ} (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (hf : ∀ S : Finset (Fin 3), Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → F)
    (S : Finset (Fin 3)) : AlgebraicCycle (PP K F n).left ℤ :=
  JacDivisors.div (PP K F n).left (detPP K F n (tauS n β S) m (hf S))

end Asm1

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_NZS =====
section

/-!
# S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
* `detPP_ne_of_slice`: a nonzero slice forces `det_k ≠ 0`;
* `detPP_ne_zero_at`: off the bad set of a direction `i0`, the slice is nonzero (the two branches of `test_S`);
* `exists_not_mem_bad`: a `K`-point off the bad set (`J`acobson, `bad ≠ univ`);
* **`detPP_ne_zero`**: `det_k ≠ 0` for every block `S` (hypotheses of `cube_PP`, `n > 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section NZS

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **A `K`-point off the bad set** (`x0 ∈ Ogood`). -/
theorem exists_not_mem_bad (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (i0 : Fin n)
    (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {s : ℕ} (A : Fin s → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (hx0g : pt (Jac K F) x0 ∈ Ogood P0 cK c2) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p.left (IsLocalRing.closedPoint K) ∉ bad P0 n β i0 x0 cK c2 A := by
  have : JacobsonSpace (PP K F n).left := LocallyOfFiniteType.jacobsonSpace (PP K F n).hom
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (Set.nonempty_compl.mpr (bad_ne_univ P0 n β i0 x0 cK c2 A hg hx0g))
    (isClosed_bad P0 n β i0 x0 cK c2 A).isOpen_compl.isLocallyClosed
  obtain ⟨p, hp⟩ := exists_kpt_of_closed (K := K) (F := F) n hzc
  exact ⟨p, hp ▸ hz⟩

end NZS

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Pick =====
section

/-!
# S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
* `xM c3 : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)` (class `[W0 + Σ [p_i]] - (3g-2)[P0]`, `cls_xM`), onto on `K`-points;
* `badM`: the closed conditions "`x0 ∉ Ogood`", "`p_l = P0`", "`p_l = p_l'`" on `X1^g`, each missing a point;
* **`exists_m_x0`**: `g` distinct points `m_l ≠ P0` with `x0 := c_3 Φ_g(m) ∈ Ogood` of the class `cube_PP` needs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Pick

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (cK c2 c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

theorem isClosed_badM (c : Unit ⊕ Fin (genusFK K F) ⊕ (Fin (genusFK K F) × Fin (genusFK K F))) :
    IsClosed (badM P0 cK c2 c3 c) := by
  rcases c with _ | l | ⟨l, l'⟩
  · exact (isOpen_Ogood P0 cK c2).isClosed_compl.preimage (xM P0 c3).left.continuous
  · exact (JacChunk.GrpPt.isClosed_ev (Jac K F) 1).preimage
      (prj K F (genusFK K F) l ≫ ajO P0).left.continuous
  · show IsClosed (if l = l' then ∅ else _)
    split_ifs
    · exact isClosed_empty
    · exact (JacChunk.GrpPt.isClosed_ev (Jac K F) 1).preimage
        ((prj K F (genusFK K F) l ≫ ajO P0) * (prj K F (genusFK K F) l' ≫ ajO P0)⁻¹).left.continuous

end Pick

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cst =====
section

/-!
# S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `gff_eq_toStalk`, `gff_surjective` (on `Spec` of a field), `gff_sum`;
* `PsiX_stalkMap_val`, `PsiX_fpull_kff`: `PsiX` of the constant `c` pulled back to `X1` is `algebraMap K F c`;
* `fpull_phiX_val`: `phiX f` is regular at a `K`-point `q` with `0 ≤ ord f`, with value `kff c`, `cval q (phiX f) = c`;
* **`fpull_phiX_incB`**: at `q` with `kPl q = inl (ptP φ)`, `fpull q (phiX (incB r)) = kff (φ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR RamanujanPetersson.JacLaw
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Gff

variable {R : Type u} [CommRing R] [IsDomain R]

end Gff

section Cst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- Regularity and value of `phiX f` at a `K`-point `q` with `0 ≤ ord_q f`. -/
theorem fpull_phiX_val (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (f : F)
    (hf : 0 ≤ (kPl q).ord f) :
    RegAt (q.left (genericPoint _)) (phiX K F f) ∧
      ∃ c : K, fpull q.left (phiX K F f) = kff c ∧ cval K F q (phiX K F f) = algebraMap K F c := by
  obtain ⟨w, hw⟩ := exists_stalk_of_ord hg q f hf (x := q.left (genericPoint _))
    (congrArg (fun y => q.left y) (Subsingleton.elim (α := Spec (.of K)) _ _))
  obtain ⟨w', hw'⟩ := exists_stalk_of_ord hg q f hf
    (x := (toUnit (X1O K F) ≫ q).left (genericPoint (X1O K F).left)) (toUnit_comp_apply q _)
  obtain ⟨c, hc⟩ : ∃ c : K, kff c = fpull q.left (phiX K F f) := gff_surjective _
  refine ⟨(regAt_iff _ _).mpr ⟨w, hw⟩, c, hc.symm, ?_⟩
  obtain ⟨-, h2⟩ := regAt_fpull (toUnit (X1O K F)).left q.left ((regAt_iff _ _).mpr ⟨w', hw'⟩)
  have h3 : cval K F q (phiX K F f) = PsiX K F (fpull (toUnit (X1O K F)).left (kff c)) := by
    rw [hc]
    exact congrArg (PsiX K F) h2.symm
  rw [h3]
  exact PsiX_fpull_kff c

end Cst

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrOpen =====
section

/-!
# S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `jacPic_psiS`, `cls_psiS`: the class of `p ≫ ψ_S` is `[Σ_{k ∈ blk} p_k] - #blk [P0]`;
* `ell_one_of_cls`: off `W`, a degree-`g` divisor in the class `[e] + g[P0]` has `ℓ = 1`;
* `blocks_of_Zdiv`: `Zdiv T = Σ_{k ∈ s} [v k]` with `#s = #T` makes `v` a bijection onto the points of `T`;
* `VJ P0 d := {x | x d⁻¹ ∈ jX0 (X0)} \ W` (open), `exists_yR_of_mem_VJ`;
* **`hH_of_mem`**: hypothesis (H) of `trPP` at every `K`-point of `ψ_S⁻¹ VJ` (`#blk = g`, `[d] = [Θ] - g[P0]`);
* **`trPP_open`**: the block trace identity once `ψ_S⁻¹ VJ` is nonempty.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section TrOpen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Off `W`, an effective... degree-`g` divisor in the class `[e] + g[P0]` has `ℓ = 1`.** -/
theorem ell_one_of_cls (hg : 0 < genusFK K F) {G : Places.Divisor K F} (hd : G.deg = genusFK K F)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F G - (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1))
    (ha : e.left (IsLocalRing.closedPoint K) ∉ W P0) : ellFK K F G = 1 := by
  obtain ⟨W0, hW⟩ := exists_isCanonicalFK (K := K) (F := F)
  have hk := constField_eq_bot' (K := K) (F := F)
  have hD : (W0 - G + Finsupp.single P0 1).deg = (genusFK K F : ℤ) - 1 := by
    rw [PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_sub, degFK_canonical hk hW, hd,
      deg_single_one (K := K) (F := F) P0]
    ring
  have h0 := ell_zero_of_not_mem_W P0 hg hW e hD (by
    rw [he, show W0 - (W0 - G + Finsupp.single P0 1) = G - Finsupp.single P0 1 by abel,
      clsK_sub (K := K) (F := F), sub_smul, one_smul]
    abel) ha
  have h1 : ellFK K F (W0 - G) = 0 := by
    have := ellFK_mono (K := K) (F := F) (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one) :
      W0 - G ≤ W0 - G + Finsupp.single P0 1)
    omega
  have hrr := riemannRochFK' hk hW G
  rw [hd, h1] at hrr
  omega

theorem isOpen_VJ (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : IsOpen (VJ P0 d) :=
  ((jX0 K F).isOpenEmbedding.isOpen_range.preimage (transl (Jac K F) d⁻¹).left.continuous).inter
    (isClosed_W P0).isOpen_compl

open Classical in
/-- **Hypothesis (H) of `trPP`** at the `K`-points of `ψ_S⁻¹ VJ`. -/
theorem hH_of_mem (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (hS : (blk n β S).card = genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hd : ((Multiplicative.toAdd (jacPicEquiv K F d) : Pic0K K F) : PicK K F) =
      thetaK K F - (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hp : p.left (genericPoint _) ∈ (psiS P0 n β S).left ⁻¹' VJ P0 d) :
    ∃ yR : LawRing K F →ₐ[K] K,
        (p ≫ psiS P0 n β S).left = Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) ≫ tauX d ∧
        ∃ a' : Fin n → (Places.Rfin K F →ₐ[K] K),
          (∀ k ∈ blk n β S, kPl (p ≫ prj K F n k) = Sum.inl (ptP (a' k))) ∧ Set.InjOn a' (blk n β S) ∧
            (blk n β S).image a' = ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)) := by
  have hgc : (IsLocalRing.closedPoint K : Spec (.of K)) = genericPoint (𝟙_ (Over (Spec (.of K)))).left :=
    Subsingleton.elim _ _
  have hpt : (p ≫ psiS P0 n β S).left (IsLocalRing.closedPoint K) ∈ VJ P0 d := by
    rw [hgc]
    exact hp
  obtain ⟨yR, hyR, hmul⟩ := exists_yR_of_mem_VJ P0 d _ hpt
  refine ⟨yR, hyR, ?_⟩
  have hcls2 : ((Multiplicative.toAdd (jacPicEquiv K F (p ≫ psiS P0 n β S)) : Pic0K K F) : PicK K F) =
      clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) -
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
    rw [← hmul, map_mul, toAdd_mul, AddSubgroup.coe_add, cls_kJ, hd]
    abel
  have hcls : clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) =
      clsK K F (∑ k ∈ blk n β S, Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ)) := by
    have h := hcls2.symm.trans (cls_psiS P0 n β S p)
    rw [hS] at h
    exact sub_left_inj.mp h
  have hell := ell_one_of_cls P0 hg (by rw [deg_Zdiv, card_lawPt]) _ hcls2 hpt.2
  have hZ := eq_of_ell_one (Zdiv_nonneg _)
    (Finset.sum_nonneg fun k _ => Finsupp.single_nonneg.2 zero_le_one) hell hcls
  have hc := card_lawPt (K := K) (F := F) yR
  exact blocks_of_Zdiv _ _ _ (Finset.card_pos.mp (by rw [hc]; exact hg)) hZ (hS.trans hc.symm)

end TrOpen

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrNe =====
section

/-!
# S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
* `VJ_nonempty`: `VJ P0 d` is a nonempty open of `J` (`J` irreducible, `W ≠ J`, translated chart);
* `exists_blocks`: a map `a` with `Σ_{k ∈ s} [a k] = Zdiv T` when `#s = #T`;
* **`psiS_VJ_nonempty`**: `ψ_S⁻¹ VJ ≠ ∅` when `#blk = g` and `[d] = [Θ] - g[P0]`;
* **`trPP_blk`**: the block trace identity `ψ_S^* trJ d f = Σ_{k ∈ blk} pr_k^* f`, unconditionally.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section TrNe

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- `VJ P0 d` is nonempty: the translated chart and `J \ W` are nonempty opens of the irreducible `J`. -/
theorem VJ_nonempty (hg : 0 < genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : (VJ P0 d).Nonempty := by
  obtain ⟨x, hx⟩ := exists_not_mem_W P0 hg
  obtain ⟨z⟩ := (inferInstance : Nonempty (X0 K F))
  have h1 : ((transl (Jac K F) d⁻¹).left ⁻¹' Set.range (jX0 K F)).Nonempty := by
    refine ⟨(transl (Jac K F) d).left (jX0 K F z), z, ?_⟩
    show jX0 K F z = ((transl (Jac K F) d ≫ transl (Jac K F) d⁻¹).left) (jX0 K F z)
    rw [transl_comp_transl, mul_inv_cancel, transl_one]
    rfl
  exact nonempty_preirreducible_inter
    ((jX0 K F).isOpenEmbedding.isOpen_range.preimage (transl (Jac K F) d⁻¹).left.continuous)
    (isClosed_W P0).isOpen_compl h1 ⟨_, hx⟩

/-- **`ψ_S⁻¹ VJ` is nonempty** (`#blk = g`, `[d] = [Θ] - g[P0]`): Jacobi inversion on the block. -/
theorem psiS_VJ_nonempty (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (hS : (blk n β S).card = genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hd : ((Multiplicative.toAdd (jacPicEquiv K F d) : Pic0K K F) : PicK K F) =
      thetaK K F - (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1)) :
    ((psiS P0 n β S).left ⁻¹' VJ P0 d).Nonempty := by
  have : JacobsonSpace (Jac K F).left := LocallyOfFiniteType.jacobsonSpace (Jac K F).hom
  obtain ⟨x, hxV, hxc⟩ := nonempty_inter_closedPoints (VJ_nonempty P0 hg d) (isOpen_VJ P0 d).isLocallyClosed
  obtain ⟨e, he⟩ := exists_pt_eq (Jac K F) x hxc
  have heV : e.left (IsLocalRing.closedPoint K) ∈ VJ P0 d := by
    rw [← he] at hxV
    exact hxV
  obtain ⟨yR, -, hmul⟩ := exists_yR_of_mem_VJ P0 d e heV
  have hTc := card_lawPt (K := K) (F := F) yR
  obtain ⟨a, ha⟩ := exists_blocks (blk n β S) (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))
    (Finset.card_pos.mp (by rw [hTc]; exact hg)) (hS.trans hTc.symm)
  obtain ⟨p, hp⟩ := exists_pt_coord hg P0 n (fun k => Sum.inl (ptP (a k)))
  have hpe : p ≫ psiS P0 n β S = e := by
    apply (jacPicEquiv K F).injective
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [cls_psiS, hS]
    simp only [hp]
    rw [ha, ← hmul, map_mul, toAdd_mul, AddSubgroup.coe_add, cls_kJ, hd]
    abel
  refine ⟨p.left (genericPoint _), ?_⟩
  have hgc : (IsLocalRing.closedPoint K : Spec (.of K)) = genericPoint (𝟙_ (Over (Spec (.of K)))).left :=
    Subsingleton.elim _ _
  show (p ≫ psiS P0 n β S).left (genericPoint (𝟙_ (Over (Spec (.of K)))).left) ∈ VJ P0 d
  rw [hpe, ← hgc]
  exact heV

end TrNe

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrA =====
section

/-!
# S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `fpull_eq_ffMap`, `fpull_comp_dom`: along dominant maps `fpull` is the field map `ffMap`;
* `surjective_hom_of_nonempty`, `surjective_fst_left`, `surjective_snd_left`; `surjective_prj`, `isDominant_prj`;
* `qb b` (the three projections `J^3 ⟶ J`), `isDominant_qb`, `Phi3_qb`;
* **`ffMap_Phi3_fpull`**: `Φ3^# (q_b^# G) = ψ_{b}^# G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Dom

variable {C P Y : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral Y]

end Dom

section GrA

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The projections `X1^n ⟶ X1` are surjective. -/
theorem surjective_prj : ∀ (n : ℕ) (k : Fin n), Surjective (prj K F n k).left
  | 0, k => k.elim0
  | n + 1, k => by
    refine Fin.lastCases ?_ (fun j => ?_) k
    · show Surjective (Fin.lastCases (snd (PP K F n) (X1O K F))
        (fun j => fst (PP K F n) (X1O K F) ≫ prj K F n j) (Fin.last n) : PP K F n ⊗ X1O K F ⟶ X1O K F).left
      rw [Fin.lastCases_last]
      exact surjective_snd_left _ _
    · show Surjective (Fin.lastCases (snd (PP K F n) (X1O K F))
        (fun j => fst (PP K F n) (X1O K F) ≫ prj K F n j) (Fin.castSucc j) : PP K F n ⊗ X1O K F ⟶ X1O K F).left
      rw [Fin.lastCases_castSucc, Over.comp_left]
      have := surjective_fst_left (PP K F n) (X1O K F)
      have := surjective_prj n j
      infer_instance

instance isDominant_prj (n : ℕ) (k : Fin n) : IsDominant (prj K F n k).left := by
  have := surjective_prj (K := K) (F := F) n k
  infer_instance

variable (P0 : Place K F)

/-- **`Φ3^# (q_b^# G) = ψ_{b}^# G`** (`Φ3` dominant). -/
theorem ffMap_Phi3_fpull (n : ℕ) (β : Fin n → Fin 3) [IsDominant (Phi3 P0 n β).left] (b : Fin 3)
    (G : (Jac K F).left.functionField) :
    (ffMap (Phi3 P0 n β).left).hom (fpull (qb K F b).left G) = fpull (psiS P0 n β {b}).left G := by
  have e : (psiS P0 n β {b}).left = (Phi3 P0 n β).left ≫ (qb K F b).left := by
    rw [← Over.comp_left, Phi3_qb]
  rw [e, fpull_comp_dom, fpull_eq_ffMap, fpull_eq_ffMap]

end GrA

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Hook =====
section

/-!
# S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`

For one translate `x0 ∉ W` and `c G := (polyEnd π G)^* D'` (`cD`):
* `hzero_D`, `hproj_D`, **`hD_D`** (`(D'^g) > 0` by multilinear expansion), `hsym_D` (exact);
* `CubePrincipal P0 x0`: a positive multiple of the cube divisor on `J^3` is principal;
* **`hcube_D`** and **`quad_D`** (the output of `DegPoly.quad_of_cube`), conditional on `CubePrincipal P0 x0`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

end Poly

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
  (hx0 : pt (Jac K F) x0 ∉ W P0) (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g)
  (π : Jac K F ⟶ Jac K F) [IsMonHom π]

/-- `c G := (polyEnd π G)^* D'`. -/
noncomputable def cD (G : ℤ[X]) : AlgebraicCycle (Jac K F).left ℤ :=
  cpull (IsogDegB.polyEnd π G).left (DTh P0 x0)

/-- `c' G := (polyEnd π G ≫ τ_{x0})^* Θ`. -/
noncomputable def cc (G : ℤ[X]) : AlgebraicCycle (Jac K F).left ℤ :=
  cpull (IsogDegB.polyEnd π G ≫ transl (Jac K F) x0).left (Theta P0)

/-- The geometric input: a positive multiple of the cube divisor on `J^3` is principal. -/
def CubePrincipal : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ h : (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left.functionField, h ≠ 0 ∧
    JacDivisors.div _ h = n • cubeZ P0 x0

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrC =====
section

/-!
# S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
* `eq_zero_of_pullback_surj`: pull-back along a dominant surjection from `X1^n` is injective on Weil divisors;
* `div_sq_eq`: `div (f ^ 2) = div f + div f`;
* **`cubePrincipal_gram`**: `h := Π_S det (grJ S) ^ (±1)` has `div h = 2 • cubeZ` (`Φ3^# h = Π_S det_k ^ (±2)`,
  `cube_PP`), so `CubePrincipal P0 x0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section GrC

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Pull-back along a dominant surjection from `X1^n` is injective on Weil divisors.** -/
theorem eq_zero_of_pullback_surj {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    [∀ z : (PP K F n).left, UniqueFactorizationMonoid ((PP K F n).left.presheaf.stalk z)]
    (Φ : (PP K F n).left ⟶ Y) [IsDominant Φ] (hsurj : Function.Surjective Φ)
    {E : AlgebraicCycle Y ℤ} (hE : E ∈ weilDivisors Y) (h0 : JacDivisors.pullback Φ E = 0) : E = 0 :=
  eq_zero_of_surj Φ hsurj hE fun i p hA' => by
    rw [cpull_comp _ Φ hE hA', h0, cpull_zero]
    rfl

variable (P0 : Place K F)

end GrC

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Surj3 =====
section

/-!
# S4-ThetaCube, file Surj3 (D-C1, part 10): `Φ3 : X1^n ⟶ J^3` is surjective and dominant
* `exists_coords`: coordinates on a block with a prescribed sum of places;
* `exists_pt_Phi3`: Jacobi inversion on each block (`#blk {b} = g`): every `K`-point of `J^3` is `p ≫ Φ3`;
* **`surjective_Phi3`**, **`isDominant_Phi3`** (closed image, contains every closed point, `J^3` Jacobson).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Surj3

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Jacobi inversion on `J^3`**: every `K`-point of `J^3` is `p ≫ Φ3` (`#blk {b} = g`). -/
theorem exists_pt_Phi3 (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3)
    (hβ : ∀ b : Fin 3, (blk n β {b}).card = genusFK K F)
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F ⊗ (Jac K F ⊗ Jac K F)) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p ≫ Phi3 P0 n β = a := by
  choose t ht using fun b : Fin 3 =>
    exists_eff_rep P0 (Multiplicative.toAdd (jacPicEquiv K F (a ≫ qb K F b))).2
  choose c hc using fun b : Fin 3 => exists_coords (blk n β {b}) (hβ b) (t b) P0
  obtain ⟨p, hp⟩ := exists_pt_coord hg P0 n (fun k => c (β k) k)
  have key : ∀ b, (p ≫ Phi3 P0 n β) ≫ qb K F b = a ≫ qb K F b := by
    intro b
    rw [Category.assoc, Phi3_qb]
    apply (jacPicEquiv K F).injective
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    have hs : ∑ k ∈ blk n β {b}, Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ) =
        ∑ i, Finsupp.single (t b i) (1 : ℤ) := by
      rw [← hc b]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : β k = b := by simpa [blk] using hk
      simp only [hp k, hk']
    rw [cls_psiS, hβ b, ht b, hs, clsK_sum]
  refine ⟨p, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · simpa [qb, q1] using key 0
  · apply CartesianMonoidalCategory.hom_ext
    · simpa [qb, q2] using key 1
    · simpa [qb, q3] using key 2

/-- **`Φ3` is surjective** (`#blk {b} = g`). -/
theorem surjective_Phi3 (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3)
    (hβ : ∀ b : Fin 3, (blk n β {b}).card = genusFK K F) : Function.Surjective (Phi3 P0 n β).left := by
  have : JacobsonSpace (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left :=
    LocallyOfFiniteType.jacobsonSpace (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom
  have : IsSeparated (Jac K F ⊗ Jac K F).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : IsSeparated (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : UniversallyClosed ((Phi3 P0 n β).left ≫ (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom) := by
    rw [Over.w (Phi3 P0 n β)]; infer_instance
  have := UniversallyClosed.of_comp_of_isSeparated (Phi3 P0 n β).left (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom
  have hcl : closedPoints (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left ⊆ Set.range (Phi3 P0 n β).left := by
    intro j hj
    let a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F ⊗ (Jac K F ⊗ Jac K F) :=
      Over.homMk (pointOfClosedPoint (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom j hj) (pointOfClosedPoint_comp _ _ _)
    obtain ⟨p, hp⟩ := exists_pt_Phi3 P0 hg n β hβ a
    refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
    have h2 : (p ≫ Phi3 P0 n β).left (IsLocalRing.closedPoint K) = j := by
      rw [hp]
      exact pointOfClosedPoint_apply (Jac K F ⊗ (Jac K F ⊗ Jac K F)).hom j hj _
    exact h2
  have h := closure_minimal hcl (Phi3 P0 n β).left.isClosedMap.isClosed_range
  rw [closure_closedPoints] at h
  exact fun j => h (Set.mem_univ j)

/-- **`Φ3` is dominant** (`#blk {b} = g`). -/
theorem isDominant_Phi3 (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3)
    (hβ : ∀ b : Fin 3, (blk n β {b}).card = genusFK K F) : IsDominant (Phi3 P0 n β).left := by
  have : Surjective (Phi3 P0 n β).left := ⟨surjective_Phi3 P0 hg n β hβ⟩
  infer_instance

end Surj3

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_JacFrob_PolyG =====
section

/-!
# S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically

For a map `ψ : J ⟶ J` whose action on the classes of the `K`-points is `πM` (through an additive map `t`
from `Pic⁰`): `cls_piter`, **`cls_polyEnd`** (`F(ψ)` acts as `aeval πM F`), `hom_ext_kpt` (maps `J ⟶ J` agreeing
on `K`-points are equal), `polyEnd_X`, **`polyEnd_mul_of_cls`** (`F G ↦ (FG)(ψ) = G(ψ) ≫ F(ψ)`: the ring map
`ℤ[π] → End(J)`), `polyEnd_eq_one_iff`, **`kerPtsEquiv`** (`Ker F(ψ)(K) ≃ ker (aeval πM F)`),
**`degree_polyEnd_eq_card_ker`** (`deg F(ψ) = #ker (aeval πM F)` when `dψ = 1`, `p ∤ F(0)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {M : Type*} [AddCommGroup M]

/-- **`deg F(ψ) = #ker (aeval πM F)`** for `dψ = 1` and `p ∤ F(0)`. -/
theorem degree_polyEnd_eq_card_ker (ψ : Jac K F ⟶ Jac K F) [IsMonHom ψ] (hπ : IsogDegB.dφ ψ = 1)
    (p : ℕ) [CharP K p] (e : Pic0K K F ≃+ M) (πM : Module.End ℤ M)
    (hψ : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
      e (Multiplicative.toAdd (jacPicEquiv K F (a ≫ ψ))) = πM (e (Multiplicative.toAdd (jacPicEquiv K F a))))
    (P : ℤ[X]) (hp : ¬ (p : ℤ) ∣ P.coeff 0) :
    IsogDegA.degree (IsogDegB.polyEnd ψ P).left = Nat.card (LinearMap.ker (aeval πM P)) := by
  rw [IsogDegB.degree_polyEnd ψ hπ p P hp]
  exact Nat.card_congr (kerPtsEquiv ψ e πM hψ P)

end Gen

end RamanujanPetersson.JacFrob


end


