-- Prove2me | Definitions.Def_RPLib_S4T_LiftSetup
-- name    : RPLib_S4T_LiftSetup
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:15:48.101846+00:00
-- url     : https://prove2.me/theorems/65c3a094-2716-49c9-81ff-cd1533aaa6a8
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: the setup over the residue field of a valuation subring of `Q̄`
-- statement:
--   The setup over the residue field of a valuation subring of `Q̄`.
--
--   Proves `RPLib.S4T.Glue.L0Stmt`:
--
--   * `exists_valuationSubring_charP` : a valuation subring `A` of a char-0 field with `CharP (ResidueField A) p`
--     (from `Ideal.image_subset_nonunits_valuationSubring` applied to `(p)` in the prime subring);
--   * `isAlgClosed_residueField` : the residue field of a valuation subring of an algebraically closed field is
--     algebraically closed (lift a monic polynomial; its root is integral, hence in `A`);
--   * `algF` : an `F`-algebra structure on `k` (`IsAlgClosed.lift` over `ZMod p`);
--   * `frobEquiv` : the `q`-power Frobenius `k ≃ₐ[F] k`, `q = #F`;
--   * `map_mem_rationalHomSet_baseChange` : `Point.map σ` is a `k`-rational endomorphism of `W_k` when `σ x = x ^ q`;
--   * `map_frobEquiv_ch` : `π ∘ π + q = a π` for `π = Point.map (frobEquiv F k)` (from `RPLib.DWS.frob_ch`);
--   * `l0` : `L0Stmt`.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_RPLib_S3_DWSIsogB
import Definitions.Def_RPLib_S4T_Glue

/-!
# S4T-LiftSetup (route L0): the setup over the residue field of a valuation subring of `Q̄`

Proves `RPLib.S4T.Glue.L0Stmt`:

* `exists_valuationSubring_charP` : a valuation subring `A` of a char-0 field with `CharP (ResidueField A) p`
  (from `Ideal.image_subset_nonunits_valuationSubring` applied to `(p)` in the prime subring);
* `isAlgClosed_residueField` : the residue field of a valuation subring of an algebraically closed field is
  algebraically closed (lift a monic polynomial; its root is integral, hence in `A`);
* `algF` : an `F`-algebra structure on `k` (`IsAlgClosed.lift` over `ZMod p`);
* `frobEquiv` : the `q`-power Frobenius `k ≃ₐ[F] k`, `q = #F`;
* `map_mem_rationalHomSet_baseChange` : `Point.map σ` is a `k`-rational endomorphism of `W_k` when `σ x = x ^ q`;
* `map_frobEquiv_ch` : `π ∘ π + q = a π` for `π = Point.map (frobEquiv F k)` (from `RPLib.DWS.frob_ch`);
* `l0` : `L0Stmt`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace RPLib.S4T.LiftSetup

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open scoped Polynomial.Bivariate

/-! ### The valuation subring -/

/-- A valuation subring of a characteristic-zero field whose residue field has characteristic `p`. -/
theorem exists_valuationSubring_charP (K : Type*) [Field K] [CharZero K] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring K, CharP (ResidueField A) p := by
  let R : Subring K := ⊥
  let I : Ideal R := Ideal.span {(p : R)}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
    have h2 : ((n * p : ℤ) : K) = 1 := by
      have := congrArg Subtype.val ha
      push_cast
      rw [hn]
      simpa using this
    have h3 : n * (p : ℤ) = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ ((1 : ℕ) : ℤ) := ⟨n, by rw [mul_comm]; exact_mod_cast h3.symm⟩
    have h5 : p ∣ 1 := Int.natCast_dvd_natCast.mp h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hpB : (p : K) ∈ B.nonunits := hB ⟨(p : R), Ideal.subset_span rfl, by simp⟩
  obtain ⟨hmem, hmax⟩ := B.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpB
  refine ⟨B, (CharP.charP_iff_prime_eq_zero hp).mpr ?_⟩
  have e : (⟨(p : K), hmem⟩ : B) = (p : B) := by ext; simp
  rw [e] at hmax
  have := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  simpa using this

/-- The residue field of a valuation subring of an algebraically closed field is algebraically closed. -/
theorem isAlgClosed_residueField {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) :
    IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  obtain ⟨g, hgf, hgdeg, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective f) hf
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hdeg : (g.map (algebraMap A K)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, Polynomial.degree_eq_natDegree hgm.ne_zero, hgdeg]
    have := Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)
    exact_mod_cast this.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (g.map (algebraMap A K)) hdeg
  have hint : IsIntegral A x := ⟨g, hgm, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hy : g.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_hom, Polynomial.eval₂_eq_eval_map]
    exact hx
  refine ⟨residue A y, ?_⟩
  rw [← hgf, Polynomial.eval_map, Polynomial.eval₂_hom, hy, map_zero]

/-! ### `F`-algebra structure and the Frobenius -/

variable (F : Type*) [Field F] [Fintype F]

/-- An `F`-algebra structure on an algebraically closed field of characteristic `ringChar F`. -/
@[instance_reducible]
noncomputable def algF (k : Type*) [Field k] [IsAlgClosed k] [CharP k (ringChar F)] : Algebra F k :=
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI := ZMod.algebra F (ringChar F)
  letI := ZMod.algebra k (ringChar F)
  (IsAlgClosed.lift (R := ZMod (ringChar F)) (S := F) (M := k)).toRingHom.toAlgebra

/-- The `q`-power Frobenius of an algebraically closed `F`-algebra, as an `F`-algebra automorphism. -/
noncomputable def frobEquiv (k : Type*) [Field k] [IsAlgClosed k] [Algebra F k] : k ≃ₐ[F] k :=
  AlgEquiv.ofBijective (FiniteField.frobeniusAlgHom F k)
    ⟨(FiniteField.frobeniusAlgHom F k).toRingHom.injective, fun y => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (Fintype.card_pos (α := F))
      exact ⟨z, by rw [FiniteField.coe_frobeniusAlgHom]; exact hz⟩⟩

theorem frobEquiv_apply (k : Type*) [Field k] [IsAlgClosed k] [Algebra F k] (x : k) :
    frobEquiv F k x = x ^ Fintype.card F := rfl

/-! ### The Frobenius on points -/

/-- If `σ x = x ^ q`, then `Point.map σ` is a `k`-rational endomorphism of `W_k` (`k`-coefficients). -/
theorem map_mem_rationalHomSet_baseChange {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k]
    [DecidableEq k] (W : WeierstrassCurve F) (σ : k →ₐ[F] k) (q : ℕ) (hσ : ∀ x, σ x = x ^ q) :
    Point.map (W' := W) σ ∈ rationalHomSet k (W.baseChange k) (W.baseChange k) := by
  refine Or.inr ⟨C (X ^ q), 1, X ^ q, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : k[X][Y]) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C (X ^ q) : k[X][Y]) x y / evalEvalBC k (1 : k[X][Y]) x y = σ x := by
    simp [evalEvalBC, Polynomial.evalEval, hσ]
  have e2 : evalEvalBC k (X ^ q : k[X][Y]) x y / evalEvalBC k (1 : k[X][Y]) x y = σ y := by
    simp [evalEvalBC, Polynomial.evalEval, hσ]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : k, a = σ x → b = σ y →
      ∃ h', Point.map (W' := W) σ (.some x y h) = .some a b h' from H _ _ e1 e2
  rintro a b rfl rfl
  exact ⟨_, Point.map_some (W' := W) σ (h : (W.baseChange k).toAffine.Nonsingular x y)⟩

/-- **`π ∘ π + q = a π`** for the Frobenius `π = Point.map (frobEquiv F k)`, `a = q + 1 - #W(F)`. -/
theorem map_ch {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic] (k : Type*)
    [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (σ : k ≃ₐ[F] k)
    (hσ : ∀ x, σ x = x ^ Fintype.card F) :
    (Point.map (W' := W) σ.toAlgHom).comp (Point.map (W' := W) σ.toAlgHom) +
        ((Fintype.card F : ℕ) : ℤ) • AddMonoidHom.id (W.baseChange k).toAffine.Point =
      RPLib.EllFq.trace W • Point.map (W' := W) σ.toAlgHom := by
  have hσ' : σ.toAlgHom = FiniteField.frobeniusAlgHom F k := AlgHom.ext fun x => hσ x
  have hfr : Point.map (W' := W) σ.toAlgHom = RPLib.EllFq.frob W k := by rw [hσ']; rfl
  rw [hfr]
  have h := RPLib.DWS.frob_ch (W := W) (L := k)
  ext P
  have hP : RPLib.EllFq.frob W k (RPLib.EllFq.frob W k P) -
      RPLib.EllFq.trace W • RPLib.EllFq.frob W k P + ((Fintype.card F : ℕ) : ℤ) • P = 0 := by
    exact DFunLike.congr_fun h P
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply]
  rw [← sub_eq_zero, ← hP]
  abel

/-! ### L0 -/

theorem l0 : RPLib.S4T.Glue.L0Stmt := by
  intro F _ _ W W' _ _ hcard hord
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  obtain ⟨A, hA⟩ := exists_valuationSubring_charP (AlgebraicClosure ℚ) (ringChar F) hp
  haveI := hA
  haveI : IsAlgClosed (ResidueField A) := isAlgClosed_residueField A
  letI : Algebra F (ResidueField A) := algF F (ResidueField A)
  have htr : RPLib.EllFq.trace W =
      (Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) := by
    simp [RPLib.EllFq.trace, RPLib.EllFq.numPoints, Nat.card_eq_fintype_card]
  have htr' : RPLib.EllFq.trace W' =
      (Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) := by
    simp [RPLib.EllFq.trace, RPLib.EllFq.numPoints, Nat.card_eq_fintype_card, hcard]
  have hlt := RPLib.DWS.trace_sq_lt_of_not_dvd (W := W) (by rw [htr]; exact hord)
  rw [htr] at hlt
  refine ⟨A, hA, inferInstance, inferInstance, frobEquiv F (ResidueField A),
    (Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ), (Fintype.card F : ℤ),
    frobEquiv_apply F _, ?_, ?_, hord, ?_⟩
  · intro m hm
    nlinarith [sq_nonneg (2 * m - ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)))]
  · obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨n, n.pos, by rw [hn]; push_cast; rfl⟩
  · intro _
    refine ⟨⟨map_mem_rationalHomSet_baseChange _ W _ _ (frobEquiv_apply F _), ?_⟩,
      ⟨map_mem_rationalHomSet_baseChange _ W' _ _ (frobEquiv_apply F _), ?_⟩⟩
    · rw [← htr]; exact map_ch W _ _ (frobEquiv_apply F _)
    · rw [← htr']; exact map_ch W' _ _ (frobEquiv_apply F _)

end RPLib.S4T.LiftSetup


