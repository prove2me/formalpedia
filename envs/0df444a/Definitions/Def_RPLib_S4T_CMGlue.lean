-- Prove2me | Definitions.Def_RPLib_S4T_CMGlue
-- name    : RPLib_S4T_CMGlue
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:16:16.095191+00:00
-- url     : https://prove2.me/theorems/21332638-0e45-414e-8d7d-615a8e5c31db
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: the Deuring lift satisfies `x² - t x + q` and has infinite order
-- statement:
--   The Deuring lift satisfies `x² - t x + q` and has infinite order.
--
--   Proves `RPLib.S4T.Glue.L2Stmt` from the FLT statements (explicit hypotheses, never used as lemmas)
--   a78cfa46 (nonzero rational maps are surjective), 0e002459 (lifting prime-to-`p` torsion), bf2cb471 (the
--   variable-change equivalence is a rational group isomorphism), 0e8f5714 (dual pairs), fe3c6240 / 195173b3 /
--   580839d4 (closure under composition, addition, negation).
--
--   * `red_inj` : a rational endomorphism in characteristic 0 whose reduction is `0` is `0`;
--   * `eq_id_of_forall_tors` : a rational endomorphism over `k` fixing every `N`-torsion point (`(N : k) ≠ 0`) is `id`;
--   * `l2` : `L2Stmt`.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_Glue
import Definitions.Def_RPLib_S2_Torsion

/-!
# S4T-CMGlue (route L1-L2): the Deuring lift satisfies `x² - t x + q` and has infinite order

Proves `RPLib.S4T.Glue.L2Stmt` from the FLT statements (explicit hypotheses, never used as lemmas)
a78cfa46 (nonzero rational maps are surjective), 0e002459 (lifting prime-to-`p` torsion), bf2cb471 (the
variable-change equivalence is a rational group isomorphism), 0e8f5714 (dual pairs), fe3c6240 / 195173b3 /
580839d4 (closure under composition, addition, negation).

* `red_inj` : a rational endomorphism in characteristic 0 whose reduction is `0` is `0`;
* `eq_id_of_forall_tors` : a rational endomorphism over `k` fixing every `N`-torsion point (`(N : k) ≠ 0`) is `id`;
* `l2` : `L2Stmt`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace RPLib.S4T.CMGlue

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

/-! ### Closure of `rationalHomSet` -/

section Closure

variable {F k : Type} [Field F] [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]

theorem nsmul_mem (h195 : FLT.S_195173b3.{0, 0}) (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (n : ℕ) : n • α ∈ rationalHomSet k W₁ W₂ := by
  induction n with
  | zero => rw [zero_nsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih => rw [succ_nsmul]; exact h195 k W₁ W₂ ih hα

theorem zsmul_mem (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0})
    (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (n : ℤ) : n • α ∈ rationalHomSet k W₁ W₂ := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, natCast_zsmul]; exact nsmul_mem h195 W₁ W₂ hα n
  · rw [negSucc_zsmul]; exact h580 k W₁ W₂ (nsmul_mem h195 W₁ W₂ hα (n + 1))

theorem sub_mem (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0})
    (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hβ : β ∈ rationalHomSet k W₁ W₂) :
    α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]; exact h195 k W₁ W₂ hα (h580 k W₁ W₂ hβ)

theorem pow_mem (hfe3 : FLT.S_fe3c6240.{0, 0}) (W : WeierstrassCurve F)
    {α : AddMonoid.End (W.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W W) (m : ℕ) : α ^ m ∈ rationalHomSet k W W := by
  induction m with
  | zero => rw [pow_zero]; exact id_mem_rationalHomSet k W
  | succ m ih => rw [pow_succ]; exact hfe3 k W W W hα ih

end Closure

/-! ### Nonzero torsion and the density argument over `k` -/

theorem exists_tors_ne_zero {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K] (Y : WeierstrassCurve K)
    [Y.IsElliptic] (N : ℕ) (hN : (N : K) ≠ 0) (h2 : 2 ≤ N) :
    ∃ Q : Y.toAffine.Point, Q ≠ 0 ∧ N • Q = 0 := by
  by_contra h
  push Not at h
  have hbot : RPLib.Torsion.tors Y N = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro Q hQ
    by_contra hQ0
    exact h Q hQ0 (RPLib.Torsion.mem_tors.mp hQ)
  have hc := RPLib.Torsion.card_tors (W := Y) N hN
  rw [hbot, AddSubgroup.card_bot] at hc
  nlinarith

/-- **Density.** A rational endomorphism of an elliptic curve over an algebraically closed `k` of characteristic
`p` fixing every `N`-torsion point with `(N : k) ≠ 0` is the identity. -/
theorem eq_id_of_forall_tors (h0e8 : FLT.S_0e8f5714.{0, 0}) (h195 : FLT.S_195173b3.{0, 0})
    (h580 : FLT.S_580839d4.{0, 0}) {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [CharP k p]
    (hp : p.Prime) (Y : WeierstrassCurve k) [Y.IsElliptic]
    {ψ : Y.toAffine.Point →+ Y.toAffine.Point} (hψ : ψ ∈ rationalHomSet k Y Y)
    (hfix : ∀ N : ℕ, (N : k) ≠ 0 → ∀ Q : Y.toAffine.Point, N • Q = 0 → ψ Q = Q) :
    ψ = AddMonoidHom.id Y.toAffine.Point := by
  by_contra hne
  have hδ : ψ - AddMonoidHom.id Y.toAffine.Point ∈ rationalHomSet k Y Y :=
    sub_mem h195 h580 Y Y hψ (id_mem_rationalHomSet k Y)
  have hδ0 : ψ - AddMonoidHom.id Y.toAffine.Point ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  obtain ⟨σ', -, n, hn, hdual⟩ := h0e8 k Y Y hδ hδ0
  have hn' : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hn1 : 1 ≤ n.toNat := by omega
  have hNk : ((n.toNat * p + 1 : ℕ) : k) ≠ 0 := by
    push_cast; rw [CharP.cast_eq_zero k p, mul_zero, zero_add]; exact one_ne_zero
  have h2 : 2 ≤ n.toNat * p + 1 := by
    have := hp.two_le
    have : p ≤ n.toNat * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  obtain ⟨Q, hQ0, hQN⟩ := exists_tors_ne_zero Y (n.toNat * p + 1) hNk h2
  have hδQ : (ψ - AddMonoidHom.id Y.toAffine.Point) Q = 0 := by
    rw [AddMonoidHom.sub_apply, hfix _ hNk Q hQN, AddMonoidHom.id_apply, sub_self]
  have hnQ : n • Q = 0 := hdual.ker_le_torsion_right hδQ
  have hn'Q : n.toNat • Q = 0 := by rw [← natCast_zsmul, hn']; exact hnQ
  apply hQ0
  have : (n.toNat * p + 1) • Q = Q := by
    rw [add_smul, one_smul, mul_comm, mul_smul, hn'Q, smul_zero, zero_add]
  rw [← this]; exact hQN

/-! ### Reduction is injective on rational endomorphisms (characteristic 0) -/

/-- **red_inj.** A rational endomorphism of the generic fibre whose reduction vanishes is `0`. -/
theorem red_inj (ha78 : FLT.S_a78cfa46.{0, 0}) (h0e0 : FLT.S_0e002459.{0})
    {A : ValuationSubring (AlgebraicClosure ℚ)} [DecidableEq (AlgebraicClosure ℚ)]
    [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)] (p : ℕ) [CharP (ResidueField A) p]
    (hp : p.Prime) (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0)
    {γ : (E.map A.subtype).toAffine.Point →+ (E.map A.subtype).toAffine.Point}
    (hγ : γ ∈ rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype))
    (h0 : ∀ P, reduceHom hΔ (γ P) = 0) : γ = 0 := by
  haveI := Glue.isElliptic_map_subtype E hΔ
  haveI : (E.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  by_contra hne
  have hsurj := ha78 (AlgebraicClosure ℚ) hγ hne
  have hNk : ((p + 1 : ℕ) : ResidueField A) ≠ 0 := by
    push_cast; rw [CharP.cast_eq_zero (ResidueField A) p, zero_add]; exact one_ne_zero
  obtain ⟨Q₀, hQ₀, hNQ⟩ := exists_tors_ne_zero (E.map (residue A)) (p + 1) hNk (by have := hp.two_le; omega)
  obtain ⟨Y, -, hY⟩ := h0e0 A E hΔ hNk Q₀ hNQ
  obtain ⟨Z, rfl⟩ := hsurj Y
  exact hQ₀ (hY ▸ h0 Z)

/-! ### Group-theoretic helpers -/

section Helpers

variable {G H : Type} [AddCommGroup G] [AddCommGroup H]

theorem zsmul_hom_apply (n : ℤ) (f : G →+ H) (x : G) : (n • f) x = n • f x := rfl

theorem iterate_comm (r : G →+ H) (a : G →+ G) (b : H →+ H) (h : ∀ P, r (a P) = b (r P)) (m : ℕ) (P : G) :
    r ((⇑a)^[m] P) = (⇑b)^[m] (r P) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

/-- `π^n (φ^n P) = q^n • P` when `π (φ P) = q • P`. -/
theorem pow_pow_apply (π φ : AddMonoid.End H) (q : ℤ) (h : ∀ P, π (φ P) = q • P) (n : ℕ) (P : H) :
    (π ^ n) ((φ ^ n) P) = (q ^ n) • P := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    rw [pow_succ π, pow_succ' φ, AddMonoid.End.coe_mul, AddMonoid.End.coe_mul, Function.comp_apply,
      Function.comp_apply, h, map_zsmul, ih, smul_smul, pow_succ, mul_comm]

end Helpers

/-! ### The Frobenius has no fixed power -/

theorem frob_iter_ne_id {F : Type} [Field F] [Fintype F] {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    [Algebra F k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k)
    (hσ : ∀ x, σ x = x ^ Fintype.card F) (m : ℕ) (hm : 0 < m) :
    ∃ P : (W.baseChange k).toAffine.Point, (⇑(Point.map (W' := W) σ.toAlgHom))^[m] P ≠ P := by
  haveI : (W.baseChange k).IsElliptic := inferInstanceAs (W.map (algebraMap F k)).IsElliptic
  set Q := Fintype.card F with hQdef
  have hQ : 1 < Q := Fintype.one_lt_card
  -- the iterate is `Point.map τ` with `τ z = z ^ Q ^ n`
  have hiter : ∀ n : ℕ, ∃ τ : k →ₐ[F] k, (∀ z, τ z = z ^ Q ^ n) ∧
      ∀ P, (⇑(Point.map (W' := W) σ.toAlgHom))^[n] P = Point.map (W' := W) τ P := by
    intro n
    induction n with
    | zero =>
      refine ⟨AlgHom.id F k, fun z => by simp, fun P => ?_⟩
      cases P <;> rfl
    | succ n ih =>
      obtain ⟨τ, hτ, hP⟩ := ih
      refine ⟨σ.toAlgHom.comp τ, fun z => ?_, fun P => ?_⟩
      · show σ (τ z) = z ^ Q ^ (n + 1)
        rw [hτ, hσ, ← pow_mul, ← pow_succ]
      · rw [Function.iterate_succ_apply', hP, Point.map_map]
  obtain ⟨τ, hτ, hP⟩ := hiter m
  have h1 : 1 < Q ^ m := Nat.one_lt_pow hm.ne' hQ
  -- a point `x` with `x ^ Q ^ m = x + 1`
  obtain ⟨x, hx⟩ : ∃ x : k, x ^ Q ^ m = x + 1 := by
    have hdeg : ((X ^ (Q ^ m) - (X + C 1) : k[X])).degree ≠ 0 := by
      have hlt : (X + C 1 : k[X]).degree < (X ^ (Q ^ m) : k[X]).degree := by
        rw [degree_X_add_C, degree_X_pow]; exact_mod_cast h1
      rw [degree_sub_eq_left_of_degree_lt hlt, degree_X_pow]
      exact_mod_cast (by omega : Q ^ m ≠ 0)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨x, ?_⟩
    simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_add, eval_C] at hx
    linear_combination hx
  -- a point above `x`
  set Wk := W.baseChange k
  obtain ⟨y, hy⟩ : ∃ y : k, y ^ 2 + (Wk.a₁ * x + Wk.a₃) * y - (x ^ 3 + Wk.a₂ * x ^ 2 + Wk.a₄ * x + Wk.a₆) = 0 := by
    have hdeg : (C 1 * X ^ 2 + C (Wk.a₁ * x + Wk.a₃) * X +
        C (-(x ^ 3 + Wk.a₂ * x ^ 2 + Wk.a₄ * x + Wk.a₆)) : k[X]).degree ≠ 0 := by
      rw [degree_quadratic one_ne_zero]; exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0)
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ?_⟩
    simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hy
    linear_combination hy
  have heq : Wk.toAffine.Equation x y := by
    rw [Affine.equation_iff]; linear_combination hy
  have hns : Wk.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp heq
  refine ⟨Point.some x y hns, fun h => ?_⟩
  rw [hP, Point.map_some] at h
  have hxx : τ x = x := (Point.some.inj h).1
  rw [hτ, hx] at hxx
  exact one_ne_zero (add_left_cancel (hxx.trans (add_zero x).symm))

/-! ### L2 -/

/-- **L2.** The Deuring lift `α` of the Frobenius satisfies `α² + q = t α`, and neither `α` nor `t - α` has a
fixed power. -/
theorem l2 (ha78 : FLT.S_a78cfa46.{0, 0}) (h0e0 : FLT.S_0e002459.{0}) (hbf2 : FLT.S_bf2cb471.{0})
    (h0e8 : FLT.S_0e8f5714.{0, 0}) (hfe3 : FLT.S_fe3c6240.{0, 0}) (h195 : FLT.S_195173b3.{0, 0})
    (h580 : FLT.S_580839d4.{0, 0}) : Glue.L2Stmt := by
  intro F _ _ W _ A _ _ _ _ _ σ hσ t q hirr hq ht hπ hπch T hT0 hpT E hΔ v hv α hα hcompat
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  haveI := Glue.isElliptic_map_subtype E hΔ
  haveI hEk : (E.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI : (W.baseChange (ResidueField A)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (ResidueField A))).IsElliptic
  set π := Point.map (W' := W) σ.toAlgHom with hπdef
  -- the variable-change equivalence is additive (bf2cb471)
  obtain ⟨ι, -, ι', -, hι, hι'ι, hιι'⟩ := hbf2 (E.map (residue A)) v hv
  have hsymm : ∀ z, (Point.equivOfVariableChangeEq hv).symm z = ι' z := by
    intro z
    rw [Equiv.symm_apply_eq, ← hι]
    exact (DFunLike.congr_fun hιι' z).symm
  let r : (E.map A.subtype).toAffine.Point →+ (W.baseChange (ResidueField A)).toAffine.Point :=
    ι'.comp (reduceHom hΔ)
  have hr : ∀ P, r (α P) = π (r P) := by
    intro P
    show ι' (reduceHom hΔ (α P)) = π (ι' (reduceHom hΔ P))
    rw [← hsymm, ← hsymm]; exact hcompat P
  -- lifting torsion (0e002459)
  have hlift : ∀ N : ℕ, (N : ResidueField A) ≠ 0 → ∀ Q : (W.baseChange (ResidueField A)).toAffine.Point,
      N • Q = 0 → ∃ Y, r Y = Q := by
    intro N hN Q hQ
    have hQ' : N • ι Q = 0 := by
      have h1 : ι (N • Q) = N • ι Q := map_nsmul ι N Q
      rw [← h1]
      have h2 : (N • Q : ((W.baseChange (ResidueField A)).baseChange (ResidueField A)).toAffine.Point) = 0 :=
        hQ
      rw [h2]; exact map_zero ι
    obtain ⟨Y, -, hY⟩ := h0e0 A E hΔ hN (ι Q) hQ'
    refine ⟨Y, ?_⟩
    show ι' (reduceHom hΔ Y) = Q
    rw [hY]; exact DFunLike.congr_fun hι'ι Q
  -- (a) the quadratic relation
  have hγ : α.comp α + q • AddMonoidHom.id (E.map A.subtype).toAffine.Point - t • α ∈
      rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype) :=
    sub_mem h195 h580 _ _
      (h195 (AlgebraicClosure ℚ) _ _ (hfe3 (AlgebraicClosure ℚ) _ _ _ hα hα)
        (zsmul_mem h195 h580 _ _ (id_mem_rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype)) q))
      (zsmul_mem h195 h580 _ _ hα t)
  have hγ0 : ∀ P, reduceHom hΔ ((α.comp α + q • AddMonoidHom.id (E.map A.subtype).toAffine.Point - t • α) P)
      = 0 := by
    intro P
    have hrP : r ((α.comp α + q • AddMonoidHom.id (E.map A.subtype).toAffine.Point - t • α) P) = 0 := by
      have hch := DFunLike.congr_fun hπch (r P)
      simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, zsmul_hom_apply,
        AddMonoidHom.id_apply] at hch
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
        zsmul_hom_apply, AddMonoidHom.id_apply, map_sub, map_add, map_zsmul, hr]
      rw [hch, sub_self]
    have hrP' : ι' (reduceHom hΔ ((α.comp α + q • AddMonoidHom.id (E.map A.subtype).toAffine.Point - t • α) P))
        = 0 := hrP
    calc reduceHom hΔ ((α.comp α + q • AddMonoidHom.id (E.map A.subtype).toAffine.Point - t • α) P)
        = ι (ι' (reduceHom hΔ ((α.comp α + q • AddMonoidHom.id (E.map A.subtype).toAffine.Point - t • α) P))) :=
          (DFunLike.congr_fun hιι' _).symm
      _ = ι 0 := by rw [hrP']
      _ = 0 := map_zero ι
  have hquad := red_inj ha78 h0e0 (ringChar F) hp E hΔ hγ hγ0
  refine ⟨sub_eq_zero.mp hquad, fun m hm => ⟨fun hfix => ?_, fun hfix => ?_⟩⟩
  · -- (b1) `α^m = id` forces `π^m = id`
    let πE : AddMonoid.End (W.baseChange (ResidueField A)).toAffine.Point := π
    have hψ : πE ^ m ∈
        rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W.baseChange (ResidueField A)) :=
      pow_mem hfe3 (W.baseChange (ResidueField A)) hπ m
    have hfixk : ∀ N : ℕ, (N : ResidueField A) ≠ 0 → ∀ Q : (W.baseChange (ResidueField A)).toAffine.Point,
        N • Q = 0 → (πE ^ m) Q = Q := by
      intro N hN Q hQ
      obtain ⟨Y, rfl⟩ := hlift N hN Q hQ
      have h1 := iterate_comm r α πE hr m Y
      rw [hfix] at h1
      exact h1.symm
    have hid := eq_id_of_forall_tors h0e8 h195 h580 (ringChar F) hp _ hψ hfixk
    obtain ⟨P, hP⟩ := frob_iter_ne_id W σ hσ m hm
    apply hP
    have := DFunLike.congr_fun hid P
    exact this
  · -- (b2) `(t - α)^m = id` forces `(t - π)^m = id`, impossible on the `p`-torsion point `T`
    set φ : AddMonoid.End (W.baseChange (ResidueField A)).toAffine.Point :=
      t • AddMonoidHom.id (W.baseChange (ResidueField A)).toAffine.Point - π with hφdef
    have hφ : φ ∈
        rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W.baseChange (ResidueField A)) :=
      sub_mem h195 h580 _ _
        (zsmul_mem h195 h580 _ _ (id_mem_rationalHomSet (ResidueField A) (W.baseChange (ResidueField A))) t) hπ
    have hrφ : ∀ P, r ((t • AddMonoidHom.id (E.map A.subtype).toAffine.Point - α) P) = φ (r P) := by
      intro P
      show r (t • P - α P) = t • r P - π (r P)
      rw [map_sub, map_zsmul, hr]
    have hfixk : ∀ N : ℕ, (N : ResidueField A) ≠ 0 → ∀ Q : (W.baseChange (ResidueField A)).toAffine.Point,
        N • Q = 0 → (φ ^ m) Q = Q := by
      intro N hN Q hQ
      obtain ⟨Y, rfl⟩ := hlift N hN Q hQ
      have h1 := iterate_comm r _ φ hrφ m Y
      rw [hfix] at h1
      exact h1.symm
    have hid := eq_id_of_forall_tors h0e8 h195 h580 (ringChar F) hp _ (pow_mem hfe3 _ hφ m) hfixk
    have hπφ : ∀ P, π (φ P) = q • P := by
      intro P
      have hch := DFunLike.congr_fun hπch P
      simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, zsmul_hom_apply,
        AddMonoidHom.id_apply] at hch
      show π (t • P - π P) = q • P
      rw [map_sub, map_zsmul, ← hch]; abel
    have hTT : (φ ^ m) T = T := by
      have := DFunLike.congr_fun hid T; rwa [AddMonoidHom.id_apply] at this
    have hqT : (q ^ m) • T = 0 := by
      obtain ⟨n, hn, rfl⟩ := hq
      have hd : ((ringChar F : ℕ) : ℤ) ∣ ((ringChar F : ℤ) ^ n) ^ m :=
        dvd_pow (dvd_pow_self _ hn.ne') hm.ne'
      obtain ⟨c, hc⟩ := hd
      rw [hc, mul_comm, mul_smul, natCast_zsmul, hpT]
      exact (zsmul_zero c : c • (0 : (W.baseChange (ResidueField A)).toAffine.Point) = 0)
    let πE : AddMonoid.End (W.baseChange (ResidueField A)).toAffine.Point := π
    have hπT : (πE ^ m) T = (πE ^ m) 0 := by
      rw [map_zero, ← hqT, ← pow_pow_apply πE φ q hπφ m T, hTT]
    rw [AddMonoid.End.coe_pow] at hπT
    exact hT0 ((Point.map_injective (W' := W) σ.toAlgHom).iterate m hπT)

end RPLib.S4T.CMGlue


