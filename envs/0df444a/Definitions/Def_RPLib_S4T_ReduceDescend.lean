-- Prove2me | Definitions.Def_RPLib_S4T_ReduceDescend
-- name    : RPLib_S4T_ReduceDescend
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:18:31.19492+00:00
-- url     : https://prove2.me/theorems/0ef0ed7e-ca7c-4424-a4a1-217c389a4a76
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: reduce the prime-to-`p` pair and make it Frobenius-equivariant
-- statement:
--   Reduce the prime-to-`p` pair and make it Frobenius-equivariant.
--
--   Proves `RPLib.S4T.Glue.L7Stmt` from the FLT statements (explicit hypotheses, never used as lemmas)
--   a78cfa46 (nonzero rational maps are surjective), 0e002459 (lifting prime-to-`p` torsion), bf2cb471 (the
--   variable-change equivalence is a rational group isomorphism), 0e8f5714 (dual pairs, through
--   `CMGlue.eq_id_of_forall_tors`), 094b1237 (rational endomorphisms commute when a nonzero `p`-torsion point exists),
--   fe3c6240 / 195173b3 / 580839d4 (closure under composition, addition, negation).
--
--   * `red_comp` (L6, repair R3): the reductions `νu, νw` of a pair `w ∘ u = N` satisfy `νw ∘ νu = N` (density on the
--     reductions of the prime-to-`p` torsion; no Henselian lemma);
--   * `eq_zero_of_nsmul` : a rational map killed by `N` (`p ∤ N`) into a curve with a nonzero `p`-torsion point is `0`;
--   * `l7` : `L7Stmt` (transport through the variable changes, then L7: `ε = ū π w̄ ∈ {N π', N π̄'}`, the second case
--     is excluded on the `p`-torsion point `T`).
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_CMGlue

/-!
# S4T-ReduceDescend (route L6-L7, repair R3): reduce the prime-to-`p` pair and make it Frobenius-equivariant

Proves `RPLib.S4T.Glue.L7Stmt` from the FLT statements (explicit hypotheses, never used as lemmas)
a78cfa46 (nonzero rational maps are surjective), 0e002459 (lifting prime-to-`p` torsion), bf2cb471 (the
variable-change equivalence is a rational group isomorphism), 0e8f5714 (dual pairs, through
`CMGlue.eq_id_of_forall_tors`), 094b1237 (rational endomorphisms commute when a nonzero `p`-torsion point exists),
fe3c6240 / 195173b3 / 580839d4 (closure under composition, addition, negation).

* `red_comp` (L6, repair R3): the reductions `νu, νw` of a pair `w ∘ u = N` satisfy `νw ∘ νu = N` (density on the
  reductions of the prime-to-`p` torsion; no Henselian lemma);
* `eq_zero_of_nsmul` : a rational map killed by `N` (`p ∤ N`) into a curve with a nonzero `p`-torsion point is `0`;
* `l7` : `L7Stmt` (transport through the variable changes, then L7: `ε = ū π w̄ ∈ {N π', N π̄'}`, the second case
  is excluded on the `p`-torsion point `T`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace RPLib.S4T.ReduceDescend

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

/-- A point killed by a prime `p` and by `N` with `p ∤ N` is `0`. -/
theorem coprime_kill {M : Type} [AddCommGroup M] (p N : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) {P : M}
    (h1 : p • P = 0) (h2 : (N : ℤ) • P = 0) : P = 0 := by
  have hc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have h1' : (p : ℤ) • P = 0 := by rw [natCast_zsmul]; exact h1
  calc P = (a * (p : ℤ) + b * (N : ℤ)) • P := by rw [hab, one_smul]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, h1', h2, smul_zero, smul_zero, add_zero]

/-- A rational map killed by `N`, `p ∤ N`, into a curve with a nonzero `p`-torsion point is `0`. -/
theorem eq_zero_of_nsmul (ha78 : FLT.S_a78cfa46.{0, 0}) {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (Y₁ Y₂ : WeierstrassCurve k) [Y₁.IsElliptic] [Y₂.IsElliptic]
    {D : Y₁.toAffine.Point →+ Y₂.toAffine.Point} (hD : D ∈ rationalHomSet k Y₁ Y₂)
    (p : ℕ) (hp : p.Prime) {T : Y₂.toAffine.Point} (hT0 : T ≠ 0) (hpT : p • T = 0)
    (N : ℕ) (hpN : ¬ p ∣ N) (h : ∀ P, (N : ℤ) • D P = 0) : D = 0 := by
  by_contra hne
  have hsurj : ∀ Q : Y₂.toAffine.Point, ∃ P : Y₁.toAffine.Point, D P = Q := ha78 k hD hne
  obtain ⟨P, hP⟩ := hsurj T
  have hNT : (N : ℤ) • T = 0 := by rw [← hP]; exact h P
  exact hT0 (coprime_kill p N hp hpN hpT hNT)

/-- **L6 (repair R3).** If `w ∘ u = N` on the generic fibres, the reductions satisfy `νw ∘ νu = N`. -/
theorem red_comp (h0e8 : FLT.S_0e8f5714.{0, 0}) (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0})
    (hfe3 : FLT.S_fe3c6240.{0, 0}) (h0e0 : FLT.S_0e002459.{0})
    {A : ValuationSubring (AlgebraicClosure ℚ)} [DecidableEq (AlgebraicClosure ℚ)]
    [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)] (p : ℕ) [CharP (ResidueField A) p]
    (hp : p.Prime) (E E' : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0)
    (hΔ' : (E'.map (residue A)).Δ ≠ 0)
    {u : (E.map A.subtype).toAffine.Point →+ (E'.map A.subtype).toAffine.Point}
    {w : (E'.map A.subtype).toAffine.Point →+ (E.map A.subtype).toAffine.Point}
    (N : ℕ) (hwu : w.comp u = (N : ℤ) • AddMonoidHom.id (E.map A.subtype).toAffine.Point)
    {νu : (E.map (residue A)).toAffine.Point →+ (E'.map (residue A)).toAffine.Point}
    {νw : (E'.map (residue A)).toAffine.Point →+ (E.map (residue A)).toAffine.Point}
    (hνu : νu ∈ rationalHomSet (ResidueField A) (E.map (residue A)) (E'.map (residue A)))
    (hνw : νw ∈ rationalHomSet (ResidueField A) (E'.map (residue A)) (E.map (residue A)))
    (hredu : (reduceHom hΔ').comp u = νu.comp (reduceHom hΔ))
    (hredw : (reduceHom hΔ).comp w = νw.comp (reduceHom hΔ')) :
    νw.comp νu = (N : ℤ) • AddMonoidHom.id (E.map (residue A)).toAffine.Point := by
  haveI : (E.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI : (E'.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  let ψ : (E.map (residue A)).toAffine.Point →+ (E.map (residue A)).toAffine.Point :=
    νw.comp νu - (N : ℤ) • AddMonoidHom.id (E.map (residue A)).toAffine.Point +
      AddMonoidHom.id (E.map (residue A)).toAffine.Point
  have hψ : ψ ∈ rationalHomSet (ResidueField A) (E.map (residue A)) (E.map (residue A)) :=
    h195 _ _ _ (CMGlue.sub_mem h195 h580 _ _ (hfe3 _ _ _ _ hνu hνw)
      (CMGlue.zsmul_mem h195 h580 _ _ (id_mem_rationalHomSet (ResidueField A) (E.map (residue A))) (N : ℤ)))
      (id_mem_rationalHomSet (ResidueField A) (E.map (residue A)))
  have hfix : ∀ ℓ : ℕ, (ℓ : ResidueField A) ≠ 0 → ∀ Q : (E.map (residue A)).toAffine.Point,
      ℓ • Q = 0 → ψ Q = Q := by
    intro ℓ hℓ Q₀ hQ₀
    obtain ⟨Q, -, hQ⟩ := h0e0 A E hΔ hℓ Q₀ hQ₀
    have h1 : νw (νu Q₀) = (N : ℤ) • Q₀ := by
      rw [← hQ]
      have e1 : reduceHom hΔ' (u Q) = νu (reduceHom hΔ Q) := DFunLike.congr_fun hredu Q
      have e2 : reduceHom hΔ (w (u Q)) = νw (reduceHom hΔ' (u Q)) := DFunLike.congr_fun hredw (u Q)
      have e3 : w (u Q) = (N : ℤ) • Q := DFunLike.congr_fun hwu Q
      rw [← e1, ← e2, e3, map_zsmul]
    show νw (νu Q₀) - (N : ℤ) • Q₀ + Q₀ = Q₀
    rw [h1, sub_self, zero_add]
  have hid := CMGlue.eq_id_of_forall_tors h0e8 h195 h580 p hp _ hψ hfix
  ext P
  have h2 : νw (νu P) - (N : ℤ) • P + P = P := DFunLike.congr_fun hid P
  show νw (νu P) = (N : ℤ) • P
  exact sub_eq_zero.mp (add_right_cancel (h2.trans (zero_add P).symm))

/-- **L7.** `L7Stmt`: transport of the reductions to `W_k, W'_k`, `w̄ ∘ ū = N`, and Frobenius-equivariance. -/
theorem l7 (ha78 : FLT.S_a78cfa46.{0, 0}) (h0e0 : FLT.S_0e002459.{0}) (hbf2 : FLT.S_bf2cb471.{0})
    (h0e8 : FLT.S_0e8f5714.{0, 0}) (hfe3 : FLT.S_fe3c6240.{0, 0}) (h195 : FLT.S_195173b3.{0, 0})
    (h580 : FLT.S_580839d4.{0, 0}) (h094 : FLT.S_094b1237.{0}) : Glue.L7Stmt := by
  intro F _ _ W W' _ _ A _ _ _ _ _ σ hσ t q hirr hq ht hπ hπch hπ' hπch' T hT0 hpT T' hT0' hpT' E E' hΔ hΔ'
    v v' hv hv' u w hu hw N hpN hwu huw νu νw hνu hνw hredu hredw
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hp⟩
  haveI : (E.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI : (E'.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  haveI : (W.baseChange (ResidueField A)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (ResidueField A))).IsElliptic
  haveI : (W'.baseChange (ResidueField A)).IsElliptic :=
    inferInstanceAs (W'.map (algebraMap F (ResidueField A))).IsElliptic
  set π := Point.map (W' := W) σ.toAlgHom with hπdef
  set π' := Point.map (W' := W') σ.toAlgHom with hπ'def
  -- L6 (repair R3), both ways
  have hνwu := red_comp h0e8 h195 h580 hfe3 h0e0 (ringChar F) hp E E' hΔ hΔ' N hwu hνu hνw hredu hredw
  have hνuw := red_comp h0e8 h195 h580 hfe3 h0e0 (ringChar F) hp E' E hΔ' hΔ N huw hνw hνu hredw hredu
  -- transport through the variable changes (bf2cb471)
  obtain ⟨i1r, hi1, k1r, hk1, -, h11r, h12r⟩ := hbf2 (E.map (residue A)) v hv
  obtain ⟨i2r, hi2, k2r, hk2, -, h21r, h22r⟩ := hbf2 (E'.map (residue A)) v' hv'
  let i1 : (W.baseChange (ResidueField A)).toAffine.Point →+ (E.map (residue A)).toAffine.Point := i1r
  let k1 : (E.map (residue A)).toAffine.Point →+ (W.baseChange (ResidueField A)).toAffine.Point := k1r
  let i2 : (W'.baseChange (ResidueField A)).toAffine.Point →+ (E'.map (residue A)).toAffine.Point := i2r
  let k2 : (E'.map (residue A)).toAffine.Point →+ (W'.baseChange (ResidueField A)).toAffine.Point := k2r
  have h11 : ∀ P, k1 (i1 P) = P := fun P => DFunLike.congr_fun h11r P
  have h12 : ∀ Z, i1 (k1 Z) = Z := fun Z => DFunLike.congr_fun h12r Z
  have h21 : ∀ P, k2 (i2 P) = P := fun P => DFunLike.congr_fun h21r P
  have h22 : ∀ Z, i2 (k2 Z) = Z := fun Z => DFunLike.congr_fun h22r Z
  let ub : (W.baseChange (ResidueField A)).toAffine.Point →+ (W'.baseChange (ResidueField A)).toAffine.Point :=
    (k2.comp νu).comp i1
  let wb : (W'.baseChange (ResidueField A)).toAffine.Point →+ (W.baseChange (ResidueField A)).toAffine.Point :=
    (k1.comp νw).comp i2
  have hub : ub ∈
      rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) :=
    hfe3 _ _ _ _ hi1 (hfe3 _ _ _ _ hνu hk2)
  have hwb : wb ∈
      rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W.baseChange (ResidueField A)) :=
    hfe3 _ _ _ _ hi2 (hfe3 _ _ _ _ hνw hk1)
  have hwubP : ∀ P : (W.baseChange (ResidueField A)).toAffine.Point, wb (ub P) = (N : ℤ) • P := by
    intro P
    show k1 (νw (i2 (k2 (νu (i1 P))))) = (N : ℤ) • P
    have e : νw (νu (i1 P)) = (N : ℤ) • i1 P := DFunLike.congr_fun hνwu (i1 P)
    rw [h22, e, map_zsmul, h11]
  have huwbP : ∀ Y : (W'.baseChange (ResidueField A)).toAffine.Point, ub (wb Y) = (N : ℤ) • Y := by
    intro Y
    show k2 (νu (i1 (k1 (νw (i2 Y))))) = (N : ℤ) • Y
    have e : νu (νw (i2 Y)) = (N : ℤ) • i2 Y := DFunLike.congr_fun hνuw (i2 Y)
    rw [h12, e, map_zsmul, h21]
  have hwub : wb.comp ub = (N : ℤ) • AddMonoidHom.id (W.baseChange (ResidueField A)).toAffine.Point := by
    ext P; exact hwubP P
  -- the Frobenius relations on points
  have chπ : ∀ P, π (π P) = t • π P - q • P := by
    intro P
    have h := DFunLike.congr_fun hπch P
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, CMGlue.zsmul_hom_apply,
      AddMonoidHom.id_apply] at h
    exact eq_sub_of_add_eq h
  have chπ' : ∀ Y, π' (π' Y) = t • π' Y - q • Y := by
    intro Y
    have h := DFunLike.congr_fun hπch' Y
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, CMGlue.zsmul_hom_apply,
      AddMonoidHom.id_apply] at h
    exact eq_sub_of_add_eq h
  -- `t - π'` kills `p`-torsion
  have hbarkill : ∀ Y : (W'.baseChange (ResidueField A)).toAffine.Point, ringChar F • Y = 0 →
      t • Y - π' Y = 0 := by
    intro Y hY
    have hqY : q • Y = 0 := by
      obtain ⟨n, hn, hqn⟩ := hq
      obtain ⟨c, hc⟩ : ((ringChar F : ℕ) : ℤ) ∣ ((ringChar F : ℕ) : ℤ) ^ n := dvd_pow_self _ hn.ne'
      rw [hqn, hc, mul_comm, mul_smul, natCast_zsmul, hY]
      exact zsmul_zero c
    apply Point.map_injective (W' := W') σ.toAlgHom
    show π' (t • Y - π' Y) = π' 0
    rw [map_sub, map_zsmul, chπ', map_zero, hqY, sub_zero, sub_self]
  -- `ε = ū π w̄` and its quadratic relation
  let ε : (W'.baseChange (ResidueField A)).toAffine.Point →+ (W'.baseChange (ResidueField A)).toAffine.Point :=
    ub.comp (π.comp wb)
  have hε : ε ∈
      rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) :=
    hfe3 _ _ _ _ (hfe3 _ _ _ _ hwb hπ) hub
  have hcomm := h094 (ringChar F) (W'.baseChange (ResidueField A)) hT0' hpT' hε hπ'
  have hcommY : ∀ Y, ε (π' Y) = π' (ε Y) := fun Y => DFunLike.congr_fun hcomm Y
  have hεε : ∀ Y, ε (ε Y) = ((N : ℤ) * t) • ε Y - ((N : ℤ) * N * q) • Y := by
    intro Y
    show ub (π (wb (ub (π (wb Y))))) = ((N : ℤ) * t) • ub (π (wb Y)) - ((N : ℤ) * N * q) • Y
    simp only [hwubP, map_zsmul, chπ, map_sub, huwbP]
    module
  -- `(ε - N π') ∘ (ε - N π̄') = 0`
  let b : (W'.baseChange (ResidueField A)).toAffine.Point →+ (W'.baseChange (ResidueField A)).toAffine.Point :=
    ε - (N : ℤ) • (t • AddMonoidHom.id (W'.baseChange (ResidueField A)).toAffine.Point - π')
  have hbar' : t • AddMonoidHom.id (W'.baseChange (ResidueField A)).toAffine.Point - π' ∈
      rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) :=
    CMGlue.sub_mem h195 h580 _ _
      (CMGlue.zsmul_mem h195 h580 _ _ (id_mem_rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A))) t)
      hπ'
  have hb : b ∈
      rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) :=
    CMGlue.sub_mem h195 h580 _ _ hε (CMGlue.zsmul_mem h195 h580 _ _ hbar' (N : ℤ))
  have hab : ∀ Y, ε (b Y) - (N : ℤ) • π' (b Y) = 0 := by
    intro Y
    show ε (ε Y - (N : ℤ) • (t • Y - π' Y)) - (N : ℤ) • π' (ε Y - (N : ℤ) • (t • Y - π' Y)) = 0
    simp only [map_sub, map_zsmul, hεε, hcommY, chπ']
    module
  by_cases hb0 : b = 0
  · -- `ε = N π̄'` is impossible: it forces `ū (π T) = 0`
    exfalso
    have hεb : ∀ Z, ε Z = (N : ℤ) • (t • Z - π' Z) := by
      intro Z
      have h : ε Z - (N : ℤ) • (t • Z - π' Z) = 0 := DFunLike.congr_fun hb0 Z
      exact sub_eq_zero.mp h
    let D' : (W.baseChange (ResidueField A)).toAffine.Point →+ (W'.baseChange (ResidueField A)).toAffine.Point :=
      ub.comp π - (t • AddMonoidHom.id (W'.baseChange (ResidueField A)).toAffine.Point - π').comp ub
    have hD' : D' ∈
        rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) :=
      CMGlue.sub_mem h195 h580 _ _ (hfe3 _ _ _ _ hπ hub) (hfe3 _ _ _ _ hub hbar')
    have hD'0 : D' = 0 := eq_zero_of_nsmul ha78 _ _ hD' (ringChar F) hp hT0' hpT' N hpN (fun P => by
      rw [← map_zsmul D' (N : ℤ) P, ← hwubP P]
      show ub (π (wb (ub P))) - (t • ub (wb (ub P)) - π' (ub (wb (ub P)))) = 0
      rw [show ub (π (wb (ub P))) = (N : ℤ) • (t • ub P - π' (ub P)) from hεb (ub P), huwbP, map_zsmul]
      module)
    have hD'T : ub (π T) = t • ub T - π' (ub T) := by
      have h : ub (π T) - (t • ub T - π' (ub T)) = 0 := DFunLike.congr_fun hD'0 T
      exact sub_eq_zero.mp h
    have hpuT : ringChar F • ub T = 0 := by rw [← map_nsmul ub (ringChar F) T, hpT, map_zero]
    have hubπT : ub (π T) = 0 := by rw [hD'T]; exact hbarkill _ hpuT
    have hNπT : (N : ℤ) • π T = 0 := by rw [← hwubP, hubπT, map_zero]
    have hpπT : ringChar F • π T = 0 := by rw [← map_nsmul π (ringChar F) T, hpT, map_zero]
    have hπT0 := coprime_kill _ N hp hpN hpπT hNπT
    exact hT0 (Point.map_injective (W' := W) σ.toAlgHom (hπT0.trans (map_zero π).symm))
  · -- `b` is surjective, so `ε = N π'`
    have hsurj : ∀ Z : (W'.baseChange (ResidueField A)).toAffine.Point,
        ∃ Y : (W'.baseChange (ResidueField A)).toAffine.Point, b Y = Z :=
      ha78 (F := ResidueField A) (W₁ := W'.baseChange (ResidueField A))
        (W₂ := W'.baseChange (ResidueField A)) _ hb hb0
    have hεπ : ∀ Z, ε Z = (N : ℤ) • π' Z := by
      intro Z
      obtain ⟨Y, rfl⟩ := hsurj Z
      exact sub_eq_zero.mp (hab Y)
    -- `ū π = π' ū`
    let D : (W.baseChange (ResidueField A)).toAffine.Point →+ (W'.baseChange (ResidueField A)).toAffine.Point :=
      ub.comp π - π'.comp ub
    have hD : D ∈
        rationalHomSet (ResidueField A) (W.baseChange (ResidueField A)) (W'.baseChange (ResidueField A)) :=
      CMGlue.sub_mem h195 h580 _ _ (hfe3 _ _ _ _ hπ hub) (hfe3 _ _ _ _ hub hπ')
    have hD0 : D = 0 := eq_zero_of_nsmul ha78 _ _ hD (ringChar F) hp hT0' hpT' N hpN (fun P => by
      rw [← map_zsmul D (N : ℤ) P, ← hwubP P]
      show ub (π (wb (ub P))) - π' (ub (wb (ub P))) = 0
      rw [show ub (π (wb (ub P))) = (N : ℤ) • π' (ub P) from hεπ (ub P), huwbP, map_zsmul, sub_self])
    have hcu : ∀ P, ub (π P) = π' (ub P) := by
      intro P
      have h : ub (π P) - π' (ub P) = 0 := DFunLike.congr_fun hD0 P
      exact sub_eq_zero.mp h
    -- `w̄ π' = π w̄`
    let D'' : (W'.baseChange (ResidueField A)).toAffine.Point →+ (W.baseChange (ResidueField A)).toAffine.Point :=
      π.comp wb - wb.comp π'
    have hD'' : D'' ∈
        rationalHomSet (ResidueField A) (W'.baseChange (ResidueField A)) (W.baseChange (ResidueField A)) :=
      CMGlue.sub_mem h195 h580 _ _ (hfe3 _ _ _ _ hwb hπ) (hfe3 _ _ _ _ hπ' hwb)
    have hD''0 : D'' = 0 := eq_zero_of_nsmul ha78 _ _ hD'' (ringChar F) hp hT0 hpT N hpN (fun Y => by
      rw [← map_zsmul D'' (N : ℤ) Y, ← huwbP Y]
      show π (wb (ub (wb Y))) - wb (π' (ub (wb Y))) = 0
      rw [← hcu (wb Y), hwubP (wb Y), hwubP (π (wb Y)), map_zsmul, sub_self])
    have hcw : ∀ Y, wb (π' Y) = π (wb Y) := by
      intro Y
      have h : π (wb Y) - wb (π' Y) = 0 := DFunLike.congr_fun hD''0 Y
      exact (sub_eq_zero.mp h).symm
    refine ⟨ub, hub, wb, hwb, fun P => ?_, fun Y => ?_, hwub⟩
    · show ub (π P) = π' (ub P)
      exact hcu P
    · show wb (π' Y) = π (wb Y)
      exact hcw Y

end RPLib.S4T.ReduceDescend


