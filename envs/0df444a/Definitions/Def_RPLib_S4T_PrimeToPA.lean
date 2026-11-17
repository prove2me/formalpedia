-- Prove2me | Definitions.Def_RPLib_S4T_PrimeToPA
-- name    : RPLib_S4T_PrimeToPA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:18:17.412641+00:00
-- url     : https://prove2.me/theorems/beacc210-8be7-446d-a8e4-404c026d26f8
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: torsion tools in characteristic 0 and the two lines of `X[p]`
-- statement:
--   Torsion tools in characteristic 0 and the two lines of `X[p]`.
--
--   Over an algebraically closed `Ω` of characteristic 0, for an elliptic curve `X` with a rational endomorphism `α`,
--   `α ∘ α + q = t α`, `q = p ^ n` (`n > 0`), `p ∤ t`, and `ᾱ := t - α`:
--   * `eq_zero_of_nsmul` (rational maps are torsion-free), `exists_nsmul_eq` (points are divisible),
--     `exists_ptors`, `pow_nsmul_eq_zero_of` (p-power torsion helpers);
--   * `Lsub α = {P | p • P = 0 ∧ α P = 0}`; `split_p` (`X[p] = L(α) ⊕ L(ᾱ)`); `exists_L_ne_zero` (repair R2:
--     `L(α) ≠ 0` when `α` has no fixed power, via 6256914e and 97650530); `L_zmultiples` (`L(α)` is a line).
--   FLT statements are explicit hypotheses (never used as lemmas).
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_CMGlue

/-!
# S4T-PrimeToP, part A: torsion tools in characteristic 0 and the two lines of `X[p]`

Over an algebraically closed `Ω` of characteristic 0, for an elliptic curve `X` with a rational endomorphism `α`,
`α ∘ α + q = t α`, `q = p ^ n` (`n > 0`), `p ∤ t`, and `ᾱ := t - α`:
* `eq_zero_of_nsmul` (rational maps are torsion-free), `exists_nsmul_eq` (points are divisible),
  `exists_ptors`, `pow_nsmul_eq_zero_of` (p-power torsion helpers);
* `Lsub α = {P | p • P = 0 ∧ α P = 0}`; `split_p` (`X[p] = L(α) ⊕ L(ᾱ)`); `exists_L_ne_zero` (repair R2:
  `L(α) ≠ 0` when `α` has no fixed power, via 6256914e and 97650530); `L_zmultiples` (`L(α)` is a line).
FLT statements are explicit hypotheses (never used as lemmas).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RPLib.S4T.PrimeToP

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### Pure group lemmas -/

section Group

variable {M : Type} [AddCommGroup M]

theorem nsmul_hom_apply {N : Type} [AddCommGroup N] (n : ℕ) (f : M →+ N) (x : M) : (n • f) x = n • f x := rfl

theorem exists_ptors (p : ℕ) {P : M} (hP : P ≠ 0) (k : ℕ) (hk : p ^ k • P = 0) :
    ∃ j : ℕ, p ^ j • P ≠ 0 ∧ p • (p ^ j • P) = 0 := by
  induction k with
  | zero => rw [pow_zero, one_smul] at hk; exact absurd hk hP
  | succ k ih =>
    by_cases h : p ^ k • P = 0
    · exact ih h
    · exact ⟨k, h, by rw [smul_smul, ← pow_succ']; exact hk⟩

theorem pow_nsmul_eq_zero_of {p : ℕ} (hp : p.Prime) {P : M} {n k : ℕ} (hn : 0 < n) (h1 : n • P = 0)
    (h2 : p ^ k • P = 0) : p ^ n • P = 0 := by
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).1 (addOrderOf_dvd_of_nsmul_eq_zero h2)
  have hd1 : addOrderOf P ∣ n := addOrderOf_dvd_of_nsmul_eq_zero h1
  rw [hjeq] at hd1
  have hjn : j < n := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.le_of_dvd hn hd1)
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
  rw [hjeq]; exact pow_dvd_pow p hjn.le

/-- Coprime torsion orders: `a • P = 0`, `b • P = 0`, `IsCoprime a b` give `P = 0`. -/
theorem eq_zero_of_coprime {P : M} {a b : ℤ} (hab : IsCoprime a b) (ha : a • P = 0) (hb : b • P = 0) : P = 0 := by
  obtain ⟨u, v, huv⟩ := hab
  calc P = (u * a + v * b) • P := by rw [huv, one_smul]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, ha, hb, smul_zero, smul_zero, add_zero]

end Group

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω]

/-! ### Torsion-freeness and divisibility -/

/-- **T1.** A rational map killed by `N ≥ 1` is `0`. -/
theorem eq_zero_of_nsmul (ha78 : FLT.S_a78cfa46.{0, 0}) (X Y : WeierstrassCurve Ω) [X.IsElliptic] [Y.IsElliptic]
    {γ : X.toAffine.Point →+ Y.toAffine.Point} (hγ : γ ∈ rationalHomSet Ω X Y) (N : ℕ) (hN : 0 < N)
    (h : ∀ P, N • γ P = 0) : γ = 0 := by
  by_contra hne
  have hs : Function.Surjective γ := ha78 Ω hγ hne
  obtain ⟨Q, hQ0, hQ⟩ := CMGlue.exists_tors_ne_zero Y (N + 1) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N))
    (by omega)
  obtain ⟨P, rfl⟩ := hs Q
  apply hQ0
  rw [add_smul, one_smul, h P, zero_add] at hQ
  exact hQ

/-- **T1'.** Two rational maps that agree after multiplication by `N ≥ 1` are equal. -/
theorem eq_of_nsmul (ha78 : FLT.S_a78cfa46.{0, 0}) (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0})
    (X Y : WeierstrassCurve Ω) [X.IsElliptic] [Y.IsElliptic]
    {γ δ : X.toAffine.Point →+ Y.toAffine.Point} (hγ : γ ∈ rationalHomSet Ω X Y) (hδ : δ ∈ rationalHomSet Ω X Y)
    (N : ℕ) (hN : 0 < N) (h : ∀ P, N • γ P = N • δ P) : γ = δ := by
  have h0 := eq_zero_of_nsmul ha78 X Y (CMGlue.sub_mem h195 h580 X Y hγ hδ) N hN (fun P =>
    show N • (γ P - δ P) = 0 by rw [nsmul_sub, h P, sub_self])
  exact sub_eq_zero.mp h0

/-- **T2.** Every point is divisible by `N ≥ 1`. -/
theorem exists_nsmul_eq (ha78 : FLT.S_a78cfa46.{0, 0}) (h195 : FLT.S_195173b3.{0, 0})
    (X : WeierstrassCurve Ω) [X.IsElliptic] (N : ℕ) (hN : 0 < N) (P : X.toAffine.Point) :
    ∃ P', N • P' = P := by
  have hmem : N • AddMonoidHom.id X.toAffine.Point ∈ rationalHomSet Ω X X :=
    CMGlue.nsmul_mem h195 X X (id_mem_rationalHomSet Ω X) N
  have hne : N • AddMonoidHom.id X.toAffine.Point ≠ 0 := by
    intro h0
    obtain ⟨Q, hQ0, hQ⟩ := CMGlue.exists_tors_ne_zero X (N + 1) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N))
      (by omega)
    have hNQ : N • Q = 0 := by
      have := DFunLike.congr_fun h0 Q
      rwa [nsmul_hom_apply, AddMonoidHom.id_apply] at this
    apply hQ0
    rw [add_smul, one_smul, hNQ, zero_add] at hQ
    exact hQ
  obtain ⟨P', hP'⟩ := (ha78 Ω hmem hne) P
  exact ⟨P', hP'⟩

/-! ### The lines `L(α)` and `L(t - α)` of `X[p]` -/

/-- `L(α) = ker α ∩ X[p]`. -/
def Lsub (X : WeierstrassCurve Ω) (p : ℕ) (α : X.toAffine.Point →+ X.toAffine.Point) :
    AddSubgroup X.toAffine.Point :=
  α.ker ⊓ RPLib.Torsion.tors X p

theorem mem_Lsub {X : WeierstrassCurve Ω} {p : ℕ} {α : X.toAffine.Point →+ X.toAffine.Point}
    {P : X.toAffine.Point} : P ∈ Lsub X p α ↔ p • P = 0 ∧ α P = 0 := by
  rw [Lsub, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, RPLib.Torsion.mem_tors, and_comm]

section Lines

variable (X : WeierstrassCurve Ω) (p : ℕ) (t q : ℤ) (α : X.toAffine.Point →+ X.toAffine.Point)

/-- `ᾱ = t - α`. -/
def bar : X.toAffine.Point →+ X.toAffine.Point := t • AddMonoidHom.id X.toAffine.Point - α

theorem bar_apply (P : X.toAffine.Point) : bar X t α P = t • P - α P := rfl

theorem bar_bar : bar X t (bar X t α) = α := by
  ext P; rw [bar_apply, bar_apply, sub_sub_cancel]

variable {X t q α}

theorem ch_apply (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α) (P : X.toAffine.Point) :
    α (α P) = t • α P - q • P := by
  have := DFunLike.congr_fun hch P
  rw [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, CMGlue.zsmul_hom_apply, CMGlue.zsmul_hom_apply,
    AddMonoidHom.id_apply] at this
  rw [← this, add_sub_cancel_right]

theorem bar_comp_apply (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α) (P : X.toAffine.Point) :
    bar X t α (α P) = q • P := by
  rw [bar_apply, ch_apply hch]; abel

theorem comp_bar_apply (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α) (P : X.toAffine.Point) :
    α (bar X t α P) = q • P := by
  rw [bar_apply, map_sub, map_zsmul, ch_apply hch]; abel

theorem bar_ch (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α) :
    (bar X t α).comp (bar X t α) + q • AddMonoidHom.id X.toAffine.Point = t • bar X t α := by
  ext P
  rw [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, CMGlue.zsmul_hom_apply, CMGlue.zsmul_hom_apply,
    AddMonoidHom.id_apply]
  rw [bar_apply X t α (bar X t α P), comp_bar_apply hch, bar_apply]
  abel

/-- The Bezout coefficient: `d * t ≡ 1 (mod p)`. -/
theorem exists_inv (hp : p.Prime) (ht : ¬ (p : ℤ) ∣ t) : ∃ d u : ℤ, d * t + u * p = 1 := by
  have hcop : IsCoprime (p : ℤ) t :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).2 ht
  obtain ⟨u, d, h⟩ := hcop
  exact ⟨d, u, by linarith⟩

theorem q_kills (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) {P : X.toAffine.Point} (hP : p • P = 0) : q • P = 0 := by
  obtain ⟨n, hn, rfl⟩ := hq
  obtain ⟨c, hc⟩ : (p : ℤ) ∣ (p : ℤ) ^ n := dvd_pow_self _ hn.ne'
  rw [hc, mul_comm, mul_smul, natCast_zsmul, hP, smul_zero]

/-- **S1.** `X[p] = L(α) ⊕ L(ᾱ)`: the decomposition `P = d • ᾱ P + d • α P`. -/
theorem split_p {d u : ℤ} (hdu : d * t + u * p = 1) {P : X.toAffine.Point} (hP : p • P = 0) :
    P = d • bar X t α P + d • α P := by
  rw [← smul_add, bar_apply, sub_add_cancel, smul_smul]
  have : (d * t) • P = (1 - u * p) • P := by rw [← hdu, add_sub_cancel_right]
  rw [this, sub_smul, one_smul, mul_smul, natCast_zsmul, hP, smul_zero, sub_zero]

theorem split_mem₀ (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α)
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) (d : ℤ) {P : X.toAffine.Point} (hP : p • P = 0) :
    d • bar X t α P ∈ Lsub X p α := by
  rw [mem_Lsub, map_zsmul, comp_bar_apply hch, q_kills p hq hP, smul_zero, smul_comm p d, ← map_nsmul, hP,
    map_zero, smul_zero]
  exact ⟨rfl, rfl⟩

theorem split_mem₁ (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α)
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) (d : ℤ) {P : X.toAffine.Point} (hP : p • P = 0) :
    d • α P ∈ Lsub X p (bar X t α) := by
  rw [mem_Lsub, map_zsmul, bar_comp_apply hch, q_kills p hq hP, smul_zero, smul_comm p d, ← map_nsmul, hP,
    map_zero, smul_zero]
  exact ⟨rfl, rfl⟩

theorem inter_eq_zero {d u : ℤ} (hdu : d * t + u * p = 1) {P : X.toAffine.Point}
    (h₀ : P ∈ Lsub X p α) (h₁ : P ∈ Lsub X p (bar X t α)) : P = 0 := by
  rw [mem_Lsub] at h₀ h₁
  rw [split_p p hdu h₀.1, h₀.2, h₁.2, smul_zero, add_zero]

end Lines

/-! ### Repair R2 and the line structure -/

/-- **S2 (repair R2).** If `α` has no fixed power, then `L(α) ≠ 0`. -/
theorem exists_L_ne_zero (h625 : FLT.S_6256914e.{0, 0}) (h976 : FLT.S_97650530.{0, 0})
    (hfe3 : FLT.S_fe3c6240.{0, 0}) (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0})
    (ha78 : FLT.S_a78cfa46.{0, 0}) {p : ℕ} (hp : p.Prime) {X : WeierstrassCurve Ω} [X.IsElliptic] {t q : ℤ}
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) {α : X.toAffine.Point →+ X.toAffine.Point}
    (hα : α ∈ rationalHomSet Ω X X) (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α)
    (hinf : ∀ m : ℕ, 0 < m → (⇑α)^[m] ≠ id) :
    ∃ P : X.toAffine.Point, P ≠ 0 ∧ P ∈ Lsub X p α := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn, rfl⟩ := hq
  have hinj : ∀ (k : ℕ) (P : X.toAffine.Point), p ^ k • P = 0 → α P = 0 → P = 0 := by
    intro k P hk hαP
    by_contra hP
    obtain ⟨j, hj0, hj⟩ := exists_ptors p hP k hk
    exact hcon _ hj0 (mem_Lsub.mpr ⟨hj, by rw [map_nsmul, hαP, smul_zero]⟩)
  have hbmem : bar X t α ∈ rationalHomSet Ω X X :=
    CMGlue.sub_mem h195 h580 X X (CMGlue.zsmul_mem h195 h580 X X (id_mem_rationalHomSet Ω X) t) hα
  have hker : ∀ P : X.toAffine.Point, ((p ^ n : ℕ) : ℤ) • P = 0 → bar X t α P = 0 := by
    intro P hP
    have hP' : p ^ n • P = 0 := by rwa [natCast_zsmul] at hP
    apply hinj n
    · rw [← map_nsmul, hP', map_zero]
    · rw [comp_bar_apply hch]; push_cast at hP; exact hP
  have hN : ((p ^ n : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  obtain ⟨γ₀, hγ₀, hγeq⟩ := h625 Ω X X hN hbmem hker
  let γ : X.toAffine.Point →+ X.toAffine.Point := γ₀
  have hγ : γ ∈ rationalHomSet Ω X X := hγ₀
  have hγP : ∀ P : X.toAffine.Point, bar X t α P = ((p ^ n : ℕ) : ℤ) • γ P := hγeq
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  have h1 : α.comp γ = AddMonoidHom.id X.toAffine.Point := by
    apply eq_of_nsmul ha78 h195 h580 X X (hfe3 Ω X X X hγ hα) (id_mem_rationalHomSet Ω X) (p ^ n) hpos
    intro P
    show p ^ n • α (γ P) = p ^ n • P
    rw [← map_nsmul, ← natCast_zsmul, ← hγP, comp_bar_apply hch, ← natCast_zsmul, Nat.cast_pow]
  have h2 : γ.comp α = AddMonoidHom.id X.toAffine.Point := by
    apply eq_of_nsmul ha78 h195 h580 X X (hfe3 Ω X X X hα hγ) (id_mem_rationalHomSet Ω X) (p ^ n) hpos
    intro P
    show p ^ n • γ (α P) = p ^ n • P
    rw [← natCast_zsmul, ← hγP, bar_comp_apply hch, ← natCast_zsmul, Nat.cast_pow]
  let αE : AddMonoid.End X.toAffine.Point := α
  let γE : AddMonoid.End X.toAffine.Point := γ
  have hαγ : αE * γE = 1 := h1
  have hγα : γE * αE = 1 := h2
  have hαγm : ∀ m : ℕ, αE ^ m * γE ^ m = 1 := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_mul]
    | succ m ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc αE, hαγ, one_mul, ih]
  have hγαm : ∀ m : ℕ, γE ^ m * αE ^ m = 1 := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_mul]
    | succ m ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc γE, hγα, one_mul, ih]
  have hfin := h976 Ω X
  have hf : ∀ m : ℕ, (αE ^ m : X.toAffine.Point →+ X.toAffine.Point) ∈ {u : (X.baseChange Ω).toAffine.Point →+
      (X.baseChange Ω).toAffine.Point | u ∈ rationalHomSet Ω X X ∧ ∃ v ∈ rationalHomSet Ω X X,
        u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _} :=
    fun m => ⟨CMGlue.pow_mem hfe3 X hα m, γE ^ m, CMGlue.pow_mem hfe3 X hγ m, hαγm m, hγαm m⟩
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun m : ℕ => (αE ^ m : X.toAffine.Point →+ X.toAffine.Point)) hf hfin
  have heq' : αE ^ a = αE ^ b := heq
  have hone : αE ^ (b - a) = 1 := by
    calc αE ^ (b - a) = (γE ^ a * αE ^ a) * αE ^ (b - a) := by rw [hγαm a, one_mul]
      _ = γE ^ a * αE ^ b := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
      _ = γE ^ a * αE ^ a := by rw [← heq']
      _ = 1 := hγαm a
  apply hinf (b - a) (Nat.sub_pos_of_lt hab)
  show (⇑αE)^[b - a] = id
  rw [← AddMonoid.End.coe_pow, hone, AddMonoid.End.coe_one]

/-- **S3.** `#L(α) = p` when both lines are nonzero. -/
theorem card_L {p : ℕ} (hp : p.Prime) {X : WeierstrassCurve Ω} [X.IsElliptic] {t q : ℤ}
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) (ht : ¬ (p : ℤ) ∣ t) {α : X.toAffine.Point →+ X.toAffine.Point}
    (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α)
    (hα0 : ∃ P : X.toAffine.Point, P ≠ 0 ∧ P ∈ Lsub X p α)
    (hb0 : ∃ P : X.toAffine.Point, P ≠ 0 ∧ P ∈ Lsub X p (bar X t α)) :
    Nat.card (Lsub X p α) = p := by
  obtain ⟨d, u, hdu⟩ := exists_inv p hp ht
  let f : Lsub X p α × Lsub X p (bar X t α) → RPLib.Torsion.tors X p := fun ab =>
    ⟨(ab.1 : X.toAffine.Point) + ab.2, RPLib.Torsion.mem_tors.mpr (by
      rw [nsmul_add, (mem_Lsub.mp ab.1.2).1, (mem_Lsub.mp ab.2.2).1, add_zero])⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have hs : (a : X.toAffine.Point) + b = a' + b' := congrArg Subtype.val h
      have h0 : (a : X.toAffine.Point) - a' ∈ Lsub X p α := AddSubgroup.sub_mem _ a.2 a'.2
      have h1e : (a : X.toAffine.Point) - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add, hs, add_comm]
      have h1 : (a : X.toAffine.Point) - a' ∈ Lsub X p (bar X t α) := by
        rw [h1e]; exact AddSubgroup.sub_mem _ b'.2 b.2
      have hz := inter_eq_zero p hdu h0 h1
      have ha : a = a' := Subtype.ext (sub_eq_zero.mp hz)
      have hb : b = b' := Subtype.ext ((sub_eq_zero.mp (h1e ▸ hz)).symm)
      rw [ha, hb]
    · rintro ⟨P, hP⟩
      have hP' : p • P = 0 := RPLib.Torsion.mem_tors.mp hP
      exact ⟨(⟨_, split_mem₀ p hch hq d hP'⟩, ⟨_, split_mem₁ p hch hq d hP'⟩),
        Subtype.ext (split_p p hdu hP').symm⟩
  have hc := Nat.card_congr (Equiv.ofBijective f hbij)
  rw [Nat.card_prod, RPLib.Torsion.card_tors (W := X) p (Nat.cast_ne_zero.mpr hp.ne_zero)] at hc
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have : Finite (Lsub X p α) := Nat.finite_of_card_ne_zero (fun h => hp2 (by rw [← hc, h, zero_mul]))
  haveI : Finite (Lsub X p (bar X t α)) :=
    Nat.finite_of_card_ne_zero (fun h => hp2 (by rw [← hc, h, mul_zero]))
  have h1 : 1 < Nat.card (Lsub X p α) := by
    obtain ⟨P, hP0, hP⟩ := hα0
    exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨P, hP⟩, 0, fun h => hP0 (congrArg Subtype.val h)⟩⟩
  have h1' : 1 < Nat.card (Lsub X p (bar X t α)) := by
    obtain ⟨P, hP0, hP⟩ := hb0
    exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨P, hP⟩, 0, fun h => hP0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hc)
  interval_cases i
  · rw [hieq, pow_zero] at h1; exact absurd h1 (lt_irrefl 1)
  · rw [hieq, pow_one]
  · rw [hieq] at hc
    have : Nat.card (Lsub X p (bar X t α)) = 1 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (hc.trans (mul_one _).symm)
    omega

/-- **S3'.** `L(α)` is a line: every element is a multiple of any nonzero one. -/
theorem L_zmultiples {p : ℕ} [Fact p.Prime] {X : WeierstrassCurve Ω} {α : X.toAffine.Point →+ X.toAffine.Point}
    (hcard : Nat.card (Lsub X p α) = p) {Y : X.toAffine.Point} (hY0 : Y ≠ 0) (hY : Y ∈ Lsub X p α)
    {Z : X.toAffine.Point} (hZ : Z ∈ Lsub X p α) : ∃ k : ℤ, k • Y = Z := by
  haveI : Finite (Lsub X p α) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).ne_zero)
  have hord : addOrderOf Y = p := addOrderOf_eq_prime (mem_Lsub.mp hY).1 hY0
  have hle : AddSubgroup.zmultiples Y ≤ Lsub X p α := AddSubgroup.zmultiples_le.mpr hY
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zmultiples, hord])
  rw [← heq] at hZ
  exact AddSubgroup.mem_zmultiples_iff.mp hZ

end RPLib.S4T.PrimeToP


