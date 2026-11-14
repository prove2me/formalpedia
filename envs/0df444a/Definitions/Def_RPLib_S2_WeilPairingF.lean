-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingF
-- name    : RPLib_S2_WeilPairingF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:56:47.112496+00:00
-- url     : https://prove2.me/theorems/08e68453-de63-4ad0-a190-b96d38915b69
-- title:
--   Weil pairing, part F: definition of $e_n$
-- statement:
--   For $n$ invertible, $\#E[n] = n^2$, every $T \in E[n]$ is $nT'$, the functions $g_T$ with $\mathrm{div}\, g_T = [n]^*(T) - [n]^*(O)$, and the Weil pairing $e_n(S,T)$ defined by $\tau_S g_T = e_n(S,T) g_T$, with $e_n(S,T)^n = 1$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Section III.8

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingE

/-!
# WPF: the Weil pairing, definition and first properties (unit S2-WeilPairing, O6 + O7 part 1)

* `En W L n hn` : `E[n]` as a finset, `card_En : #E[n] = n²`.
* `exists_nsmul_eq` : every `T ∈ E[n]` is `n • T'` (counting `[n] : E[n²] → E[n]`).
* `dT`, `gT` : `div g_T = [n]^*(T) - [n]^*(O)`.
* `ePair W L n S T` : `τ_S g_T = e(S,T) · g_T`; multiplicative in `S`, `e(S,T)^n = 1`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.Weil

section Pairing

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- Abel-Jacobi existence, finset form. -/
theorem exists_of_sum_eq_zero' (D : Pt W L → ℤ) (Z : Finset (Pt W L))
    (hZ : ∀ P, D P ≠ 0 → P ∈ Z) (hdeg : ∑ P ∈ Z, D P = 0) (hsum : ∑ P ∈ Z, D P • P = 0) :
    ∃ g : FF W L, g ≠ 0 ∧ ∀ P, ord W L g P = D P := by
  have hsub : (Finsupp.onFinset Z D hZ).support ⊆ Z := Finsupp.support_onFinset_subset
  have hz : ∀ x ∈ Z, x ∉ (Finsupp.onFinset Z D hZ).support → D x = 0 := fun x _ hx => by
    by_contra h
    exact hx (Finsupp.mem_support_iff.mpr (by rw [Finsupp.onFinset_apply]; exact h))
  obtain ⟨g, hg, h⟩ := exists_of_sum_eq_zero (W := W) (L := L) (Finsupp.onFinset Z D hZ)
    (by
      simp only [Finsupp.onFinset_apply]
      rw [Finset.sum_subset hsub hz]
      exact hdeg)
    (by
      simp only [Finsupp.onFinset_apply]
      rw [Finset.sum_subset hsub (fun x hx hx' => by rw [hz x hx hx', zero_smul])]
      exact hsum)
  exact ⟨g, hg, fun P => by rw [h P, Finsupp.onFinset_apply]⟩

lemma finite_En (n : ℕ) (hn : (n : L) ≠ 0) : {P : Pt W L | n • P = 0}.Finite := by
  have h := RPLib.Torsion.finite_tors (W := W.baseChange L) n hn
  exact (Set.finite_coe_iff.mp h).subset (fun P hP => hP)

variable (W L) in
/-- `E[n]` as a finset. -/
noncomputable def En (n : ℕ) (hn : (n : L) ≠ 0) : Finset (Pt W L) :=
  (finite_En (W := W) n hn).toFinset

lemma mem_En {n : ℕ} {hn : (n : L) ≠ 0} {P : Pt W L} : P ∈ En W L n hn ↔ n • P = 0 := by
  rw [En, Set.Finite.mem_toFinset]
  rfl

lemma card_En (n : ℕ) (hn : (n : L) ≠ 0) : (En W L n hn).card = n ^ 2 := by
  rw [En, ← Set.ncard_eq_toFinset_card _ (finite_En n hn), ← Nat.card_coe_set_eq]
  exact RPLib.Torsion.card_tors (W := W.baseChange L) n hn

lemma ne_zero_of_cast {n : ℕ} (hn : (n : L) ≠ 0) : n ≠ 0 := by
  rintro rfl
  exact hn Nat.cast_zero

/-- **Divisibility of `E[n]`**: every `n`-torsion point is `n` times a point. -/
lemma exists_nsmul_eq {n : ℕ} (hn : (n : L) ≠ 0) {T : Pt W L} (hT : n • T = 0) :
    ∃ T' : Pt W L, n • T' = T := by
  have hn2 : ((n * n : ℕ) : L) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hn hn
  haveI := RPLib.Torsion.finite_tors (W := W.baseChange L) n hn
  haveI := RPLib.Torsion.finite_tors (W := W.baseChange L) (n * n) hn2
  let φ : RPLib.Torsion.tors (W.baseChange L) (n * n) →+ RPLib.Torsion.tors (W.baseChange L) n :=
    { toFun := fun P => ⟨n • P.1, by
        rw [RPLib.Torsion.mem_tors, smul_smul]
        exact RPLib.Torsion.mem_tors.mp P.2⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun P Q => by
        apply Subtype.ext
        simp [nsmul_add] }
  have hker : Nat.card φ.ker = n ^ 2 := by
    rw [← RPLib.Torsion.card_tors (W := W.baseChange L) n hn,
      ← RPLib.Torsion.card_sub_tors (W := W.baseChange L) (dvd_mul_right n n)]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h
      apply Subtype.ext
      rw [AddSubgroup.coe_nsmul]
      exact congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      have h2 := congrArg Subtype.val h
      rw [AddSubgroup.coe_nsmul] at h2
      exact h2
  have hn0 : 0 < n ^ 2 := pow_pos (Nat.pos_of_ne_zero (ne_zero_of_cast hn)) 2
  have hrange : φ.range = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, hker,
      RPLib.Torsion.card_tors (W := W.baseChange L) (n * n) hn2] at h1
    rw [RPLib.Torsion.card_tors (W := W.baseChange L) n hn]
    exact Nat.eq_of_mul_eq_mul_right hn0 (by rw [← h1]; ring)
  obtain ⟨P, hP⟩ := AddMonoidHom.range_eq_top.mp hrange ⟨T, hT⟩
  exact ⟨P.1, congrArg Subtype.val hP⟩

/-- Sums over a fibre of `[n]` are sums over a coset of `E[n]`. -/
lemma sum_fiber {n : ℕ} (hn : (n : L) ≠ 0) {T T' : Pt W L} (hT' : n • T' = T)
    (Z : Finset (Pt W L)) (hZ : ∀ P, n • P = T → P ∈ Z) {A : Type*} [AddCommMonoid A]
    (φ : Pt W L → A) :
    ∑ P ∈ Z, (if n • P = T then φ P else 0) = ∑ R ∈ En W L n hn, φ (T' + R) := by
  rw [← Finset.sum_filter]
  have hfil : Z.filter (fun P => n • P = T) = (En W L n hn).image (fun R => T' + R) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_image, mem_En]
    constructor
    · rintro ⟨_, hP⟩
      exact ⟨P - T', by rw [nsmul_sub, hP, hT', sub_self], by abel⟩
    · rintro ⟨R, hR, rfl⟩
      have h : n • (T' + R) = T := by rw [nsmul_add, hT', hR, add_zero]
      exact ⟨hZ _ h, h⟩
  rw [hfil, Finset.sum_image (fun a _ b _ h => add_left_cancel h)]

variable (W L) in
/-- The divisor `D_T = [n]^*(T) - [n]^*(O)`, as a function on points. -/
def dT (n : ℕ) (T P : Pt W L) : ℤ := (if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0)

lemma dT_add {n : ℕ} {S : Pt W L} (hS : n • S = 0) (T P : Pt W L) :
    dT W L n T (P + S) = dT W L n T P := by
  simp only [dT, nsmul_add, hS, add_zero]

lemma exists_gT {n : ℕ} (hn : (n : L) ≠ 0) {T : Pt W L} (hT : n • T = 0) :
    ∃ g : FF W L, g ≠ 0 ∧ ∀ P, ord W L g P = dT W L n T P := by
  obtain ⟨T', hT'⟩ := exists_nsmul_eq hn hT
  have h00 : n • (0 : Pt W L) = 0 := smul_zero n
  let Z : Finset (Pt W L) := (En W L n hn).image (fun R => T' + R) ∪ En W L n hn
  have hZ1 : ∀ P, n • P = T → P ∈ Z := fun P hP => Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨P - T', mem_En.mpr (by rw [nsmul_sub, hP, hT', sub_self]), by abel⟩)
  have hZ0 : ∀ P : Pt W L, n • P = 0 → P ∈ Z := fun P hP => Finset.mem_union_right _ (mem_En.mpr hP)
  apply exists_of_sum_eq_zero' _ Z
  · intro P hP
    by_contra hPZ
    apply hP
    simp only [dT, if_neg (fun h => hPZ (hZ1 P h)), if_neg (fun h => hPZ (hZ0 P h)), sub_self]
  · simp only [dT, Finset.sum_sub_distrib]
    rw [show (∑ P ∈ Z, if n • P = T then (1 : ℤ) else 0) = ∑ R ∈ En W L n hn, (1 : ℤ) from
        sum_fiber hn hT' Z hZ1 (fun _ => (1 : ℤ)),
      show (∑ P ∈ Z, if n • P = 0 then (1 : ℤ) else 0) = ∑ R ∈ En W L n hn, (1 : ℤ) from
        sum_fiber hn h00 Z hZ0 (fun _ => (1 : ℤ)), sub_self]
  · simp only [dT, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul]
    rw [show (∑ P ∈ Z, if n • P = T then P else 0) = ∑ R ∈ En W L n hn, (T' + R) from
        sum_fiber hn hT' Z hZ1 (fun P => P),
      show (∑ P ∈ Z, if n • P = 0 then P else 0) = ∑ R ∈ En W L n hn, ((0 : Pt W L) + R) from
        sum_fiber hn h00 Z hZ0 (fun P => P)]
    simp only [zero_add]
    rw [Finset.sum_add_distrib, Finset.sum_const, card_En, add_sub_cancel_right, pow_two, ← smul_smul,
      hT', hT]

variable (W L) in
/-- `g_T`, a function with divisor `D_T` (and `1` when `T ∉ E[n]` or `n = 0` in `L`). -/
noncomputable def gT (n : ℕ) (T : Pt W L) : FF W L :=
  if h : (n : L) ≠ 0 ∧ n • T = 0 then (exists_gT h.1 h.2).choose else 1

lemma gT_ne_zero (n : ℕ) (T : Pt W L) : gT W L n T ≠ 0 := by
  rw [gT]
  split_ifs with h
  · exact (exists_gT h.1 h.2).choose_spec.1
  · exact one_ne_zero

lemma ord_gT {n : ℕ} (hn : (n : L) ≠ 0) {T : Pt W L} (hT : n • T = 0) (P : Pt W L) :
    ord W L (gT W L n T) P = dT W L n T P := by
  have h : (n : L) ≠ 0 ∧ n • T = 0 := ⟨hn, hT⟩
  rw [gT, dif_pos h]
  exact (exists_gT h.1 h.2).choose_spec.2 P

lemma alg_cancel {c d : L} {g : FF W L} (hg : g ≠ 0)
    (h : algebraMap L (FF W L) c * g = algebraMap L (FF W L) d * g) : c = d :=
  (algebraMap L (FF W L)).injective (mul_right_cancel₀ hg h)

lemma exists_tau_gT {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0) (hT : n • T = 0) :
    ∃ c : L, c ≠ 0 ∧ tau W L S (gT W L n T) = algebraMap L (FF W L) c * gT W L n T :=
  exists_const_of_ord_eq (tau_ne_zero S (gT_ne_zero n T)) (gT_ne_zero n T)
    (fun P _ => by rw [ord_tau, ord_gT hn hT, ord_gT hn hT, dT_add hS])

open Classical in
variable (W L) in
/-- **The Weil pairing** `e_n(S, T)`: `τ_S g_T = e_n(S,T) · g_T`. -/
noncomputable def ePair (n : ℕ) (S T : Pt W L) : L :=
  if h : ∃ c : L, tau W L S (gT W L n T) = algebraMap L (FF W L) c * gT W L n T then h.choose else 1

lemma tau_gT {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0) (hT : n • T = 0) :
    tau W L S (gT W L n T) = algebraMap L (FF W L) (ePair W L n S T) * gT W L n T := by
  have h : ∃ c : L, tau W L S (gT W L n T) = algebraMap L (FF W L) c * gT W L n T :=
    (exists_tau_gT hn hS hT).imp (fun _ hc => hc.2)
  rw [ePair, dif_pos h]
  exact h.choose_spec

lemma ePair_ne_zero {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0) (hT : n • T = 0) :
    ePair W L n S T ≠ 0 := by
  intro h0
  have h := tau_gT hn hS hT
  rw [h0, map_zero, zero_mul] at h
  exact tau_ne_zero S (gT_ne_zero n T) h

lemma ePair_zero_left {n : ℕ} (hn : (n : L) ≠ 0) {T : Pt W L} (hT : n • T = 0) :
    ePair W L n 0 T = 1 := by
  apply alg_cancel (gT_ne_zero n T)
  rw [← tau_gT hn (smul_zero n) hT, tau_zero_apply, map_one, one_mul]

lemma ePair_add_left {n : ℕ} (hn : (n : L) ≠ 0) {S₁ S₂ T : Pt W L} (hS₁ : n • S₁ = 0)
    (hS₂ : n • S₂ = 0) (hT : n • T = 0) :
    ePair W L n (S₁ + S₂) T = ePair W L n S₁ T * ePair W L n S₂ T := by
  have hS : n • (S₁ + S₂) = 0 := by rw [nsmul_add, hS₁, hS₂, add_zero]
  apply alg_cancel (gT_ne_zero n T)
  rw [← tau_gT hn hS hT, tau_add_apply, tau_gT hn hS₂ hT, map_mul, AlgEquiv.commutes,
    tau_gT hn hS₁ hT, map_mul]
  ring

lemma ePair_nsmul_left {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0)
    (hT : n • T = 0) (m : ℕ) : ePair W L n (m • S) T = ePair W L n S T ^ m := by
  induction m with
  | zero => rw [zero_smul, ePair_zero_left hn hT, pow_zero]
  | succ m ih =>
    have hm : n • (m • S) = 0 := by rw [smul_comm, hS, smul_zero]
    rw [succ_nsmul, ePair_add_left hn hm hS hT, ih, pow_succ]

/-- `e_n(S, T)` is an `n`-th root of unity. -/
lemma ePair_pow {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0) (hT : n • T = 0) :
    ePair W L n S T ^ n = 1 := by
  rw [← ePair_nsmul_left hn hS hT, hS, ePair_zero_left hn hT]

end Pairing

end RPLib.Weil


