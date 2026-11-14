-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingK
-- name    : RPLib_S2_WeilPairingK
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:50:38.766976+00:00
-- url     : https://prove2.me/theorems/cf682de6-aa45-4c13-bdfc-d248d3f50cdc
-- title:
--   Determinants from an alternating nondegenerate pairing
-- statement:
--   If $e$ is a bimultiplicative, alternating, nondegenerate pairing on a free $\mathbb{Z}/n$-module $G$ of rank 2 and $A$ is linear with $e(AP, AQ) = e(P,Q)^d$, then $\det A = d$ in $\mathbb{Z}/n$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Proposition III.8.6

import Mathlib

/-!
# WPK: determinant from an alternating nondegenerate pairing (unit S2-WeilPairing, O10 part 1)

Pure algebra, Mathlib only. If `e : G → G → M` (`G` a free `ZMod n`-module of rank 2, `M` a
commutative group) is bimultiplicative, alternating and nondegenerate, and `A` is `ZMod n`-linear
with `e (A P) (A Q) = e P Q ^ d`, then `det A = d`.
-/

set_option autoImplicit false

namespace RPLib.Weil

section DetLemma

variable {n : ℕ} [NeZero n] {G : Type*} [AddCommGroup G] [Module (ZMod n) G]
  {M : Type*} [CommGroup M]

lemma pe_zero_left (e : G → G → M) (hadd_l : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q) (Q : G) :
    e 0 Q = 1 := by
  have h := hadd_l 0 0 Q
  rw [add_zero] at h
  calc e 0 Q = e 0 Q * e 0 Q * (e 0 Q)⁻¹ := by rw [mul_inv_cancel_right]
    _ = 1 := by rw [← h, mul_inv_cancel]

lemma pe_zero_right (e : G → G → M) (hadd_r : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q') (P : G) :
    e P 0 = 1 := by
  have h := hadd_r P 0 0
  rw [add_zero] at h
  calc e P 0 = e P 0 * e P 0 * (e P 0)⁻¹ := by rw [mul_inv_cancel_right]
    _ = 1 := by rw [← h, mul_inv_cancel]

lemma pe_nsmul_left (e : G → G → M) (hadd_l : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q)
    (m : ℕ) (P Q : G) : e (m • P) Q = e P Q ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, pe_zero_left e hadd_l]
  | succ m ih => rw [succ_nsmul, hadd_l, ih, pow_succ]

lemma pe_nsmul_right (e : G → G → M) (hadd_r : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q')
    (m : ℕ) (P Q : G) : e P (m • Q) = e P Q ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, pe_zero_right e hadd_r]
  | succ m ih => rw [succ_nsmul, hadd_r, ih, pow_succ]

lemma pe_smul_left (e : G → G → M) (hadd_l : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q)
    (x : ZMod n) (P Q : G) : e (x • P) Q = e P Q ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul (ZMod n)]
  exact pe_nsmul_left e hadd_l _ P Q

lemma pe_smul_right (e : G → G → M) (hadd_r : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q')
    (x : ZMod n) (P Q : G) : e P (x • Q) = e P Q ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x, Nat.cast_smul_eq_nsmul (ZMod n)]
  exact pe_nsmul_right e hadd_r _ P Q

lemma pe_swap (e : G → G → M) (hadd_l : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q)
    (hadd_r : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q') (hself : ∀ P, e P P = 1) (P Q : G) :
    e Q P = (e P Q)⁻¹ := by
  have h := hself (P + Q)
  rw [hadd_l, hadd_r, hadd_r, hself P, hself Q, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **Determinant from a pairing.** -/
theorem det_eq_of_pairing (e : G → G → M)
    (hadd_l : ∀ P P' Q, e (P + P') Q = e P Q * e P' Q)
    (hadd_r : ∀ P Q Q', e P (Q + Q') = e P Q * e P Q')
    (hself : ∀ P, e P P = 1) (hnd : ∀ Q, (∀ P, e P Q = 1) → Q = 0)
    (b : Module.Basis (Fin 2) (ZMod n) G) (A : G →ₗ[ZMod n] G) (d : ℕ)
    (hA : ∀ P Q, e (A P) (A Q) = e P Q ^ d) : LinearMap.det A = (d : ZMod n) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : M, ζ = e (b 0) (b 1) := ⟨_, rfl⟩
  have hsl := pe_smul_left (n := n) e hadd_l
  have hsr := pe_smul_right (n := n) e hadd_r
  have hsk := pe_swap e hadd_l hadd_r hself
  have hζn : ζ ^ n = 1 := by
    rw [hζ, ← pe_nsmul_left e hadd_l, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self,
      zero_smul, pe_zero_left e hadd_l]
  have hpow : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => by
    conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hζn, one_pow, one_mul]
  have hφadd : ∀ x y : ZMod n, ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := fun x y => by
    rw [ZMod.val_add, hpow, pow_add]
  have hφmul : ∀ x y : ZMod n, ζ ^ (x * y).val = ζ ^ (x.val * y.val) := fun x y => by
    rw [ZMod.val_mul, hpow]
  have hneg : ∀ x : ZMod n, ζ ^ (-x).val = (ζ ^ x.val)⁻¹ := fun x => by
    have h := hφadd x (-x)
    rw [add_neg_cancel, ZMod.val_zero, pow_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hrepr : ∀ P : G, P = b.repr P 0 • b 0 + b.repr P 1 • b 1 := fun P => by
    conv_lhs => rw [← b.sum_repr P]
    rw [Fin.sum_univ_two]
  have hkey : ∀ x : ZMod n, ζ ^ x.val = 1 → x = 0 := by
    intro x hx
    have h0 : x • b 1 = 0 := hnd _ (fun P => by
      rw [hrepr P, hadd_l, hsl, hsl, hsr, hsr, hself, ← hζ, hx]
      simp)
    have h1 := congrArg (fun v => b.repr v 1) h0
    simpa using h1
  have hinj : ∀ x y : ZMod n, ζ ^ x.val = ζ ^ y.val → x = y := fun x y hxy => by
    have h3 := hφadd (x - y) y
    rw [sub_add_cancel, hxy] at h3
    have h4 : ζ ^ (x - y).val = 1 := mul_right_cancel (h3.symm.trans (one_mul _).symm)
    exact sub_eq_zero.mp (hkey _ h4)
  have hform : ∀ a c b' d' : ZMod n,
      e (a • b 0 + c • b 1) (b' • b 0 + d' • b 1) = ζ ^ (a * d' - b' * c).val := by
    intro a c b' d'
    rw [sub_eq_add_neg, hφadd, hneg, hφmul, hφmul]
    rw [hadd_l, hadd_r, hadd_r, hsl, hsl, hsl, hsl, hsr, hsr, hsr, hsr, hself, hself,
      hsk (b 0) (b 1), ← hζ]
    simp only [one_pow, one_mul, mul_one]
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm d'.val a.val]
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  apply hinj
  rw [ZMod.val_natCast, hpow, ← hform, ← hrepr, ← hrepr, hA, hζ]

end DetLemma

end RPLib.Weil


