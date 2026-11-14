-- Prove2me | Definitions.Def_RPLib_S2_WeilPairing
-- name    : RPLib_S2_WeilPairing
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:06:54.790327+00:00
-- url     : https://prove2.me/theorems/8aca8088-bb73-4cec-ba7d-90507d36d684
-- title:
--   The Weil pairing on $E[n]$ and $\det(\text{Frobenius} \mid E[n]) = q$
-- statement:
--   For $E$ elliptic over $k$, $L \supseteq k$ algebraically closed and $n$ invertible: $e_n : E[n] \times E[n] \to \mu_n(L)$ is bimultiplicative, alternating, nondegenerate and Galois equivariant. For $k = \mathbb{F}_q$ the $q$-power Frobenius acts on $E[n]$ with determinant $q$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Section III.8 and Proposition V.2.3

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingJ
import Definitions.Def_RPLib_S2_WeilPairingK
import Definitions.Def_RPLib_S2_EllFq

/-!
# The Weil pairing on `E[n]` and `det (Frobenius | E[n]) = q` (unit S2-WeilPairing, goal file)

For `W` elliptic over `k`, `L ⊇ k` algebraically closed and `(n : L) ≠ 0`, `ePair W L n` (built in
`WeilPairingF` from functions with prescribed divisors, via Mathlib's class group of the coordinate
ring) is a pairing `E[n] × E[n] → μ_n(L)` that is
* bimultiplicative (`ePair_add_left`, `ePair_add_right`), with values in `μ_n` (`ePair_pow`);
* alternating (`ePair_self`) and nondegenerate (`ePair_nondeg_left`, `ePair_nondeg_right`);
* equivariant for every `σ : L ≃ₐ[k] L` (`ePair_sig`); with `L = k̄` these automorphisms restrict
  onto `Gal(k^sep/k)`, and the values are separable over `k` (`isSeparable_ePair`).
For `k = F` finite with `q` elements: `e(πS, πT) = e(S,T)^q` (`ePair_frob`), and the determinant
of Frobenius on `E[n] ≅ (ℤ/n)²` is `q` (`det_frobTors`), via the pure-algebra lemma
`det_eq_of_pairing` (`WeilPairingK`).
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.Weil

section Separable

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

/-- The values of the Weil pairing are separable over `k` (roots of `X^n - 1`, `n ≠ 0` in `k`). -/
theorem isSeparable_ePair {n : ℕ} (hnk : (n : k) ≠ 0) {S T : Pt W L} (hS : n • S = 0)
    (hT : n • T = 0) : IsSeparable k (ePair W L n S T) := by
  have hn : (n : L) ≠ 0 := by
    rw [← map_natCast (algebraMap k L)]
    exact (map_ne_zero_iff _ (algebraMap k L).injective).mpr hnk
  have hsep : (X ^ n - C (1 : k)).Separable := separable_X_pow_sub_C 1 hnk one_ne_zero
  have hroot : aeval (ePair W L n S T) (X ^ n - C (1 : k)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, ePair_pow hn hS hT, sub_self]
  exact hsep.of_dvd (minpoly.dvd k _ hroot)

end Separable

section Frobenius

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  (L : Type*) [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

/-- The `q`-power Frobenius of `L` as an automorphism (`L` is perfect). -/
noncomputable def frobAut : L ≃ₐ[F] L :=
  AlgEquiv.ofBijective (FiniteField.frobeniusAlgHom F L)
    ⟨RingHom.injective (FiniteField.frobeniusAlgHom F L).toRingHom, fun y => by
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (Fintype.card_pos (α := F))
      exact ⟨x, by rw [FiniteField.coe_frobeniusAlgHom]; exact hx⟩⟩

lemma frobAut_apply (x : L) : frobAut (F := F) L x = x ^ Fintype.card F := rfl

lemma frob_eq_ptMap (P : Pt W L) : RPLib.EllFq.frob W L P = ptMap (frobAut L) P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

variable {L}

/-- `e_n(πS, πT) = e_n(S, T)^q` for the `q`-power Frobenius `π` of `RPLib.EllFq`. -/
theorem ePair_frob {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0) (hT : n • T = 0) :
    ePair W L n (RPLib.EllFq.frob W L S) (RPLib.EllFq.frob W L T) =
      ePair W L n S T ^ Fintype.card F := by
  rw [frob_eq_ptMap, frob_eq_ptMap, ePair_sig (frobAut L) hn hS hT, frobAut_apply]

variable (W L)

/-- `E[n]` is a `ℤ/n`-module (use as a local instance). -/
noncomputable def torsModule (n : ℕ) [NeZero n] :
    Module (ZMod n) (RPLib.Torsion.tors (W.baseChange L) n) :=
  AddCommGroup.zmodModule (fun P => Subtype.ext (RPLib.Torsion.mem_tors.mp P.2))

attribute [local instance] torsModule

lemma frob_mem_tors (n : ℕ) {P : Pt W L} (hP : n • P = 0) : n • RPLib.EllFq.frob W L P = 0 := by
  rw [← map_nsmul, hP, map_zero]

/-- Frobenius on `E[n]` as an additive map. -/
noncomputable def frobTorsHom (n : ℕ) :
    RPLib.Torsion.tors (W.baseChange L) n →+ RPLib.Torsion.tors (W.baseChange L) n where
  toFun P := ⟨RPLib.EllFq.frob W L P, frob_mem_tors W L n (RPLib.Torsion.mem_tors.mp P.2)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ (P : Pt W L) Q)

/-- Frobenius on `E[n]` as a `ℤ/n`-linear map. -/
noncomputable def frobTors (n : ℕ) [NeZero n] :
    RPLib.Torsion.tors (W.baseChange L) n →ₗ[ZMod n] RPLib.Torsion.tors (W.baseChange L) n :=
  (frobTorsHom W L n).toZModLinearMap n

lemma frobTors_apply (n : ℕ) [NeZero n] (P : RPLib.Torsion.tors (W.baseChange L) n) :
    ((frobTors W L n P : RPLib.Torsion.tors (W.baseChange L) n) : Pt W L) =
      RPLib.EllFq.frob W L P := rfl

/-- **`det (π | E[n]) = q`** in `ℤ/n`, for `(n : L) ≠ 0`. -/
theorem det_frobTors (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.det (frobTors W L n) = (Fintype.card F : ZMod n) := by
  obtain ⟨e⟩ := RPLib.Torsion.tors_equiv (W := W.baseChange L) n hn
  let eL := e.toLinearEquiv (ZMod.map_smul (n := n) e)
  let b := (Module.Basis.finTwoProd (ZMod n)).map eL.symm
  have mem : ∀ P : RPLib.Torsion.tors (W.baseChange L) n, n • (P : Pt W L) = 0 :=
    fun P => RPLib.Torsion.mem_tors.mp P.2
  refine det_eq_of_pairing
    (fun P Q : RPLib.Torsion.tors (W.baseChange L) n =>
      Units.mk0 (ePair W L n P Q) (ePair_ne_zero hn (mem P) (mem Q))) ?_ ?_ ?_ ?_ b _ _ ?_
  · intro P P' Q
    ext
    simp only [Units.val_mk0, Units.val_mul, AddSubgroup.coe_add]
    exact ePair_add_left hn (mem P) (mem P') (mem Q)
  · intro P Q Q'
    ext
    simp only [Units.val_mk0, Units.val_mul, AddSubgroup.coe_add]
    exact ePair_add_right hn (mem P) (mem Q) (mem Q')
  · intro P
    ext
    simp only [Units.val_mk0, Units.val_one]
    exact ePair_self hn (mem P)
  · intro Q hQ
    apply Subtype.ext
    apply ePair_nondeg_right hn (mem Q)
    intro S hS
    have h := congrArg Units.val (hQ ⟨S, RPLib.Torsion.mem_tors.mpr hS⟩)
    simpa only [Units.val_mk0, Units.val_one] using h
  · intro P Q
    ext
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val]
    exact ePair_frob hn (mem P) (mem Q)

end Frobenius

end RPLib.Weil


